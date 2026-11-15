using System;
using System.Collections.Generic;
using System.Globalization;
using System.Threading;
using System.Threading.Tasks;
using LibVLCSharp.Shared;
using Nuvio.Diagnostics;
using Windows.Data.Json;
using Windows.UI.Core;

namespace Nuvio.Playback
{
    // OpenRequest is defined once, in NativeMediaPlayer.cs; both engines share it.

    /// <summary>
    /// Plays streams with LibVLC for the Nuvio web app. The page sends commands through
    /// <see cref="Bridge.AppBridge"/> and gets "player.*" events back (see docs/bridge.md).
    /// </summary>
    /// <remarks>
    /// Public members must be called on the UI thread, and events are raised on it. LibVLC is only
    /// touched on a private serial worker — except MediaPlayer.Stop(), which runs on a dedicated
    /// stop thread per request (see StopPlayer): Stop() is synchronous and blocks until VLC's
    /// threads exit, so running it on the worker let one stop during Opening stall the queue
    /// forever. LibVLC must never be called from inside one of its own event callbacks; the stop
    /// thread is a plain background thread, not a callback thread.
    /// </remarks>
    internal sealed class VlcPlayer : IDisposable
    {
        private const int NetworkCachingMs = 3000;
        private const int MaxReconnects = 5;
        // How far from the end a stop has to be before it counts as a dropped connection.
        private const long EarlyEndToleranceMs = 60000;
        private const string PlaybackErrorMessage = "VLC could not play this stream.";
        private static readonly TimeSpan StartupTimeout = TimeSpan.FromSeconds(20);
        // A stop that has not returned after this long is declared dead: the
        // player is abandoned (replaced before the next play) and the stop
        // thread is left to finish on its own. 5s is far above a healthy stop
        // (the input thread exits in milliseconds once asked) and far below
        // the 35s UI open timer, so recovery never waits on it. It is a
        // diagnostic horizon only: recovery happens at StopGrace, below.
        private static readonly TimeSpan StopTimeout = TimeSpan.FromSeconds(5);
        // How long the serial worker waits for a stop before giving up on
        // the player instead. A healthy stop returns in milliseconds, so
        // 500ms is generous headroom for a loaded Xbox and still
        // imperceptible next to a seconds-long open; the queue is never
        // stalled longer than this by any single stop.
        private static readonly TimeSpan StopGrace = TimeSpan.FromMilliseconds(500);
        private static readonly TimeSpan OpenTimeout = TimeSpan.FromSeconds(30);
        private static readonly TimeSpan WatchdogTick = TimeSpan.FromSeconds(5);
        private static readonly TimeSpan VlcStatsInterval = TimeSpan.FromSeconds(2);
        private static readonly TimeSpan TimeReportInterval = TimeSpan.FromMilliseconds(250);
        private static readonly TimeSpan ReadyFallbackDelay = TimeSpan.FromSeconds(2);
        private static readonly string[] AllowedSchemes = { "http", "https", "rtsp", "rtmp", "rtp", "udp", "mms", "ftp", "smb" };

        private readonly CoreDispatcher _dispatcher;
        private readonly object _queueLock = new object();
        private Task _queue = Task.CompletedTask;
        // Logging-only diagnostic: items enqueued on the serial worker but not yet started.
        private int _queueDepth;

        // Stop-thread state. The blocking MediaPlayer.Stop() never runs on
        // the serial worker (see StopPlayer); one dedicated thread per stop
        // request runs it, and the bookkeeping below is guarded by _stopLock.
        private readonly object _stopLock = new object();
        private Task _stopTask;            // outstanding stop, else null
        private MediaPlayer _stopPlayer;   // player the outstanding stop targets
        private int _stopsInFlight;        // stop tasks issued and not yet finished
        private bool _playerPoisoned;      // current _mediaPlayer had a stop that outran StopGrace
        private bool _disposePending;      // Dispose() was called while a stop was running
        // Generation of the live MediaPlayer, bumped on every (re)creation.
        // VLC events carry the epoch they were raised under; a late event
        // from an abandoned player must never be mistaken for an event of
        // the player that replaced it (see QueueFromVlc/PostFromVlc).
        private long _playerEpoch;

        // Open-watchdog state. The watchdog runs on its own timer task and
        // reads managed fields only — never LibVLC: this class touches LibVLC
        // on its serial worker only (see the class remarks), and the watchdog
        // exists precisely for the case where that worker never runs, so it
        // must not depend on the worker or on any LibVLC call to decide.
        // _openFailedSeq holds the load seq whose terminal error was already
        // raised (or -1); it is per-generation, so a stale watchdog can never
        // poison a newer load, and no reset is needed when a load starts.
        private long _openFailedSeq = -1;
        // Last VoutCount seen on the worker; the UI-thread stats line reads
        // this field instead of calling LibVLC off the worker.
        private int _voutCount;

        // UI thread state.
        private long _loadSeq;
        private string _pageId;
        private bool _readySent;
        // First-frame gate for the video view (log 25, fix (a) part 2):
        // the view is shown only once a frame has actually been presented
        // for this load, never on vout creation or a timeout. _firstFrameShown
        // is the per-load latch; _displayedBaseline is the first
        // DisplayedPictures count observed for this load (-1 = not yet seen).
        // The baseline matters because the counters lag across reopens
        // (log 25: a stale readBytes, a frozen displayed count), so a stale
        // nonzero count must never pass as a fresh frame — only an increase
        // over the baseline proves presentation during this load.
        private bool _firstFrameShown;
        private long _displayedBaseline = -1;
        private bool _durationSent;
        private int _lastBufferingPercent = -1;
        private DateTime _lastTimeReport = DateTime.MinValue;
        private DateTime _lastVlcStatsLog = DateTime.MinValue;
        private bool _vlcBuffering;

        // Set once LibVLC has started or failed to; _libVlc, _mediaPlayer and _initError are only
        // written before that.
        private readonly ManualResetEventSlim _ready = new ManualResetEventSlim(false);
        private int _initStarted;
        private LibVLC _libVlc;
        private MediaPlayer _mediaPlayer;
        private string _initError;

        // Worker state.
        private OpenRequest _request;
        private HttpMediaInput _input;
        private int _vlcLogLines;
        private volatile bool _hasPlayed;
        private bool _inputStarted;
        private int _reconnects;
        private bool _wantPaused;
        private int _wantVolume = 100;
        private bool _wantMute;
        private float _wantRate = 1f;
        private int? _wantAudioTrack;
        private int? _wantSpuTrack;
        private long _pendingSeekMs = -1;
        private long _spuDelayUs;
        private long _audioDelayUs;
        private string _aspectMode = "fit";
        private int _viewWidth;
        private int _viewHeight;

        // Swap-chain options from the VideoView's Initialized event. They must be passed to the
        // LibVLC constructor so VLC renders into the VideoView's swap chain instead of creating
        // its own D3D11 device — on Xbox its own device fails with DXGI_ERROR_DEVICE_REMOVED
        // (hr=0x887A0005) and playback is a black screen. The options can arrive after LibVLC
        // has already started (see ApplySwapChainOptions), so the last real set is kept here.
        private readonly object _swapChainLock = new object();
        private string[] _swapChainOptions;
        private bool _swapChainOptionsApplied;
        private bool _coreInitialized;
        private bool _unavailable;
        private bool _disposed;

        // Shared between VLC callback threads, the worker and the UI thread.
        private long _workerLoadSeq;
        private long _lastTimeMs;
        private long _lengthMs;
        private int _trackRefreshQueued;

        public VlcPlayer(CoreDispatcher dispatcher)
        {
            _dispatcher = dispatcher;
        }

        /// <summary>Raised on the UI thread with an event type such as "player.time" and its payload.</summary>
        public event Action<string, JsonObject> EventRaised;

        /// <summary>Raised once LibVLC exists so the VideoView can be attached to it.</summary>
        public event Action<MediaPlayer> MediaPlayerCreated;

        /// <summary>Raised when frames of the current stream start or stop being shown.</summary>
        public event Action<bool> VideoVisibleChanged;

        /// <summary>
        /// Optional UI-thread probe supplied by the hybrid player: given this
        /// player's current MediaPlayer, describes the VideoView it should
        /// render into (actual Opacity + whether that exact player is bound).
        /// Read only on the UI thread, where LogVlcStats and MarkVideoReady
        /// run; null when no view is bound. Diagnostic only — it never
        /// changes playback, and a probe failure is logged, not thrown.
        /// </summary>
        public Func<MediaPlayer, string> ViewStateProbe { get; set; }

        /// <summary>The LibVLC version once it has started, otherwise null.</summary>
        public string Version { get; private set; }

        public void Initialize(string[] swapChainOptions)
        {
            var options = CopySwapChainOptions(swapChainOptions);
            lock (_swapChainLock)
            {
                // Prefer real options wherever they came from: EnsureVlc can call this with an
                // empty array when the VideoView has not fired Initialized yet, while
                // ApplySwapChainOptions may already have stored the real ones.
                if (options != null)
                {
                    _swapChainOptions = options;
                }
                else
                {
                    options = _swapChainOptions;
                }
            }
            if (Interlocked.Exchange(ref _initStarted, 1) == 1)
            {
                return;
            }
            // Not on the worker queue: a load that arrives first waits on the worker for this.
            Task.Run(() => CreateLibVlc(options));
        }

        /// <summary>
        /// Applies the VideoView's swap-chain options when they arrive after LibVLC has already
        /// started. Called on the UI thread (from HybridMediaPlayer.SetVlcSwapChainOptions).
        /// If LibVLC has not started yet the options are just stored for Initialize. If it
        /// started without real options and nothing is playing, LibVLC is re-created with them
        /// on the worker queue; the new MediaPlayer is published through MediaPlayerCreated so
        /// the VideoView re-attaches. If playback is active the options are only stored: tearing
        /// LibVLC down mid-stream would break the playing stream, and the re-create happens
        /// at the next Stop or Open instead (see MaybeRecreateWithSwapChainOptions).
        /// </summary>
        public void ApplySwapChainOptions(string[] options)
        {
            var copy = CopySwapChainOptions(options);
            if (copy == null || _disposed)
            {
                return;
            }
            lock (_swapChainLock)
            {
                _swapChainOptions = copy;
            }
            if (Interlocked.CompareExchange(ref _initStarted, 0, 0) == 0)
            {
                // Not started yet; Initialize picks the stored options up.
                return;
            }
            Enqueue(() => ApplySwapChainOptionsOnWorker());
        }

        // Worker. Waits out an in-flight first start (it runs on its own task, not this queue,
        // so waiting here cannot deadlock), then re-creates LibVLC only while idle.
        private void ApplySwapChainOptionsOnWorker()
        {
            if (_disposed)
            {
                return;
            }
            if (!_ready.Wait(StartupTimeout))
            {
                Log.Write("LibVLC did not finish starting; keeping the swap-chain options for the next start");
                return;
            }
            lock (_swapChainLock)
            {
                if (_swapChainOptionsApplied)
                {
                    return;
                }
            }
            if (_request != null || _hasPlayed)
            {
                Log.Write("LibVLC swap-chain options arrived while VLC is playing; keeping them for the next start");
                return;
            }
            MaybeRecreateWithSwapChainOptions();
        }

        // Worker. Re-creates LibVLC with the stored swap-chain options, if it was started
        // without them. Call only while idle: the callers in Stop/Open have already asked
        // for a stop, and this method itself refuses to run while one is still outstanding
        // (a stop thread owns the player until Stop() returns). ApplySwapChainOptionsOnWorker
        // checks for active playback itself.
        // The new MediaPlayer is published through MediaPlayerCreated (inside CreateLibVlc),
        // so the VideoView re-attaches; volume/mute/rate/track preferences live in fields
        // and are re-applied when the next stream plays.
        private void MaybeRecreateWithSwapChainOptions()
        {
            if (_disposed || _unavailable)
            {
                return;
            }
            string[] stored;
            lock (_swapChainLock)
            {
                stored = _swapChainOptions;
                if (stored == null || _swapChainOptionsApplied)
                {
                    return;
                }
            }
            Log.Write("Recreating LibVLC with the video surface swap-chain options");
            // Never dispose the player while its stop is still running: the
            // stop thread owns it until Stop() returns. The re-create is
            // deferred, not lost — the stored options are kept and the next
            // Stop or Open retries it.
            if (IsStopOutstanding())
            {
                Log.Write("LibVLC re-create deferred: a stop is still running");
                return;
            }
            if (_libVlc != null)
            {
                _libVlc.Log -= OnLibVlcLog;
            }
            _mediaPlayer?.Dispose();
            _mediaPlayer = null;
            _libVlc?.Dispose();
            _libVlc = null;
            _initError = null;
            Interlocked.Exchange(ref _vlcLogLines, 0);
            // _ready stays set and _initStarted stays 1: creation below runs synchronously on
            // this queue, so any Open queued after this sees the new instance without waiting.
            CreateLibVlc(stored);
        }

        // Runs on a worker thread: Initialize's Task.Run, or the serial worker queue for a
        // re-create (where it runs synchronously). Creates LibVLC with the given swap-chain
        // options and publishes the new MediaPlayer through MediaPlayerCreated.
        private void CreateLibVlc(string[] swapChainOptions)
        {
            var options = new List<string>(swapChainOptions ?? new string[0])
            {
                "--no-video-title-show",
                "--no-osd",
                "--no-sub-autodetect-file",
                "--http-reconnect",
                "--network-caching=" + NetworkCachingMs,
            };
            try
            {
                if (_disposed)
                {
                    return;
                }
                Log.Write("Starting LibVLC");
                if (!_coreInitialized)
                {
                    LibVLCSharp.Shared.Core.Initialize();
                    _coreInitialized = true;
                }
#if DEBUG
                _libVlc = new LibVLC(true, options.ToArray());
#else
                _libVlc = new LibVLC(false, options.ToArray());
#endif
                _mediaPlayer = new MediaPlayer(_libVlc);
                Interlocked.Increment(ref _playerEpoch);
                Subscribe(_mediaPlayer);
                _libVlc.Log += OnLibVlcLog;
                lock (_swapChainLock)
                {
                    _swapChainOptionsApplied = swapChainOptions != null && swapChainOptions.Length > 0;
                }
                Log.Write("LibVLC " + _libVlc.Version + " ready");
            }
            catch (Exception ex)
            {
                Log.Error("LibVLC failed to start", ex);
                _initError = ex.Message;
                _mediaPlayer = null;
                _libVlc = null;
                lock (_swapChainLock)
                {
                    _swapChainOptionsApplied = false;
                }
            }
            finally
            {
                _ready.Set();
            }
            var mediaPlayer = _mediaPlayer;
            if (mediaPlayer != null)
            {
                var version = _libVlc.Version;
                RunOnUi(() =>
                {
                    Version = version;
                    MediaPlayerCreated?.Invoke(mediaPlayer);
                });
            }
        }

        // Defensive copy of swap-chain options; null when there are no real options to apply.
        // Option values are never logged.
        private static string[] CopySwapChainOptions(string[] options)
        {
            if (options == null || options.Length == 0)
            {
                return null;
            }
            var copy = new string[options.Length];
            Array.Copy(options, copy, options.Length);
            return copy;
        }

        /// <summary>Marks VLC as unusable so loads fail with a message instead of waiting.</summary>
        public void SetUnavailable(string reason)
        {
            // Set even when LibVLC already started: the surface is gone, so a later
            // swap-chain re-create must not resurrect VLC against it.
            _unavailable = true;
            if (Interlocked.Exchange(ref _initStarted, 1) == 1)
            {
                return;
            }
            _initError = reason;
            _ready.Set();
        }

        public void Open(OpenRequest request)
        {
            BeginTransition();
            var seq = _loadSeq;
            _pageId = request.Id;
            if (string.IsNullOrEmpty(request.Url) || !IsAllowedUrl(request.Url))
            {
                Log.Write("Can't play " + Log.DescribeUrl(request.Url) + ": unsupported link");
                Enqueue(() =>
                {
                    StopPlayer();
                    Interlocked.Exchange(ref _workerLoadSeq, seq);
                    _request = null;
                    _hasPlayed = false;
                });
                RaiseEnded("error", "This kind of link can't be played.");
                return;
            }

            Log.Write("Open " + Log.DescribeUrl(request.Url) + (request.StartSeconds > 0 ? " at " + Math.Round(request.StartSeconds) + "s" : ""));
            RaiseState("opening", null);
            // The open watchdog is independent of the worker queue: it must
            // still fire when the queued lambda below never runs.
            _ = WatchVlcOpenAsync(seq);
            Enqueue(() =>
            {
                if (!_ready.Wait(StartupTimeout) || _mediaPlayer == null)
                {
                    ReportStartFailure(seq);
                    return;
                }
                StopPlayer();
                // A swap-chain re-create deferred while a previous stream was playing takes
                // effect here, before the new stream starts on the fresh instance.
                MaybeRecreateWithSwapChainOptions();
                if (_mediaPlayer == null)
                {
                    ReportStartFailure(seq);
                    return;
                }
                Interlocked.Exchange(ref _workerLoadSeq, seq);
                Interlocked.Exchange(ref _lengthMs, 0);
                _request = request;
                _hasPlayed = false;
                _reconnects = 0;
                _pendingSeekMs = -1;
                _wantPaused = false;
                _wantAudioTrack = null;
                _wantSpuTrack = null;
                if (!StartPlayback(request.StartSeconds))
                {
                    ReportStartFailure(seq);
                    return;
                }
            });
        }

        public void Stop()
        {
            if (_pageId != null)
            {
                Log.Write("Stop");
            }
            BeginTransition();
            _pageId = null;
            var seq = _loadSeq;
            Enqueue(() =>
            {
                Log.Write("VLC stop requested (worker)");
                StopPlayer();
                Log.Write("VLC stop done");
                Interlocked.Exchange(ref _workerLoadSeq, seq);
                _request = null;
                _hasPlayed = false;
                // A swap-chain re-create deferred while a stream was playing takes effect now
                // that playback has stopped; the next Open uses the fresh instance.
                MaybeRecreateWithSwapChainOptions();
            });
        }

        public void SetPaused(bool paused)
        {
            Enqueue(() =>
            {
                _wantPaused = paused;
                if (_hasPlayed)
                {
                    _mediaPlayer.SetPause(paused);
                }
            });
        }

        public void TogglePause()
        {
            Enqueue(() =>
            {
                _wantPaused = !_wantPaused;
                if (_hasPlayed)
                {
                    _mediaPlayer.SetPause(_wantPaused);
                }
            });
        }

        public void Seek(double seconds)
        {
            if (double.IsNaN(seconds) || seconds < 0)
            {
                return;
            }
            var ms = (long)(seconds * 1000);
            Interlocked.Exchange(ref _lastTimeMs, ms);
            Enqueue(() =>
            {
                if (_hasPlayed && _mediaPlayer.IsSeekable)
                {
                    _mediaPlayer.Time = ms;
                }
                else if (!_hasPlayed)
                {
                    _pendingSeekMs = ms;
                }
            });
        }

        public void SetVolume(int volume)
        {
            var v = Math.Max(0, Math.Min(200, volume));
            Enqueue(() =>
            {
                _wantVolume = v;
                if (_hasPlayed)
                {
                    _mediaPlayer.Volume = v;
                }
            });
        }

        public void SetMute(bool muted)
        {
            Enqueue(() =>
            {
                _wantMute = muted;
                if (_hasPlayed)
                {
                    _mediaPlayer.Mute = muted;
                }
            });
        }

        public void SetRate(double rate)
        {
            if (double.IsNaN(rate) || rate <= 0)
            {
                return;
            }
            var r = (float)Math.Min(4, rate);
            Enqueue(() =>
            {
                _wantRate = r;
                if (_hasPlayed)
                {
                    _mediaPlayer.SetRate(r);
                }
            });
        }

        /// <summary>A VLC audio track id from "player.tracks", or -1 for none.</summary>
        public void SetAudioTrack(int id)
        {
            Enqueue(() =>
            {
                _wantAudioTrack = id;
                ApplyTrackPreferences();
                QueueTrackRefresh();
            });
        }

        /// <summary>A VLC subtitle track id from "player.tracks", or -1 for none.</summary>
        public void SetSubtitleTrack(int id)
        {
            Enqueue(() =>
            {
                _wantSpuTrack = id;
                ApplyTrackPreferences();
                QueueTrackRefresh();
            });
        }

        public void SetSubtitleDelay(long ms)
        {
            var us = ms * 1000;
            Enqueue(() =>
            {
                _spuDelayUs = us;
                if (_hasPlayed)
                {
                    _mediaPlayer.SetSpuDelay(us);
                }
            });
        }

        public void SetAudioDelay(long ms)
        {
            var us = ms * 1000;
            Enqueue(() =>
            {
                _audioDelayUs = us;
                if (_hasPlayed)
                {
                    _mediaPlayer.SetAudioDelay(us);
                }
            });
        }

        /// <summary>"fit", "fill" (crop to the screen), "stretch", or a ratio such as "16:9".</summary>
        public void SetAspect(string mode)
        {
            Enqueue(() =>
            {
                _aspectMode = string.IsNullOrEmpty(mode) ? "fit" : mode;
                ApplyVideoScale();
            });
        }

        public void SetViewSize(double width, double height)
        {
            var w = (int)Math.Round(width);
            var h = (int)Math.Round(height);
            if (w <= 0 || h <= 0)
            {
                return;
            }
            Enqueue(() =>
            {
                _viewWidth = w;
                _viewHeight = h;
                ApplyVideoScale();
            });
        }

        public void Dispose()
        {
            _disposed = true;
            EventRaised = null;
            MediaPlayerCreated = null;
            VideoVisibleChanged = null;
            Enqueue(() =>
            {
                if (!StopPlayer())
                {
                    // A stop is still running: disposing the player or the
                    // instance now would block on the same stuck input thread
                    // the stop is waiting for. Defer the teardown to the stop
                    // thread (see RunStop): it disposes the player and the
                    // instance when the stop returns — or never, if it never
                    // returns, in which case the leak is bounded to this
                    // player until the process exits, and the 5s watchdog
                    // has logged it.
                    lock (_stopLock)
                    {
                        _disposePending = true;
                    }
                    Log.Write("VLC dispose deferred: a stop is still running");
                    return;
                }
                _mediaPlayer?.Dispose();
                _mediaPlayer = null;
                _libVlc?.Dispose();
                _libVlc = null;
            });
        }

        // Worker. Reports a LibVLC start failure (including a failed swap-chain re-create)
        // for the load that is waiting on it.
        private void ReportStartFailure(long seq)
        {
            Interlocked.Exchange(ref _openFailedSeq, seq);
            var message = "VLC failed to start" + (_initError != null ? ": " + _initError : " (timed out).");
            Log.Write(message);
            RunOnUi(() =>
            {
                if (seq == _loadSeq)
                {
                    RaiseEnded("error", message);
                }
            });
        }

        // Open watchdog, mirroring FfmpegPlayer.WatchOpenTimeoutAsync: progress
        // every 5 seconds, failure at 30 seconds. It runs on its own timer
        // task and reads managed fields only (_hasPlayed, _lastTimeMs, the
        // worker's load seq) — never LibVLC — so it still fires when the
        // serial worker queue is stuck and the Open lambda never runs. The
        // open is confirmed by the first tick that sees Playing with the
        // position advanced past the previous tick, exactly like FFmpeg's
        // ConfirmOpenByPlayback; _readySent ends the watch the same way
        // FFmpeg's does. A frozen position after Playing is a failed open:
        // a stream that reached Playing but never advanced proves nothing.
        private async Task WatchVlcOpenAsync(long seq)
        {
            try
            {
                var previousTimeMs = Interlocked.Read(ref _lastTimeMs);
                for (var elapsed = 5; elapsed <= (int)OpenTimeout.TotalSeconds; elapsed += 5)
                {
                    await Task.Delay(WatchdogTick).ConfigureAwait(false);
                    if (_disposed || seq != _loadSeq || _readySent || Interlocked.Read(ref _openFailedSeq) == seq)
                    {
                        return;
                    }
                    // _workerLoadSeq only becomes seq when the Open lambda
                    // reaches StartPlayback, so until then the worker has
                    // not started this load at all — and _hasPlayed /
                    // _lastTimeMs are still the previous load's. Refresh the
                    // baseline while waiting so the first tick after the
                    // worker reaches the load compares against fresh values.
                    var workerReached = Interlocked.Read(ref _workerLoadSeq) == seq;
                    var timeMs = Interlocked.Read(ref _lastTimeMs);
                    if (workerReached && _hasPlayed && timeMs > previousTimeMs)
                    {
                        Log.Write("VLC open confirmed (playing at " + Math.Round(timeMs / 1000.0) + "s after " + elapsed + "s)");
                        return;
                    }
                    previousTimeMs = timeMs;
                    if (elapsed < (int)OpenTimeout.TotalSeconds)
                    {
                        Log.Write("VLC open still waiting (" + elapsed + "s/" + (int)OpenTimeout.TotalSeconds + "s, workerReached=" + workerReached +
                            " played=" + _hasPlayed + " time=" + Math.Round(timeMs / 1000.0) + "s)");
                    }
                    else
                    {
                        FailVlcOpen(seq, "workerReached=" + workerReached + " played=" + _hasPlayed + " time=" + Math.Round(timeMs / 1000.0) + "s");
                    }
                }
            }
            catch (Exception ex)
            {
                Log.Error("VLC open watchdog failed", ex);
            }
        }

        // Fails the open through the existing VLC error signal — the same
        // "player.ended" error OnEncounteredError raises — so the hybrid
        // player and the view model handle it exactly like any other VLC
        // failure, with no new failure path: in auto mode the hybrid
        // remembers the URL in _bothFailedUrls and the view model tries the
        // next source; in forced-vlc mode nothing is remembered and the
        // view model tries the next source with VLC again. The per-seq
        // Exchange makes a second failure for the same load a no-op, and a
        // late Playing/ready for this load is suppressed by the same mark.
        // This only raises the failure: it does not stop VLC (a stop would
        // queue behind the same stuck worker, or block this thread), so a
        // stuck worker stays stuck until the queue fix lands — the open is
        // bounded and loud instead of silent and endless.
        private void FailVlcOpen(long seq, string detail)
        {
            if (Interlocked.Exchange(ref _openFailedSeq, seq) == seq)
            {
                return;
            }
            Log.Write("VLC open failed (OpenTimeout) after " + (int)OpenTimeout.TotalSeconds + "s (" + detail + ")");
            RunOnUi(() =>
            {
                if (seq == _loadSeq)
                {
                    RaiseEnded("error", PlaybackErrorMessage);
                }
            });
        }

        private void BeginTransition()
        {
            _loadSeq++;
            _readySent = false;
            _firstFrameShown = false;
            _displayedBaseline = -1;
            _durationSent = false;
            _lastBufferingPercent = -1;
            _vlcBuffering = false;
            VideoVisibleChanged?.Invoke(false);
        }

        // Worker: (re)opens the current request, resuming at startSeconds.
        // Returns false only when there is no usable player at all (the
        // player had to be replaced after an abandoned stop and the
        // replacement failed); the caller then reports a start failure.
        private bool StartPlayback(double startSeconds)
        {
            Log.Write("VLC StartPlayback entered (workerLoadSeq=" + Interlocked.Read(ref _workerLoadSeq) + ")");
            if (IsPlayerStuck() || !StopPlayer())
            {
                // A stop is still running for this player (or just outran the
                // grace): playing on it would let the late Stop() kill the new
                // stream as soon as it lands. Play on a fresh player instead;
                // the old one stays owned by its stop thread and is reclaimed
                // when Stop() returns. If the replacement fails but the stop
                // finished in the meantime, the live player is stopped and
                // usable again — play on it.
                if (!RecreatePlayer() && IsPlayerStuck())
                {
                    return false;
                }
            }
            _inputStarted = false;
            Interlocked.Exchange(ref _lastTimeMs, (long)(startSeconds * 1000));
            var options = new List<string>
            {
                ":network-caching=" + NetworkCachingMs,
                ":http-reconnect",
            };
            if (startSeconds > 0)
            {
                options.Add(":start-time=" + startSeconds.ToString("0.###", CultureInfo.InvariantCulture));
            }
            if (!_request.HardwareDecoding)
            {
                options.Add(":avcodec-hw=none");
                Log.Write("VLC hardware decoding disabled; using software decoding");
            }
            else
            {
                // Force D3D11 hardware decoding. Leaving it to VLC's default
                // left high-bitrate HEVC on slow software decoding on Xbox.
                // (The "vlc error [mem] Invalid get/release function
                // pointers" log line is unrelated benign noise from VLC
                // 3.0.16 probing the imem access module — removed upstream
                // in 2021 — not a broken input.)
                options.Add(":avcodec-hw=d3d11va");
            }
            Media media;
            // Plain files keep going through Windows' HTTP stack: VLC's own
            // HTTPS failed to open links on the Xbox, and only the Windows
            // stack sends arbitrary request headers. HLS/DASH playlists need
            // VLC to fetch the segments itself, so they stay on VLC's HTTP.
            if (UseWindowsHttp(_request.Url))
            {
                options.Add(":file-caching=" + NetworkCachingMs);
                _input = new HttpMediaInput(_request.Url, _request.Headers);
                media = new Media(_libVlc, _input, options.ToArray());
            }
            else
            {
                string value;
                if (_request.Headers.TryGetValue("User-Agent", out value))
                {
                    options.Add(":http-user-agent=" + value);
                }
                if (_request.Headers.TryGetValue("Referer", out value))
                {
                    options.Add(":http-referrer=" + value);
                }
                media = new Media(_libVlc, _request.Url, FromType.FromLocation, options.ToArray());
            }
            using (media)
            {
                var accepted = _mediaPlayer.Play(media);
                Log.Write("VLC play requested (accepted=" + accepted + " state=" + SafeState() + ")");
            }
            return true;
        }

        // Worker. Asks for playback to stop without ever blocking this
        // serial queue on VLC. _input.Abort() runs here (fast: it only
        // closes the pending response, which breaks a pending read), while
        // the blocking MediaPlayer.Stop() runs on a dedicated stop thread.
        //
        // Why a thread, not the queue: LibVLCSharp documents Stop() as
        // synchronous — "will block until all VLC threads have been joined"
        // — and a stop issued during Opening (moov parse) can therefore
        // never return. On the queue that killed every later open; on its
        // own thread it only costs one thread. Stop() is never called from
        // a VLC callback (the one deadlock the docs warn about), touches
        // no UI object, and two threads never stop the same player: issue
        // is serialised on this queue, and a second request for a player
        // that already has a stop running joins the running one.
        //
        // The queue waits at most StopGrace for the common fast stop, so a
        // new stream can still Play on the same player right after a normal
        // stop. If the stop outruns the grace, this returns false and the
        // player is poisoned: the caller must replace it (RecreatePlayer)
        // before playing, so the late Stop() can never kill the new stream.
        // Returns true when the player is stopped (or there was nothing to
        // stop), false when a stop is still in flight.
        private bool StopPlayer()
        {
            _input?.Abort();
            _voutCount = 0;
            MediaPlayer player;
            HttpMediaInput input;
            Task stopTask;
            lock (_stopLock)
            {
                player = _mediaPlayer;
                input = _input;
                _input = null;
                if (player == null)
                {
                    input?.Dispose();
                    return true;
                }
                if (_stopPlayer == player && _stopTask != null && !_stopTask.IsCompleted)
                {
                    // A stop for this same player is already running; joining
                    // it instead of calling Stop() a second time.
                    stopTask = _stopTask;
                }
                else
                {
                    var started = DateTime.UtcNow;
                    stopTask = Task.Factory.StartNew(() => RunStop(player, input, started),
                        CancellationToken.None, TaskCreationOptions.LongRunning, TaskScheduler.Default);
                    _stopPlayer = player;
                    _stopTask = stopTask;
                    _stopsInFlight++;
                    Log.Write("VLC stop requested (state=" + SafeState() + ")");
                    // Diagnostic horizon only: recovery already happened (or
                    // was refused) at StopGrace; this line just says the stop
                    // is still stuck long after any healthy stop would have
                    // returned.
                    var ignored = Task.Delay(StopTimeout).ContinueWith(_ =>
                    {
                        if (!stopTask.IsCompleted)
                        {
                            Log.Write("VLC stop still has not returned after 5s; the player is abandoned (its stop thread, input and player leak until the stop ever returns)");
                        }
                    }, TaskScheduler.Default);
                }
            }
            bool stopped;
            try
            {
                stopped = stopTask.Wait(StopGrace);
            }
            catch (Exception)
            {
                stopped = false;
            }
            if (stopped)
            {
                return true;
            }
            lock (_stopLock)
            {
                if (_mediaPlayer == player)
                {
                    _playerPoisoned = true;
                }
            }
            Log.Write("VLC stop did not return within 500ms; the player will be replaced before the next play");
            return false;
        }

        // Stop thread. Runs the one blocking call, then owns the captured
        // pair until it is safe to release: the input is disposed only after
        // Stop() returns (the input thread may still be inside it until
        // then), and the player is disposed only if it has already been
        // replaced (the live player is never disposed from here) — or if
        // Dispose() is pending and this is the last stop still running.
        private void RunStop(MediaPlayer player, HttpMediaInput input, DateTime started)
        {
            try
            {
                player.Stop();
                var elapsed = (long)(DateTime.UtcNow - started).TotalMilliseconds;
                Log.Write("VLC stop done (took " + elapsed + "ms)");
            }
            catch (Exception ex)
            {
                Log.Error("VLC stop failed", ex);
            }
            finally
            {
                try
                {
                    input?.Dispose();
                }
                catch (Exception ex)
                {
                    Log.Error("Disposing the stopped VLC input failed", ex);
                }
                MediaPlayer capturedToDispose = null;
                MediaPlayer liveToDispose = null;
                LibVLC libVlc = null;
                lock (_stopLock)
                {
                    _stopsInFlight--;
                    if (_stopPlayer == player)
                    {
                        _stopPlayer = null;
                        _stopTask = null;
                    }
                    if (_mediaPlayer == player)
                    {
                        // The stop finished for the live player: it is usable
                        // again, so clear a poison flag set while it was stuck.
                        _playerPoisoned = false;
                    }
                    else
                    {
                        // Replaced while stopping: reclaim it now that it stopped.
                        capturedToDispose = player;
                    }
                    if (_disposePending && _stopsInFlight == 0 && _mediaPlayer != null)
                    {
                        // Last stop finished and Dispose() was requested:
                        // tear the live player and the instance down here,
                        // on this thread, never on the queue.
                        liveToDispose = _mediaPlayer;
                        _mediaPlayer = null;
                        libVlc = _libVlc;
                        _libVlc = null;
                    }
                }
                if (capturedToDispose != null)
                {
                    try
                    {
                        capturedToDispose.Dispose();
                    }
                    catch (Exception ex)
                    {
                        Log.Error("Disposing the abandoned VLC player failed", ex);
                    }
                }
                if (liveToDispose != null)
                {
                    try
                    {
                        liveToDispose.Dispose();
                    }
                    catch (Exception ex)
                    {
                        Log.Error("Disposing the VLC player after a deferred stop failed", ex);
                    }
                }
                if (libVlc != null)
                {
                    try
                    {
                        libVlc.Dispose();
                    }
                    catch (Exception ex)
                    {
                        Log.Error("Disposing LibVLC after a deferred stop failed", ex);
                    }
                }
            }
        }

        // Worker. True while a stop thread still owns a player (its Stop()
        // has not returned). Callers that would dispose or replace the
        // player must defer instead.
        private bool IsStopOutstanding()
        {
            lock (_stopLock)
            {
                return _stopPlayer != null;
            }
        }

        // Worker. True while the live player cannot be played on: a stop is
        // still running for it, or a stop outran StopGrace and poisoned it.
        private bool IsPlayerStuck()
        {
            lock (_stopLock)
            {
                return _playerPoisoned || (_stopPlayer != null && _stopPlayer == _mediaPlayer);
            }
        }

        // Worker. Replaces the live MediaPlayer with a fresh one on the same
        // LibVLC instance. Used when a stop outran StopGrace: the old player
        // is still owned by its stop thread and must never be played on
        // again (its late Stop() would kill the new stream). The old player
        // is disposed by its stop thread once Stop() returns, and its late
        // events are dropped by the epoch check in QueueFromVlc/PostFromVlc.
        // The new player is published through MediaPlayerCreated so the
        // VideoView re-attaches, exactly as a LibVLC re-create does.
        // Returns false only if no replacement could be made (no instance,
        // disposed, or the player is not actually stuck); the caller must
        // then not Play at all.
        private bool RecreatePlayer()
        {
            if (_disposed || _libVlc == null || _mediaPlayer == null)
            {
                return false;
            }
            lock (_stopLock)
            {
                if (!_playerPoisoned && _stopPlayer != _mediaPlayer)
                {
                    // Nothing to recover from; never orphan a live player.
                    return false;
                }
            }
            MediaPlayer player;
            try
            {
                player = new MediaPlayer(_libVlc);
            }
            catch (Exception ex)
            {
                Log.Error("Recreating the VLC player failed", ex);
                return false;
            }
            Subscribe(player);
            _mediaPlayer = player;
            Interlocked.Increment(ref _playerEpoch);
            lock (_stopLock)
            {
                _playerPoisoned = false;
            }
            var version = _libVlc.Version;
            Log.Write("Recreated the VLC player after a stop that did not return");
            RunOnUi(() =>
            {
                Version = version;
                MediaPlayerCreated?.Invoke(player);
            });
            return true;
        }

        // Plain files go through Windows' HTTP stack. HLS and DASH playlists need VLC to fetch the
        // segments itself, so they stay on VLC's own HTTP code.
        private static bool UseWindowsHttp(string url)
        {
            Uri uri;
            if (!Uri.TryCreate(url, UriKind.Absolute, out uri) ||
                (uri.Scheme != Uri.UriSchemeHttps && uri.Scheme != Uri.UriSchemeHttp))
            {
                return false;
            }
            var path = uri.AbsolutePath;
            return !path.EndsWith(".m3u8", StringComparison.OrdinalIgnoreCase) &&
                !path.EndsWith(".m3u", StringComparison.OrdinalIgnoreCase) &&
                !path.EndsWith(".mpd", StringComparison.OrdinalIgnoreCase);
        }

        // Called on VLC threads. Only warnings and errors, and only so many, to keep the log small.
        private void OnLibVlcLog(object sender, LogEventArgs e)
        {
            try
            {
                if (e.Level < LogLevel.Warning || Interlocked.Increment(ref _vlcLogLines) > 400)
                {
                    return;
                }
                Log.Write("vlc " + e.Level.ToString().ToLowerInvariant() + " [" + e.Module + "] " + e.Message);
            }
            catch
            {
                // Never let logging break VLC's thread.
            }
        }

        private void Subscribe(MediaPlayer mediaPlayer)
        {
            mediaPlayer.Opening += (s, e) => QueueFromVlc(OnOpening);
            mediaPlayer.Playing += (s, e) => QueueFromVlc(OnPlaying);
            mediaPlayer.Paused += (s, e) => PostFromVlc(seq => OnPaused());
            mediaPlayer.Stopped += (s, e) => QueueFromVlc(OnStopped);
            mediaPlayer.Buffering += (s, e) =>
            {
                var cache = e.Cache;
                PostFromVlc(seq => OnBuffering(cache));
            };
            mediaPlayer.TimeChanged += (s, e) =>
            {
                var time = e.Time;
                Interlocked.Exchange(ref _lastTimeMs, time);
                PostFromVlc(seq => OnTimeChanged(time));
            };
            mediaPlayer.LengthChanged += (s, e) =>
            {
                var length = e.Length;
                Interlocked.Exchange(ref _lengthMs, length);
                PostFromVlc(seq => OnLengthChanged(length));
            };
            mediaPlayer.Vout += (s, e) =>
            {
                if (e.Count > 0)
                {
                    QueueFromVlc(OnVideoOutput);
                }
            };
            mediaPlayer.ESAdded += (s, e) => QueueTrackRefresh();
            mediaPlayer.ESDeleted += (s, e) => QueueTrackRefresh();
            mediaPlayer.ESSelected += (s, e) => QueueTrackRefresh();
            mediaPlayer.EndReached += (s, e) => QueueFromVlc(OnEndReached);
            mediaPlayer.EncounteredError += (s, e) => QueueFromVlc(OnEncounteredError);
        }

        // Worker. VLC's state line for the open: before this, a VLC load
        // that never reached Playing left no trace at all in the log —
        // the "Open ..." line was the last word.
        private void OnOpening(long seq)
        {
            Log.Write("VLC opening (state=" + SafeState() + ")");
        }

        // Worker.
        private void OnStopped(long seq)
        {
            Log.Write("VLC stopped (state=" + SafeState() + ")");
        }

        // The player may already be disposed when a queued callback runs;
        // never let a state read throw.
        private string SafeState()
        {
            try
            {
                var player = _mediaPlayer;
                return player == null ? "no-player" : player.State.ToString();
            }
            catch (Exception)
            {
                return "unknown";
            }
        }

        // Worker.
        private void OnPlaying(long seq)
        {
            _hasPlayed = true;
            if (!_inputStarted)
            {
                _inputStarted = true;
                Log.Write("Playing (state=" + SafeState() + ") at " + Math.Round(Interlocked.Read(ref _lastTimeMs) / 1000.0) + "s");
                if (_pendingSeekMs >= 0 && _mediaPlayer.IsSeekable)
                {
                    _mediaPlayer.Time = _pendingSeekMs;
                }
                _pendingSeekMs = -1;
                if (_spuDelayUs != 0)
                {
                    _mediaPlayer.SetSpuDelay(_spuDelayUs);
                }
                if (_audioDelayUs != 0)
                {
                    _mediaPlayer.SetAudioDelay(_audioDelayUs);
                }
                ApplyVideoScale();
            }
            _mediaPlayer.Volume = _wantVolume;
            _mediaPlayer.Mute = _wantMute;
            if (Math.Abs(_mediaPlayer.Rate - _wantRate) > 0.001f)
            {
                _mediaPlayer.SetRate(_wantRate);
            }
            if (_wantPaused)
            {
                _mediaPlayer.SetPause(true);
            }
            ApplyTrackPreferences();
            RefreshTracks(seq);

            var hasVideoOutput = _mediaPlayer.VoutCount > 0;
            _voutCount = (int)_mediaPlayer.VoutCount;
            var paused = _wantPaused;
            RunOnUi(() =>
            {
                if (seq != _loadSeq || Interlocked.Read(ref _openFailedSeq) == seq)
                {
                    return;
                }
                RaiseState(paused ? "paused" : "playing", null);
                if (hasVideoOutput)
                {
                    MarkVideoReady(seq, true);
                }
                else
                {
                    // Audio-only streams never create a video output.
                    ScheduleReadyFallback(seq);
                }
            });
        }

        // UI thread.
        private void OnPaused()
        {
            Log.Write("VLC paused at " + Math.Round(Interlocked.Read(ref _lastTimeMs) / 1000.0) + "s");
            RaiseState("paused", null);
        }

        // Worker.
        private void OnVideoOutput(long seq)
        {
            uint width = 0;
            uint height = 0;
            _mediaPlayer.Size(0, ref width, ref height);
            _voutCount = (int)_mediaPlayer.VoutCount;
            if (width > 0 && height > 0)
            {
                Log.Write("VLC video output ready (" + width + "x" + height + ")");
            }
            RunOnUi(() =>
            {
                if (seq != _loadSeq || Interlocked.Read(ref _openFailedSeq) == seq)
                {
                    return;
                }
                if (width > 0 && height > 0)
                {
                    var payload = new JsonObject();
                    payload.SetNamedValue("width", JsonValue.CreateNumberValue(width));
                    payload.SetNamedValue("height", JsonValue.CreateNumberValue(height));
                    Raise("player.video", payload);
                }
                MarkVideoReady(seq, true);
            });
        }

        // Worker.
        private void OnEndReached(long seq)
        {
            // VLC reports a dropped HTTP connection as a normal end of stream. If that happens well
            // before the end, pick the stream back up where it stopped instead of ending playback.
            var length = Interlocked.Read(ref _lengthMs);
            var time = Interlocked.Read(ref _lastTimeMs);
            if (_hasPlayed && length > 0 && time + EarlyEndToleranceMs < length && TryReconnect(time / 1000.0))
            {
                return;
            }
            // A stream that ends before it ever played failed to open; reporting it as finished
            // would make the app move on to the next episode.
            var failedToOpen = !_hasPlayed;
            if (failedToOpen)
            {
                Interlocked.Exchange(ref _openFailedSeq, seq);
            }
            Log.Write(failedToOpen ? "Stream ended before it played (state=" + SafeState() + ")" : "Stream finished");
            RunOnUi(() =>
            {
                if (seq == _loadSeq)
                {
                    RaiseEnded(failedToOpen ? "error" : "eof", failedToOpen ? PlaybackErrorMessage : null);
                }
            });
        }

        // Worker.
        private void OnEncounteredError(long seq)
        {
            var length = Interlocked.Read(ref _lengthMs);
            var time = Interlocked.Read(ref _lastTimeMs);
            if (_hasPlayed && TryReconnect(length > 0 ? time / 1000.0 : 0))
            {
                return;
            }
            Interlocked.Exchange(ref _openFailedSeq, seq);
            Log.Write("VLC could not play the stream (state=" + SafeState() + ") at " + Math.Round(Interlocked.Read(ref _lastTimeMs) / 1000.0) + "s");
            RunOnUi(() =>
            {
                if (seq == _loadSeq)
                {
                    RaiseEnded("error", PlaybackErrorMessage);
                }
            });
        }

        // Worker.
        private bool TryReconnect(double resumeSeconds)
        {
            if (_request == null || _reconnects >= MaxReconnects)
            {
                return false;
            }
            _reconnects++;
            Log.Write("Stream dropped, reconnecting at " + Math.Round(resumeSeconds) + "s (attempt " + _reconnects + ")");
            var seq = Interlocked.Read(ref _workerLoadSeq);
            RunOnUi(() =>
            {
                if (seq == _loadSeq)
                {
                    RaiseState("buffering", null);
                }
            });
            // A reconnect that cannot play (no usable player) reports the
            // failure instead of claiming a reconnect happened.
            return StartPlayback(resumeSeconds);
        }

        // Worker.
        private void ApplyTrackPreferences()
        {
            if (_mediaPlayer == null || !_hasPlayed)
            {
                return;
            }
            if (_wantAudioTrack.HasValue && _mediaPlayer.AudioTrack != _wantAudioTrack.Value)
            {
                _mediaPlayer.SetAudioTrack(_wantAudioTrack.Value);
            }
            if (_wantSpuTrack.HasValue && _mediaPlayer.Spu != _wantSpuTrack.Value)
            {
                _mediaPlayer.SetSpu(_wantSpuTrack.Value);
            }
        }

        // Worker. "fill" crops the picture to the screen, "stretch" distorts it to the screen and a
        // ratio forces that shape; "fit" lets VLC letterbox.
        private void ApplyVideoScale()
        {
            if (_mediaPlayer == null)
            {
                return;
            }
            var viewAspect = _viewWidth > 0 && _viewHeight > 0 ? _viewWidth + ":" + _viewHeight : null;
            switch (_aspectMode)
            {
                case "fill":
                    _mediaPlayer.AspectRatio = null;
                    _mediaPlayer.CropGeometry = viewAspect;
                    break;
                case "stretch":
                    _mediaPlayer.CropGeometry = null;
                    _mediaPlayer.AspectRatio = viewAspect;
                    break;
                case "fit":
                    _mediaPlayer.AspectRatio = null;
                    _mediaPlayer.CropGeometry = null;
                    break;
                default:
                    _mediaPlayer.CropGeometry = null;
                    _mediaPlayer.AspectRatio = _aspectMode.Contains(":") ? _aspectMode : null;
                    break;
            }
        }

        private void QueueTrackRefresh()
        {
            // A file with many tracks raises a burst of ES events; refresh once per burst.
            if (Interlocked.Exchange(ref _trackRefreshQueued, 1) == 1)
            {
                return;
            }
            var epoch = Interlocked.Read(ref _playerEpoch);
            Enqueue(() =>
            {
                Interlocked.Exchange(ref _trackRefreshQueued, 0);
                if (epoch != Interlocked.Read(ref _playerEpoch) || _mediaPlayer == null || _request == null)
                {
                    return;
                }
                ApplyTrackPreferences();
                RefreshTracks(Interlocked.Read(ref _workerLoadSeq));
            });
        }

        // Worker. Track ids are VLC's own ES ids; -1 means none.
        private void RefreshTracks(long seq)
        {
            MediaTrack[] mediaTracks;
            using (var media = _mediaPlayer.Media)
            {
                mediaTracks = media != null ? media.Tracks : new MediaTrack[0];
            }
            var currentAudio = _mediaPlayer.AudioTrack;
            var currentSpu = _mediaPlayer.Spu;
            var audio = TracksToJson(_mediaPlayer.AudioTrackDescription, mediaTracks, TrackType.Audio, currentAudio);
            var subtitles = TracksToJson(_mediaPlayer.SpuDescription, mediaTracks, TrackType.Text, currentSpu);

            RunOnUi(() =>
            {
                if (seq != _loadSeq)
                {
                    return;
                }
                var payload = new JsonObject();
                payload.SetNamedValue("audio", audio);
                payload.SetNamedValue("subtitles", subtitles);
                payload.SetNamedValue("audioId", JsonValue.CreateNumberValue(currentAudio));
                payload.SetNamedValue("subtitleId", JsonValue.CreateNumberValue(currentSpu));
                Raise("player.tracks", payload);
            });
        }

        private static JsonArray TracksToJson(LibVLCSharp.Shared.Structures.TrackDescription[] descriptions,
            MediaTrack[] mediaTracks, TrackType trackType, int selectedId)
        {
            var array = new JsonArray();
            if (descriptions == null)
            {
                return array;
            }
            foreach (var description in descriptions)
            {
                if (description.Id < 0)
                {
                    continue; // "Disable"
                }
                var item = new JsonObject();
                item.SetNamedValue("id", JsonValue.CreateNumberValue(description.Id));
                item.SetNamedValue("name", JsonValue.CreateStringValue(description.Name ?? string.Empty));
                item.SetNamedValue("selected", JsonValue.CreateBooleanValue(description.Id == selectedId));
                foreach (var mediaTrack in mediaTracks)
                {
                    if (mediaTrack.Id != description.Id || mediaTrack.TrackType != trackType)
                    {
                        continue;
                    }
                    if (!string.IsNullOrEmpty(mediaTrack.Language))
                    {
                        item.SetNamedValue("lang", JsonValue.CreateStringValue(mediaTrack.Language));
                    }
                    if (!string.IsNullOrEmpty(mediaTrack.Description))
                    {
                        item.SetNamedValue("title", JsonValue.CreateStringValue(mediaTrack.Description));
                    }
                    var codec = FourCcToString(mediaTrack.Codec);
                    if (codec != null)
                    {
                        item.SetNamedValue("codec", JsonValue.CreateStringValue(codec));
                    }
                    break;
                }
                array.Add(item);
            }
            return array;
        }

        private void OnBuffering(float cache)
        {
            var percent = (int)Math.Round(cache);
            var previous = _lastBufferingPercent;
            if (percent == previous)
            {
                return;
            }
            _lastBufferingPercent = percent;
            // Startup buffering (before the first Playing) is covered by
            // the Opening/Playing lines; a dip mid-playback is the stall
            // signal the log was missing.
            if (_hasPlayed && percent < 100 && !_vlcBuffering)
            {
                _vlcBuffering = true;
                Log.Write("VLC buffering started (cache=" + percent + "%) at " + Math.Round(Interlocked.Read(ref _lastTimeMs) / 1000.0) + "s");
            }
            else if (_vlcBuffering && percent == 100)
            {
                _vlcBuffering = false;
                Log.Write("VLC buffering ended at " + Math.Round(Interlocked.Read(ref _lastTimeMs) / 1000.0) + "s");
            }
            var payload = new JsonObject();
            payload.SetNamedValue("percent", JsonValue.CreateNumberValue(percent));
            Raise("player.buffering", payload);
        }

        private void OnLengthChanged(long lengthMs)
        {
            // VLC sometimes refines the length after its first estimate; the first is good enough
            // and keeps the seek bar from jumping.
            if (_durationSent || lengthMs <= 0)
            {
                return;
            }
            _durationSent = true;
            var payload = new JsonObject();
            payload.SetNamedValue("duration", JsonValue.CreateNumberValue(lengthMs / 1000.0));
            Raise("player.duration", payload);
        }

        private void OnTimeChanged(long timeMs)
        {
            var now = DateTime.UtcNow;
            if (now - _lastTimeReport < TimeReportInterval)
            {
                return;
            }
            _lastTimeReport = now;
            var payload = new JsonObject();
            payload.SetNamedValue("time", JsonValue.CreateNumberValue(Math.Max(0, timeMs) / 1000.0));
            payload.SetNamedValue("duration", JsonValue.CreateNumberValue(Math.Max(0, Interlocked.Read(ref _lengthMs)) / 1000.0));
            Raise("player.time", payload);
            // Periodic proof the decoder is still producing frames: VLC's
            // own counters (decoded/displayed/lost pictures, lost audio
            // buffers, bitrates) come from Media.Statistics. A heartbeat
            // that stops arriving while Playing means time itself froze.
            // 2 seconds while Playing, not 10: the decoded-vs-displayed
            // gap is the second defect's signal, and a 10-second cadence
            // leaves a short playback with one sample or none.
            if (_hasPlayed && now - _lastVlcStatsLog >= VlcStatsInterval)
            {
                _lastVlcStatsLog = now;
                LogVlcStats(timeMs);
            }
            // First presented frame, not first stats line: the view is shown
            // from here (see CheckFirstFramePresented), at most once per
            // 250ms tick, so the show lags the first presented frame by
            // about one tick.
            if (!_firstFrameShown && _hasPlayed && _voutCount > 0)
            {
                CheckFirstFramePresented(seq: _loadSeq);
            }
        }

        // UI thread. Media.Statistics wraps libvlc_media_get_stats; the
        // "--stats" option defaults to true in VLC, so the counters are
        // live while playing. All-zero counters while Playing would mean
        // statistics are unavailable for this input. vout is the last
        // VoutCount seen on the worker (read here as a managed field, never
        // a LibVLC call off the worker); view is the hybrid player's probe
        // of the VideoView — actual Opacity plus whether this exact player
        // is bound to it. Decoded rising while displayed stays 0 with
        // vout > 0 and opacity 1 is the decoded-without-display defect.
        private void LogVlcStats(long timeMs)
        {
            try
            {
                var player = _mediaPlayer;
                if (player == null) return;
                using (var media = player.Media)
                {
                    if (media == null) return;
                    var stats = media.Statistics;
                    Log.Write("VLC stats: time=" + Math.Round(timeMs / 1000.0) + "s state=" + SafeState() +
                        " decodedVideo=" + stats.DecodedVideo + " displayed=" + stats.DisplayedPictures +
                        " lost=" + stats.LostPictures + " lostABuf=" + stats.LostAudioBuffers +
                        " inputBitrate=" + Math.Round(stats.InputBitrate) + " demuxBitrate=" + Math.Round(stats.DemuxBitrate) +
                        " readBytes=" + stats.ReadBytes +
                        " vout=" + _voutCount + " view=[" + ProbeViewState() + "]");
                }
            }
            catch (Exception ex)
            {
                Log.Write("VLC stats: could not read statistics: " + ex.GetType().Name);
            }
        }

        // UI thread. Runs the hybrid player's view probe for the current
        // player; never throws, so a broken probe cannot break playback.
        private string ProbeViewState()
        {
            var probe = ViewStateProbe;
            if (probe == null)
            {
                return "probe=none";
            }
            try
            {
                return probe(_mediaPlayer);
            }
            catch (Exception ex)
            {
                return "probe=error:" + ex.GetType().Name;
            }
        }

        // UI thread. Marks the load ready: raises player.ready, which the
        // view model turns into Ready (hides the loading spinner, enables
        // the controls) and which ends the open watchdog exactly as before.
        // It deliberately does NOT show the video view anymore. Readiness
        // means "playback is usable"; the view is shown separately by
        // MarkFirstFrameShown once a frame has actually been presented, so
        // the 2s fallback below can no longer expose a stale or uninitialised
        // surface: for audio-only it fires ready with the view still hidden,
        // which is the correct state (there is no video to show).
        private void MarkVideoReady(long seq, bool hasVideoOutput)
        {
            if (seq != _loadSeq || _readySent || Interlocked.Read(ref _openFailedSeq) == seq)
            {
                return;
            }
            _readySent = true;
            Log.Write((hasVideoOutput ? "VLC video track ready" : "VLC ready (no video output yet)") +
                " [view: " + ProbeViewState() + "]");
            Raise("player.ready", new JsonObject());
        }

        // UI thread. The only signal in LibVLCSharp for "a frame was
        // actually presented" is Media.Statistics.DisplayedPictures (there
        // is no first-frame event on MediaPlayer or VideoView): it counts
        // frames the vout presented, so vout creation alone — the old show
        // condition — does not move it. Runs on the OnTimeChanged tick
        // (at most every 250ms while time advances), so the show lags the
        // first presented frame by about one tick, typically under half a
        // second. A load whose time pulse stops (log 25 opening 3: zero
        // stats in 20s while Playing) never shows the view, which is honest:
        // nothing is being presented. A load that is paused at open shows
        // nothing until it resumes and time advances.
        private void CheckFirstFramePresented(long seq)
        {
            try
            {
                var player = _mediaPlayer;
                if (player == null) return;
                using (var media = player.Media)
                {
                    if (media == null) return;
                    var displayed = media.Statistics.DisplayedPictures;
                    if (_displayedBaseline < 0)
                    {
                        _displayedBaseline = displayed;
                        Log.Write("VLC first-frame watch armed (displayed=" + displayed + ")");
                        return;
                    }
                    if (displayed > _displayedBaseline)
                    {
                        MarkFirstFrameShown(seq, displayed);
                    }
                }
            }
            catch (Exception ex)
            {
                Log.Write("VLC first-frame check: could not read statistics: " + ex.GetType().Name);
            }
        }

        // UI thread. Shows the video view on the first frame presented for
        // this load. The probe runs before VideoVisibleChanged applies the
        // show: it answers whether this exact player was already bound to
        // the view when the frame landed (the opacity it reports is the
        // pre-show value; the hybrid player logs the applied opacity right
        // after it sets it).
        private void MarkFirstFrameShown(long seq, long displayed)
        {
            if (seq != _loadSeq || _firstFrameShown || Interlocked.Read(ref _openFailedSeq) == seq)
            {
                return;
            }
            _firstFrameShown = true;
            Log.Write("VLC first frame presented (displayed=" + displayed + ") [view: " + ProbeViewState() + "]");
            VideoVisibleChanged?.Invoke(true);
        }

        private async void ScheduleReadyFallback(long seq)
        {
            await Task.Delay(ReadyFallbackDelay);
            MarkVideoReady(seq, false);
        }

        private void RaiseState(string state, string message)
        {
            var payload = new JsonObject();
            payload.SetNamedValue("state", JsonValue.CreateStringValue(state));
            if (message != null)
            {
                payload.SetNamedValue("message", JsonValue.CreateStringValue(message));
            }
            Raise("player.state", payload);
        }

        private void RaiseEnded(string reason, string errorMessage)
        {
            var payload = new JsonObject();
            payload.SetNamedValue("reason", JsonValue.CreateStringValue(reason));
            if (errorMessage != null)
            {
                payload.SetNamedValue("message", JsonValue.CreateStringValue(errorMessage));
            }
            Raise("player.ended", payload);
        }

        // UI thread. Tags the event with the page's id for the current load.
        private void Raise(string type, JsonObject payload)
        {
            payload.SetNamedValue("id", _pageId != null ? JsonValue.CreateStringValue(_pageId) : JsonValue.CreateNullValue());
            EventRaised?.Invoke(type, payload);
        }

        // Runs work on the worker, if the stream VLC raised the event for is still the loaded one.
        private void QueueFromVlc(Action<long> work)
        {
            var seq = Interlocked.Read(ref _workerLoadSeq);
            var epoch = Interlocked.Read(ref _playerEpoch);
            Enqueue(() =>
            {
                if (seq == Interlocked.Read(ref _workerLoadSeq) && epoch == Interlocked.Read(ref _playerEpoch))
                {
                    work(seq);
                }
            });
        }

        // Runs work on the UI thread, if the stream VLC raised the event for is still the loaded one.
        private void PostFromVlc(Action<long> work)
        {
            var seq = Interlocked.Read(ref _workerLoadSeq);
            var epoch = Interlocked.Read(ref _playerEpoch);
            RunOnUi(() =>
            {
                if (seq == _loadSeq && epoch == Interlocked.Read(ref _playerEpoch))
                {
                    work(seq);
                }
            });
        }

        private void Enqueue(Action action)
        {
            int depth;
            lock (_queueLock)
            {
                depth = Interlocked.Increment(ref _queueDepth);
                _queue = _queue.ContinueWith(_ =>
                {
                    Interlocked.Decrement(ref _queueDepth);
                    try
                    {
                        action();
                    }
                    catch (Exception ex)
                    {
                        Log.Error("VLC worker", ex);
                    }
                }, TaskScheduler.Default);
            }
            Log.Write("VLC worker enqueue depth=" + depth);
        }

        private void RunOnUi(Action action)
        {
            var ignored = _dispatcher.RunAsync(CoreDispatcherPriority.Normal, () =>
            {
                try
                {
                    action();
                }
                catch (Exception ex)
                {
                    Log.Error("VLC UI callback", ex);
                }
            });
        }

        private static bool IsAllowedUrl(string url)
        {
            var colon = url.IndexOf(':');
            return colon > 0 && Array.IndexOf(AllowedSchemes, url.Substring(0, colon).ToLowerInvariant()) >= 0;
        }

        private static string FourCcToString(uint fourcc)
        {
            if (fourcc == 0)
            {
                return null;
            }
            var chars = new char[4];
            for (var i = 0; i < 4; i++)
            {
                chars[i] = (char)((fourcc >> (8 * i)) & 0xFF);
            }
            var text = new string(chars).Trim(' ', '\0');
            return text.Length == 0 ? null : text.ToLowerInvariant();
        }
    }
}
