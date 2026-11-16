using System;
using System.Collections.Generic;
using System.IO;
using System.Runtime.InteropServices;
using System.Threading;
using System.Threading.Tasks;
using LibVLCSharp.Shared;
using Nuvio.Diagnostics;
using Windows.Web.Http;
using Windows.Web.Http.Filters;

namespace Nuvio.Playback
{
    /// <summary>
    /// Feeds VLC a stream downloaded with Windows' own HTTP stack instead of VLC's. VLC's UWP build
    /// failed to open every https link on the Xbox within a fraction of a second, while Windows'
    /// stack handles certificates, redirects (e.g. addon to debrid server) and TLS itself. It also
    /// sends any request headers a stream asks for, which LibVLC 3 can't (only User-Agent and Referer).
    /// Seeking is done with HTTP range requests.
    /// </summary>
    /// <remarks>VLC calls Open, Read, Seek and Close on its input thread, one at a time.</remarks>
    internal sealed class HttpMediaInput : MediaInput
    {
        private const string DefaultUserAgent = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) NuvioUWP-VLC";
        private static readonly HttpClient Client = CreateClient();

        private readonly object _sync = new object();
        // One cancellation source for the input's lifetime: Abort() cancels
        // its token so a request in flight is asked to stop at once, and
        // every network wait also has a hard 15s bound (WaitBounded) so the
        // input thread is freed even if the WinRT stack ignores the
        // cancellation. Created in the constructor, never replaced, disposed
        // once by Close().
        private CancellationTokenSource _cts;
        private static readonly TimeSpan RequestTimeout = TimeSpan.FromSeconds(15);
        private string _lastInputOp = "Idle";
        private long _lastInputOpTicks;
        private readonly IDictionary<string, string> _headers;
        private readonly byte[] _buffer = new byte[256 * 1024];
        private Uri _uri;
        private HttpResponseMessage _response;
        private Stream _body;
        private ulong _position;
        private ulong _length;
        private bool _supportsRanges;
        private bool _aborted;
        private bool _retriedRead;

        // Read-flood guard: once the input is dead (broken or missing body
        // after a failed resume), Read returns -1 silently and only retries
        // every 5s. No log line on the healthy path; the first error of each
        // death bout is still logged in full, then one summary every 5s.
        // All of these are touched on VLC's single input thread only, same
        // as _retriedRead. No Thread.Sleep here: Thread.Sleep is not proven
        // for this UWP target (Microsoft Learn "Applies to" lists .NET /
        // .NET Framework / .NET Standard only, no UWP row, unlike
        // Interlocked.Exchange which lists UWP 10.0), so the dead path spins
        // cheaply on a flag check + counter instead of sleeping.
        private bool _dead;
        private long _deadSinceTicks;
        private long _deadReadCount;
        private long _lastSummaryTicks;
        private long _lastResumeAttemptTicks;
        private string _lastErrorKind;

        // Same throttling for repeated failed seeks (cheap insurance: a
        // seek does network I/O, so it cannot flood like Read, but a
        // demuxer retrying seeks must not log a full stack per attempt).
        private long _seekFailCount;
        private long _seekFailSinceTicks;
        private long _lastSeekFailTicks;
        private long _lastSeekSummaryTicks;
        private string _lastSeekErrorKind;

        // Stop diagnostics (step 2b): progress counters for the input
        // thread, read by the 5s stop watcher only. Cheap writes, no log
        // lines (Read is a hot path), no branching on them anywhere.
        private long _readCount;
        private long _lastReadUtcTicks;
        private long _closeCount;

        internal long ReadCount
        {
            get { return Interlocked.Read(ref _readCount); }
        }

        internal long CloseCount
        {
            get { return Interlocked.Read(ref _closeCount); }
        }

        /// <summary>Milliseconds since the last Read, or -1 when no Read ever ran.</summary>
        internal long LastReadAgeMs
        {
            get
            {
                var ticks = Interlocked.Read(ref _lastReadUtcTicks);
                if (ticks == 0)
                {
                    return -1;
                }
                return (long)(DateTime.UtcNow - new DateTime(ticks)).TotalMilliseconds;
            }
        }

        /// <summary>Last operation the input thread entered: "OpenAt", "Read", "Seek" or "Idle".</summary>
        internal string LastInputOp
        {
            get { return _lastInputOp; }
        }

        /// <summary>Milliseconds since the input thread entered its current operation, or -1 when idle.</summary>
        internal long LastInputOpAgeMs
        {
            get
            {
                if (_lastInputOp == "Idle")
                {
                    return -1;
                }
                var ticks = Interlocked.Read(ref _lastInputOpTicks);
                if (ticks == 0)
                {
                    return -1;
                }
                return (long)(DateTime.UtcNow - new DateTime(ticks)).TotalMilliseconds;
            }
        }

        private void SetInputOp(string op)
        {
            _lastInputOp = op;
            Interlocked.Exchange(ref _lastInputOpTicks, DateTime.UtcNow.Ticks);
        }

        public HttpMediaInput(string url, IDictionary<string, string> headers)
        {
            _uri = new Uri(url);
            _headers = headers ?? new Dictionary<string, string>();
            _cts = new CancellationTokenSource();
            CanSeek = true;
        }

        /// <summary>Breaks off a pending read so VLC can stop without waiting for the network.</summary>
        public void Abort()
        {
            lock (_sync)
            {
                _aborted = true;
                // Cancel first: a request in flight is asked to stop before
                // the body is torn down. Skipped when Close() already
                // disposed the source (nothing left to cancel).
                if (_cts != null)
                {
                    try
                    {
                        _cts.Cancel();
                    }
                    catch (ObjectDisposedException)
                    {
                    }
                }
                CloseResponse();
            }
        }

        public override bool Open(out ulong size)
        {
            try
            {
                OpenAt(0);
                Log.Write("Opened stream: " + (_length > 0 ? Math.Round(_length / 1048576.0) + " MB" : "unknown size") +
                    (_supportsRanges ? ", seekable" : ", not seekable") + ", from " + Log.DescribeUrl(_uri.AbsoluteUri));
                size = _length;
                return true;
            }
            catch (Exception ex)
            {
                Log.Error("Opening the stream failed", ex);
                size = 0;
                return false;
            }
        }

        public override int Read(IntPtr buf, uint len)
        {
            Interlocked.Increment(ref _readCount);
            Interlocked.Exchange(ref _lastReadUtcTicks, DateTime.UtcNow.Ticks);
            var resumedFromDead = false;
            long failedReadsBeforeRecovery = 0;
            var entryPos = _position;
            if (_dead)
            {
                if (TryRearm())
                {
                    resumedFromDead = true;
                    failedReadsBeforeRecovery = _deadReadCount;
                    _dead = false;
                    _retriedRead = false;
                }
                else
                {
                    CountDeadRead();
                    return -1;
                }
            }
            try
            {
                var read = ReadOnce(len);
                if (resumedFromDead && read > 0)
                {
                    Log.Write("Stream read recovered at " + entryPos + " after " + failedReadsBeforeRecovery + " failed reads");
                }
                _retriedRead = false;
                return read;
            }
            catch (Exception ex)
            {
                if (_aborted)
                {
                    return -1;
                }
                // A dropped connection: pick the download back up where it stopped.
                // Rearmed every 5s while dead (TryRearm above); a failed resume
                // enters the dead state instead of retrying on every Read.
                if (!_retriedRead && _supportsRanges && (_length == 0 || _position < _length))
                {
                    _retriedRead = true;
                    Log.Write("Stream read failed (" + ex.Message + "), resuming at " + _position);
                    try
                    {
                        OpenAt(_position);
                        var read = ReadOnce(len);
                        if (resumedFromDead && read > 0)
                        {
                            Log.Write("Stream read recovered at " + entryPos + " after " + failedReadsBeforeRecovery + " failed reads");
                        }
                        _retriedRead = false;
                        return read;
                    }
                    catch (Exception retryEx)
                    {
                        Log.Error("Resuming the stream failed", retryEx);
                        EnterDead(retryEx);
                    }
                }
                else
                {
                    if (!_dead)
                    {
                        Log.Error("Stream read failed", ex);
                        EnterDead(ex);
                    }
                    else
                    {
                        CountDeadRead();
                    }
                }
                return -1;
            }

            int ReadOnce(uint length)
            {
                var body = _body;
                if (body == null)
                {
                    throw new IOException("No response");
                }
                SetInputOp("Read");
                try
                {
                    var readTask = body.ReadAsync(_buffer, 0, (int)Math.Min(length, (uint)_buffer.Length), _cts.Token);
                    var read = WaitBounded(readTask, "Read", _position);
                    if (read > 0)
                    {
                        Marshal.Copy(_buffer, 0, buf, read);
                        _position += (ulong)read;
                    }
                    return read;
                }
                finally
                {
                    SetInputOp("Idle");
                }
            }
        }

        public override bool Seek(ulong offset)
        {
            if (offset == _position && _body != null)
            {
                return true;
            }
            if (!_supportsRanges)
            {
                return false;
            }
            SetInputOp("Seek");
            try
            {
                OpenAt(offset);
                return true;
            }
            catch (Exception ex)
            {
                var now = DateTime.UtcNow;
                var newBout = _lastSeekFailTicks == 0 || (now - new DateTime(_lastSeekFailTicks)).TotalSeconds >= 5;
                if (newBout)
                {
                    Log.Error("Seeking the stream failed", ex);
                    _seekFailCount = 1;
                    _seekFailSinceTicks = now.Ticks;
                    _lastSeekSummaryTicks = now.Ticks;
                    _lastSeekErrorKind = ex.GetType().Name;
                }
                else
                {
                    _seekFailCount++;
                    _lastSeekErrorKind = ex.GetType().Name;
                    if ((now - new DateTime(_lastSeekSummaryTicks)).TotalSeconds >= 5)
                    {
                        _lastSeekSummaryTicks = now.Ticks;
                        Log.Write("Seeking the stream still failing at " + _position + " (" + _lastSeekErrorKind + "): " + _seekFailCount + " failed seeks suppressed since " + new DateTime(_seekFailSinceTicks).ToString("HH:mm:ss"));
                    }
                }
                _lastSeekFailTicks = now.Ticks;
                if (_body != null)
                {
                    Log.Write("Seek to " + offset + " failed, keeping previous body at " + _position);
                }
                return false;
            }
            finally
            {
                SetInputOp("Idle");
            }
        }

        public override void Close()
        {
            Interlocked.Increment(ref _closeCount);
            lock (_sync)
            {
                CloseResponse();
                if (_cts != null)
                {
                    _cts.Dispose();
                    _cts = null;
                }
            }
        }

        private void OpenAt(ulong offset)
        {
            lock (_sync)
            {
                // Swap on success only: the previous body stays alive if any
                // step below throws, so a failed seek no longer kills the input.
                if (_aborted)
                {
                    throw new OperationCanceledException();
                }
            }

            SetInputOp("OpenAt");
            try
            {
                var request = new HttpRequestMessage(HttpMethod.Get, _uri);
                request.Headers.TryAppendWithoutValidation("Range", "bytes=" + offset + "-");
                var hasUserAgent = false;
                foreach (var header in _headers)
                {
                    if (string.IsNullOrWhiteSpace(header.Key) || header.Key.Equals("Range", StringComparison.OrdinalIgnoreCase))
                    {
                        continue;
                    }
                    hasUserAgent |= header.Key.Equals("User-Agent", StringComparison.OrdinalIgnoreCase);
                    request.Headers.TryAppendWithoutValidation(header.Key, header.Value ?? string.Empty);
                }
                if (!hasUserAgent)
                {
                    request.Headers.TryAppendWithoutValidation("User-Agent", DefaultUserAgent);
                }
                var sendTask = Client.SendRequestAsync(request, HttpCompletionOption.ResponseHeadersRead).AsTask(_cts.Token);
                var response = WaitBounded(sendTask, "OpenAt", offset);
                if (!response.IsSuccessStatusCode)
                {
                    var status = (int)response.StatusCode + " " + response.ReasonPhrase;
                    response.Dispose();
                    throw new IOException("HTTP " + status);
                }

                // Keep using the address the redirects led to, so seeks skip the addon's redirect.
                if (response.RequestMessage != null && response.RequestMessage.RequestUri != null)
                {
                    _uri = response.RequestMessage.RequestUri;
                }
                var range = response.Content.Headers.ContentRange;
                if (response.StatusCode == HttpStatusCode.PartialContent && range != null && range.Length.HasValue)
                {
                    _length = range.Length.Value;
                    _supportsRanges = true;
                }
                else
                {
                    if (offset > 0)
                    {
                        response.Dispose();
                        throw new IOException("The server doesn't support seeking");
                    }
                    _length = response.Content.Headers.ContentLength ?? 0;
                    _supportsRanges = false;
                }

                Stream body;
                try
                {
                    body = WaitBounded(response.Content.ReadAsInputStreamAsync().AsTask(_cts.Token), "OpenAt", offset).AsStreamForRead(0);
                }
                catch
                {
                    response.Dispose();
                    throw;
                }
                lock (_sync)
                {
                    if (_aborted)
                    {
                        body.Dispose();
                        response.Dispose();
                        throw new OperationCanceledException();
                    }
                    CloseResponse();
                    _response = response;
                    _body = body;
                    _position = offset;
                    _dead = false;
                    _retriedRead = false;
                }
            }
            finally
            {
                SetInputOp("Idle");
            }
        }

        private void CloseResponse()
        {
            _body?.Dispose();
            _body = null;
            _response?.Dispose();
            _response = null;
        }

        /// <summary>Waits for one network step with a hard 15s bound: the
        /// input thread is freed at the timeout even if the WinRT stack
        /// ignores the cancellation request. A late result is disposed so no
        /// socket leaks. A cancelled wait (Abort() fired) is reported as an
        /// OperationCanceledException, as before.</summary>
        private T WaitBounded<T>(Task<T> task, string op, ulong position)
        {
            var completed = Task.WhenAny(task, Task.Delay(RequestTimeout)).GetAwaiter().GetResult();
            if (!ReferenceEquals(completed, task))
            {
                var ignored = task.ContinueWith(t =>
                {
                    if (t.Status == TaskStatus.RanToCompletion)
                    {
                        var disposable = t.Result as IDisposable;
                        if (disposable != null)
                        {
                            disposable.Dispose();
                        }
                    }
                }, TaskScheduler.Default);
                throw new IOException("HTTP request timed out (op=" + op + " at " + position + ")");
            }
            if (task.IsCanceled)
            {
                if (_aborted)
                {
                    Log.Write("HTTP request cancelled (op=" + op + ")");
                }
                throw new OperationCanceledException();
            }
            return task.GetAwaiter().GetResult();
        }

        private void EnterDead(Exception ex)
        {
            var now = DateTime.UtcNow;
            _dead = true;
            _deadSinceTicks = now.Ticks;
            _deadReadCount = 0;
            _lastSummaryTicks = now.Ticks;
            _lastResumeAttemptTicks = now.Ticks;
            _lastErrorKind = ex.GetType().Name;
            Log.Write("Stream read dead at " + _position + " (" + _lastErrorKind + "), silent -1 until recovery; reads=0");
        }

        private void CountDeadRead()
        {
            _deadReadCount++;
            var now = DateTime.UtcNow;
            if ((now - new DateTime(_lastSummaryTicks)).TotalSeconds >= 5)
            {
                _lastSummaryTicks = now.Ticks;
                Log.Write("Stream read still dead at " + _position + ": " + _deadReadCount + " failed reads suppressed since " + new DateTime(_deadSinceTicks).ToString("HH:mm:ss"));
            }
        }

        private bool TryRearm()
        {
            var now = DateTime.UtcNow;
            if ((now - new DateTime(_lastResumeAttemptTicks)).TotalSeconds < 5)
            {
                return false;
            }
            _lastResumeAttemptTicks = now.Ticks;
            return true;
        }

        private static HttpClient CreateClient()
        {
            var filter = new HttpBaseProtocolFilter { AllowAutoRedirect = true, AutomaticDecompression = false };
            // Don't let Windows cache gigabytes of video.
            filter.CacheControl.ReadBehavior = HttpCacheReadBehavior.NoCache;
            filter.CacheControl.WriteBehavior = HttpCacheWriteBehavior.NoCache;
            return new HttpClient(filter);
        }
    }
}
