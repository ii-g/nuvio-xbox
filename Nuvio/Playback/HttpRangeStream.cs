using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Net.Http;
using System.Net.Http.Headers;
using System.Threading;
using System.Threading.Tasks;
using Nuvio.Diagnostics;

namespace Nuvio.Playback
{
    /// <summary>
    /// Seekable HTTP stream for media sources that need request headers. It requests bounded byte
    /// ranges, so playback does not buffer an entire video in memory. Servers that ignore Range are
    /// still streamed from the beginning when the player seeks.
    /// </summary>
    internal sealed class HttpRangeStream : Stream
    {
        // Larger sequential ranges reduce request/round-trip stalls on high-bitrate Xbox playback.
        // The response body is streamed, so this does not buffer the whole range in memory.
        private const int RangeSize = 4 * 1024 * 1024;
        // R1: a transient range failure must not kill the open. Log 33 showed
        // the same URL failing HTTP 500 and then succeeding ~11s later, so a
        // failed round-trip gets bounded retries with backoff instead of
        // failing the open at once. Non-transient statuses fail immediately.
        private const int MaxRangeAttempts = 3;
        private const int MaxRetryWaitMs = 5000;
        // R2: how many times a 0-byte read mid-range reopens the range
        // before failing loudly instead of ending playback silently.
        private const int MaxZeroReadReopens = 2;
        private readonly HttpClient _client;
        private readonly Uri _uri;
        private readonly SemaphoreSlim _readGate = new SemaphoreSlim(1, 1);
        private HttpResponseMessage _response;
        private Stream _responseStream;
        private long _position;
        private long _responsePosition;
        private long _responseEnd;
        private bool _disposed;

        private HttpRangeStream(HttpClient client, Uri uri, long length, string contentType)
        {
            _client = client;
            _uri = uri;
            // length < 0 means the server never reported one: Length reports
            // long.MaxValue so the stream stays seekable/readable and WMF can
            // still play it; the end is signalled by a 0-byte read instead.
            _unknownLength = length < 0;
            _length = _unknownLength ? long.MaxValue : length;
            ContentType = string.IsNullOrWhiteSpace(contentType) ||
                contentType.Equals("application/octet-stream", StringComparison.OrdinalIgnoreCase)
                ? GuessContentType(uri) : contentType;
        }

        public string ContentType { get; }
        public override bool CanRead => !_disposed;
        public override bool CanSeek => !_disposed;
        public override bool CanWrite => false;
        public override long Length => _length;
        private readonly long _length;
        private readonly bool _unknownLength;

        public override long Position
        {
            get { return _position; }
            set { Seek(value, SeekOrigin.Begin); }
        }

        public static async Task<HttpRangeStream> CreateAsync(Uri uri, IDictionary<string, string> headers, CancellationToken token)
        {
            var handler = new HttpClientHandler { AllowAutoRedirect = true };
            var client = new HttpClient(handler);
            try
            {
                AddDefaultHeaders(client, headers, uri);
                long? length = null;
                string contentType = null;

                // A failed HEAD must not kill playback: some origins reject HEAD
                // outright while serving GET fine.
                try
                {
                    using (var head = new HttpRequestMessage(HttpMethod.Head, uri))
                    using (var response = await client.SendAsync(head, HttpCompletionOption.ResponseHeadersRead, token))
                    {
                        if (response.IsSuccessStatusCode)
                        {
                            length = response.Content.Headers.ContentLength;
                            contentType = response.Content.Headers.ContentType == null ? null : response.Content.Headers.ContentType.MediaType;
                        }
                    }
                }
                catch (Exception ex) when (!(ex is OperationCanceledException))
                {
                    Log.Write("Media HEAD request failed for host " + uri.Host + "; continuing with a range probe (" + ex.Message + ")");
                }

                if (!length.HasValue || length.Value <= 0)
                {
                    // A 0-0 range probe is only a hint. Some servers answer it with
                    // 403/405 while serving the media itself, so never throw here:
                    // an unsuccessful probe just means the length stays unknown.
                    try
                    {
                        using (var probe = new HttpRequestMessage(HttpMethod.Get, uri))
                        {
                            probe.Headers.Range = new RangeHeaderValue(0, 0);
                            using (var response = await client.SendAsync(probe, HttpCompletionOption.ResponseHeadersRead, token))
                            {
                                if (response.IsSuccessStatusCode)
                                {
                                    var range = response.Content.Headers.ContentRange;
                                    length = range != null && range.Length.HasValue
                                        ? range.Length
                                        : response.Content.Headers.ContentLength;
                                    if (string.IsNullOrWhiteSpace(contentType) && response.Content.Headers.ContentType != null)
                                        contentType = response.Content.Headers.ContentType.MediaType;
                                }
                                else
                                {
                                    Log.Write("Media range probe for host " + uri.Host + " returned HTTP " + (int)response.StatusCode + "; continuing without a known length");
                                }
                            }
                        }
                    }
                    catch (Exception ex) when (!(ex is OperationCanceledException))
                    {
                        Log.Write("Media range probe failed for host " + uri.Host + "; continuing without a known length (" + ex.Message + ")");
                    }
                }

                if (!length.HasValue || length.Value <= 0)
                {
                    Log.Write("The server did not report the media length for host " + uri.Host + "; streaming with an unknown length");
                    length = -1;
                }

                return new HttpRangeStream(client, uri, length.Value, contentType);
            }
            catch
            {
                client.Dispose();
                throw;
            }
        }

        private static void AddDefaultHeaders(HttpClient client, IDictionary<string, string> headers, Uri uri)
        {
            var hasUserAgent = false;
            if (headers != null)
            {
                foreach (var header in headers)
                {
                    if (string.IsNullOrWhiteSpace(header.Key) ||
                        header.Key.Equals("Range", StringComparison.OrdinalIgnoreCase))
                        continue;

                    // R4: one bad header from addon data must not kill the
                    // open. Skip it, log its name only (never its value),
                    // and continue with the remaining headers.
                    bool applied;
                    try
                    {
                        applied = client.DefaultRequestHeaders.TryAddWithoutValidation(header.Key, header.Value ?? string.Empty);
                    }
                    catch (Exception)
                    {
                        applied = false;
                    }
                    if (!applied)
                    {
                        Log.Write("Skipping media request header '" + SafeHeaderName(header.Key) + "' for host " + uri.Host + ": the native HTTP stack cannot apply it");
                        continue;
                    }
                    if (header.Key.Equals("User-Agent", StringComparison.OrdinalIgnoreCase)) hasUserAgent = true;
                }
            }
            // Some origins (and CDNs) reject requests with no User-Agent at all.
            if (!hasUserAgent) client.DefaultRequestHeaders.TryAddWithoutValidation("User-Agent", "NuvioUWP");
        }

        // Header names come from addon data, so only a plain token-shaped
        // name is ever written to the log; anything else is not logged.
        private static string SafeHeaderName(string name)
        {
            if (string.IsNullOrEmpty(name)) return "(empty)";
            foreach (var c in name)
            {
                if (!(char.IsLetterOrDigit(c) || c == '-' || c == '_')) return "(invalid header name)";
            }
            return name;
        }

        public override async Task<int> ReadAsync(byte[] buffer, int offset, int count, CancellationToken cancellationToken)
        {
            if (_disposed) throw new ObjectDisposedException(nameof(HttpRangeStream));
            if (buffer == null) throw new ArgumentNullException(nameof(buffer));
            if (offset < 0 || count < 0 || offset + count > buffer.Length) throw new ArgumentOutOfRangeException();
            if (count == 0 || _position >= Length) return 0;

            var gateStart = Environment.TickCount;
            await _readGate.WaitAsync(cancellationToken);
            var gateWaitMs = Environment.TickCount - gateStart;
            try
            {
                if (_position >= Length) return 0;
                // R2: a 0-byte read before the end of the range means the
                // response was cut short, not end-of-stream. Reopen the
                // range from _position and continue; after bounded reopens
                // fail loudly so FFmpeg reports an error instead of ending
                // playback silently. A genuine end of range (available <= 0,
                // e.g. after a 416) still returns 0 as before.
                var zeroReopens = 0;
                while (true)
                {
                    if (_responseStream == null || _position != _responsePosition || _position >= _responseEnd)
                        await OpenRangeAsync(cancellationToken, gateWaitMs);

                    var available = (int)Math.Min(count, Math.Min(int.MaxValue, _responseEnd - _position));
                    if (available <= 0) return 0;
                    var read = await _responseStream.ReadAsync(buffer, offset, available, cancellationToken);
                    if (read > 0)
                    {
                        _position += read;
                        _responsePosition += read;
                        return read;
                    }
                    if (zeroReopens >= MaxZeroReadReopens)
                    {
                        Log.Write("FFmpeg range read ended early for host " + _uri.Host + " at byte " + _position + " after " + (zeroReopens + 1) + " empty reads; failing the read instead of ending playback");
                        throw new IOException("The media response ended before the requested range was complete.");
                    }
                    zeroReopens++;
                    Log.Write("FFmpeg range read returned 0 bytes for host " + _uri.Host + " at byte " + _position + " before the end of the range; reopening the range (attempt " + zeroReopens + "/" + MaxZeroReadReopens + ")");
                    CloseResponse();
                }
            }
            finally
            {
                _readGate.Release();
            }
        }

        private async Task OpenRangeAsync(CancellationToken token, int gateWaitMs)
        {
            CloseResponse();
            var start = _position;
            var end = Math.Min(Length - 1, start + RangeSize - 1);
            HttpResponseMessage response = null;
            var attempt = 0;

            // Retry loop: only the range request itself is retried, and only
            // for transient failures (5xx/429/408 or a network blip). A 416
            // returns at once (end of stream), other 4xx fail at once, and
            // body handling below (wrong offset, skip cap) is deterministic
            // so it is never retried.
            while (true)
            {
                attempt++;
                var request = new HttpRequestMessage(HttpMethod.Get, _uri);
                request.Headers.Range = new RangeHeaderValue(start, end);
                try
                {
                    var getStart = Environment.TickCount;
                    try
                    {
                        response = await _client.SendAsync(request, HttpCompletionOption.ResponseHeadersRead, token);
                    }
                    catch (HttpRequestException ex) when (attempt < MaxRangeAttempts)
                    {
                        token.ThrowIfCancellationRequested();
                        var blipWaitMs = RetryBackoffMs(attempt);
                        Log.Write("FFmpeg range read failed for host " + _uri.Host + ": " + ex.Message + " (attempt " + attempt + "/" + MaxRangeAttempts + "), retrying in " + blipWaitMs + "ms");
                        request.Dispose();
                        await Task.Delay(blipWaitMs, token);
                        continue;
                    }
                    var getMs = Environment.TickCount - getStart;
                    Log.Write("FFmpeg range read: bytes=" + start + "-" + end + " getMs=" + getMs + " gateWaitMs=" + gateWaitMs);
                    request.Dispose();
                    if (response.StatusCode == HttpStatusCode.RequestedRangeNotSatisfiable)
                    {
                        // Past the end of a stream whose length was never reported:
                        // signal end-of-stream instead of failing the read.
                        _responseEnd = _position;
                        _responsePosition = _position;
                        response.Dispose();
                        return;
                    }
                    if (response.IsSuccessStatusCode) break;
                    var status = (int)response.StatusCode;
                    if (!IsTransientStatus(status) || attempt >= MaxRangeAttempts)
                    {
                        response.EnsureSuccessStatusCode();
                    }
                    var waitMs = RetryWaitMs(response, attempt);
                    Log.Write("FFmpeg range read failed for host " + _uri.Host + ": HTTP " + status + " (attempt " + attempt + "/" + MaxRangeAttempts + "), retrying in " + waitMs + "ms");
                    response.Dispose();
                    response = null;
                    await Task.Delay(waitMs, token);
                }
                catch
                {
                    request.Dispose();
                    response?.Dispose();
                    throw;
                }
            }

            try
            {
                var stream = await response.Content.ReadAsStreamAsync();
                if (response.StatusCode == HttpStatusCode.PartialContent)
                {
                    var contentRange = response.Content.Headers.ContentRange;
                    var actualStart = contentRange != null && contentRange.From.HasValue ? contentRange.From.Value : start;
                    if (actualStart != start)
                    {
                        stream.Dispose();
                        response.Dispose();
                        throw new IOException("The server returned a byte range at the wrong offset.");
                    }
                    var responseLength = response.Content.Headers.ContentLength;
                    _responseEnd = Math.Min(Length, start + (responseLength.HasValue ? responseLength.Value : end - start + 1));
                    _responsePosition = start;
                }
                else
                {
                    // Some origins ignore Range and return 200. Consume forward without keeping the
                    // whole response in memory; seeks may re-request from byte zero.
                    if (start > 0)
                        await SkipAsync(stream, start, token);
                    _responseEnd = Length;
                    _responsePosition = start;
                }

                _response = response;
                _responseStream = stream;
            }
            catch
            {
                response?.Dispose();
                throw;
            }
        }

        private static bool IsTransientStatus(int status)
        {
            return status == 408 || status == 429 || (status >= 500 && status < 600);
        }

        private static int RetryBackoffMs(int attempt)
        {
            return attempt <= 1 ? 500 : 1000;
        }

        private static int RetryWaitMs(HttpResponseMessage response, int attempt)
        {
            var waitMs = RetryBackoffMs(attempt);
            var retryAfter = RetryAfterSeconds(response);
            if (retryAfter.HasValue)
                waitMs = Math.Max(waitMs, (int)Math.Min(MaxRetryWaitMs, retryAfter.Value * 1000));
            return Math.Min(waitMs, MaxRetryWaitMs);
        }

        // Same Retry-After reading as HttpService: a delta in seconds, or an
        // absolute date. Only the numeric wait is ever logged, never headers.
        private static double? RetryAfterSeconds(HttpResponseMessage response)
        {
            var retry = response.Headers.RetryAfter;
            if (retry == null) return null;
            if (retry.Delta.HasValue) return Math.Max(0, retry.Delta.Value.TotalSeconds);
            if (retry.Date.HasValue) return Math.Max(0, (retry.Date.Value - DateTimeOffset.UtcNow).TotalSeconds);
            return null;
        }

        // R3: cap for skipping past a server that ignores Range. Without
        // one, a late seek in a multi-GB file downloads gigabytes before
        // resuming. 32 MB still covers header/probe seeks and short resumes
        // while a deep seek on a range-less server fails fast and loudly.
        private const long MaxSkipBytes = 32L * 1024 * 1024;

        private async Task SkipAsync(Stream stream, long bytes, CancellationToken token)
        {
            var scratch = new byte[32 * 1024];
            var skipped = 0L;
            while (skipped < bytes)
            {
                token.ThrowIfCancellationRequested();
                var allowance = MaxSkipBytes - skipped;
                if (allowance <= 0)
                {
                    Log.Write("FFmpeg range skip gave up for host " + _uri.Host + ": the server ignores byte ranges and the seek target is " + bytes + " bytes in, past the " + MaxSkipBytes + "-byte skip limit");
                    throw new IOException("The server ignores byte ranges and the seek position is beyond the skip limit.");
                }
                var read = await stream.ReadAsync(scratch, 0, (int)Math.Min(scratch.Length, Math.Min(bytes - skipped, allowance)), token);
                if (read <= 0) throw new EndOfStreamException("The server ended the media before the requested seek position.");
                skipped += read;
            }
        }

        private static string GuessContentType(Uri uri)
        {
            switch (Path.GetExtension(uri.AbsolutePath).ToLowerInvariant())
            {
                case ".mp4": case ".m4v": return "video/mp4";
                case ".mkv": return "video/x-matroska";
                case ".webm": return "video/webm";
                case ".mov": return "video/quicktime";
                case ".ts": return "video/mp2t";
                case ".avi": return "video/x-msvideo";
                case ".mp3": return "audio/mpeg";
                case ".m4a": return "audio/mp4";
                default: return "application/octet-stream";
            }
        }

        private void CloseResponse()
        {
            try { _responseStream?.Dispose(); } catch { }
            try { _response?.Dispose(); } catch { }
            _responseStream = null;
            _response = null;
            _responsePosition = _position;
            _responseEnd = _position;
        }

        public override int Read(byte[] buffer, int offset, int count)
        {
            return ReadAsync(buffer, offset, count, CancellationToken.None).GetAwaiter().GetResult();
        }

        public override long Seek(long offset, SeekOrigin origin)
        {
            if (_disposed) throw new ObjectDisposedException(nameof(HttpRangeStream));
            long target;
            switch (origin)
            {
                case SeekOrigin.Begin: target = offset; break;
                case SeekOrigin.Current: target = _position + offset; break;
                case SeekOrigin.End:
                    if (_unknownLength) throw new NotSupportedException("The media length is unknown, so seeking from the end is not supported.");
                    target = Length + offset;
                    break;
                default: throw new ArgumentOutOfRangeException(nameof(origin));
            }
            if (target < 0 || target > Length) throw new ArgumentOutOfRangeException(nameof(offset));
            if (target != _position)
            {
                _position = target;
                CloseResponse();
            }
            return _position;
        }

        public override void Flush() { }
        public override void SetLength(long value) { throw new NotSupportedException(); }
        public override void Write(byte[] buffer, int offset, int count) { throw new NotSupportedException(); }

        protected override void Dispose(bool disposing)
        {
            if (_disposed) return;
            _disposed = true;
            if (disposing)
            {
                CloseResponse();
                _client.Dispose();
                _readGate.Dispose();
            }
            base.Dispose(disposing);
        }
    }
}
