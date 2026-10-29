import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import crypto from 'node:crypto';
import { spawn } from 'node:child_process';
import { pipeline } from 'node:stream/promises';
import { fileURLToPath } from 'node:url';

const env = (k, d) => Number(process.env[k] ?? d);
const PORT = env('PORT', 3000);
const MAX_VIDEO_MB = env('MAX_VIDEO_MB', 1024);       // largest accepted upload
const MAX_VOICE_MB = env('MAX_VOICE_MB', 600);        // largest accepted voice recording (WAV)
const MAX_VIDEO_MIN = env('MAX_VIDEO_MIN', 30);       // longest accepted video
const MAX_JOBS = env('MAX_JOBS', 1);                  // ffmpeg exports running at once
const MAX_QUEUE = env('MAX_QUEUE', 5);                // exports allowed to wait; more get a "busy" reply
const TTL_MIN = env('TTL_MIN', 60);                   // files are deleted this long after last use
const HOURLY_UPLOADS = env('HOURLY_UPLOADS', 20);     // per visitor
const HOURLY_EXPORTS = env('HOURLY_EXPORTS', 15);     // per visitor

const PUBLIC = path.join(path.dirname(fileURLToPath(import.meta.url)), 'public');
const WORK = fs.mkdtempSync(path.join(os.tmpdir(), 'vover-'));
const videos = new Map(); // id -> { file, ext, last }

const TYPES = { '.mjs': 'text/javascript', '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.svg': 'image/svg+xml' };

// ---------- helpers ----------
// ffmpeg and ffprobe are only needed for the server fallback; the app works without them for in-browser exports.
let hasFfmpeg = true;

class HttpError extends Error { constructor(status, message) { super(message); this.status = status; } }

const exec = (cmd, args) => new Promise((resolve, reject) => {
  const p = spawn(cmd, args);
  let out = '', err = '';
  p.stdout.on('data', (d) => (out += d));
  p.stderr.on('data', (d) => (err += d));
  p.on('error', reject);
  p.on('close', (code) => (code === 0 ? resolve(out) : reject(new Error(err.slice(-600)))));
});
const ffmpeg = (args) => exec('ffmpeg', ['-y', '-hide_banner', '-loglevel', 'error', ...args]);

// Saves the request body to disk, refusing anything over maxBytes.
async function save(req, file, maxBytes) {
  if (Number(req.headers['content-length'] || 0) > maxBytes) throw new HttpError(413, `File too large (limit ${Math.round(maxBytes / 1e6)} MB).`);
  let size = 0;
  const guard = async function* (src) {
    for await (const chunk of src) {
      size += chunk.length;
      if (size > maxBytes) throw new HttpError(413, `File too large (limit ${Math.round(maxBytes / 1e6)} MB).`);
      yield chunk;
    }
  };
  try { await pipeline(req, guard, fs.createWriteStream(file)); } catch (e) { fs.rm(file, () => {}); throw e; }
}

// Only one export per MAX_JOBS runs at a time; the rest wait in a short queue.
let running = 0;
const waiting = [];
async function withSlot(fn) {
  if (running >= MAX_JOBS) {
    if (waiting.length >= MAX_QUEUE) throw new HttpError(503, 'The server is busy exporting other videos. Try again in a minute.');
    await new Promise((resolve) => waiting.push(resolve));
  } else running++;
  try { return await fn(); }
  finally { const next = waiting.shift(); if (next) next(); else running--; }
}

// Simple per-visitor hourly counters.
const hits = new Map();
function limit(req, kind, max) {
  const key = `${kind}:${req.socket.remoteAddress}`;
  const now = Date.now();
  const recent = (hits.get(key) || []).filter((t) => now - t < 3600e3);
  if (recent.length >= max) throw new HttpError(429, 'Hourly limit reached. Please try again later.');
  recent.push(now);
  hits.set(key, recent);
}

// Remove old uploads so the disk does not fill up.
setInterval(() => {
  const cutoff = Date.now() - TTL_MIN * 60e3;
  for (const [id, v] of videos) if (v.last < cutoff) { fs.rm(v.file, () => {}); videos.delete(id); }
  for (const f of fs.readdirSync(WORK)) {
    const p = path.join(WORK, f);
    try { if (fs.statSync(p).mtimeMs < cutoff) fs.rmSync(p, { force: true }); } catch {}
  }
}, 5 * 60e3).unref();

const json = (res, body, status = 200) => {
  res.writeHead(status, { 'Content-Type': 'application/json' });
  res.end(JSON.stringify(body));
};

// ---------- routes ----------
const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  try {
    if (url.pathname.startsWith('/api/') && req.method === 'POST' && !hasFfmpeg) {
      throw new HttpError(501, 'This server does not have ffmpeg installed, so it cannot process this video. Try an MP4 or MOV file in Chrome or Edge, or install ffmpeg.');
    }
    if (req.method === 'POST' && url.pathname === '/api/video') {
      limit(req, 'upload', HOURLY_UPLOADS);
      const id = crypto.randomUUID();
      const ext = path.extname(url.searchParams.get('name') || '').toLowerCase().replace(/[^.a-z0-9]/g, '') || '.mp4';
      const file = path.join(WORK, id + ext);
      await save(req, file, MAX_VIDEO_MB * 1e6);
      try {
        const info = JSON.parse(await exec('ffprobe', ['-v', 'error', '-show_entries', 'format=duration:stream=codec_type', '-of', 'json', file]));
        if (!info.streams?.some((s) => s.codec_type === 'video')) throw new Error('no video');
        if (Number(info.format.duration) > MAX_VIDEO_MIN * 60) throw new HttpError(413, `Video is too long (limit ${MAX_VIDEO_MIN} minutes).`);
      } catch (e) {
        fs.rm(file, () => {});
        throw e instanceof HttpError ? e : new HttpError(415, 'That file does not look like a video.');
      }
      videos.set(id, { file, ext, last: Date.now() });
      return json(res, { id });
    }

    if (req.method === 'POST' && url.pathname === '/api/export') {
      limit(req, 'export', HOURLY_EXPORTS);
      const v = videos.get(url.searchParams.get('id'));
      if (!v) throw new HttpError(404, 'Video expired or not found. Re-upload it.');
      v.last = Date.now();
      const gain = Math.max(0, Math.min(4, Number(url.searchParams.get('gain') ?? 1)));
      const offset = Math.max(0, Number(url.searchParams.get('offset') ?? 0)); // seconds the voice starts after the video
      const keep = url.searchParams.get('keep') === '1'; // keep original as quiet background
      // spans of the video to leave out, "a-b,c-d" in seconds (the voice already arrives with them removed)
      const cuts = (url.searchParams.get('cuts') || '').split(',').slice(0, 200).map((x) => x.split('-').map(Number))
        .filter(([a, b]) => Number.isFinite(a) && Number.isFinite(b) && a >= 0 && b > a);
      const id = crypto.randomUUID();
      const wav = path.join(WORK, id + '.wav');
      const out = path.join(WORK, id + '.mp4');
      const cleanup = () => { fs.rm(wav, () => {}); fs.rm(out, () => {}); };
      try {
        await save(req, wav, MAX_VOICE_MB * 1e6);
        await withSlot(() => mix(v, wav, out, { gain, offset, keep, cuts }));
      } catch (e) { cleanup(); throw e; }
      res.writeHead(200, { 'Content-Type': 'video/mp4', 'Content-Length': fs.statSync(out).size });
      res.on('close', cleanup); // the finished file is deleted as soon as it has been sent
      return fs.createReadStream(out).pipe(res);
    }

    if (req.method === 'GET' && url.pathname === '/api/video-exists') {
      const v = videos.get(url.searchParams.get('id'));
      if (v) v.last = Date.now();
      return json(res, { ok: !!v });
    }

    if (req.method === 'GET') {
      const rel = url.pathname === '/' ? 'index.html' : url.pathname === '/studio' ? 'studio.html' : url.pathname.slice(1);
      const file = path.join(PUBLIC, path.normalize(rel));
      if (!file.startsWith(PUBLIC) || !fs.existsSync(file) || !fs.statSync(file).isFile()) { res.writeHead(404); return res.end('Not found'); }
      res.writeHead(200, { 'Content-Type': TYPES[path.extname(file)] || 'application/octet-stream', 'Cache-Control': 'no-store' });
      return fs.createReadStream(file).pipe(res);
    }
    res.writeHead(405); res.end();
  } catch (e) {
    const status = e.status || 500;
    if (status === 500) console.error(e);
    if (!res.headersSent) json(res, { error: status === 500 ? 'Something went wrong while processing the video.' : e.message }, status);
    else res.end();
    if (status === 413) req.resume(); // drain so the browser can read the reply
  }
});

// Video is copied untouched when the container allows it; otherwise it is re-encoded to H.264.
// The voice is padded with silence so a take shorter than the video keeps the video's full length.
async function mix(v, wav, out, { gain, offset, keep, cuts }) {
  const delay = Math.round(offset * 1000);
  const voice = `[1:a]adelay=${delay}|${delay},volume=${gain}${cuts.length ? '' : ',apad'}[v]`; // with cuts the voice already arrives at the edited length
  // cut spans are dropped from the picture and from the original sound, which forces the video to be re-encoded
  const gone = cuts.map(([a, b]) => `between(t,${a},${b})`).join('+');
  const vf = cuts.length ? `[0:v:0]select='not(${gone})',setpts=N/FRAME_RATE/TB[vid]` : '';
  const orig = cuts.length ? `[0:a]aselect='not(${gone})',asetpts=N/SR/TB,volume=0.15[o]` : '[0:a]volume=0.15[o]';
  const filters = {
    keep: `${voice};${orig};[o][v]amix=inputs=2:duration=first:normalize=0[a]`,
    plain: `${voice};[v]anull[a]`,
  };
  const tail = ['-c:a', 'aac', '-b:a', '192k', '-movflags', '+faststart', '-shortest', out];
  const copyOk = ['.mp4', '.mov', '.m4v'].includes(v.ext);
  let failure;
  // if the source has no audio track the "keep original" mix fails, so fall back to voice only
  for (const mixName of keep ? ['keep', 'plain'] : ['plain']) {
    const graph = cuts.length ? `${vf};${filters[mixName]}` : filters[mixName];
    const base = ['-i', v.file, '-i', wav, '-filter_complex', graph, '-map', cuts.length ? '[vid]' : '0:v:0', '-map', '[a]'];
    const attempts = copyOk && !cuts.length ? ['copy', 'encode'] : ['encode'];
    for (const how of attempts) {
      const codec = how === 'copy' ? ['-c:v', 'copy'] : ['-c:v', 'libx264', '-preset', 'veryfast', '-pix_fmt', 'yuv420p'];
      try { return await ffmpeg([...base, ...codec, ...tail]); } catch (e) { failure = e; }
    }
  }
  throw failure;
}

const probe = (cmd) => exec(cmd, ['-version']).then(() => true, () => false);
hasFfmpeg = (await probe('ffmpeg')) && (await probe('ffprobe'));
if (!hasFfmpeg) console.warn('ffmpeg/ffprobe not found on PATH. In-browser exports still work; WebM files and "keep original audio" need the server and will be refused.');

server.listen(PORT, () => console.log(`Voiceover Studio on http://localhost:${PORT}`));
process.on('exit', () => fs.rmSync(WORK, { recursive: true, force: true }));
process.on('SIGINT', () => process.exit(0));
process.on('SIGTERM', () => process.exit(0));
