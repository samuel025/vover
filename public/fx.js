// Audio and caption helpers. Everything here is plain maths on Float32Arrays, so it runs on the user's device.

const tick = () => new Promise((r) => setTimeout(r));

// ---------- FFT ----------
function makeFFT(n) {
  const rev = new Uint32Array(n), cos = new Float32Array(n / 2), sin = new Float32Array(n / 2);
  const bits = Math.log2(n);
  for (let i = 0; i < n; i++) { let r = 0; for (let b = 0; b < bits; b++) r |= ((i >> b) & 1) << (bits - 1 - b); rev[i] = r; }
  for (let i = 0; i < n / 2; i++) { cos[i] = Math.cos((2 * Math.PI * i) / n); sin[i] = -Math.sin((2 * Math.PI * i) / n); }
  // in place; invert flips the sign of the imaginary twiddle
  return (re, im, invert) => {
    for (let i = 0; i < n; i++) { const j = rev[i]; if (j > i) { let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
    for (let size = 2; size <= n; size <<= 1) {
      const half = size >> 1, step = n / size;
      for (let s = 0; s < n; s += size) {
        for (let k = 0, w = 0; k < half; k++, w += step) {
          const wr = cos[w], wi = invert ? -sin[w] : sin[w];
          const a = s + k, b = a + half;
          const tr = re[b] * wr - im[b] * wi, ti = re[b] * wi + im[b] * wr;
          re[b] = re[a] - tr; im[b] = im[a] - ti; re[a] += tr; im[a] += ti;
        }
      }
    }
  };
}

// ---------- noise reduction ----------
// Spectral subtraction: the quietest stretches of the recording are taken as the room noise, and that noise
// is turned down in every frame. Sine windows at 50% overlap rebuild the signal exactly.
export async function denoise(x, onProgress) {
  const N = 1024, H = N / 2, fft = makeFFT(N);
  const win = new Float32Array(N).map((_, i) => Math.sin((Math.PI * (i + 0.5)) / N));
  const frames = Math.max(1, Math.floor((x.length - N) / H) + 1);
  // 1. find the quietest tenth of the frames
  const level = new Float32Array(frames);
  for (let f = 0; f < frames; f++) { let e = 0; for (let i = f * H; i < f * H + N; i += 4) e += x[i] * x[i]; level[f] = e; }
  const order = [...level.keys()].sort((a, b) => level[a] - level[b]);
  const quiet = order.slice(0, Math.max(8, Math.min(300, Math.floor(frames / 10))));
  const re = new Float32Array(N), im = new Float32Array(N), noise = new Float32Array(N / 2 + 1);
  for (const f of quiet) {
    for (let i = 0; i < N; i++) { re[i] = (x[f * H + i] || 0) * win[i]; im[i] = 0; }
    fft(re, im, false);
    for (let k = 0; k <= N / 2; k++) noise[k] += Math.hypot(re[k], im[k]) / quiet.length;
  }
  // 2. turn the noise down in every frame
  const out = new Float32Array(x.length), gain = new Float32Array(N / 2 + 1), prev = new Float32Array(N / 2 + 1).fill(1);
  for (let f = 0; f < frames; f++) {
    for (let i = 0; i < N; i++) { re[i] = (x[f * H + i] || 0) * win[i]; im[i] = 0; }
    fft(re, im, false);
    for (let k = 0; k <= N / 2; k++) {
      const m = Math.hypot(re[k], im[k]) || 1e-9;
      gain[k] = Math.max(0.08, 1 - (1.8 * noise[k]) / m);
    }
    for (let k = 0; k <= N / 2; k++) { // smooth across neighbouring bins and across time so no "bubbling" is left behind
      const g = (gain[Math.max(0, k - 1)] + gain[k] + gain[Math.min(N / 2, k + 1)]) / 3;
      const s = Math.max(g, prev[k] * 0.6);
      prev[k] = s;
      re[k] *= s; im[k] *= s;
      if (k > 0 && k < N / 2) { re[N - k] *= s; im[N - k] *= s; }
    }
    fft(re, im, true);
    for (let i = 0; i < N && f * H + i < out.length; i++) out[f * H + i] += (re[i] / N) * win[i];
    if (f % 400 === 0) { onProgress?.(f / frames); await tick(); }
  }
  return out;
}

// Loudness to aim for: the level that 99.9% of the samples stay under, so one click does not decide the volume.
export function normaliseGain(x) {
  const bins = new Uint32Array(1000); let n = 0;
  for (let i = 0; i < x.length; i += 7) { bins[Math.min(999, Math.floor(Math.abs(x[i]) * 1000))]++; n++; }
  if (!n) return 1;
  let acc = 0, p = 0;
  for (let b = 0; b < 1000; b++) { acc += bins[b]; if (acc >= n * 0.999) { p = (b + 1) / 1000; break; } }
  return p < 0.005 ? 1 : Math.min(8, 0.9 / p);
}

// ---------- changing speed without changing pitch (WSOLA) ----------
// r > 1 makes it shorter (faster), r < 1 longer.
export function stretch(x, r) {
  if (Math.abs(r - 1) < 1e-3 || !x.length) return x;
  const N = 1024, Hs = N / 2, tol = 256;
  const win = new Float32Array(N).map((_, i) => 0.5 - 0.5 * Math.cos((2 * Math.PI * i) / N));
  const out = new Float32Array(Math.floor(x.length / r) + N);
  const at = (i) => (i >= 0 && i < x.length ? x[i] : 0);
  let chosen = 0;
  for (let k = 0; ; k++) {
    const nominal = Math.round(k * Hs * r);
    if (nominal >= x.length) break;
    let pos = nominal;
    if (k > 0) {
      const want = chosen + Hs; // where the previous frame would have continued
      let best = -Infinity;
      for (let d = -tol; d <= tol; d += 2) {
        const p = nominal + d;
        if (p < 0) continue;
        let c = 0;
        for (let i = 0; i < Hs; i += 4) c += at(p + i) * at(want + i);
        if (c > best) { best = c; pos = p; }
      }
    }
    chosen = pos;
    const o = k * Hs;
    if (o + N > out.length) break;
    for (let i = 0; i < N; i++) out[o + i] += at(pos + i) * win[i];
  }
  return out.subarray(0, Math.floor(x.length / r));
}

// ---------- background music ----------
// Music loops under the voice and dips while the voice is speaking. Returns voice + music, same length as the voice.
export function mixMusic(voice, music, rate, { volume, duck }) {
  const out = new Float32Array(voice.length), len = music.length;
  if (!len) return voice;
  const win = Math.round(rate * 0.05);
  let env = 1;
  const atk = 1 - Math.exp(-1 / (rate * 0.08)), rel = 1 - Math.exp(-1 / (rate * 0.5));
  const fadeOut = Math.min(voice.length, Math.round(rate * 1.5));
  let target = 1;
  for (let i = 0; i < out.length; i++) {
    if (i % win === 0) {
      if (duck) { let e = 0; const end = Math.min(voice.length, i + win); for (let j = i; j < end; j++) e += voice[j] * voice[j]; target = Math.sqrt(e / win) > 0.012 ? 0.22 : 1; }
      else target = 1;
    }
    env += (target - env) * (target < env ? atk : rel);
    const tail = i > voice.length - fadeOut ? (voice.length - i) / fadeOut : 1;
    const v = voice[i] + music[i % len] * volume * env * tail;
    out[i] = v > 1 ? 1 : v < -1 ? -1 : v;
  }
  return out;
}

// ---------- pauses ----------
// Finds long stretches of silence in the voice and returns the spans (seconds) that can be cut out, leaving a short
// breath of `keep` seconds on each side so the speech does not run together.
export function findPauses(peaks, B, rate, { minPause = 0.9, keep = 0.3 } = {}) {
  if (peaks.length < 8) return [];
  const sorted = [...peaks].sort((a, b) => a - b);
  const floor = sorted[Math.floor(sorted.length * 0.1)];
  const limit = Math.max(0.012, floor * 3);
  const sec = (i) => (i * B) / rate;
  const out = [];
  let start = -1;
  for (let i = 0; i <= peaks.length; i++) {
    const quiet = i < peaks.length && peaks[i] < limit;
    if (quiet && start < 0) start = i;
    if (!quiet && start >= 0) {
      const a = sec(start), b = sec(i);
      if (b - a >= minPause) out.push({ a: a + keep, b: b - keep });
      start = -1;
    }
  }
  return out;
}

// ---------- captions ----------
// The script is already cut into sections with start times. Inside each section the words are spread across the
// section's span (longer words get more time) and grouped into short lines.
export function buildCaptions(sections, endTime, maxWords = 6) {
  const out = [];
  sections.forEach((sec, i) => {
    const words = sec.text.split(/\s+/).filter(Boolean);
    if (!words.length) return;
    const a = sec.start, b = i + 1 < sections.length ? sections[i + 1].start : endTime;
    const weight = words.map((w) => w.length + 2), total = weight.reduce((n, x) => n + x, 0);
    let t = a, line = [], lineStart = a;
    words.forEach((w, k) => {
      line.push(w);
      t += ((b - a) * weight[k]) / total;
      if (line.length >= maxWords || /[.?!]$/.test(w) || k === words.length - 1) {
        out.push({ t0: lineStart, t1: t, text: line.join(' ') });
        line = []; lineStart = t;
      }
    });
  });
  return out;
}

const stamp = (t) => {
  const ms = Math.round(t * 1000), p = (n, l = 2) => String(n).padStart(l, '0');
  return `${p(Math.floor(ms / 3600000))}:${p(Math.floor(ms / 60000) % 60)}:${p(Math.floor(ms / 1000) % 60)},${p(ms % 1000, 3)}`;
};
export const toSrt = (lines) => lines.map((l, i) => `${i + 1}\n${stamp(l.t0)} --> ${stamp(l.t1)}\n${l.text}\n`).join('\n');

// ---------- voice presets: equaliser and de-esser ----------
function biquad(type, f0, Q, gainDb, rate) {
  const A = Math.pow(10, gainDb / 40), w0 = (2 * Math.PI * f0) / rate, cos = Math.cos(w0), sin = Math.sin(w0), alpha = sin / (2 * Q);
  let b0, b1, b2, a0, a1, a2;
  if (type === 'hp') { b0 = (1 + cos) / 2; b1 = -(1 + cos); b2 = (1 + cos) / 2; a0 = 1 + alpha; a1 = -2 * cos; a2 = 1 - alpha; }
  else if (type === 'bp') { b0 = alpha; b1 = 0; b2 = -alpha; a0 = 1 + alpha; a1 = -2 * cos; a2 = 1 - alpha; }
  else if (type === 'peak') { b0 = 1 + alpha * A; b1 = -2 * cos; b2 = 1 - alpha * A; a0 = 1 + alpha / A; a1 = -2 * cos; a2 = 1 - alpha / A; }
  else {
    const sq = 2 * Math.sqrt(A) * alpha;
    if (type === 'lowshelf') { b0 = A * (A + 1 - (A - 1) * cos + sq); b1 = 2 * A * (A - 1 - (A + 1) * cos); b2 = A * (A + 1 - (A - 1) * cos - sq); a0 = A + 1 + (A - 1) * cos + sq; a1 = -2 * (A - 1 + (A + 1) * cos); a2 = A + 1 + (A - 1) * cos - sq; }
    else { b0 = A * (A + 1 + (A - 1) * cos + sq); b1 = -2 * A * (A - 1 + (A + 1) * cos); b2 = A * (A + 1 + (A - 1) * cos - sq); a0 = A + 1 - (A - 1) * cos + sq; a1 = 2 * (A - 1 - (A + 1) * cos); a2 = A + 1 - (A - 1) * cos - sq; }
  }
  return [b0 / a0, b1 / a0, b2 / a0, a1 / a0, a2 / a0];
}
function runFilter(x, [b0, b1, b2, a1, a2]) { // in place
  let x1 = 0, x2 = 0, y1 = 0, y2 = 0;
  for (let i = 0; i < x.length; i++) {
    const v = x[i], y = b0 * v + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2;
    x2 = x1; x1 = v; y2 = y1; y1 = y; x[i] = y;
  }
}

// [type, frequency Hz, Q, gain dB]
export const EQ_PRESETS = {
  podcast: [['hp', 80, 0.7, 0], ['peak', 250, 1, -2.5], ['peak', 3500, 1, 2.5], ['highshelf', 10000, 0.7, 2]], // clear and present
  warm: [['hp', 70, 0.7, 0], ['lowshelf', 150, 0.7, 3], ['peak', 3000, 1, 1.5], ['highshelf', 9000, 0.7, -1.5]],  // fuller, softer top
  bright: [['hp', 100, 0.7, 0], ['peak', 300, 1, -2], ['peak', 4500, 1, 3.5], ['highshelf', 9000, 0.7, 3]],       // crisp, for dull recordings
};

// The "s" and "t" sounds sit around 5 to 9 kHz. That band is turned down only while it is louder than usual, the rest is untouched.
export function deess(x, rate, amount) {
  const [ratio, floor, pct] = amount === 'strong' ? [6, 0.25, 0.5] : [3, 0.5, 0.65]; // how hard, the most it may turn down, and how much of the sibilance counts as normal
  const band = Float32Array.from(x);
  runFilter(band, biquad('bp', 6500, 1.2, 0, rate));
  const att = 1 - Math.exp(-1 / (rate * 0.001)), rel = 1 - Math.exp(-1 / (rate * 0.04));
  const env = new Float32Array(x.length);
  let e = 0;
  for (let i = 0; i < x.length; i++) { const a = Math.abs(band[i]); e += (a - e) * (a > e ? att : rel); env[i] = e; }
  const sample = [];
  for (let i = 0; i < env.length; i += 64) if (env[i] > 1e-4) sample.push(env[i]);
  if (sample.length < 50) return x;
  sample.sort((a, b) => a - b);
  const thr = sample[Math.floor(sample.length * pct)]; // what is louder than this much sibilance is turned down
  const out = new Float32Array(x.length);
  for (let i = 0; i < x.length; i++) {
    const gain = env[i] > thr ? Math.max(floor, Math.pow(thr / env[i], 1 - 1 / ratio)) : 1;
    out[i] = x[i] - band[i] * (1 - gain);
  }
  return out;
}

export function enhanceVoice(x, rate, { eq, deess: amount }) {
  let y = x;
  if (EQ_PRESETS[eq]) { y = Float32Array.from(x); for (const [t, f, q, g] of EQ_PRESETS[eq]) runFilter(y, biquad(t, f, q, g, rate)); }
  if (amount === 'light' || amount === 'strong') y = deess(y, rate, amount);
  return y;
}

// ---------- zoom and pan ----------
// A zoom is { a, b, k, x1, y1, x2, y2 }: from time a to b the picture is zoomed to k times, looking at (x1, y1) and sliding
// to (x2, y2). Positions are fractions of the picture. It eases in and out over the first and last half second.
// Returns the visible window as fractions of the picture ({ k, x, y, w } with x, y the top-left), or null when no zoom is on.
export function zoomState(zooms, g) {
  const z = zooms.find((q) => g >= q.a && g < q.b);
  if (!z) return null;
  const len = z.b - z.a, ramp = Math.max(0.01, Math.min(0.5, len / 3)), t = g - z.a;
  const u = Math.min(1, t / ramp, (z.b - g) / ramp), f = u * u * (3 - 2 * u);
  const k = 1 + (z.k - 1) * f, w = 1 / k, p = len > 0 ? t / len : 0;
  const cx = z.x1 + (z.x2 - z.x1) * p, cy = z.y1 + (z.y2 - z.y1) * p;
  return { k, w, x: Math.max(0, Math.min(1 - w, cx - w / 2)), y: Math.max(0, Math.min(1 - w, cy - w / 2)) };
}
