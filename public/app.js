import { denoise, normaliseGain, stretch, mixMusic, findPauses, buildCaptions, toSrt } from './fx.js';
import { exportLocally, pickSaveTarget, Unsupported } from './export.js';

const $ = (id) => document.getElementById(id);
const video = $('video'), scriptEl = $('script'), prompter = $('prompter'), wordsEl = $('words');
const timeline = $('timeline'), canvas = $('wave');

// take.samples holds the voice on the video's own timeline: sample 0 is video time 0.
const state = { file: null, serverId: null, take: null, recording: false, recPaused: false, playing: false, range: null, attempts: {} };
let ctx, stream, node, analyser, voiceSrc, listenSrc, mixCache = null, workletReady = false;
let base = new Float32Array(0), chunks = [], chunkLen = 0, capturing = false;
let spans = [], lastNow = -1, lastSec = -1;
let speed = 1;
let capStart = 0, draft = null;
let cuts = [], cutStart = null, splits = [], speeds = [], editVer = 0, history = [], future = [], music = null, musicId = 0;
let cleaned = null, cleaning = null, finalCache = {}, abCache = null, lastClipKey = '', lastCap = null;
// cuts: { a, b } spans of the video (seconds) that are skipped in playback and left out of the export

const B = 1024; // samples per waveform bucket
let peaks = [], curMax = 0, curCnt = 0;

const fmt = (t) => `${Math.floor(t / 60)}:${(t % 60).toFixed(1).padStart(4, '0')}`;
const status = (s) => ($('status').textContent = s);
const hasTake = () => !!state.take && state.take.samples.length > 0;
const canSeek = () => !!state.file && (!state.recording || state.recPaused);

// ---------- persistence (survives a page refresh) ----------
const db = new Promise((res) => {
  const r = indexedDB.open('voiceover-studio', 1);
  r.onupgradeneeded = () => r.result.createObjectStore('kv');
  r.onsuccess = () => res(r.result);
  r.onerror = () => res(null);
});
const kv = {
  async get(k) { const d = await db; return d ? new Promise((r) => { const q = d.transaction('kv').objectStore('kv').get(k); q.onsuccess = () => r(q.result); q.onerror = () => r(); }) : undefined; },
  async set(k, v) {
    const d = await db;
    if (!d) return false;
    return new Promise((r) => {
      try {
        const tx = d.transaction('kv', 'readwrite');
        tx.objectStore('kv').put(v, k);
        tx.oncomplete = () => r(true);
        tx.onerror = tx.onabort = () => r(false);
      } catch { r(false); }
    });
  },
  async del(k) { const d = await db; if (d) try { d.transaction('kv', 'readwrite').objectStore('kv').delete(k); } catch {} },
};
const saveTake = () => (hasTake() ? kv.set('take', state.take) : kv.del('take'));
const saveAttempts = () => kv.set('attempts', state.attempts);
const getCtx = () => (ctx ||= new AudioContext());
const concat = (arrs) => { const out = new Float32Array(arrs.reduce((n, a) => n + a.length, 0)); let o = 0; for (const a of arrs) { out.set(a, o); o += a.length; } return out; };
const hasEnergy = (a) => { for (let i = 0; i < a.length; i += 16) if (Math.abs(a[i]) > 0.01) return true; return false; };
scriptEl.addEventListener('input', () => { try { localStorage.setItem('script', scriptEl.value); } catch {} });

// ---------- ui state ----------
function updateUI() {
  const v = !!state.file, rec = state.recording, idle = v && (!rec || state.recPaused);
  $('rec').disabled = !v;
  $('rec').classList.toggle('live', rec);
  $('pauseRec').hidden = !rec;
  $('pauseRec').textContent = state.recPaused ? 'Resume' : 'Pause';
  $('play').disabled = !v || (rec && !state.recPaused); // playback is allowed while recording is paused, to find the trim point
  $('play').textContent = state.playing ? 'Pause' : 'Play';
  ['toStart', 'back', 'fwd'].forEach((k) => ($(k).disabled = !idle));
  $('trim').disabled = !idle || !hasTake();
  $('cut').disabled = !idle;
  $('undo').disabled = !idle || !history.length; $('redo').disabled = !idle || !future.length;
  const gone = v && !!video.duration && editedLen() < 0.05; // every clip was deleted
  for (const k of ['split', 'clipSpeed', 'delClip']) $(k).disabled = !idle || gone;
  wrap.classList.toggle('gone', gone);
  if (gone) for (const k of ['cut', 'rec', 'play', 'toStart', 'back', 'fwd']) $(k).disabled = true;
  $('pauses').disabled = !idle || !hasTake();
  $('srt').disabled = !v;
  $('cut').textContent = cutStart === null ? '✂ Cut' : '✂ Cut ends here';
  $('clear').disabled = rec || !hasTake();
  $('export').disabled = rec || !(hasTake() || music) || gone;
  $('hear').disabled = rec;
  secEl.classList.toggle('busy', rec && !state.recPaused);
  timeline.classList.toggle('disabled', !v);
  $('badge').hidden = !rec;
  $('badge').classList.toggle('paused', state.recPaused);
  $('badgeText').textContent = state.recPaused ? 'PAUSED' : 'REC';
  updateRecLabel();
  $('takeLen').textContent = hasTake() ? `voice ${fmt(toEdit(state.take.samples.length / state.take.rate))}` : '';
}
function updateRecLabel() {
  const t = video.currentTime;
  $('recLabel').textContent = state.recording ? 'Stop' : hasTake() && t > 0.05 ? `Record from ${fmt(toEdit(t))}` : 'Record';
}

// ---------- video upload ----------
// The video stays on this device. It is only sent to the server if a server export is needed (see export below).
async function loadVideo(file, restored) {
  if (!file) return;
  stopAll();
  if (!restored) { discardTake(); kv.set('video', { file }); cuts = []; splits = []; speeds = []; cutStart = null; history = []; future = []; touched(); try { localStorage.removeItem('edit'); } catch {} }
  state.file = file; state.serverId = null;
  video.src = URL.createObjectURL(file) + '#t=0.001'; // starting a hair in makes the browser paint the first frame instead of a blank player
  video.hidden = false;
  $('empty').hidden = true;
  navigator.storage?.persist?.();
  if (!restored && !(await kv.set('video', { file }))) status('Ready, but the browser would not save this video, so a refresh will clear it.');
  else status(restored ? 'Welcome back. Your video, script and take were restored.' : 'Ready. Paste your script, then press Record.');
  updateUI();
}
$('file').onchange = (e) => loadVideo(e.target.files[0]);

const wrap = $('videoWrap');
// listen on the whole window so a drop anywhere on the page is caught instead of the browser opening the file
let dragDepth = 0;
const hasFiles = (e) => [...(e.dataTransfer?.types || [])].includes('Files');
window.addEventListener('dragenter', (e) => { if (hasFiles(e)) { dragDepth++; wrap.classList.add('drag'); } });
window.addEventListener('dragleave', (e) => { if (hasFiles(e) && --dragDepth <= 0) { dragDepth = 0; wrap.classList.remove('drag'); } });
window.addEventListener('dragover', (e) => { if (hasFiles(e)) e.preventDefault(); });
window.addEventListener('drop', (e) => {
  if (!hasFiles(e)) return;
  e.preventDefault(); dragDepth = 0; wrap.classList.remove('drag');
  const f = [...e.dataTransfer.files].find((x) => x.type.startsWith('video/') || /\.(mp4|mov|webm|m4v|mkv)$/i.test(x.name));
  if (f) loadVideo(f); else status('That file is not a video.');
});

video.onloadedmetadata = () => { loadEdit(); layoutWords(); drawWave(); };
video.onended = () => { if (state.playing) stopPlay(); else if (state.recording && !state.recPaused) stopRecording(); };

// ---------- timeline (playhead + scrub) ----------
function seekTo(t) {
  if (!canSeek() || !video.duration) return;
  const c = cutAt(t);
  if (c) t = c.b < video.duration ? c.b : c.a; // never park the playhead inside a cut
  video.currentTime = Math.max(0, Math.min(video.duration, t));
  if (state.playing) startVoice();
}
function scrubAt(e) {
  const r = timeline.getBoundingClientRect();
  seekTo(toSrc(Math.max(0, Math.min(1, (e.clientX - r.left) / r.width)) * editedLen()));
}
let scrubbing = false;
timeline.onpointerdown = (e) => { if (!canSeek()) return; scrubbing = true; timeline.setPointerCapture(e.pointerId); scrubAt(e); };
timeline.onpointermove = (e) => { if (scrubbing) scrubAt(e); };
timeline.onpointerup = timeline.onpointercancel = () => { scrubbing = false; };

// ---------- editing: cuts, splits, clip speed, undo ----------
// The original video is never changed. Everything below is a list of edits: parts to skip (cuts), places where it was
// split into clips (splits) and parts that play faster or slower (speeds). Playback follows the list and the export applies it.
// The timeline shows the edited video, so the functions toEdit and toSrc convert between video time and timeline time.
const cutAt = (t) => cuts.find((c) => t >= c.a && t < c.b);
const speedAt = (t) => speeds.find((x) => t >= x.a && t < x.b)?.r ?? 1;
const keptSpans = () => {
  const out = []; let at = 0;
  if (!video.duration) return out;
  for (const c of cuts) { if (c.a > at) out.push({ a: at, b: c.a }); at = c.b; }
  if (at < video.duration) out.push({ a: at, b: video.duration });
  return out;
};
const touched = () => { editVer++; abCache = null; };

// the kept video as pieces of constant speed, with where each starts on the edited timeline
let segCache = null;
function segs() {
  if (segCache?.ver === editVer && segCache.dur === video.duration) return segCache.list;
  const list = []; let e = 0;
  for (const k of keptSpans()) {
    const edges = [k.a, ...speeds.flatMap((x) => [x.a, x.b]).filter((t) => t > k.a && t < k.b), k.b].sort((x, y) => x - y);
    for (let i = 0; i + 1 < edges.length; i++) {
      const a = edges[i], b = edges[i + 1];
      if (b - a < 1e-6) continue;
      const r = speedAt((a + b) / 2);
      list.push({ a, b, r, e0: e });
      e += (b - a) / r;
    }
  }
  segCache = { ver: editVer, dur: video.duration, list, total: e };
  return list;
}
const editedLen = () => { segs(); return segCache.total; };
function toEdit(t) {
  const list = segs();
  if (!list.length) return t;
  for (const g of list) {
    if (t < g.a) return g.e0;
    if (t <= g.b) return g.e0 + (t - g.a) / g.r;
  }
  return editedLen();
}
function toSrc(e) {
  const list = segs();
  if (!list.length) return e;
  for (const g of list) if (e < g.e0 + (g.b - g.a) / g.r - 1e-9) return g.a + (Math.max(0, e - g.e0)) * g.r;
  return list[list.length - 1].b;
}
const seekBy = (d) => seekTo(toSrc(Math.max(0, Math.min(editedLen(), toEdit(video.currentTime) + d))));

// clips are the kept parts between split points
function clipAt(t) {
  t = Math.min(t, (video.duration || 0) - 1e-3);
  const k = keptSpans().find((x) => t >= x.a && t < x.b);
  if (!k) return null;
  let a = k.a, b = k.b;
  for (const x of [...splits].sort((m, n) => m - n)) { if (x <= k.a || x >= k.b) continue; if (x <= t) a = x; else { b = x; break; } }
  return { a, b };
}
const allClips = () => {
  const out = [];
  for (const k of keptSpans()) {
    let a = k.a;
    for (const x of [...splits].sort((m, n) => m - n)) if (x > k.a && x < k.b) { out.push({ a, b: x }); a = x; }
    out.push({ a, b: k.b });
  }
  return out;
};

function saveEdit() { try { localStorage.setItem('edit', JSON.stringify({ dur: video.duration, cuts, splits, speeds })); } catch {} }
function loadEdit() {
  cuts = []; splits = []; speeds = [];
  try {
    const e = JSON.parse(localStorage.getItem('edit') || 'null');
    if (e && Math.abs(e.dur - video.duration) < 0.01) { cuts = e.cuts || []; splits = e.splits || []; speeds = e.speeds || []; }
  } catch {}
  touched(); renderCuts();
}

// undo / redo: a snapshot is the edit lists plus the recorded voice (the voice arrays are never changed in place, so keeping them is cheap)
const snap = () => ({ edit: JSON.stringify({ cuts, splits, speeds }), take: state.take ? { samples: state.take.samples, rate: state.take.rate } : null });
function checkpoint() { history.push(snap()); if (history.length > 15) history.shift(); future = []; updateUI(); }
function applySnap(sn) {
  const e = JSON.parse(sn.edit);
  cuts = e.cuts; splits = e.splits; speeds = e.speeds; cutStart = null;
  state.take = sn.take ? { ...sn.take } : null; mixCache = null;
  rebuildPeaks(state.take?.samples || new Float32Array(0));
  saveEdit(); saveTake(); touched(); renderCuts(); renderSections(); drawWave(); updateUI();
}
function undo() { if (!canSeek() || !history.length) return; stopPlay(); future.push(snap()); applySnap(history.pop()); status('Undone.'); }
function redo() { if (!canSeek() || !future.length) return; stopPlay(); history.push(snap()); applySnap(future.pop()); status('Redone.'); }
$('undo').onclick = undo;
$('redo').onclick = redo;

function mergeCut(a, b) {
  const rest = cuts.filter((c) => c.b < a || c.a > b), hit = cuts.filter((c) => !(c.b < a || c.a > b));
  cuts = [...rest, { a: Math.min(a, ...hit.map((c) => c.a)), b: Math.max(b, ...hit.map((c) => c.b)) }].sort((x, y) => x.a - y.a);
  splits = splits.filter((t) => t <= a || t >= b);
}
function commitEdit() { touched(); saveEdit(); renderCuts(); }

function renderCuts() {
  const L = editedLen() || 1, pct = (t) => (toEdit(t) / L) * 100 + '%';
  const tiles = [];
  for (const g of segs()) { // faster / slower parts, merged when they touch
    const last = tiles[tiles.length - 1];
    if (g.r === 1) continue;
    if (last && last.r === g.r && Math.abs(last.e1 - g.e0) < 1e-6) last.e1 = g.e0 + (g.b - g.a) / g.r;
    else tiles.push({ r: g.r, e0: g.e0, e1: g.e0 + (g.b - g.a) / g.r });
  }
  $('cuts').innerHTML =
    tiles.map((x) => `<b class="spd" style="left:${(x.e0 / L) * 100}%;width:${((x.e1 - x.e0) / L) * 100}%">${x.r}×</b>`).join('')
    + splits.filter((t) => !cutAt(t)).map((t) => `<i class="split" style="left:${pct(t)}"></i>`).join('')
    + cuts.filter((c) => c.a > 0 && c.b < video.duration).map((c) => `<i style="left:${pct(c.a)}"></i>`).join('')
    + (cutStart === null ? '' : `<i class="pending" style="left:${pct(cutStart)}"></i>`);
  $('dur').textContent = fmt(editedLen());
  const bar = $('cutbar');
  bar.hidden = !cuts.length && cutStart === null;
  bar.innerHTML = (cutStart !== null
    ? `<span>Cut starts at ${fmt(toEdit(cutStart))}. Move to where it ends, then press Cut again (Esc cancels).</span>`
    : cuts.map((c, i) => `<span>✂ ${(c.b - c.a).toFixed(1)}s removed at ${fmt(toEdit(c.a))}</span><button class="btn ghost" data-restore="${i}">Restore</button>`).join(''))
    + (cuts.length ? `<span class="sub">Edited length ${fmt(editedLen())}</span>` : '');
  lastClipKey = '';
  drawWave(); renderMarks(); updateUI();
}
$('cutbar').onclick = (e) => {
  const i = e.target.dataset?.restore;
  if (i === undefined) return;
  checkpoint(); cuts.splice(+i, 1); commitEdit(); status('Cut restored.');
};

// the clip under the playhead is the selected one: it is outlined on the timeline and is what Delete and Clip speed act on
function updateClip() {
  const c = video.duration ? clipAt(video.currentTime) : null, key = c ? c.a + '-' + c.b + '-' + editVer : '';
  if (key === lastClipKey) return;
  lastClipKey = key;
  const sel = $('clipSel'), L = editedLen() || 1;
  if (!c) { sel.style.display = 'none'; $('clipInfo').textContent = ''; return; }
  const e0 = toEdit(c.a), e1 = toEdit(c.b), n = allClips();
  sel.style.display = n.length > 1 ? '' : 'none';
  sel.style.left = (e0 / L) * 100 + '%'; sel.style.width = ((e1 - e0) / L) * 100 + '%';
  $('clipInfo').textContent = `Clip ${n.findIndex((x) => x.a === c.a) + 1} of ${n.length} · ${(e1 - e0).toFixed(1)}s`;
  $('clipSpeed').value = String(speedAt((c.a + c.b) / 2));
}

function cutPress() {
  if (!canSeek()) return;
  const t = video.currentTime;
  if (cutStart === null) { cutStart = t; renderCuts(); return status(`Cut starts at ${fmt(toEdit(t))}. Move to where it ends, then press Cut again.`); }
  const a = Math.min(cutStart, t), b = Math.max(cutStart, t);
  if (b - a < 0.1) return status('Move the playhead away from the start point first.');
  cutStart = null;
  checkpoint(); mergeCut(a, b); commitEdit();
  seekTo(b);
  status(`Removed ${(b - a).toFixed(1)}s. It is skipped in playback and left out of the export.`);
}
function cancelCut() { if (cutStart !== null) { cutStart = null; renderCuts(); status('Cut cancelled.'); } }
$('cut').onclick = cutPress;

function splitHere() {
  if (!canSeek()) return;
  const t = video.currentTime, c = clipAt(t);
  if (!c || t - c.a < 0.15 || c.b - t < 0.15) return status('Move the playhead into the middle of a clip to split it.');
  checkpoint(); splits.push(t); commitEdit();
  status(`Split at ${fmt(toEdit(t))}. Click a clip, then press Delete to remove it.`);
}
function deleteClip() {
  if (!canSeek()) return;
  const c = clipAt(video.currentTime);
  if (!c) return;
  const all = editedLen() - (toEdit(c.b) - toEdit(c.a)) < 0.05;
  checkpoint(); mergeCut(c.a, c.b); commitEdit();
  if (all) { seekTo(0); return status('Everything was deleted. Press Undo (Ctrl+Z) to bring it back.'); }
  seekTo(c.b);
  status(`Deleted the clip (${(c.b - c.a).toFixed(1)}s).`);
}
function setClipSpeed(r) {
  if (!canSeek()) return;
  const c = clipAt(video.currentTime);
  if (!c) return;
  checkpoint();
  const next = [];
  for (const x of speeds) { // keep what lies outside this clip
    if (x.b <= c.a || x.a >= c.b) next.push(x);
    else { if (x.a < c.a - 0.01) next.push({ ...x, b: c.a }); if (x.b > c.b + 0.01) next.push({ ...x, a: c.b }); }
  }
  if (r !== 1) next.push({ a: c.a, b: c.b, r });
  speeds = next.sort((m, n) => m.a - n.a);
  commitEdit();
  status(r === 1 ? 'Clip back to normal speed.' : `Clip now plays at ${r}×. The voice is sped up to match when you export.`);
}
$('split').onclick = splitHere;
$('delClip').onclick = deleteClip;
$('clipSpeed').onchange = (e) => setClipSpeed(+e.target.value);

// cut out long silences in the recording (and the video under them)
$('pauses').onclick = () => {
  if (!hasTake()) return;
  const found = findPauses(peaks, B, state.take.rate).filter((x) => x.b - x.a > 0.1);
  if (!found.length) return status('No long pauses found.');
  checkpoint();
  let saved = 0;
  for (const x of found) { mergeCut(x.a, x.b); saved += x.b - x.a; }
  commitEdit();
  status(`Removed ${found.length} long pause${found.length > 1 ? 's' : ''}, ${saved.toFixed(1)}s in all. Undo brings them back.`);
};

// ---------- audio: noise, volume, fades, music ----------
function ensureClean() {
  if (!$('denoise').checked || !hasTake() || cleaned?.ref === state.take.samples) return Promise.resolve();
  return (cleaning ||= (async () => {
    const ref = state.take.samples;
    status('Reducing background noise…');
    const out = await denoise(ref, (p) => status(`Reducing background noise… ${Math.round(p * 100)}%`));
    cleaned = { ref, samples: out }; mixCache = null; touched();
    status('Background noise reduced.');
  })().finally(() => { cleaning = null; }));
}
const zeros = (n) => new Float32Array(Math.max(0, Math.round(n)));
const titleCard = (k) => { const text = $(k + 'Text').value.trim(), sec = +$(k + 'Sec').value; return text && sec > 0 ? { text, sec } : null; };

// The finished sound for the edited video: voice with cuts and speed changes applied, fades, then music underneath.
// With `cards` it also leaves room for the title cards (that is the export; playback has no cards).
function finalAudio(cards = false) {
  const base = hasTake() ? mixed() : { samples: new Float32Array(0), rate: getCtx().sampleRate };
  const intro = cards ? titleCard('intro') : null, outro = cards ? titleCard('outro') : null;
  const key = [editVer, $('fade').value, $('mvol').value, $('duck').checked, music?.id, intro?.sec, outro?.sec].join('|');
  const hit = finalCache[cards];
  if (hit && hit.key === key && hit.base === base) return hit.audio;
  const rate = base.rate, list = segs(), joint = Math.round(rate * 0.01);
  const parts = list.map((g) => {
    const from = Math.round(g.a * rate), len = Math.round((g.b - g.a) * rate), raw = new Float32Array(len);
    if (from < base.samples.length) raw.set(base.samples.subarray(from, from + len));
    const out = stretch(raw, g.r);
    if (list.length > 1) for (let i = 0; i < Math.min(joint, out.length >> 1); i++) { const k = i / joint; out[i] *= k; out[out.length - 1 - i] *= k; } // no click where a cut joins
    return out;
  });
  let v = concat(parts);
  const L = Math.round(editedLen() * rate);
  if (v.length < L) v = concat([v, zeros(L - v.length)]);
  const fade = Math.round(+$('fade').value * rate);
  for (let i = 0; i < Math.min(fade, v.length >> 1); i++) { const k = i / fade; v[i] *= k; v[v.length - 1 - i] *= k; }
  if (intro || outro) v = concat([zeros((intro?.sec || 0) * rate), v, zeros((outro?.sec || 0) * rate)]);
  if (music) v = mixMusic(v, music.samples, rate, { volume: $('mvol').value / 100, duck: $('duck').checked });
  const audio = { samples: v, rate };
  finalCache[cards] = { key, base, audio };
  return audio;
}

async function loadMusic(file, restored) {
  try {
    const buf = await getCtx().decodeAudioData(await file.arrayBuffer()); // decoding also converts it to this device's sample rate
    const mono = new Float32Array(buf.length);
    for (let c = 0; c < buf.numberOfChannels; c++) { const d = buf.getChannelData(c); for (let i = 0; i < mono.length; i++) mono[i] += d[i] / buf.numberOfChannels; }
    music = { samples: mono, name: file.name, id: ++musicId };
    if (!restored) kv.set('music', { file });
    $('musicName').textContent = file.name; $('musicOpts').hidden = false;
    touched(); updateUI();
    if (!restored) status('Music added. It loops under your voice and dips while you speak.');
  } catch { status('Could not read that audio file.'); }
}
$('musicFile').onchange = (e) => { if (e.target.files[0]) loadMusic(e.target.files[0]); e.target.value = ''; };
$('musicOff').onclick = () => { music = null; kv.del('music'); $('musicName').textContent = ''; $('musicOpts').hidden = true; touched(); updateUI(); };

// ---------- picture & text settings ----------
const fxIds = ['denoise', 'norm', 'fade', 'mvol', 'duck', 'shape', 'crop', 'caps', 'introText', 'introSec', 'outroText', 'outroSec'];
function applyShape() {
  const sh = $('shape').value;
  wrap.classList.toggle('shape-vertical', sh === 'vertical');
  wrap.classList.toggle('shape-square', sh === 'square');
  wrap.style.setProperty('--crop', $('crop').value + '%');
  $('cropRow').hidden = sh === 'original';
}
for (const id of fxIds) {
  $(id).addEventListener('change', () => {
    try { localStorage.setItem('fx', JSON.stringify(Object.fromEntries(fxIds.map((k) => [k, $(k).type === 'checkbox' ? $(k).checked : $(k).value])))); } catch {}
    if (id === 'denoise' || id === 'norm') { mixCache = null; touched(); }
    if (id === 'denoise') ensureClean();
    applyShape(); touched();
  });
}
$('crop').addEventListener('input', applyShape);
try {
  const f = JSON.parse(localStorage.getItem('fx') || 'null');
  if (f) for (const k of fxIds) if (k in f) { if ($(k).type === 'checkbox') $(k).checked = f[k]; else $(k).value = f[k]; }
} catch {}

// captions: the script's words spread over each section's time span
let capCache = null;
function captionList() {
  const key = sections.map((x) => x.start.toFixed(2)).join() + '|' + scriptEl.value.length + '|' + video.duration;
  if (capCache?.key !== key) capCache = { key, list: buildCaptions(sections, video.duration || 0) };
  return capCache.list;
}
$('srt').onclick = () => {
  const lead = titleCard('intro')?.sec || 0;
  const lines = captionList().map((c) => ({ t0: toEdit(c.t0) + lead, t1: toEdit(c.t1) + lead, text: c.text })).filter((l) => l.t1 - l.t0 > 0.05);
  if (!lines.length) return status('Add a script first, there is nothing to caption.');
  Object.assign(document.createElement('a'), { href: URL.createObjectURL(new Blob([toSrt(lines)], { type: 'text/plain' })), download: 'captions.srt' }).click();
  status('Captions downloaded. Their timing follows your section start times, so use "Fit to my voice" for the best match.');
};

function drawWave() {
  const dpr = devicePixelRatio || 1;
  canvas.width = canvas.clientWidth * dpr;
  canvas.height = canvas.clientHeight * dpr;
  const g = canvas.getContext('2d'), W = canvas.width, H = canvas.height;
  g.clearRect(0, 0, W, H);
  const L = editedLen();
  if (!L || !ctx && !peaks.length) return;
  const rate = state.take?.rate || ctx?.sampleRate || 48000;
  const perPx = L / W; // seconds of edited video per pixel
  g.fillStyle = '#ffb88e26';
  g.fillRect(0, 0, Math.min(W, (toEdit(Math.min(video.duration, (peaks.length * B) / rate)) / L) * W), H);
  g.fillStyle = '#f08a4b';
  for (let x = 0; x < W; x++) {
    const s0 = toSrc(x * perPx), b0 = Math.floor((s0 * rate) / B), b1 = Math.max(b0 + 1, Math.floor(((s0 + perPx) * rate) / B));
    if (b0 >= peaks.length) break;
    let mx = 0;
    for (let b = b0; b < b1 && b < peaks.length; b++) mx = Math.max(mx, peaks[b]);
    const h = Math.max(2 * dpr, Math.min(1, mx * 1.6) * H * 0.9);
    g.fillRect(x, (H - h) / 2, 1, h);
  }
}
addEventListener('resize', drawWave);

function pushPeaks(arr) {
  for (let i = 0; i < arr.length; i++) {
    const a = Math.abs(arr[i]);
    if (a > curMax) curMax = a;
    if (++curCnt === B) { peaks.push(curMax); curMax = 0; curCnt = 0; }
  }
}
function rebuildPeaks(samples) { peaks = []; curMax = 0; curCnt = 0; pushPeaks(samples); }

// ---------- script, sections and teleprompter ----------
// A blank line in the script starts a new section. Every section has a start time on the video, and the
// teleprompter reads a section across the span between its start and the next section's start.
let sections = []; // { text, w0 (index of its first word), n (word count), start (seconds) }
const secEl = $('sections');
const esc = (t) => t.replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

const sectionEnd = (i) => (i + 1 < sections.length ? sections[i + 1].start : video.duration || 0);
function sectionAt(t) { let i = 0; while (i + 1 < sections.length && t >= sections[i + 1].start - 1e-6) i++; return i; }

function spreadEvenly() {
  const total = sections.reduce((n, x) => n + x.n, 0) || 1;
  let seen = 0;
  for (const x of sections) { x.start = (video.duration || 0) * (seen / total); seen += x.n; }
}
function saveMarks() { try { localStorage.setItem('marks', JSON.stringify({ n: sections.length, dur: video.duration, starts: sections.map((x) => x.start) })); } catch {} }
function loadMarks() {
  try {
    const m = JSON.parse(localStorage.getItem('marks'));
    if (m && m.n === sections.length && Math.abs(m.dur - video.duration) < 0.5) { sections.forEach((x, i) => (x.start = m.starts[i])); return true; }
  } catch {}
  return false;
}

function layoutWords() {
  let w0 = 0;
  sections = scriptEl.value.split(/\n\s*\n/).map((t) => t.trim()).filter(Boolean).map((text) => {
    const n = text.split(/\s+/).length, x = { text, w0, n, start: 0 };
    w0 += n;
    return x;
  });
  if (!(video.duration && loadMarks())) spreadEvenly();
  wordsEl.replaceChildren(...sections.map((x) => {
    const para = document.createElement('p');
    para.append(...x.text.split(/\s+/).map((w) => Object.assign(document.createElement('span'), { textContent: w + ' ' })));
    return para;
  }));
  spans = [...wordsEl.querySelectorAll('span')];
  lastNow = -1; lastSec = -1;
  updateWpm(); renderMarks(); renderSections();
}
const wordsPerSec = () => (video.duration ? spans.length / video.duration : 2.5);
function posAt(t) {
  if (!sections.length) return 0;
  const i = sectionAt(t), x = sections[i], len = sectionEnd(i) - x.start;
  const frac = len > 0 ? Math.max(0, Math.min(1, ((t - x.start) / len) * speed)) : 0;
  return x.w0 + frac * (x.n - 1);
}
function updateWpm() {
  $('wpm').textContent = spans.length && video.duration ? `About ${Math.round(wordsPerSec() * speed * 60)} words per minute` : 'Add a script and a video to see the pace.';
}

function renderMarks() {
  const d = editedLen();
  $('marks').replaceChildren(...(d ? sections.slice(1).map((x, i) => Object.assign(document.createElement('i'), { style: `left:${(toEdit(x.start) / d) * 100}%`, title: `Section ${i + 2}` })) : []));
  [...$('marks').children].forEach((m, i) => (m.dataset.n = i + 2));
}
function renderSections() {
  if (!sections.length) { secEl.innerHTML = '<p class="sub pad">Paste a script and leave a blank line between sections. Each section can then be retaken on its own, and the teleprompter follows your section start times.</p>'; return; }
  const tools = `<div class="sec-tools"><button class="btn sm" data-a="mark">Next section starts now (M)</button><button class="btn sm ghost" data-a="fit" ${hasTake() ? '' : 'disabled'}>Fit to my voice</button><button class="btn sm ghost" data-a="even">Spread evenly</button></div>`;
  secEl.innerHTML = tools + sections.map((x, i) => {
    const earlier = (state.attempts[i] || []).map((a, k) => `<div class="att">Earlier take ${k + 1} (${(a.samples.length / a.rate).toFixed(1)}s)<span><button class="btn sm ghost" data-a="listen" data-i="${i}" data-k="${k}">Listen</button><button class="btn sm ghost" data-a="use" data-i="${i}" data-k="${k}">Use</button></span></div>`).join('');
    return `<div class="sec-row" data-row="${i}"><div class="sec-top"><b>${i + 1}</b><span class="snip">${esc(x.text.split(/\s+/).slice(0, 9).join(' '))}…</span><span class="t">${fmt(toEdit(x.start))}</span></div><div class="sec-btns"><button class="btn sm" data-a="go" data-i="${i}">Go to</button><button class="btn sm rec" data-a="retake" data-i="${i}">Retake</button>${i ? `<button class="btn sm ghost" data-a="set" data-i="${i}">Start here</button>` : ''}</div>${earlier}</div>`;
  }).join('');
  lastSec = -1;
}
secEl.onclick = (e) => {
  const b = e.target.closest('button');
  if (!b || b.disabled) return;
  const i = +b.dataset.i, k = +b.dataset.k;
  ({ go: () => seekTo(sections[i].start), retake: () => retakeSection(i), set: () => setStart(i), mark: markNext, fit: fitToVoice, listen: () => listen(i, k), use: () => useAttempt(i, k),
     even: () => { spreadEvenly(); marksChanged('Sections spread evenly across the video.'); } })[b.dataset.a]?.();
};
function marksChanged(msg) { saveMarks(); renderMarks(); renderSections(); if (msg) status(msg); }

function setStart(i) {
  const lo = sections[i - 1].start + 0.1, hi = (i + 1 < sections.length ? sections[i + 1].start : video.duration) - 0.1;
  sections[i].start = Math.max(lo, Math.min(hi, video.currentTime));
  marksChanged(`Section ${i + 1} now starts at ${fmt(toEdit(sections[i].start))}.`);
}
// While reading: press M the moment you begin the next section, and the teleprompter follows your real pace from then on.
function markNext() {
  if (!sections.length) return;
  const t = video.currentTime, j = sectionAt(t) + 1;
  if (j >= sections.length) { status('You are already in the last section.'); return; }
  sections[j].start = t;
  for (let k = j + 1; k < sections.length; k++) sections[k].start = Math.max(sections[k].start, t + 0.1 * (k - j));
  marksChanged(`Section ${j + 1} now starts at ${fmt(toEdit(t))}.`);
}
// Places section breaks at the longest pauses in the recorded voice.
function fitToVoice() {
  const need = sections.length - 1;
  if (!hasTake() || need < 1) { status('Record your voice first, and have at least two sections.'); return; }
  const sec = B / state.take.rate;
  const ref = [...peaks].sort((a, b) => a - b)[Math.floor(peaks.length * 0.95)] || 0;
  const thr = Math.max(0.01, ref * 0.06);
  const gaps = [];
  let run = 0;
  for (let b = 0; b < peaks.length; b++) {
    if (peaks[b] < thr) { run++; continue; }
    if (run * sec >= 0.3 && b - run > 0) gaps.push({ len: run, end: b });
    run = 0;
  }
  const picked = gaps.sort((a, b) => b.len - a.len).slice(0, need).sort((a, b) => a.end - b.end);
  if (picked.length < need) { status(`Found ${picked.length} clear pauses for ${need} section breaks. Use "Start here" to place them by hand.`); return; }
  picked.forEach((g, i) => (sections[i + 1].start = Math.max(sections[i].start + 0.1, g.end * sec - 0.15)));
  marksChanged('Sections lined up with the pauses in your voice.');
}

function setTab(tab) {
  const tabs = { edit: ['tabEdit', scriptEl], read: ['tabRead', prompter], sections: ['tabSections', secEl] };
  for (const [k, [btn, el]] of Object.entries(tabs)) { $(btn).classList.toggle('on', k === tab); el.hidden = k !== tab; }
  if (tab !== 'edit') layoutWords();
}
$('tabEdit').onclick = () => setTab('edit');
$('tabRead').onclick = () => setTab('read');
$('tabSections').onclick = () => setTab('sections');

function setSpeed(v) {
  speed = Math.max(0.4, Math.min(2.5, Math.round(v * 20) / 20));
  $('speed').value = speed;
  $('speedLabel').textContent = speed.toFixed(2) + '×';
  updateWpm();
}
$('speed').oninput = (e) => setSpeed(+e.target.value);
$('slower').onclick = () => setSpeed(speed - 0.1);
$('faster').onclick = () => setSpeed(speed + 0.1);
$('mirror').onchange = (e) => wordsEl.classList.toggle('mirror', e.target.checked);

// ---------- fullscreen teleprompter ----------
const isFull = () => document.fullscreenElement === prompter;
function applyFont() { wordsEl.style.fontSize = $('fs').value * (isFull() ? 1.9 : 1) + 'px'; }
function toggleFullscreen() {
  if (document.fullscreenElement) { document.exitFullscreen(); return; }
  setTab('read');
  prompter.requestFullscreen?.().catch(() => status('Fullscreen is not available in this browser.'));
}
$('fs').oninput = applyFont;
$('fullscreen').onclick = toggleFullscreen;
document.addEventListener('fullscreenchange', applyFont);
function showCount(n) {
  $('countdown').textContent = $('hudCount').textContent = n;
  $('countdown').hidden = $('hudCount').hidden = n === null;
}

function tick() {
  const t = video.currentTime || 0;
  if (video.duration) $('playhead').style.left = (editedLen() ? (toEdit(t) / editedLen()) * 100 : 0) + '%';
  $('cur').textContent = fmt(toEdit(t));
  if (!state.recording) updateRecLabel();
  // a section retake stops by itself at the end of its section
  if (state.recording && !state.recPaused && state.range && t >= state.range.end - 0.02) stopRecording();
  if (state.playing) { // faster / slower parts of the video
    const want = Math.min(16, (+$('rate').value || 1) * speedAt(t));
    if (Math.abs(video.playbackRate - want) > 1e-3) video.playbackRate = want;
  }
  updateClip();
  if ($('caps').checked) {
    const c = captionList().find((x) => t >= x.t0 && t < x.t1);
    if (c !== lastCap) { lastCap = c; $('caption').hidden = !c; $('caption').innerHTML = c ? `<span>${esc(c.text)}</span>` : ''; }
  } else if (lastCap) { lastCap = null; $('caption').hidden = true; }
  const recLive = state.recording && !state.recPaused;
  if ((state.playing || recLive) && cuts.length) { // jump over cut parts
    const c = cutAt(t + (recLive ? 0 : 0.02));
    if (c && recLive) {
      // The voice stays lined up with the original video, so the skipped stretch is filled with silence in the take.
      if (c.b >= video.duration - 0.05) stopRecording();
      else {
        const gap = new Float32Array(Math.max(0, Math.round((c.b - t) * ctx.sampleRate)));
        chunks.push(gap); chunkLen += gap.length;
        if (!state.range) pushPeaks(gap);
        video.currentTime = c.b;
      }
    } else if (c) {
      if (c.b >= video.duration - 0.05) { video.currentTime = video.duration; stopPlay(); }
      else { video.currentTime = c.b; startVoice(); }
    }
  }
  const sec = sectionAt(t);
  if (sec !== lastSec) {
    secEl.querySelector('.sec-row.cur')?.classList.remove('cur');
    secEl.querySelector(`[data-row="${sec}"]`)?.classList.add('cur');
    lastSec = sec;
  }
  if (!spans.length || prompter.hidden) return;
  const pos = posAt(t), i = Math.floor(pos), f = pos - i;
  const a = spans[i].offsetTop, b = (spans[i + 1] || spans[i]).offsetTop;
  wordsEl.style.transform = `translateY(${prompter.clientHeight * 0.4 - (a + (b - a) * f) - spans[i].offsetHeight / 2}px)`;
  if (i !== lastNow) {
    spans[lastNow]?.classList.remove('now');
    spans[i].classList.add('now');
    lastNow = i;
  }
  if (isFull()) {
    $('hudTime').textContent = `${fmt(toEdit(t))} / ${fmt(editedLen())}`;
    $('hudSec').textContent = `Section ${sec + 1} of ${sections.length}`;
    $('hudState').textContent = `${state.recording ? (state.recPaused ? 'Paused' : 'Recording') : 'Ready'} · ${speed.toFixed(2)}×`;
  }
}
(function loop() { tick(); requestAnimationFrame(loop); })();

// ---------- microphone ----------
async function initMic(deviceId) {
  try {
    stream?.getTracks().forEach((t) => t.stop());
    stream = await navigator.mediaDevices.getUserMedia({
      audio: { deviceId: deviceId ? { exact: deviceId } : undefined, echoCancellation: false, noiseSuppression: false, autoGainControl: false, channelCount: 1 },
    });
  } catch { status('Microphone blocked. Allow access to record.'); return false; }
  if (!workletReady) {
    const src = URL.createObjectURL(new Blob([`
      class P extends AudioWorkletProcessor {
        process(i){ const c=i[0][0]; if(c) this.port.postMessage(c.slice()); return true; }
      }
      registerProcessor('pcm', P);`], { type: 'text/javascript' }));
    await getCtx().audioWorklet.addModule(src);
    workletReady = true;
  }
  node?.disconnect();
  const mic = ctx.createMediaStreamSource(stream);
  analyser = ctx.createAnalyser(); analyser.fftSize = 512;
  node = new AudioWorkletNode(ctx, 'pcm');
  node.port.onmessage = (e) => {
    if (!capturing) return;
    chunks.push(e.data); chunkLen += e.data.length;
    if (!state.range) pushPeaks(e.data); // a section retake keeps the existing waveform until it is finished
  };
  mic.connect(analyser); mic.connect(node);
  const devs = (await navigator.mediaDevices.enumerateDevices()).filter((d) => d.kind === 'audioinput');
  const cur = stream.getAudioTracks()[0].getSettings().deviceId;
  $('mic').replaceChildren(...devs.map((d) => new Option(d.label || 'Microphone', d.deviceId, false, d.deviceId === cur)));
  return true;
}
$('mic').onchange = (e) => initMic(e.target.value);
const lvl = new Float32Array(512);
let recentPeak = 0;
setInterval(() => {
  if (analyser) {
    analyser.getFloatTimeDomainData(lvl);
    let sum = 0, pk = 0;
    for (const v of lvl) { sum += v * v; pk = Math.max(pk, Math.abs(v)); }
    $('level').style.width = Math.min(100, Math.sqrt(sum / lvl.length) * 300) + '%';
    recentPeak = Math.max(pk, recentPeak * 0.9);
    const loud = recentPeak > 0.97, quiet = recentPeak < 0.04;
    $('levelHint').textContent = loud ? 'Too loud, it is clipping. Move back or lower the input volume.' : quiet ? 'No sound yet. Speak to test your level.' : 'Level is good.';
    $('levelHint').classList.toggle('warn', loud);
    if (state.recording) $('badgeText').textContent = (state.recPaused ? 'PAUSED' : 'REC') + (loud && !state.recPaused ? ' · TOO LOUD' : '');
  }
  if (capturing) drawWave();
}, 150);

// ---------- recording ----------
// Puts freshly recorded pieces into the voice timeline. With no `end` it replaces everything after `start`;
// with an `end` (a section retake) it replaces only that span and keeps the rest.
function splice(existing, start, end, pieces) {
  const total = pieces.reduce((n, c) => n + c.length, 0);
  const keepTail = end != null;
  const writeLen = keepTail ? Math.max(0, Math.min(total, end - start)) : total;
  const out = new Float32Array(keepTail ? Math.max(existing.length, start + writeLen) : start + writeLen);
  out.set(keepTail ? existing : existing.subarray(0, Math.min(existing.length, start)));
  let o = start, left = writeLen;
  for (const c of pieces) {
    if (left <= 0) break;
    const part = c.length > left ? c.subarray(0, left) : c;
    out.set(part, o); o += part.length; left -= part.length;
  }
  return out;
}
const rangeEndIdx = () => (state.range ? Math.round(state.range.end * ctx.sampleRate) : null);

function beginCapture() {
  checkpoint();
  video.playbackRate = 1; // the voice is recorded in real time, so the video must not run faster or slower
  capStart = Math.round(video.currentTime * ctx.sampleRate);
  const have = hasTake() ? state.take.samples : new Float32Array(0);
  base = have; // splice() copies from it, the take itself is untouched until the capture is committed
  const r = state.range;
  if (r && !('old' in r)) { // remember the audio this retake replaces, so it can be brought back
    const a = Math.round(r.start * ctx.sampleRate);
    r.oldStart = a;
    r.old = have.slice(a, Math.min(rangeEndIdx(), have.length));
  }
  if (!r) { rebuildPeaks(have.subarray(0, Math.min(have.length, capStart))); for (let n = capStart - have.length; n > 0; n -= B) peaks.push(0); }
  chunks = []; chunkLen = 0; capturing = true;
  startDraft();
}
function commitCapture() {
  capturing = false;
  const r = state.range;
  if (r && !r.saved && chunkLen > 0 && hasEnergy(r.old)) { pushAttempt(r.sec, { start: r.oldStart, samples: r.old, rate: ctx.sampleRate }); r.saved = true; }
  state.take = { samples: splice(base, capStart, rangeEndIdx(), chunks), rate: ctx.sampleRate };
  mixCache = null;
  chunks = []; chunkLen = 0; base = new Float32Array(0);
  rebuildPeaks(state.take.samples);
  saveTake(); clearDraft();
  drawWave(); renderSections();
}

// Crash safety: while recording, what has been captured is saved every few seconds, so a crashed or closed tab can be recovered.
function startDraft() {
  clearDraft();
  dropDraft(); // starting a new recording means an old interrupted one is no longer wanted
  draft = { sent: 0, parts: 0 };
}
function saveDraft() {
  if (!capturing || !draft || chunks.length === draft.sent) return;
  const piece = concat(chunks.slice(draft.sent));
  draft.sent = chunks.length;
  const part = draft.parts++;
  const meta = { start: capStart, end: rangeEndIdx(), rate: ctx.sampleRate, parts: draft.parts };
  kv.set('draft-' + part, piece).then(() => kv.set('draft', meta));
}
setInterval(saveDraft, 4000);
function clearDraft() {
  if (!draft) return;
  kv.del('draft');
  for (let i = 0; i < draft.parts; i++) kv.del('draft-' + i);
  draft = null;
}
async function dropDraft() {
  const m = await kv.get('draft');
  kv.del('draft');
  for (let i = 0; i < (m?.parts || 0); i++) kv.del('draft-' + i);
  $('recover').hidden = true;
}
async function checkDraft() {
  const m = await kv.get('draft');
  if (!m?.parts) return;
  $('recover').hidden = false;
  $('recoverText').textContent = 'A recording was interrupted. You can recover what was captured.';
  $('recoverYes').onclick = async () => {
    const pieces = [];
    for (let i = 0; i < m.parts; i++) { const p = await kv.get('draft-' + i); if (p) pieces.push(p); }
    const existing = hasTake() ? state.take.samples : new Float32Array(0);
    state.take = { samples: splice(existing, m.start, m.end, pieces), rate: m.rate };
    mixCache = null; rebuildPeaks(state.take.samples);
    saveTake(); dropDraft(); drawWave(); updateUI(); renderSections();
    status('Recovered the interrupted recording.');
  };
  $('recoverNo').onclick = dropDraft;
}

function pushAttempt(sec, a) {
  const list = (state.attempts[sec] ||= []);
  list.push(a);
  if (list.length > 5) list.shift();
  saveAttempts();
}
function useAttempt(i, k) {
  const a = state.attempts[i]?.[k];
  if (!a || (state.recording && !state.recPaused)) return;
  stopPlay(); checkpoint();
  const have = hasTake() ? state.take.samples : new Float32Array(0);
  const end = a.start + a.samples.length;
  const current = have.slice(a.start, Math.min(end, have.length));
  const out = new Float32Array(Math.max(have.length, end));
  out.set(have); out.set(a.samples, a.start);
  state.take = { samples: out, rate: a.rate };
  if (hasEnergy(current)) state.attempts[i][k] = { start: a.start, samples: current, rate: a.rate }; else state.attempts[i].splice(k, 1); // nothing is lost: the replaced audio becomes an earlier take
  mixCache = null; rebuildPeaks(out);
  saveTake(); saveAttempts(); drawWave(); renderSections(); updateUI();
  status(`Section ${i + 1} now uses that take. The one it replaced is kept in the list.`);
}
function listen(i, k) {
  const a = state.attempts[i]?.[k];
  if (!a) return;
  stopVoice();
  try { listenSrc?.stop(); } catch {}
  getCtx().resume();
  const ab = ctx.createBuffer(1, a.samples.length, a.rate);
  ab.copyToChannel(a.samples, 0);
  listenSrc = ctx.createBufferSource(); listenSrc.buffer = ab; listenSrc.connect(ctx.destination); listenSrc.start();
}
function retakeSection(i) {
  if (!state.file || !sections[i]) return;
  if (state.recording && !state.recPaused) return;
  if (state.recording) stopRecording();
  video.currentTime = sections[i].start;
  startRecording({ sec: i, start: sections[i].start, end: sectionEnd(i) });
}

async function startRecording(range = null) {
  if (!(stream?.active || (await initMic()))) return;
  await ctx.resume();
  stopPlay();
  if (video.duration - video.currentTime < 0.2) { status('The playhead is at the end. Move it back to where you want to record from.'); return; }
  state.range = range;
  setTab('read');
  video.muted = true;
  for (let n = 3; n > 0; n--) {
    showCount(n);
    await new Promise((r) => setTimeout(r, 1000));
  }
  showCount(null);
  state.recording = true; state.recPaused = false;
  beginCapture();
  await video.play();
  status(range ? `Retaking section ${range.sec + 1}… it stops by itself at the end of the section.` : 'Recording… read the highlighted text. Press M when you start each new section.');
  updateUI();
}
function pauseRecording() {
  video.pause();
  commitCapture();
  state.recPaused = true;
  status('Paused. Press Play to listen back, scrub to find your trim point, then Trim or Resume from there.');
  updateUI();
}
async function resumeRecording() {
  stopPlay();
  video.muted = true;
  await ctx.resume();
  state.recPaused = false;
  beginCapture();
  await video.play();
  status('Recording…');
  updateUI();
}
function stopRecording() {
  stopPlay();
  video.pause();
  if (!state.recPaused) commitCapture();
  video.playbackRate = +$('rate').value;
  state.recording = false; state.recPaused = false; state.range = null;
  video.muted = !$('hear').checked;
  status(`Take saved (${fmt(toEdit(state.take.samples.length / state.take.rate))}). Play it back, record more from the playhead, or export.`);
  updateUI();
}
$('rec').onclick = () => (state.recording ? stopRecording() : startRecording());
$('pauseRec').onclick = () => (state.recPaused ? resumeRecording() : pauseRecording());

$('trim').onclick = () => {
  if (!hasTake()) return;
  const n = Math.round(video.currentTime * state.take.rate);
  if (n >= state.take.samples.length) { status('Nothing recorded after the playhead.'); return; }
  checkpoint();
  state.take.samples = state.take.samples.slice(0, n);
  mixCache = null;
  rebuildPeaks(state.take.samples);
  saveTake();
  drawWave(); renderSections();
  status(`Trimmed at ${fmt(toEdit(video.currentTime))}. Press Record to continue from here.`);
  updateUI();
};

function discardTake() {
  stopPlay(); state.take = null; mixCache = null; peaks = []; capturing = false; state.attempts = {};
  kv.del('take'); kv.del('attempts'); drawWave(); updateUI(); renderSections();
}
$('clear').onclick = () => { checkpoint(); discardTake(); status('Take discarded.'); };

// ---------- mix (nudge + volume) ----------
function mixed() {
  if (mixCache) return mixCache;
  const { rate } = state.take;
  let src = state.take.samples;
  if ($('denoise').checked && cleaned?.ref === src) src = cleaned.samples; // the cleaned copy is made in the background
  const nudge = Math.round((Number($('nudge').value) || 0) * rate / 1000);
  const gain = ($('vol').value / 100) * ($('norm').checked ? normaliseGain(src) : 1);
  const out = new Float32Array(Math.max(0, src.length + nudge));
  if (nudge >= 0) out.set(src, nudge); else out.set(src.subarray(-nudge));
  for (let i = 0; i < out.length; i++) out[i] = Math.max(-1, Math.min(1, out[i] * gain));
  return (mixCache = { samples: out, rate });
}
$('vol').oninput = $('nudge').oninput = () => { mixCache = null; touched(); };

// ---------- playback ----------
function stopVoice() { try { voiceSrc?.stop(); } catch {} voiceSrc = null; }
function startVoice() {
  stopVoice();
  if (!ctx || (!hasTake() && !music)) return;
  const fa = finalAudio(false);
  if (!fa.samples.length) return;
  if (abCache?.fa !== fa) { const ab = ctx.createBuffer(1, fa.samples.length, fa.rate); ab.copyToChannel(fa.samples, 0); abCache = { fa, ab }; }
  voiceSrc = ctx.createBufferSource();
  voiceSrc.buffer = abCache.ab;
  voiceSrc.playbackRate.value = +$('rate').value; // the audio already has cuts and speed changes in it, so only the player's own speed applies
  voiceSrc.connect(ctx.destination);
  const at = toEdit(video.currentTime);
  if (at < abCache.ab.duration) voiceSrc.start(0, at);
}
async function startPlay() {
  if (video.duration - video.currentTime < 0.05) video.currentTime = 0;
  await getCtx().resume();
  await ensureClean();
  try { listenSrc?.stop(); } catch {}
  video.muted = !$('hear').checked;
  state.playing = true;
  startVoice();
  await video.play();
  updateUI();
}
function stopPlay() {
  if (!state.playing) return;
  stopVoice(); video.pause(); video.playbackRate = +$('rate').value; state.playing = false; updateUI();
}
function stopAll() { if (state.recording) stopRecording(); stopPlay(); }
const togglePlay = () => (state.playing ? stopPlay() : startPlay());
$('play').onclick = togglePlay;
$('toStart').onclick = () => seekTo(0);
$('back').onclick = () => seekBy(-5);
$('fwd').onclick = () => seekBy(5);
$('rate').onchange = (e) => {
  video.playbackRate = +e.target.value * speedAt(video.currentTime);
  if (voiceSrc) voiceSrc.playbackRate.value = +e.target.value;
};
$('hear').onchange = () => { if (!state.recording) video.muted = !$('hear').checked; };

// ---------- export ----------
function wav({ samples, rate }) {
  const b = new DataView(new ArrayBuffer(44 + samples.length * 4));
  const w = (o, s) => [...s].forEach((c, i) => b.setUint8(o + i, c.charCodeAt(0)));
  w(0, 'RIFF'); b.setUint32(4, 36 + samples.length * 4, true); w(8, 'WAVEfmt ');
  b.setUint32(16, 16, true); b.setUint16(20, 3, true); b.setUint16(22, 1, true);
  b.setUint32(24, rate, true); b.setUint32(28, rate * 4, true); b.setUint16(32, 4, true); b.setUint16(34, 32, true);
  w(36, 'data'); b.setUint32(40, samples.length * 4, true);
  new Float32Array(b.buffer, 44).set(samples);
  return new Blob([b], { type: 'audio/wav' });
}
// Reads a server reply as JSON; a missing server (404 page, network error) becomes a plain message.
async function reply(r) {
  let body = null;
  try { body = await r.json(); } catch {}
  if (!r.ok) throw new Error(body?.error || 'The export server is not available here.');
  return body;
}
async function serverExport(why) {
  status(`${why} Using the server instead…`);
  try {
    if (!state.serverId || !(await reply(await fetch('/api/video-exists?id=' + state.serverId))).ok) {
      status('Uploading the video to the server…');
      state.serverId = (await reply(await fetch('/api/video?name=' + encodeURIComponent(state.file.name), { method: 'POST', body: state.file, duplex: 'half' }))).id;
    }
    status('Merging your voice into the video on the server…');
    const q = new URLSearchParams({ id: state.serverId, gain: 1, keep: $('keep').checked ? 1 : 0 });
    if (cuts.length) q.set('cuts', cuts.map((c) => `${c.a.toFixed(3)}-${c.b.toFixed(3)}`).join(','));
    const r = await fetch('/api/export?' + q, { method: 'POST', body: wav(finalAudio(false)) });
    if (!r.ok) await reply(r);
    return r.blob();
  } catch (e) {
    throw new Error(`${why} ${e.message}`);
  }
}
const download = (blob) => Object.assign(document.createElement('a'), { href: URL.createObjectURL(blob), download: 'voiceover.mp4' }).click();

$('export').onclick = async () => {
  const btn = $('export');
  stopAll();
  // The save dialog has to open straight from the click, before any slow work.
  let handle = null;
  try { handle = await pickSaveTarget('voiceover.mp4'); } catch (e) { if (e.name === 'AbortError') return; }
  btn.disabled = true; btn.textContent = 'Exporting…';
  try {
    await ensureClean();
    const shape = $('shape').value, captions = $('caps').checked ? captionList() : null, intro = titleCard('intro'), outro = titleCard('outro');
    // these edits are drawn onto every frame, so only a browser that can encode video can do them (the server only handles cuts)
    const heavy = !!(captions?.length || intro || outro || shape !== 'original' || speeds.length);
    let blob = null, local = false, note = '';
    if ($('keep').checked) {
      if (heavy) throw new Error('Keeping the original audio cannot be combined with speed changes, captions, titles or cropping. Turn one off.');
      blob = await serverExport('Keeping the original audio needs the server.');
    } else {
      try {
        status('Exporting on this device…');
        const fx = { shape, crop: $('crop').value / 100, captions, intro, outro };
        const r = await exportLocally({ file: state.file, voice: finalAudio(true), segs: segs(), fx, saveHandle: handle, onProgress: (p) => (btn.textContent = `Exporting ${Math.round(p * 100)}%`) });
        blob = r.blob; local = true;
        if (r.audioCodec !== 'aac') note = ' This browser cannot make AAC audio, so the voice is Opus. Most players handle it, but QuickTime and some older devices may not.';
      } catch (e) {
        if (!(e instanceof Unsupported)) console.warn('Local export failed', e);
        if (heavy) throw new Error((e instanceof Unsupported ? e.message : 'Exporting on this device failed.') + ' These edits need Chrome or Edge on a computer.');
        blob = await serverExport(e instanceof Unsupported ? e.message : 'Exporting on this device failed.');
      }
    }
    if (blob && handle) { const w = await handle.createWritable(); await w.write(blob); await w.close(); } // server result into the file the user picked
    else if (blob) download(blob);
    status(local ? 'Exported on this device. Nothing was uploaded.' + note : 'Exported voiceover.mp4');
  } catch (e) { status('Export failed: ' + e.message); }
  btn.textContent = 'Export MP4'; updateUI();
};

// ---------- keyboard ----------
document.addEventListener('keydown', (e) => {
  if (/TEXTAREA|INPUT|SELECT/.test(e.target.tagName) || !state.file) return;
  const k = e.key.toLowerCase();
  if ((e.ctrlKey || e.metaKey) && (k === 'z' || k === 'y')) { e.preventDefault(); (k === 'y' || e.shiftKey ? redo : undo)(); return; }
  if (e.metaKey || e.ctrlKey) return;
  const cur = sectionAt(video.currentTime);
  if (e.code === 'Space') { e.preventDefault(); state.recording ? $('pauseRec').click() : togglePlay(); }
  else if (k === 'r') $('rec').click();
  else if (k === 't') $('trim').click();
  else if (k === 'x') cutPress();
  else if (k === 'b') splitHere();
  else if (e.key === 'Delete' || e.key === 'Backspace') { e.preventDefault(); deleteClip(); }
  else if (e.key === 'Escape') cancelCut();
  else if (k === 'f') toggleFullscreen();
  else if (k === 'm') markNext();
  else if (k === 's') retakeSection(cur);
  else if (e.key === '[') seekTo(sections[video.currentTime - sections[cur]?.start > 1.5 ? cur : Math.max(0, cur - 1)]?.start ?? 0);
  else if (e.key === ']') { if (sections[cur + 1]) seekTo(sections[cur + 1].start); }
  else if (e.key === 'ArrowUp') { e.preventDefault(); setSpeed(speed + 0.1); }
  else if (e.key === 'ArrowDown') { e.preventDefault(); setSpeed(speed - 0.1); }
  else if (e.key === 'ArrowLeft') seekBy(-(e.shiftKey ? 1 : 5));
  else if (e.key === 'ArrowRight') seekBy(e.shiftKey ? 1 : 5);
});
applyFont();
applyShape();
updateUI();

(async function restore() {
  try { scriptEl.value = localStorage.getItem('script') || ''; } catch {}
  const saved = await kv.get('video');
  if (!saved?.file) return;
  await loadVideo(saved.file, saved);
  const take = await kv.get('take');
  if (take?.samples?.length) {
    state.take = take; rebuildPeaks(take.samples); mixCache = null;
    drawWave(); updateUI();
  }
  state.attempts = (await kv.get('attempts')) || {};
  const savedMusic = await kv.get('music');
  if (savedMusic?.file) await loadMusic(savedMusic.file, true);
  renderSections();
  checkDraft();
})();
