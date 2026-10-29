import { denoise, normaliseGain, stretch, mixMusic, findPauses, buildCaptions, toSrt, enhanceVoice, zoomState } from './fx.js';
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
let cutStart = null, editVer = 0, history = [], future = [], music = null, musicId = 0, takes = [], playK = -1, zooms = [], zsel = null, pick = null, zoomDirty = false;
let cleaned = null, cleaning = null, finalCache = {}, abCache = null, lastClipKey = '', lastCap = null;

const B = 1024; // samples per waveform bucket
let peaks = [], curMax = 0, curCnt = 0, live = null;

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
  $('redoLine').hidden = !rec || state.recPaused;
  $('pauseRec').textContent = state.recPaused ? 'Resume' : 'Pause';
  $('play').disabled = !v || (rec && !state.recPaused); // playback is allowed while recording is paused, to find the trim point
  $('play').textContent = state.playing ? 'Pause' : 'Play';
  ['toStart', 'back', 'fwd'].forEach((k) => ($(k).disabled = !idle));
  $('trim').disabled = !idle || !hasTake();
  $('cut').disabled = !idle;
  $('undo').disabled = !idle || !history.length; $('redo').disabled = !idle || !future.length;
  const gone = v && !!total() && editedLen() < 0.05; // every clip was deleted
  for (const k of ['split', 'clipSpeed', 'delClip']) $(k).disabled = !idle || gone;
  wrap.classList.toggle('gone', gone);
  if (gone) for (const k of ['cut', 'rec', 'play', 'toStart', 'back', 'fwd']) $(k).disabled = true;
  $('pauses').disabled = !idle || !hasTake();
  $('zoomAdd').disabled = !idle;
  $('srt').disabled = !v;
  $('cut').textContent = cutStart === null ? '✂ Cut' : '✂ Cut ends here';
  $('clear').disabled = rec || !hasTake();
  $('expAudio').disabled = rec || !hasTake();
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
  const t = gNow();
  $('recLabel').textContent = state.recording ? 'Stop' : hasTake() && t > 0.05 ? `Record from ${fmt(toEdit(t))}` : 'Record';
}

// ---------- video upload ----------
// The video stays on this device. It is only sent to the server if a server export is needed (see export below).
// a file the browser cannot play (some MKV or HEVC videos) would otherwise just sit there looking broken
video.onerror = () => { if (state.file && !jumping) status('This browser cannot play that video. Try an MP4 (H.264) or WebM file.'); };
$('file').onchange = (e) => loadVideo(e.target.files[0]);

const wrap = $('videoWrap');
// The whole page accepts a dropped video. If a drop were ignored the browser would open the file in a new tab, so every
// drag and drop is claimed here (except plain text going into the script box).
const isFileDrag = (e) => [...(e.dataTransfer?.types || [])].some((t) => t === 'Files' || t === 'application/x-moz-file');
const inText = (e) => /TEXTAREA|INPUT/.test(e.target?.tagName || '');
let dragTimer = 0;
const dragOn = () => { wrap.classList.add('drag'); clearTimeout(dragTimer); dragTimer = setTimeout(() => wrap.classList.remove('drag'), 150); }; // dragover repeats while hovering; stops = left
const claim = (e) => { if (isFileDrag(e) || !inText(e)) { e.preventDefault(); if (e.dataTransfer) e.dataTransfer.dropEffect = 'copy'; return true; } return false; };
for (const type of ['dragenter', 'dragover']) document.addEventListener(type, (e) => { if (claim(e) && isFileDrag(e)) dragOn(); }, true);
document.addEventListener('drop', (e) => {
  if (!claim(e)) return;
  clearTimeout(dragTimer); wrap.classList.remove('drag');
  const files = [...(e.dataTransfer?.files || [])];
  if (!files.length) return;
  const f = files.find((x) => x.type.startsWith('video/') || /\.(mp4|mov|webm|m4v|mkv|avi|ogv)$/i.test(x.name));
  if (f) (sources.length ? addVideo(f) : loadVideo(f)); else status('That file is not a video.');
}, true);


// ---------- timeline (playhead + scrub) ----------
function seekTo(g) {
  if (!canSeek() || !total()) return;
  gSeek(snapG(Math.max(0, Math.min(total(), g)))).then(() => { if (state.playing) startVoice(); }); // never park the playhead inside a cut
  if (!state.playing) playK = -1;
}
function scrubAt(e) {
  const r = timeline.getBoundingClientRect();
  seekTo(toSrc(Math.max(0, Math.min(1, (e.clientX - r.left) / r.width)) * editedLen()));
}
let scrubbing = false;
timeline.onpointerdown = (e) => { if (!canSeek()) return; scrubbing = true; timeline.setPointerCapture(e.pointerId); scrubAt(e); };
timeline.onpointermove = (e) => { if (scrubbing) scrubAt(e); };
timeline.onpointerup = timeline.onpointercancel = () => { scrubbing = false; };

// ---------- project: videos and clips ----------
// A project is one or more videos placed back to back on one "project time" line (the voice and the script use it too:
// voice sample 0 is project time 0). The edit is a list of clips, each a slice of one video with its own speed. The order of
// the list is the order on the timeline, so clips can be cut, split, trimmed, sped up, deleted and moved around.
// The original files are never changed. toEdit and toSrc convert between project time and the position on the edited timeline.
let sources = [];  // { id, name, file, url, dur, off }
let clips = [];    // { a, b, r } in project time; r is the speed
let loaded = -1, seekToken = 0, jumping = false;
const total = () => (sources.length ? sources[sources.length - 1].off + sources[sources.length - 1].dur : 0);
const srcOf = (g) => { for (let k = 0; k < sources.length; k++) if (g < sources[k].off + sources[k].dur - 1e-6) return k; return Math.max(0, sources.length - 1); };
const gNow = () => (loaded >= 0 ? sources[loaded].off + (video.currentTime || 0) : 0);

function probe(file) {
  return new Promise((res, rej) => {
    const v = document.createElement('video'), url = URL.createObjectURL(file);
    v.preload = 'metadata';
    v.onloadedmetadata = () => res({ dur: v.duration, url });
    v.onerror = () => rej(new Error('unplayable'));
    v.src = url;
  });
}
function loadSource(i) {
  if (i === loaded) return Promise.resolve();
  loaded = i;
  return new Promise((res) => {
    const done = () => { video.removeEventListener('loadeddata', done); res(); };
    video.addEventListener('loadeddata', done);
    video.src = sources[i].url + '#t=0.001'; // starting a hair in makes the browser paint the first frame instead of a blank player
  });
}
// moves the playhead to project time g, switching to another video file when it lives in one
function gSeek(g) {
  if (!sources.length) return Promise.resolve();
  g = Math.max(0, Math.min(total(), g));
  const i = srcOf(g), token = ++seekToken;
  if (i === loaded) { video.currentTime = g - sources[i].off; return Promise.resolve(); }
  return loadSource(i).then(() => { if (token === seekToken) video.currentTime = g - sources[i].off; });
}

const touched = () => { editVer++; abCache = null; };
const sameSrc = (c) => srcOf((c.a + c.b) / 2);
const clipIndexAt = (g) => clips.findIndex((c) => g >= c.a && g < c.b);
const speedAt = (g) => clips[clipIndexAt(g)]?.r ?? 1;
// where a project time goes when it is not inside any clip (it was cut): the next clip that starts after it
function snapG(g) {
  if (clipIndexAt(g) >= 0 || !clips.length) return g;
  const later = clips.filter((c) => c.a >= g).map((c) => c.a);
  return later.length ? Math.min(...later) : Math.max(...clips.map((c) => c.b)) - 1e-3;
}

// the clips with where each starts on the edited timeline
let segCache = null;
function segs() {
  if (segCache?.ver === editVer && segCache.n === clips.length && segCache.t === total()) return segCache.list;
  let e = 0;
  const list = clips.map((c) => { const s = { ...c, e0: e, src: sameSrc(c) }; e += (c.b - c.a) / c.r; return s; });
  segCache = { ver: editVer, n: clips.length, t: total(), list, total: e };
  return list;
}
const editedLen = () => { segs(); return segCache.total; };
function toEdit(g) {
  const list = segs();
  if (!list.length) return g;
  for (const s of list) if (g >= s.a && g < s.b) return s.e0 + (g - s.a) / s.r;
  const before = list.filter((s) => s.b <= g + 1e-9).sort((x, y) => y.b - x.b)[0]; // cut: sits at the end of what came before it
  return before ? before.e0 + (before.b - before.a) / before.r : 0;
}
function toSrc(e) {
  const list = segs();
  if (!list.length) return e;
  for (const s of list) if (e < s.e0 + (s.b - s.a) / s.r - 1e-9) return s.a + Math.max(0, e - s.e0) * s.r;
  return list[list.length - 1].b - 1e-3;
}
const seekBy = (d) => seekTo(toSrc(Math.max(0, Math.min(editedLen(), toEdit(gNow()) + d))));
const curIdx = () => clipIndexAt(Math.min(gNow(), total() - 1e-3));
const gapsOf = () => { // parts of the videos that no clip uses (they were cut or trimmed away)
  const out = [];
  for (const s of sources) {
    const used = clips.filter((c) => c.a >= s.off - 1e-6 && c.b <= s.off + s.dur + 1e-6).sort((x, y) => x.a - y.a);
    let at = s.off;
    for (const c of used) { if (c.a - at > 0.05) out.push({ a: at, b: c.a }); at = Math.max(at, c.b); }
    if (s.off + s.dur - at > 0.05) out.push({ a: at, b: s.off + s.dur });
  }
  return out;
};
// true when the export could be done by cutting the one video alone: no moving, no speed changes, no second video
const plainEdit = () => sources.length === 1 && clips.every((c, i) => c.r === 1 && (i === 0 || c.a >= clips[i - 1].b - 1e-6));

function newProject() {
  discardTake();
  sources = []; clips = []; zooms = []; zsel = null; pick = null; loaded = -1; takes = []; cutStart = null; history = []; future = []; touched();
  try { localStorage.removeItem('project'); localStorage.removeItem('marks'); } catch {}
  kv.get('sources').then((m) => { for (const x of m || []) kv.del('src-' + x.id); kv.del('video'); }).then(() => kv.del('takes'));
}
async function addSource(file, id) {
  const { dur, url } = await probe(file);
  const s = { id: id || crypto.randomUUID(), name: file.name, file, url, dur, off: total() };
  sources.push(s);
  return s;
}
const saveSources = () => kv.set('sources', sources.map(({ id, name, dur }) => ({ id, name, dur })));
function saveProject() { try { localStorage.setItem('project', JSON.stringify({ total: total(), clips, zooms })); } catch {} }

async function showProject(msg) {
  state.file = sources[0]?.file || null;
  video.hidden = !sources.length; $('empty').hidden = !!sources.length;
  await gSeek(clips.length ? clips[0].a : 0);
  touched(); layoutWords(); renderCuts(); renderTakes(); renderZooms(); updateUI();
  if (msg) status(msg);
}
// Starts a new project from one video.
async function loadVideo(file) {
  if (!file) return;
  stopAll();
  state.serverId = null;
  try {
    newProject();
    const s = await addSource(file);
    clips = [{ a: 0, b: s.dur, r: 1 }];
    navigator.storage?.persist?.();
    await showProject('Loading the video…');
    kv.set('src-' + s.id, { file }).then(async (ok) => {
      saveSources(); saveProject();
      status(ok ? 'Ready. Paste your script, then press Record.' : 'Ready, but the browser would not save this video, so a refresh will clear it.');
    });
  } catch { status('This browser cannot play that video. Try an MP4 (H.264) or WebM file.'); }
}
// Adds another video to the end of the timeline.
async function addVideo(file) {
  if (!file) return;
  if (!sources.length) return loadVideo(file);
  if (state.recording && !state.recPaused) return status('Stop recording first.');
  stopPlay();
  try {
    checkpoint();
    const s = await addSource(file);
    clips.push({ a: s.off, b: s.off + s.dur, r: 1 });
    kv.set('src-' + s.id, { file }); saveSources();
    commitEdit(); updateUI();
    status(`Added ${file.name} at the end. Your script and recording now run across both videos. Use New project to start over instead.`);
  } catch { history.pop(); status('This browser cannot play that video. Try an MP4 (H.264) or WebM file.'); }
}
// A blank workspace: the video, script, recording, takes, music and edits are cleared (the original video file is never touched).
function blankWorkspace() {
  if (state.recording && !state.recPaused) return status('Stop recording first.');
  if (sources.length && !confirm('Start a blank workspace? Your video, script, recording and edits will be cleared. The original video file on your computer is not touched.')) return;
  stopAll();
  newProject();
  state.file = null; state.serverId = null;
  video.removeAttribute('src'); video.load();
  scriptEl.value = ''; try { localStorage.removeItem('script'); } catch {}
  music = null; kv.del('music'); $('musicName').textContent = ''; $('musicOpts').hidden = true;
  renderSections(); drawWave();
  showProject('Blank workspace. Drop a video here or click browse to begin.');
}
$('newProject').onclick = blankWorkspace;
$('addFile').onchange = (e) => { addVideo(e.target.files[0]); e.target.value = ''; };

// undo / redo: a snapshot is the clips, the videos and the recorded voice (the voice arrays are never changed in place, so keeping them is cheap)
const snap = () => ({ clips: JSON.stringify(clips), zooms: JSON.stringify(zooms), sources: sources.slice(), take: state.take ? { samples: state.take.samples, rate: state.take.rate } : null });
function checkpoint() { history.push(snap()); if (history.length > 15) history.shift(); future = []; updateUI(); }
function applySnap(sn) {
  clips = JSON.parse(sn.clips); zooms = JSON.parse(sn.zooms); zsel = null; pick = null; sources = sn.sources.slice(); cutStart = null;
  if (loaded >= sources.length) loaded = -1;
  state.take = sn.take ? { ...sn.take } : null; mixCache = null;
  rebuildPeaks(state.take?.samples || new Float32Array(0));
  saveProject(); saveSources(); saveTake(); touched(); renderCuts(); renderZooms(); renderSections(); drawWave(); updateUI();
  if (loaded < 0 || clipIndexAt(gNow()) < 0) gSeek(snapG(gNow()));
}
function undo() { if (!canSeek() || !history.length) return; stopPlay(); future.push(snap()); applySnap(history.pop()); status('Undone.'); }
function redo() { if (!canSeek() || !future.length) return; stopPlay(); history.push(snap()); applySnap(future.pop()); status('Redone.'); }
$('undo').onclick = undo;
$('redo').onclick = redo;
function commitEdit() { touched(); saveProject(); renderCuts(); }

// takes the part [a, b] of project time out of every clip that covers it
function removeSpan(a, b) {
  const next = [];
  for (const c of clips) {
    if (b <= c.a || a >= c.b) { next.push(c); continue; }
    if (a > c.a + 0.01) next.push({ ...c, b: a });
    if (b < c.b - 0.01) next.push({ ...c, a: b });
  }
  clips = next;
}

const SRC_TINT = ['', 's1', 's2', 's3'];
function renderCuts() {
  const L = editedLen() || 1, list = segs(), k = curIdx();
  $('strip').innerHTML = list.map((s, i) => {
    const w = ((s.b - s.a) / s.r / L) * 100;
    const label = `${i + 1}${s.r !== 1 ? ` · ${s.r}×` : ''}${sources.length > 1 ? ` · ${esc(sources[s.src].name)}` : ''}`;
    return `<div class="blk ${SRC_TINT[s.src % 4]}${i === k ? ' sel' : ''}" data-i="${i}" style="left:${(s.e0 / L) * 100}%;width:${w}%" title="${esc(sources[s.src]?.name || '')}"><span>${label}</span></div>`;
  }).join('');
  // a dot where a clip was split in two, a red line where something was cut out or clips from different places meet
  $('cuts').innerHTML = list.slice(1).map((s, i) => {
    const prev = list[i], joined = Math.abs(prev.b - s.a) < 1e-3 && prev.src === s.src && prev.r === s.r;
    return `<i class="${joined ? 'split' : ''}" style="left:${(s.e0 / L) * 100}%"></i>`;
  }).join('') + (cutStart === null ? '' : `<i class="pending" style="left:${(toEdit(cutStart) / L) * 100}%"></i>`)
    + zooms.map((z) => `<b class="zm${z === zsel ? ' sel' : ''}" style="left:${(toEdit(z.a) / L) * 100}%;width:${Math.max(0.5, ((toEdit(z.b) - toEdit(z.a)) / L) * 100)}%">🔍 ${z.k.toFixed(1)}×</b>`).join('');
  $('dur').textContent = fmt(editedLen());
  const gaps = gapsOf(), bar = $('cutbar');
  bar.hidden = !gaps.length && cutStart === null;
  bar.innerHTML = (cutStart !== null
    ? `<span>Cut starts at ${fmt(toEdit(cutStart))}. Move to where it ends, then press Cut again (Esc cancels).</span>`
    : gaps.map((g, i) => `<span>✂ ${(g.b - g.a).toFixed(1)}s removed</span><button class="btn ghost" data-restore="${i}">Restore</button>`).join(''))
    + (gaps.length ? `<span class="sub">Edited length ${fmt(editedLen())}</span>` : '');
  lastClipKey = '';
  drawWave(); renderMarks(); updateUI();
}
$('cutbar').onclick = (e) => {
  const i = e.target.dataset?.restore;
  if (i === undefined) return;
  const g = gapsOf()[+i];
  if (!g) return;
  checkpoint();
  const before = clips.findIndex((c) => Math.abs(c.b - g.a) < 0.06), after = clips.findIndex((c) => Math.abs(c.a - g.b) < 0.06);
  if (before >= 0) clips[before].b = g.b; // the clip next to it grows back over the gap
  else if (after >= 0) clips[after].a = g.a;
  else { const prev = clips.reduce((m, c, j) => (c.b <= g.a && (m < 0 || c.b > clips[m].b) ? j : m), -1); clips.splice(prev + 1, 0, { a: g.a, b: g.b, r: 1 }); }
  commitEdit(); status('Restored.');
};

// the clip under the playhead is the selected one: it is outlined on the timeline and is what Delete and Clip speed act on
function updateClip() {
  const k = total() ? curIdx() : -1, key = k + '-' + editVer;
  if (key === lastClipKey) return;
  lastClipKey = key;
  $('strip').querySelector('.blk.sel')?.classList.remove('sel');
  if (k < 0) { $('clipInfo').textContent = ''; return; }
  $('strip').querySelector(`[data-i="${k}"]`)?.classList.add('sel');
  const s = segs()[k];
  $('clipInfo').textContent = `Clip ${k + 1} of ${clips.length} · ${((s.b - s.a) / s.r).toFixed(1)}s`;
  $('clipSpeed').value = String(s.r);
}

// project-time pieces for an edited-timeline span (a clip can be in several places, so there can be several)
function spansForEdited(lo, hi) {
  const out = [];
  for (const s of segs()) {
    const e1 = s.e0 + (s.b - s.a) / s.r, x = Math.max(lo, s.e0), y = Math.min(hi, e1);
    if (y - x > 1e-6) out.push([s.a + (x - s.e0) * s.r, s.a + (y - s.e0) * s.r]);
  }
  return out;
}
function cutPress() {
  if (!canSeek()) return;
  const t = gNow();
  if (cutStart === null) { cutStart = t; renderCuts(); return status(`Cut starts at ${fmt(toEdit(t))}. Move to where it ends, then press Cut again.`); }
  const e0 = toEdit(cutStart), e1 = toEdit(t), lo = Math.min(e0, e1), hi = Math.max(e0, e1);
  if (hi - lo < 0.1) return status('Move the playhead away from the start point first.');
  cutStart = null;
  checkpoint();
  for (const [a, b] of spansForEdited(lo, hi)) removeSpan(a, b);
  commitEdit();
  seekTo(toSrc(lo));
  status(`Removed ${(hi - lo).toFixed(1)}s. It is skipped in playback and left out of the export.`);
}
function cancelCut() { if (cutStart !== null) { cutStart = null; renderCuts(); status('Cut cancelled.'); } }
$('cut').onclick = cutPress;

function splitHere() {
  if (!canSeek()) return;
  const g = gNow(), k = clipIndexAt(g), c = clips[k];
  if (!c || g - c.a < 0.15 || c.b - g < 0.15) return status('Move the playhead into the middle of a clip to split it.');
  checkpoint(); clips.splice(k, 1, { ...c, b: g }, { ...c, a: g }); commitEdit();
  status(`Split at ${fmt(toEdit(g))}. Click a clip, then press Delete to remove it, or drag it to move it.`);
}
function deleteClip() {
  if (!canSeek()) return;
  const k = curIdx();
  if (k < 0) return;
  const c = clips[k], at = toEdit(c.a);
  checkpoint(); clips.splice(k, 1); commitEdit();
  if (!clips.length) { seekTo(0); return status('Everything was deleted. Press Undo (Ctrl+Z) to bring it back.'); }
  seekTo(toSrc(Math.min(at, editedLen() - 0.01)));
  status(`Deleted the clip (${((c.b - c.a) / c.r).toFixed(1)}s).`);
}
function setClipSpeed(r) {
  if (!canSeek()) return;
  const k = curIdx();
  if (k < 0) return;
  checkpoint(); clips[k].r = r; commitEdit();
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
  for (const x of found) { removeSpan(x.a, x.b); saved += x.b - x.a; }
  commitEdit();
  status(`Removed ${found.length} long pause${found.length > 1 ? 's' : ''}, ${saved.toFixed(1)}s in all. Undo brings them back.`);
};

// ---------- the strip: drag a clip's edge to trim it, drag a clip to move it ----------
const strip = $('strip');
let sdrag = null;
const edgeAt = (blk, x) => { const r = blk.getBoundingClientRect(); return r.width < 18 ? null : x - r.left < 7 ? 'l' : r.right - x < 7 ? 'r' : null; };
strip.onpointerdown = (e) => {
  const blk = e.target.closest('.blk');
  if (!blk || !canSeek()) return;
  e.stopPropagation();
  strip.setPointerCapture(e.pointerId);
  const i = +blk.dataset.i, c = clips[i], W = strip.getBoundingClientRect().width;
  const si = srcOf((c.a + c.b) / 2), joined = (o, j, side) => j !== i && srcOf((o.a + o.b) / 2) === si && Math.abs(side === 'r' ? o.a - c.b : o.b - c.a) < 1e-3;
  // a clip that was split from this one shares the edge, so it moves along with it (found now: it moves while dragging)
  sdrag = { i, c0: { ...c }, edge: edgeAt(blk, e.clientX), x0: e.clientX, perPx: editedLen() / W, moved: false, saved: false, to: i,
    pr: clips.findIndex((o, j) => joined(o, j, 'r')), pl: clips.findIndex((o, j) => joined(o, j, 'l')) };
};
strip.onpointermove = (e) => {
  if (!sdrag) { const blk = e.target.closest?.('.blk'); strip.style.cursor = blk && edgeAt(blk, e.clientX) ? 'col-resize' : ''; return; }
  const dx = e.clientX - sdrag.x0;
  if (!sdrag.moved && Math.abs(dx) < 4) return;
  sdrag.moved = true;
  if (!sdrag.saved) { checkpoint(); sdrag.saved = true; }
  if (sdrag.edge) trimEdge(sdrag, dx * sdrag.perPx * sdrag.c0.r);
  else moveHint(e);
};
strip.onpointerup = strip.onpointercancel = (e) => {
  const d = sdrag; sdrag = null;
  if (!d) return;
  strip.querySelector('.drop')?.remove();
  if (!d.moved) { // a plain click puts the playhead there
    const r = strip.getBoundingClientRect();
    return seekTo(toSrc(((e.clientX - r.left) / r.width) * editedLen()));
  }
  if (d.edge) { commitEdit(); return; }
  if (d.to !== d.i) { const [c] = clips.splice(d.i, 1); clips.splice(d.to, 0, c); commitEdit(); status(`Moved the clip to position ${d.to + 1}.`); }
  else renderCuts();
};
// dragging an edge: a clip grows or shrinks, and a clip joined to it (a split) moves with it
function trimEdge(d, dg) {
  const c = clips[d.i], c0 = d.c0, s = sources[srcOf((c0.a + c0.b) / 2)];
  const others = clips.filter((_, j) => j !== d.i && j !== d.pr && j !== d.pl);
  if (d.edge === 'r') {
    const partner = clips[d.pr];
    const wall = Math.min(s.off + s.dur, ...others.filter((o) => o.a >= c0.b - 1e-6 && o.a < s.off + s.dur).map((o) => o.a));
    c.b = Math.max(c0.a + 0.1, Math.min(partner ? partner.b - 0.1 : wall, c0.b + dg));
    if (partner) partner.a = c.b;
    renderCuts(); seekTo(c.b - 0.01);
  } else {
    const partner = clips[d.pl];
    const wall = Math.max(s.off, ...others.filter((o) => o.b <= c0.a + 1e-6 && o.b > s.off).map((o) => o.b));
    c.a = Math.min(c0.b - 0.1, Math.max(partner ? partner.a + 0.1 : wall, c0.a + dg));
    if (partner) partner.b = c.a;
    renderCuts(); seekTo(c.a);
  }
  touched();
}
// dragging a clip: shows where it would land
function moveHint(e) {
  const r = strip.getBoundingClientRect(), L = editedLen(), x = ((e.clientX - r.left) / r.width) * L;
  const list = segs();
  let to = 0;
  list.forEach((s, j) => { if (j !== sdrag.i && s.e0 + (s.b - s.a) / s.r / 2 < x) to++; });
  sdrag.to = to;
  strip.querySelectorAll('.blk').forEach((b) => b.classList.toggle('dragging', +b.dataset.i === sdrag.i));
  strip.querySelector('.drop')?.remove();
  const rest = list.filter((_, j) => j !== sdrag.i);
  const at = to === 0 ? 0 : (rest[to - 1].e0 + (rest[to - 1].b - rest[to - 1].a) / rest[to - 1].r);
  const line = Object.assign(document.createElement('div'), { className: 'drop' });
  line.style.left = (at / L) * 100 + '%';
  strip.append(line);
}

// ---------- zoom & pan ----------
// Where the picture sits inside the player (it can be letterboxed, or cropped to a vertical or square shape).
function pictureRect() {
  const W = video.clientWidth, H = video.clientHeight, vw = video.videoWidth, vh = video.videoHeight;
  if (!vw || !W) return null;
  const cover = $('shape').value !== 'original', k = cover ? Math.max(W / vw, H / vh) : Math.min(W / vw, H / vh);
  const pw = vw * k, ph = vh * k;
  return { pw, ph, ox: cover ? (W - pw) * ($('crop').value / 100) : (W - pw) / 2, oy: (H - ph) / 2 };
}
// shows the zoom in the preview by scaling the player itself
function applyZoomPreview(g) {
  const zs = pick ? null : zoomState(zooms, g), r = zs && pictureRect();
  if (!zs || !r) { if (video.style.transform) video.style.transform = ''; return; }
  video.style.transformOrigin = '0 0';
  video.style.transform = `translate(${r.ox}px,${r.oy}px) scale(${zs.k}) translate(${-(r.ox + zs.x * r.pw)}px,${-(r.oy + zs.y * r.ph)}px)`;
}
function placeDots() {
  const r = pictureRect(), show = !!(pick && zsel && r);
  $('zdotA').hidden = $('zdotB').hidden = !show;
  if (!show) return;
  for (const [id, x, y] of [['zdotA', zsel.x1, zsel.y1], ['zdotB', zsel.x2, zsel.y2]]) { $(id).style.left = r.ox + x * r.pw + 'px'; $(id).style.top = r.oy + y * r.ph + 'px'; }
  $('zdotB').hidden = !zsel.pan;
}
function zoomChanged() { touched(); saveProject(); renderCuts(); }
// A zoom eases in and out, so at its first or last frame the picture looks normal. When something about a zoom changes the
// playhead moves to the middle of it, where the full effect shows in the player.
function showZoom(z) {
  const ramp = Math.min(0.5, (z.b - z.a) / 3), g = gNow();
  if (g < z.a + ramp || g >= z.b - ramp) seekTo(z.a + (z.b - z.a) / 2);
}
function renderZooms() {
  const el = $('zoomList');
  $('zoomAdd').disabled = !state.file || (state.recording && !state.recPaused);
  if (!zooms.length) { el.innerHTML = '<p class="sub">Add a zoom to point at part of the screen, for example a button in a screen recording. It eases in, holds, and eases out.</p>'; return; }
  el.innerHTML = zooms.map((z, i) => {
    const sel = z === zsel;
    return `<div class="zoom${sel ? ' sel' : ''}" data-i="${i}"><div class="zhead" data-a="select"><b>Zoom ${i + 1}</b><span class="meta">${fmt(toEdit(z.a))} · ${(z.b - z.a).toFixed(1)}s · ${z.k.toFixed(1)}×${z.pan ? ' · pans' : ''}</span><button class="btn sm ghost" data-a="del" title="Remove this zoom">✕</button></div>
      ${sel ? `<label class="row">Zoom in <input type="range" data-f="k" min="1.2" max="4" step="0.1" value="${z.k}" /></label>
      <label class="row">Length <input type="range" data-f="len" min="1" max="15" step="0.5" value="${Math.min(15, z.b - z.a)}" /></label>
      <div class="acts"><button class="btn sm${pick === 'start' ? ' on' : ''}" data-a="start">${pick === 'start' ? 'Click the video…' : 'Choose where to zoom'}</button><button class="btn sm${pick === 'end' ? ' on' : ''}" data-a="end">${pick === 'end' ? 'Click the video…' : z.pan ? 'Change where it pans to' : 'Pan to somewhere else'}</button>${z.pan ? '<button class="btn sm ghost" data-a="nopan">Stop panning</button>' : ''}</div>` : ''}</div>`;
  }).join('');
  wrap.classList.toggle('picking', !!pick);
}
$('zoomAdd').onclick = () => {
  if (!total()) return;
  const g = gNow(), next = Math.min(total(), ...zooms.filter((z) => z.a > g).map((z) => z.a));
  if (zooms.some((z) => g < z.b && g >= z.a)) return status('There is already a zoom here. Move the playhead to an empty part first.');
  if (next - g < 0.5) return status('Not enough room for a zoom here. Move the playhead earlier.');
  checkpoint();
  zsel = { a: g, b: Math.min(g + 3, next), k: 2, x1: 0.5, y1: 0.5, x2: 0.5, y2: 0.5, pan: false };
  zooms.push(zsel); zooms.sort((p, q) => p.a - q.a); pick = null;
  zoomChanged(); renderZooms(); showZoom(zsel);
  status('Zoom added, shown in the player. Press "Choose where to zoom", then click the spot on the video.');
};
$('zoomList').onclick = (e) => {
  const b = e.target.closest('[data-a]'), row = e.target.closest('.zoom');
  if (!b || !row) return;
  const z = zooms[+row.dataset.i], a = b.dataset.a;
  if (a === 'select') { zsel = z; pick = null; showZoom(z); }
  else if (a === 'del') { checkpoint(); zooms = zooms.filter((q) => q !== z); if (zsel === z) { zsel = null; pick = null; } zoomChanged(); }
  else if (a === 'start' || a === 'end') { zsel = z; pick = pick === a ? null : a; if (pick) status('Click the spot on the video.'); }
  else if (a === 'nopan') { checkpoint(); z.pan = false; z.x2 = z.x1; z.y2 = z.y1; zoomChanged(); }
  renderZooms();
};
// sliders: the first movement saves one undo step, then the zoom follows the slider
$('zoomList').oninput = (e) => {
  const f = e.target.dataset.f;
  if (!f || !zsel) return;
  if (!zoomDirty) { checkpoint(); zoomDirty = true; }
  showZoom(zsel);
  if (f === 'k') zsel.k = +e.target.value;
  else { const next = Math.min(total(), ...zooms.filter((z) => z.a > zsel.a).map((z) => z.a)); zsel.b = Math.min(zsel.a + +e.target.value, next); }
  const meta = $('zoomList').querySelector('.zoom.sel .meta');
  if (meta) meta.textContent = `${fmt(toEdit(zsel.a))} · ${(zsel.b - zsel.a).toFixed(1)}s · ${zsel.k.toFixed(1)}×${zsel.pan ? ' · pans' : ''}`;
  zoomChanged();
};
$('zoomList').onchange = () => { zoomDirty = false; };
// choosing a spot: click the video while "Choose where to zoom" / "Pan to" is on
wrap.addEventListener('click', (e) => {
  if (!pick || !zsel) return;
  const r = pictureRect(), b = wrap.getBoundingClientRect();
  if (!r) return;
  const x = Math.max(0, Math.min(1, (e.clientX - b.left - r.ox) / r.pw)), y = Math.max(0, Math.min(1, (e.clientY - b.top - r.oy) / r.ph));
  checkpoint();
  if (pick === 'start') { zsel.x1 = x; zsel.y1 = y; if (!zsel.pan) { zsel.x2 = x; zsel.y2 = y; } }
  else { zsel.x2 = x; zsel.y2 = y; zsel.pan = true; }
  pick = null; zoomChanged(); renderZooms(); showZoom(zsel);
  status(zsel.pan ? 'Done. The zoom slides from the first spot to the second.' : 'Done. Play it to see the zoom.');
});

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
const fxIds = ['denoise', 'norm', 'eq', 'deess', 'fade', 'mvol', 'duck', 'shape', 'crop', 'caps', 'introText', 'introSec', 'outroText', 'outroSec'];
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
    if (id === 'denoise' || id === 'norm' || id === 'eq' || id === 'deess') { mixCache = null; touched(); }
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
  const key = sections.map((x) => x.start.toFixed(2)).join() + '|' + scriptEl.value.length + '|' + total();
  if (capCache?.key !== key) capCache = { key, list: buildCaptions(sections, total() || 0) };
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
  g.fillRect(0, 0, Math.min(W, (toEdit(Math.min(total(), (peaks.length * B) / rate)) / L) * W), H);
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
function livePush(arr) {
  for (let i = 0; i < arr.length; i++) {
    const a = Math.abs(arr[i]);
    if (a > live.max) live.max = a;
    if (++live.cnt === B) { peaks[live.idx++] = live.max; live.max = 0; live.cnt = 0; }
  }
}
function rebuildPeaks(samples) { peaks = []; curMax = 0; curCnt = 0; pushPeaks(samples); }

// ---------- script, sections and teleprompter ----------
// A blank line in the script starts a new section. Every section has a start time on the video, and the
// teleprompter reads a section across the span between its start and the next section's start.
let sections = []; // { text, w0 (index of its first word), n (word count), start (seconds) }
const secEl = $('sections');
const esc = (t) => t.replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

const sectionEnd = (i) => (i + 1 < sections.length ? sections[i + 1].start : total() || 0);
function sectionAt(t) { let i = 0; while (i + 1 < sections.length && t >= sections[i + 1].start - 1e-6) i++; return i; }

function spreadEvenly() {
  const words = sections.reduce((n, x) => n + x.n, 0) || 1;
  let seen = 0;
  for (const x of sections) { x.start = (total() || 0) * (seen / words); seen += x.n; }
}
function saveMarks() { try { localStorage.setItem('marks', JSON.stringify({ n: sections.length, dur: total(), starts: sections.map((x) => x.start) })); } catch {} }
function loadMarks() {
  try {
    const m = JSON.parse(localStorage.getItem('marks'));
    // adding a video later keeps the section times, they stay valid
    if (m && m.n === sections.length) { sections.forEach((x, i) => (x.start = m.starts[i])); return true; }
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
  if (!(total() && loadMarks())) spreadEvenly();
  wordsEl.replaceChildren(...sections.map((x) => {
    const para = document.createElement('p');
    para.append(...x.text.split(/\s+/).map((w) => Object.assign(document.createElement('span'), { textContent: w + ' ' })));
    return para;
  }));
  spans = [...wordsEl.querySelectorAll('span')];
  lastNow = -1; lastSec = -1;
  updateWpm(); renderMarks(); renderSections();
}
const wordsPerSec = () => (total() ? spans.length / total() : 2.5);
function posAt(t) {
  if (!sections.length) return 0;
  const i = sectionAt(t), x = sections[i], len = sectionEnd(i) - x.start;
  const frac = len > 0 ? Math.max(0, Math.min(1, ((t - x.start) / len) * speed)) : 0;
  return x.w0 + frac * (x.n - 1);
}
function updateWpm() {
  $('wpm').textContent = spans.length && total() ? `About ${Math.round(wordsPerSec() * speed * 60)} words per minute` : 'Add a script and a video to see the pace.';
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
  const lo = sections[i - 1].start + 0.1, hi = (i + 1 < sections.length ? sections[i + 1].start : total()) - 0.1;
  sections[i].start = Math.max(lo, Math.min(hi, gNow()));
  marksChanged(`Section ${i + 1} now starts at ${fmt(toEdit(sections[i].start))}.`);
}
// While reading: press M the moment you begin the next section, and the teleprompter follows your real pace from then on.
function markNext() {
  if (!sections.length) return;
  const t = gNow(), j = sectionAt(t) + 1;
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

// the side panel shows one group of controls at a time, so nothing needs scrolling past
function setPanel(name) {
  for (const b of document.querySelectorAll('#panelTabs button')) b.classList.toggle('on', b.dataset.p === name);
  for (const el of document.querySelectorAll('.panel')) el.hidden = el.dataset.panel !== name;
  try { localStorage.setItem('panel', name); } catch {}
}
$('panelTabs').onclick = (e) => { const b = e.target.closest('button'); if (b) setPanel(b.dataset.p); };
function setTab(tab) {
  setPanel('script');
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

// moves to the next piece of the timeline; while recording the voice captured so far is put away and a new piece starts there
async function jumpTo(g) {
  if (jumping) return;
  jumping = true;
  const recLive = state.recording && !state.recPaused;
  try {
    if (recLive) commitCapture();
    await gSeek(g);
    playK = clipIndexAt(g);
    if (state.playing) startVoice();
    if (recLive) beginCapture(true);
    if ((state.playing || recLive) && video.paused) await video.play().catch(() => {});
  } finally { jumping = false; }
}
video.onended = () => { if (state.playing || (state.recording && !state.recPaused)) tick(); };

function tick() {
  const t = gNow();
  if (total()) $('playhead').style.left = (editedLen() ? (toEdit(t) / editedLen()) * 100 : 0) + '%';
  $('cur').textContent = fmt(toEdit(t));
  if (!state.recording) updateRecLabel();
  // a section retake stops by itself at the end of its section
  if (state.recording && !state.recPaused && state.range && t >= state.range.end - 0.02) stopRecording();
  if (state.playing) { // faster / slower parts of the video
    const want = Math.min(16, (+$('rate').value || 1) * speedAt(t));
    if (Math.abs(video.playbackRate - want) > 1e-3) video.playbackRate = want;
  }
  updateClip();
  applyZoomPreview(t); placeDots();
  if ($('caps').checked) {
    const c = captionList().find((x) => t >= x.t0 && t < x.t1);
    if (c !== lastCap) { lastCap = c; $('caption').hidden = !c; $('caption').innerHTML = c ? `<span>${esc(c.text)}</span>` : ''; }
  } else if (lastCap) { lastCap = null; $('caption').hidden = true; }
  const recLive = state.recording && !state.recPaused;
  if ((state.playing || recLive) && clips.length && !jumping) { // follow the edit: skip cut parts and move between clips
    let k = clipIndexAt(t);
    if (k < 0 && playK >= 0 && playK < clips.length && Math.abs(t - clips[playK].b) < 0.15) k = playK; // right at the end of the clip being played
    if (k < 0) jumpTo(snapG(t));
    else {
      playK = k;
      if (t >= clips[k].b - (recLive ? 0 : 0.03)) {
        const next = clips[k + 1];
        if (!next) { if (recLive) stopRecording(); else stopPlay(); }
        else if (!(Math.abs(next.a - clips[k].b) < 1e-3 && srcOf(next.a) === loaded)) jumpTo(next.a); // a split in the middle of one video needs no jump
      }
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
    if (!state.range && live) livePush(e.data); // a section retake keeps the existing waveform until it is finished
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
// Puts freshly recorded pieces into the voice timeline. With an `end` it replaces only the span from `start` to `end` and keeps the rest;
// with none it replaces everything after `start` (nothing records that way any more, the old draft format did).
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

function beginCapture(quiet = false) {
  if (!quiet) checkpoint();
  video.playbackRate = 1; // the voice is recorded in real time, so the video must not run faster or slower
  capStart = Math.round(gNow() * ctx.sampleRate);
  const have = hasTake() ? state.take.samples : new Float32Array(0);
  base = have; // splice() copies from it, the take itself is untouched until the capture is committed
  const r = state.range;
  if (r && !('old' in r)) { // remember the audio this retake replaces, so it can be brought back
    const a = Math.round(r.start * ctx.sampleRate);
    r.oldStart = a;
    r.old = have.slice(a, Math.min(rangeEndIdx(), have.length));
  }
  if (!r) { // the live waveform draws over what is already there, from where this capture starts
    rebuildPeaks(have);
    while (peaks.length < Math.floor(capStart / B)) peaks.push(0);
    live = { idx: Math.floor(capStart / B), cnt: capStart % B, max: 0 };
  }
  chunks = []; chunkLen = 0; capturing = true;
  startDraft();
}
function commitCapture() {
  capturing = false;
  const r = state.range;
  if (r && !r.saved && chunkLen > 0 && hasEnergy(r.old)) { pushAttempt(r.sec, { start: r.oldStart, samples: r.old, rate: ctx.sampleRate }); r.saved = true; }
  state.take = { samples: splice(base, capStart, state.range ? rangeEndIdx() : capStart + chunkLen, chunks), rate: ctx.sampleRate }; // only the recorded span is replaced; the rest of the voice is kept
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
    state.take = { samples: splice(existing, m.start, m.end ?? m.start + pieces.reduce((n, c) => n + c.length, 0), pieces), rate: m.rate };
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
async function retakeSection(i) {
  if (!state.file || !sections[i]) return;
  if (state.recording && !state.recPaused) return;
  if (state.recording) stopRecording();
  await gSeek(snapG(sections[i].start));
  startRecording({ sec: i, start: sections[i].start, end: sectionEnd(i) });
}

async function startRecording(range = null) {
  if (!(stream?.active || (await initMic()))) return;
  await ctx.resume();
  stopPlay();
  if (editedLen() - toEdit(gNow()) < 0.2) { status('The playhead is at the end. Move it back to where you want to record from.'); return; }
  state.range = range;
  setTab('read');
  video.muted = true;
  for (let n = 3; n > 0; n--) {
    showCount(n);
    await new Promise((r) => setTimeout(r, 1000));
  }
  showCount(null);
  state.recording = true; state.recPaused = false; playK = curIdx();
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
  state.recPaused = false; playK = curIdx();
  beginCapture();
  await video.play();
  status('Recording…');
  updateUI();
}
function stopRecording() {
  const wasRange = !!state.range;
  stopPlay();
  video.pause();
  if (!state.recPaused) commitCapture();
  if (!wasRange) archiveTake(); // a section retake is kept with the section instead
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
  const n = Math.round(gNow() * state.take.rate);
  if (n >= state.take.samples.length) { status('Nothing recorded after the playhead.'); return; }
  checkpoint();
  state.take.samples = state.take.samples.slice(0, n);
  mixCache = null;
  rebuildPeaks(state.take.samples);
  saveTake();
  drawWave(); renderSections();
  status(`Trimmed at ${fmt(toEdit(gNow()))}. Press Record to continue from here.`);
  updateUI();
};

function discardTake() {
  stopPlay(); state.take = null; mixCache = null; peaks = []; capturing = false; state.attempts = {};
  kv.del('take'); kv.del('attempts'); drawWave(); updateUI(); renderSections();
}
$('clear').onclick = () => { archiveTake(); checkpoint(); discardTake(); status('Take discarded.'); };

// ---------- takes ----------
// Every time you stop recording, the voice as it stands is kept here, so you can listen back, star the best one and switch to it.
let takeCounter = 0, listening = null;
const takesMeta = () => kv.set('takes', { n: takeCounter, list: takes.map(({ id, name, stars, at, rate }) => ({ id, name, stars, at, rate })) });
function archiveTake() {
  if (!hasTake() || takes.some((t) => t.samples === state.take.samples)) return;
  const t = { id: crypto.randomUUID(), name: `Take ${++takeCounter}`, samples: state.take.samples, rate: state.take.rate, stars: 0, at: Date.now() };
  takes.push(t);
  kv.set('take-' + t.id, { samples: t.samples });
  while (takes.length > 10) { // keep ten; the oldest unstarred one goes first
    const k = takes.findIndex((x) => !x.stars && x.samples !== state.take.samples);
    const [gone] = takes.splice(k >= 0 ? k : 0, 1);
    kv.del('take-' + gone.id);
  }
  takesMeta(); renderTakes();
}
function renderTakes() {
  const el = $('takes');
  if (!takes.length) { el.innerHTML = '<p class="sub">Each time you stop recording, that take is kept here. Listen back, give stars to the best one and switch between them.</p>'; return; }
  el.innerHTML = takes.slice().reverse().map((t) => {
    const cur = t.samples === state.take?.samples;
    const time = new Date(t.at).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    return `<div class="take${cur ? ' cur' : ''}"><div><b>${esc(t.name)}</b> <span class="meta">${fmt(t.samples.length / t.rate)} · ${time}${cur ? ' · in use' : ''}</span></div>
      <div class="stars">${[1, 2, 3, 4, 5].map((n) => `<button data-a="star" data-id="${t.id}" data-n="${n}" class="${n <= t.stars ? 'on' : ''}" title="${n} star${n > 1 ? 's' : ''}">★</button>`).join('')}</div>
      <div class="acts"><button class="btn sm ghost" data-a="listen" data-id="${t.id}">${listening === t.id ? 'Stop' : 'Listen'}</button>${cur ? '' : `<button class="btn sm" data-a="use" data-id="${t.id}">Use</button>`}<button class="btn sm ghost" data-a="del" data-id="${t.id}" title="Delete this take">✕</button></div></div>`;
  }).join('');
}
$('takes').onclick = (e) => {
  const b = e.target.closest('button');
  const t = b && takes.find((x) => x.id === b.dataset.id);
  if (!t) return;
  if (b.dataset.a === 'star') { t.stars = t.stars === +b.dataset.n ? 0 : +b.dataset.n; takesMeta(); renderTakes(); }
  else if (b.dataset.a === 'listen') {
    try { listenSrc?.stop(); } catch {}
    if (listening === t.id) { listening = null; return renderTakes(); }
    stopVoice(); getCtx().resume();
    const ab = ctx.createBuffer(1, t.samples.length, t.rate);
    ab.copyToChannel(t.samples, 0);
    listenSrc = ctx.createBufferSource(); listenSrc.buffer = ab; listenSrc.connect(ctx.destination);
    listenSrc.onended = () => { if (listening === t.id) { listening = null; renderTakes(); } };
    listenSrc.start(); listening = t.id; renderTakes();
  } else if (b.dataset.a === 'use') {
    if (state.recording && !state.recPaused) return status('Stop recording first.');
    stopPlay(); try { listenSrc?.stop(); } catch {} listening = null;
    checkpoint(); archiveTake();
    state.take = { samples: t.samples, rate: t.rate }; mixCache = null;
    rebuildPeaks(t.samples); saveTake(); touched(); drawWave(); renderSections(); renderTakes(); updateUI();
    status(`Now using ${t.name}. The one you had before is kept in the list.`);
  } else if (b.dataset.a === 'del') {
    takes = takes.filter((x) => x !== t); kv.del('take-' + t.id); takesMeta(); renderTakes();
  }
};

// ---------- redo this line ----------
// While recording: goes back to the start of the sentence you are reading (or the one before, if you only just began it),
// puts what you recorded before it away, and starts again from there. The start is moved to the nearest pause in your voice.
function nearestPause(t0) {
  if (peaks.length < 20 || !hasTake()) return null;
  const sec = B / state.take.rate, sorted = [...peaks].sort((a, b) => a - b);
  const thr = Math.max(0.01, (sorted[Math.floor(sorted.length * 0.95)] || 0) * 0.06);
  const lo = Math.max(0, Math.floor((t0 - 1.5) / sec)), hi = Math.min(peaks.length - 1, Math.floor((t0 + 1.5) / sec));
  let best = null, run = 0;
  for (let b = lo; b <= hi + 1; b++) {
    if (b <= hi && peaks[b] < thr) { run++; continue; }
    if (run * sec >= 0.2) { const end = b * sec - 0.05; if (best === null || Math.abs(end - t0) < Math.abs(best - t0)) best = end; }
    run = 0;
  }
  return best;
}
async function redoLine() {
  if (!state.recording || state.recPaused || jumping) return;
  const g = gNow(), lines = buildCaptions(sections, total(), Infinity);
  if (!lines.length) return status('Add a script first, so the app knows where each sentence starts.');
  let i = lines.findIndex((x) => g >= x.t0 && g < x.t1);
  if (i < 0) i = lines.length - 1;
  if (i > 0 && g - lines[i].t0 < 0.8) i--; // you had only just started this sentence, so redo the one before
  const from = lines[i];
  pauseRecording(); // puts the voice recorded so far away and pauses the video
  let t0 = nearestPause(from.t0) ?? from.t0;
  if (state.range) t0 = Math.max(t0, state.range.start);
  await gSeek(snapG(t0));
  showCount(1);
  await new Promise((r) => setTimeout(r, 900));
  showCount(null);
  if (state.recording && state.recPaused) { await resumeRecording(); status(`Back at "${from.text.split(/\s+/).slice(0, 5).join(' ')}…". Read it again.`); }
}
$('redoLine').onclick = redoLine;

// ---------- mix (nudge + volume) ----------
let enhCache = null;
function enhanced(src, rate) { // voice tone and de-esser, kept until the voice or the settings change
  const eq = $('eq').value, de = $('deess').value, key = eq + '|' + de;
  if (eq === 'off' && de === 'off') return src;
  if (enhCache?.ref !== src || enhCache.key !== key) enhCache = { ref: src, key, samples: enhanceVoice(src, rate, { eq, deess: de }) };
  return enhCache.samples;
}
function mixed() {
  if (mixCache) return mixCache;
  const { rate } = state.take;
  let src = state.take.samples;
  if ($('denoise').checked && cleaned?.ref === src) src = cleaned.samples; // the cleaned copy is made in the background
  src = enhanced(src, rate);
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
  const at = toEdit(gNow());
  if (at < abCache.ab.duration) voiceSrc.start(0, at);
}
async function startPlay() {
  if (editedLen() - toEdit(gNow()) < 0.05) await gSeek(toSrc(0));
  await getCtx().resume();
  await ensureClean();
  try { listenSrc?.stop(); } catch {}
  video.muted = !$('hear').checked;
  state.playing = true; playK = curIdx();
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
$('toStart').onclick = () => seekTo(toSrc(0));
$('back').onclick = () => seekBy(-5);
$('fwd').onclick = () => seekBy(5);
$('rate').onchange = (e) => {
  video.playbackRate = +e.target.value * speedAt(gNow());
  if (voiceSrc) voiceSrc.playbackRate.value = +e.target.value;
};
$('hear').onchange = () => { if (!state.recording) video.muted = !$('hear').checked; };

// ---------- save and import the recording as audio ----------
// The saved file is the recording as it lines up with the video (it starts at the video's 0:00), so importing it on
// another video puts every word back where it was and you can carry on recording from there.
function wav16({ samples, rate }) {
  const b = new DataView(new ArrayBuffer(44 + samples.length * 2));
  const w = (o, t) => [...t].forEach((c, i) => b.setUint8(o + i, c.charCodeAt(0)));
  w(0, 'RIFF'); b.setUint32(4, 36 + samples.length * 2, true); w(8, 'WAVEfmt ');
  b.setUint32(16, 16, true); b.setUint16(20, 1, true); b.setUint16(22, 1, true);
  b.setUint32(24, rate, true); b.setUint32(28, rate * 2, true); b.setUint16(32, 2, true); b.setUint16(34, 16, true);
  w(36, 'data'); b.setUint32(40, samples.length * 2, true);
  for (let i = 0; i < samples.length; i++) b.setInt16(44 + i * 2, Math.max(-1, Math.min(1, samples[i])) * 0x7fff, true);
  return new Blob([b], { type: 'audio/wav' });
}
$('expAudio').onclick = () => {
  if (!hasTake()) return;
  Object.assign(document.createElement('a'), { href: URL.createObjectURL(wav16(state.take)), download: 'voiceover-audio.wav' }).click();
  status('Audio saved. Use Import audio on any video to put this recording back and carry on from it.');
};
$('audioFile').onchange = async (e) => {
  const f = e.target.files[0]; e.target.value = '';
  if (!f) return;
  if (!state.file) return status('Add the video first, then import the audio onto it.');
  if (state.recording && !state.recPaused) return status('Stop recording first.');
  try {
    const buf = await getCtx().decodeAudioData(await f.arrayBuffer()); // also converts it to this device's sample rate
    const mono = new Float32Array(buf.length);
    for (let c = 0; c < buf.numberOfChannels; c++) { const d = buf.getChannelData(c); for (let i = 0; i < mono.length; i++) mono[i] += d[i] / buf.numberOfChannels; }
    stopPlay(); archiveTake(); checkpoint();
    state.take = { samples: mono, rate: buf.sampleRate }; state.attempts = {}; mixCache = null; cleaned = null;
    rebuildPeaks(mono); saveTake(); saveAttempts(); touched(); drawWave(); renderSections(); renderTakes(); updateUI();
    status(`Imported ${f.name} (${fmt(buf.duration)}). Move the playhead and press Record to carry on from it. Undo brings back what was there.`);
  } catch { status('Could not read that audio file.'); }
};

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
    const gaps = gapsOf();
    if (gaps.length) q.set('cuts', gaps.map((c) => `${c.a.toFixed(3)}-${c.b.toFixed(3)}`).join(','));
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
    const heavy = !!(captions?.length || intro || outro || shape !== 'original' || zooms.length || !plainEdit());
    let blob = null, local = false, note = '';
    if ($('keep').checked) {
      if (heavy) throw new Error('Keeping the original audio cannot be combined with speed changes, moved clips, several videos, captions, titles zooms or cropping. Turn one off.');
      blob = await serverExport('Keeping the original audio needs the server.');
    } else {
      try {
        status('Exporting on this device…');
        const fx = { shape, crop: $('crop').value / 100, captions, intro, outro, zooms };
        const r = await exportLocally({ sources: sources.map((x) => ({ file: x.file, off: x.off })), voice: finalAudio(true), segs: segs().map((g) => ({ src: g.src, a: g.a - sources[g.src].off, b: g.b - sources[g.src].off, r: g.r })), fx, saveHandle: handle, onProgress: (p) => (btn.textContent = `Exporting ${Math.round(p * 100)}%`) });
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
  const cur = sectionAt(gNow());
  if (e.code === 'Space') { e.preventDefault(); state.recording ? $('pauseRec').click() : togglePlay(); }
  else if (k === 'r') $('rec').click();
  else if (k === 't') $('trim').click();
  else if (k === 'x') cutPress();
  else if (k === 'l') redoLine();
  else if (k === 'b') splitHere();
  else if (e.key === 'Delete' || e.key === 'Backspace') { e.preventDefault(); deleteClip(); }
  else if (e.key === 'Escape') cancelCut();
  else if (k === 'f') toggleFullscreen();
  else if (k === 'm') markNext();
  else if (k === 's') retakeSection(cur);
  else if (e.key === '[') seekTo(sections[gNow() - sections[cur]?.start > 1.5 ? cur : Math.max(0, cur - 1)]?.start ?? 0);
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
  let meta = await kv.get('sources'), legacy = false;
  if (!meta?.length) { // projects saved before several videos were supported
    const old = await kv.get('video');
    meta = old?.file ? [{ id: crypto.randomUUID(), name: old.file.name, file: old.file }] : [];
    legacy = meta.length > 0;
  }
  try {
    for (const m of meta) { const rec = m.file ? { file: m.file } : await kv.get('src-' + m.id); if (rec?.file) await addSource(rec.file, m.id); }
  } catch { return status('This browser cannot play the saved video any more. Upload it again.'); }
  if (!sources.length) return;
  if (legacy) { kv.set('src-' + sources[0].id, { file: sources[0].file }); saveSources(); kv.del('video'); }
  clips = sources.map((x) => ({ a: x.off, b: x.off + x.dur, r: 1 }));
  try { // the saved edit counts only if it still fits the videos
    const e = JSON.parse(localStorage.getItem('project') || 'null');
    if (e && Math.abs(e.total - total()) < 0.05 && Array.isArray(e.clips) && e.clips.every((c) => c.b > c.a && c.a >= 0 && c.b <= total() + 0.01)) { clips = e.clips; zooms = (e.zooms || []).filter((z) => z.b > z.a); }
  } catch {}
  const take = await kv.get('take');
  if (take?.samples?.length) { state.take = take; rebuildPeaks(take.samples); mixCache = null; }
  state.attempts = (await kv.get('attempts')) || {};
  const tm = await kv.get('takes');
  if (tm) { takeCounter = tm.n || 0; for (const t of tm.list || []) { const d = await kv.get('take-' + t.id); if (d?.samples) takes.push({ ...t, samples: d.samples }); } }
  // a saved take that is the same recording as the one in use keeps its identity, so it shows as "in use"
  if (state.take) { const same = takes.find((t) => t.samples.length === state.take.samples.length && t.rate === state.take.rate); if (same) state.take.samples = same.samples; }
  await showProject('Welcome back. Your video, script and take were restored.');
  drawWave();
  const savedMusic = await kv.get('music');
  if (savedMusic?.file) await loadMusic(savedMusic.file, true);
  renderSections();
  checkDraft();
})();
