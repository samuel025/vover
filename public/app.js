import { denoise, normaliseGain, stretch, mixMusic, findPauses, buildCaptions, toSrt, enhanceVoice, zoomState } from './fx.js';
import { exportLocally, pickSaveTarget, Unsupported } from './export.js';

const $ = (id) => document.getElementById(id);
let video = $('video'), spare = $('video2');
const scriptEl = $('script'), prompter = $('prompter'), wordsEl = $('words');
const timeline = $('tbody'), canvas = $('wave');

// take.samples holds the voice on the video's own timeline: sample 0 is video time 0.
const state = { file: null, serverId: null, take: null, recording: false, recPaused: false, playing: false, range: null, attempts: {} };
let ctx, stream, node, analyser, voiceSrc, listenSrc, mixCache = null, workletReady = false;
let base = new Float32Array(0), chunks = [], chunkLen = 0, capturing = false;
let spans = [], lastNow = -1, lastSec = -1;
let speed = 1;
let capStart = 0, draft = null;
let cutStart = null, editVer = 0, history = [], future = [], music = null, musicId = 0, takes = [], playK = -1, voiceFree = true, selTrack = 'video', zooms = [], zsel = null, pick = null, zoomDirty = false, vsp = [], asel = null, osources = [], ovl = [], osel = null;
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
// writing a long recording to storage copies all of it, so quick edits (undo, drags) share one write
let takeTimer = 0;
const writeTake = () => { clearTimeout(takeTimer); takeTimer = 0; return hasTake() ? kv.set('take', state.take) : kv.del('take'); };
const saveTake = () => { clearTimeout(takeTimer); takeTimer = setTimeout(writeTake, 700); };
addEventListener('pagehide', () => { if (takeTimer) writeTake(); });
document.addEventListener('visibilitychange', () => { if (document.hidden && takeTimer) writeTake(); });
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
  const onOv = voiceFree && selTrack === 'overlay', onVo = onVoice(), what = onOv ? 'overlay' : onVo ? 'voice' : 'clip';
  $('split').textContent = onOv ? 'Split overlay' : onVo ? 'Split voice' : 'Split'; $('delClip').textContent = onOv ? 'Delete overlay' : onVo ? 'Delete voice' : 'Delete';
  $('selTag').textContent = `${TRACKS[onOv ? 'overlay' : onVo ? 'voice' : 'video']} track`; $('selTag').dataset.t = onOv ? 'overlay' : onVo ? 'voice' : 'video';
  $('clipSpeed').disabled ||= onOv || onVo;
  document.querySelectorAll('#thead .th').forEach((el) => el.classList.toggle('sel', el.dataset.t === (onOv ? 'overlay' : onVo ? 'voice' : 'video')));
  $('linkVoice').checked = !voiceFree;
  syncInspector();
  wrap.classList.toggle('gone', gone);
  if (gone) for (const k of ['cut', 'rec', 'play', 'toStart', 'back', 'fwd']) $(k).disabled = true;
  $('pauses').disabled = !idle || !hasTake() || voiceFree;
  $('pauses').title = voiceFree ? 'Tick "Link voice to video" to cut out pauses' : 'Cuts long silences out of the recording and the video';
  $('zoomAdd').disabled = !idle;
  $('srt').disabled = !v;
  $('cut').classList.toggle('on', razor);
  $('clear').disabled = rec || !hasTake();
  $('expAudio').disabled = rec || !hasTake();
  $('export').disabled = rec || !(hasTake() || music) || gone;
  $('hear').disabled = rec;
  secEl.classList.toggle('busy', rec && !state.recPaused);
  $('timeline').classList.toggle('disabled', !v);
  $('badge').hidden = !rec;
  $('badge').classList.toggle('paused', state.recPaused);
  $('badgeText').textContent = state.recPaused ? 'PAUSED' : 'REC';
  updateRecLabel();
  $('takeLen').textContent = hasTake() ? `voice ${fmt(voiceFree ? voiceSec() : toEdit(voiceSec()))}` : '';
}
function updateRecLabel() {
  const t = gNow();
  $('recLabel').textContent = state.recording ? 'Stop' : hasTake() && t > 0.05 ? `Record from ${fmt(toEdit(t))}` : 'Record';
}

// ---------- video upload ----------
// The video stays on this device. It is only sent to the server if a server export is needed (see export below).
// a file the browser cannot play (some MKV or HEVC videos) would otherwise just sit there looking broken
for (const el of [video, spare]) el.onerror = () => { if (state.file && !jumping && el === video) status('This browser cannot play that video. Try an MP4 (H.264) or WebM file.'); };
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


// ---------- tracks: which one the buttons act on ----------
// Clicking a clip, a track name, or the empty part of a track selects that track. Split, Cut, Delete and Speed act on it.
const onVoice = () => voiceFree && selTrack === 'voice';
const TRACKS = { overlay: 'Overlay', video: 'Video', voice: 'Voice' };
function setTrack(t, quiet) {
  if (t === 'voice' && !voiceFree) { if (!quiet) status('The voice is linked to the video. Untick "Link voice to video" to edit it on its own.'); t = 'video'; }
  selTrack = t;
  document.querySelectorAll('#thead .th').forEach((el) => el.classList.toggle('sel', el.dataset.t === t));
  updateUI();
}
$('thead').onclick = (e) => { const t = e.target.closest('.th')?.dataset.t; if (t) setTrack(t); };
const trackAtY = (y) => { const r = $('tbody').getBoundingClientRect(); return y - r.top < 30 ? 'overlay' : y - r.top < 60 ? 'video' : 'voice'; };

// ---------- timeline (playhead + scrub) ----------
function seekTo(g) {
  if (!canSeek() || !total()) return;
  gSeek(snapG(Math.max(0, Math.min(total(), g)))).then(() => { if (state.playing) startVoice(); }); // never park the playhead inside a cut
  if (!state.playing) playK = -1;
}
function scrubAt(e) {
  const r = timeline.getBoundingClientRect();
  seekTo(toSrc(eAtX(e.clientX)));
}
let scrubbing = false;
// clicking the timeline takes the keyboard back from a menu or button, so Delete, B and the space bar act on the timeline
const releaseFocus = () => { const a = document.activeElement; if (a && /SELECT|BUTTON/.test(a.tagName)) a.blur(); };
timeline.addEventListener('pointerdown', releaseFocus, true);
timeline.onpointerdown = (e) => { if (!canSeek() || e.button) return; setTrack(trackAtY(e.clientY), true); scrubbing = true; timeline.setPointerCapture(e.pointerId); scrubAt(e); };
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
// A gap in the video track is a "blank" source with no file: nothing plays there, and a clock stands in for the video.
const bk = { t: 0, since: 0, on: false };
const isBlankSrc = (i) => !!sources[i]?.blank;
const blankT = () => Math.min(sources[loaded]?.dur ?? 0, bk.t + (bk.on ? ((performance.now() - bk.since) / 1000) * (state.recording ? 1 : +$('rate').value || 1) : 0));
const gNow = () => (loaded >= 0 && sources[loaded] ? sources[loaded].off + (isBlankSrc(loaded) ? blankT() : video.currentTime || 0) : 0);
const vPlay = () => { if (isBlankSrc(loaded)) { bk.t = blankT(); bk.since = performance.now(); bk.on = true; return Promise.resolve(); } return video.play(); };
const vPause = () => { if (isBlankSrc(loaded)) { bk.t = blankT(); bk.on = false; } video.pause(); };
const vPaused = () => (isBlankSrc(loaded) ? !bk.on : video.paused);
const realTotal = () => sources.reduce((m, x) => (x.blank ? m : Math.max(m, x.off + x.dur)), 0);

function probe(file) {
  return new Promise((res, rej) => {
    const v = document.createElement('video'), url = URL.createObjectURL(file);
    v.preload = 'metadata';
    v.onloadedmetadata = () => res({ dur: v.duration, url, vw: v.videoWidth, vh: v.videoHeight });
    v.onerror = () => rej(new Error('unplayable'));
    v.src = url;
  });
}
// Two players take turns. The one on screen plays; the other loads the next video and waits on the exact frame needed, then they swap
// in one step, so changing from one video to another never shows a blank player or the start of the video.
const prep = { i: -1, t: 0, p: null };
function prepare(i, g) {
  if (isBlankSrc(i)) return Promise.resolve();
  const t = Math.max(0, g - sources[i].off);
  if (prep.i === i && Math.abs(prep.t - t) < 0.05 && prep.p) return prep.p; // already on its way
  prep.i = i; prep.t = t;
  const el = spare;
  prep.p = new Promise((res) => {
    const place = () => { if (Math.abs(el.currentTime - t) > 0.04) { el.addEventListener('seeked', () => res(), { once: true }); el.currentTime = t; } else res(); };
    if (el.dataset.i === String(i) && el.readyState >= 2) place(); // this player already holds that video
    else { el.dataset.i = String(i); el.addEventListener('loadeddata', place, { once: true }); el.src = sources[i].url + '#t=' + t; } // the #t starts it at the right moment
  });
  return prep.p;
}
function swapPlayers(i) {
  const old = video;
  video = spare; spare = old;
  video.id = 'video'; spare.id = 'video2';
  video.hidden = false; video.muted = old.muted;
  video.style.visibility = ''; spare.style.visibility = 'hidden';
  spare.pause(); spare.style.transform = '';
  loaded = i; bk.on = false; prep.i = -1; prep.p = null;
}
// moves the playhead to project time g, switching to another video file when it lives in one
async function gSeek(g) {
  if (!sources.length) return;
  g = Math.max(0, Math.min(total(), g));
  const i = srcOf(g), token = ++seekToken;
  if (isBlankSrc(i)) { // a gap: hide the picture and run the clock from here
    if (!isBlankSrc(loaded)) { video.pause(); video.style.visibility = 'hidden'; bk.on = false; }
    loaded = i; bk.t = g - sources[i].off; bk.since = performance.now();
    return;
  }
  if (i === loaded) { video.currentTime = g - sources[i].off; return; }
  await prepare(i, g);
  if (token !== seekToken || prep.i !== i) return;
  swapPlayers(i);
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
    if (s.blank) continue;
    const used = clips.filter((c) => c.a >= s.off - 1e-6 && c.b <= s.off + s.dur + 1e-6).sort((x, y) => x.a - y.a);
    let at = s.off;
    for (const c of used) { if (c.a - at > 0.05) out.push({ a: at, b: c.a }); at = Math.max(at, c.b); }
    if (s.off + s.dur - at > 0.05) out.push({ a: at, b: s.off + s.dur });
  }
  return out;
};
// true when the export could be done by cutting the one video alone: no moving, no speed changes, no second video
const plainEdit = () => !ovl.length && sources.length === 1 && clips.every((c, i) => c.r === 1 && (i === 0 || c.a >= clips[i - 1].b - 1e-6));

// ---------- gaps: clips that sit wherever they are put ----------
// With the voice on its own track the video track works like a normal editor: deleting or moving a clip leaves empty space instead of
// closing up. Every real clip has a start time on the timeline; the space between them is filled by gap clips taken from one "gap" source.
const isBlankClip = (c) => !!c && !!sources[sameSrc(c)]?.blank;
const realItems = () => segs().filter((g) => !sources[g.src].blank).map((g) => ({ c: { a: g.a, b: g.b, r: g.r }, at: g.e0 }));
function layout(items) {
  const keepE = loaded >= 0 && clips.length ? toEdit(gNow()) : 0, was = sources[loaded];
  items = items.slice().sort((x, y) => x.at - y.at);
  const real = sources.filter((x) => !x.blank), base = realTotal(), out = [];
  let end = 0;
  for (const it of items) { // a clip dropped on top of another is pushed along to the end of it
    const at = Math.max(it.at, end);
    if (at - end > 0.02) out.push({ a: 0, b: at - end, r: 1, gap: true });
    out.push(it.c); end = at + (it.c.b - it.c.a) / it.c.r;
  }
  if (padEnd() - end > 0.02) out.push({ a: 0, b: padEnd() - end, r: 1, gap: true }); // an overlay or voice running past the main video: empty space to hold it
  const dur = out.reduce((n, c) => n + (c.gap ? c.b : 0), 0);
  sources = dur > 0 ? [...real, { id: 'gap', name: 'Gap', blank: true, dur, off: base }] : real;
  let o = base;
  for (const c of out) if (c.gap) { const d = c.b; c.a = o; c.b = o + d; o += d; delete c.gap; }
  clips = out;
  touched(); saveSources();
  if (loaded >= 0 && sources[loaded] !== was) { loaded = -1; if (clips.length) gSeek(snapG(toSrc(keepE))); }
}
// where the last thing on the overlay or voice track ends
const voiceEnd = () => (voiceFree && hasTake() && !state.recording ? (pieces().at(-1)?.e ?? 0) : 0);
const padEnd = () => Math.max(oEnd(), voiceEnd());
// keeps the main track as long as the last thing on any track, so playback and export stop exactly there
function syncTail() {
  if (!voiceFree || !sources.length || state.recording) return false;
  const real = segs().filter((g) => !sources[g.src].blank), last = real[real.length - 1], end = last ? last.e0 + (last.b - last.a) / last.r : 0;
  if (Math.abs(editedLen() - Math.max(end, padEnd())) <= 0.05) return false;
  layout(realItems());
  return true;
}
// removes gap clips and the gap source (the voice is tied to the video again, so there is nothing to leave space for)
function dropGaps() {
  const was = sources[loaded];
  clips = clips.filter((c) => !isBlankClip(c)); sources = sources.filter((x) => !x.blank);
  if (sources[loaded] !== was) loaded = -1;
  touched(); saveSources();
}

// ---------- timeline zoom and scroll ----------
// The timeline can show just part of the edited video, so cuts and trims can be placed precisely, and it can be scrolled to the side:
// there is always empty room after the last thing, so clips can be dragged on without limit. The export stops at the last thing on any track.
// view.len is how many seconds are visible (0 means "fit": all of what is there) and view.s is where the visible part starts.
let view = { s: 0, len: 0 }, reach = 0;
// with the voice on its own track the timeline is as long as the longer of the video and the voice, so no voice is ever hidden
const extent = () => (voiceFree && hasTake() ? Math.max(editedLen(), voiceSec()) : editedLen());
const runway = (C) => Math.max(10, C * 0.25);
function vr() {
  const C = extent() || 1, L = Math.max(C + runway(C), reach), len = view.len ? Math.max(0.5, Math.min(L, view.len)) : C;
  return { L, C, len, s: view.len ? Math.max(0, Math.min(L - len, view.s)) : 0 };
}
const pctE = (e) => { const v = vr(); return ((e - v.s) / v.len) * 100; };
const eAtX = (clientX, el = timeline) => { const r = el.getBoundingClientRect(), v = vr(); return v.s + Math.max(0, Math.min(1, (clientX - r.left) / r.width)) * v.len; };
function setView(s, len) { view = { s, len }; renderCuts(); updateScroll(); }
function zoomBy(factor, anchor) {
  const v = vr(), len = Math.min(v.C, Math.max(0.5, v.len / factor));
  const a = anchor ?? (toEdit(gNow()) >= v.s && toEdit(gNow()) <= v.s + v.len ? toEdit(gNow()) : v.s + v.len / 2); // keep the playhead (or the middle) where it is
  const rel = (a - v.s) / v.len;
  setView(Math.max(0, a - rel * len), len >= v.C - 1e-6 ? 0 : len);
}
function updateScroll() {
  const v = vr(), bar = $('tscroll'), fit = !view.len || (Math.abs(v.len - v.C) < 1e-6 && v.s < 1e-6);
  bar.hidden = !total();
  $('tzLevel').textContent = fit ? 'Fit' : (v.C / v.len).toFixed(v.C / v.len < 10 ? 1 : 0) + '×';
  if (total()) { const t = bar.firstElementChild; t.style.left = (v.s / v.L) * 100 + '%'; t.style.width = (v.len / v.L) * 100 + '%'; }
}
$('tzIn').onclick = () => zoomBy(1.6);
$('tzOut').onclick = () => zoomBy(1 / 1.6);
$('tzFit').onclick = () => setView(0, 0);
timeline.addEventListener('wheel', (e) => {
  if (!total()) return;
  const v = vr();
  if (e.ctrlKey || e.metaKey) { e.preventDefault(); zoomBy(e.deltaY < 0 ? 1.25 : 0.8, eAtX(e.clientX)); }
  else { e.preventDefault(); setView(v.s + ((e.deltaX || e.deltaY) / timeline.clientWidth) * v.len, v.len); } // scroll along the zoomed timeline
}, { passive: false });
// While a clip or voice piece is being dragged, holding it near either side scrolls along; to the right there is no end.
let edge = null;
function edgeStart(onMove) {
  const v = vr();
  if (!view.len) view = { s: v.s, len: v.len }; // pin the window so it scrolls instead of rescaling
  edge = { x: 0, onMove, timer: setInterval(() => {
    const r = timeline.getBoundingClientRect(), w = vr(), zone = 56;
    const dir = edge.x > r.right - zone ? Math.min(1, (edge.x - (r.right - zone)) / zone) : edge.x < r.left + zone ? -Math.min(1, (r.left + zone - edge.x) / zone) : 0;
    if (!dir || (dir < 0 && w.s <= 0)) return;
    reach = Math.max(reach, w.s + w.len * 1.1);
    setView(Math.max(0, w.s + dir * w.len * 0.025), w.len);
    edge.onMove({ clientX: edge.x });
  }, 30) };
}
const edgeTrack = (e) => { if (edge) edge.x = e.clientX; };
function edgeStop() { if (edge) { clearInterval(edge.timer); edge = null; } reach = 0; }
// the bar under the timeline shows which part is visible; drag it to scroll, click it to jump
let barDrag = null;
$('tscroll').onpointerdown = (e) => {
  const v = vr(), r = $('tscroll').getBoundingClientRect(), t = (e.clientX - r.left) / r.width * v.L;
  $('tscroll').setPointerCapture(e.pointerId);
  const onThumb = t >= v.s && t <= v.s + v.len;
  barDrag = { dx: onThumb ? t - v.s : v.len / 2 };
  setView(Math.max(0, Math.min(v.L - v.len, t - barDrag.dx)), v.len);
};
$('tscroll').onpointermove = (e) => {
  if (!barDrag) return;
  const v = vr(), r = $('tscroll').getBoundingClientRect(), t = (e.clientX - r.left) / r.width * v.L;
  setView(Math.max(0, Math.min(v.L - v.len, t - barDrag.dx)), v.len);
};
$('tscroll').onpointerup = $('tscroll').onpointercancel = () => { barDrag = null; };

function newProject() {
  discardTake();
  view = { s: 0, len: 0 }; voiceFree = true; vsp = []; asel = null; ovl = []; osources = []; osel = null; syncMode(); sources = []; clips = []; zooms = []; zsel = null; pick = null; loaded = -1; takes = []; cutStart = null; history = []; future = []; touched();
  try { localStorage.removeItem('project'); localStorage.removeItem('marks'); } catch {}
  kv.get('sources').then((m) => { for (const x of m || []) kv.del('src-' + x.id); kv.del('video'); }).then(() => kv.get('osources')).then((m) => { for (const x of m || []) kv.del('osrc-' + x.id); kv.del('osources'); }).then(() => kv.del('takes'));
}
async function addSource(file, id) {
  const { dur, url, vw, vh } = await probe(file);
  const s = { id: id || crypto.randomUUID(), name: file.name, file, url, dur, vw, vh, off: total() };
  sources.push(s);
  return s;
}
const saveSources = () => kv.set('sources', sources.map(({ id, name, dur, blank }) => ({ id, name, dur, blank })));
function saveProject() { try { localStorage.setItem('project', JSON.stringify({ total: total(), clips, zooms, voiceFree, vsp, ovl })); } catch {} }

async function showProject(msg) {
  state.file = sources[0]?.file || null;
  video.hidden = spare.hidden = !sources.length; $('empty').hidden = !!sources.length;
  await gSeek(clips.length ? clips[0].a : 0);
  applyShape(); touched(); layoutWords(); renderCuts(); renderTakes(); renderZooms(); updateUI();
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
  const pool = sources.filter((x) => x.blank), k = curIdx();
  try {
    checkpoint();
    // with separate tracks the video goes into the empty space under the playhead, or at the end
    const items = voiceFree ? realItems() : null, e = toEdit(gNow()), atEnd = editedLen(), into = voiceFree && isBlankClip(clips[k]);
    if (voiceFree) { if (isBlankSrc(loaded)) loaded = -1; sources = sources.filter((x) => !x.blank); }
    let s;
    try { s = await addSource(file); } catch (err) { sources = [...sources, ...pool]; throw err; }
    if (voiceFree) { items.push({ c: { a: s.off, b: s.off + s.dur, r: 1 }, at: into ? e : atEnd }); layout(items); if (loaded < 0) await gSeek(snapG(toSrc(e))); }
    else clips.push({ a: s.off, b: s.off + s.dur, r: 1 });
    kv.set('src-' + s.id, { file }); saveSources();
    commitEdit(); updateUI();
    status(voiceFree ? `Added ${file.name} ${into ? 'in the empty space at the playhead' : 'at the end'}. Drag it anywhere on the timeline.` : `Added ${file.name} at the end. Your script and recording now run across both videos. Use New project to start over instead.`);
  } catch { history.pop(); status('This browser cannot play that video. Try an MP4 (H.264) or WebM file.'); }
}
// A blank workspace: the video, script, recording, takes, music and edits are cleared (the original video file is never touched).
function blankWorkspace() {
  if (state.recording && !state.recPaused) return status('Stop recording first.');
  if (sources.length && !confirm('Start a blank workspace? Your video, script, recording and edits will be cleared. The original video file on your computer is not touched.')) return;
  stopAll();
  newProject();
  state.file = null; state.serverId = null;
  for (const el of [video, spare]) { el.removeAttribute('src'); el.removeAttribute('data-i'); el.load(); }
  prep.i = -1; prep.p = null;
  scriptEl.value = ''; try { localStorage.removeItem('script'); } catch {}
  music = null; kv.del('music'); $('musicName').textContent = ''; $('musicOpts').hidden = true;
  renderSections(); drawWave();
  showProject('Blank workspace. Drop a video here or click browse to begin.');
}
$('newProject').onclick = blankWorkspace;

// ---------- save and open a whole workspace ----------
// One file holds everything: a header (settings, edits, script) followed by the video files, the voice and the music, side by side.
// Blobs are joined without being read into memory, so large videos are fine. Opening writes it all into the browser's own storage and reloads,
// which runs the same restore path as coming back to the page.
const WS_MAGIC = 'VOVER1\n';
const lsGet = (k) => { try { return localStorage.getItem(k); } catch { return null; } };
async function saveWorkspace() {
  if (!sources.length) return status('There is nothing to save yet. Add a video first.');
  stopAll();
  let handle = null;
  try {
    if (window.showSaveFilePicker) handle = await window.showSaveFilePicker({ suggestedName: 'workspace.vover', types: [{ description: 'Voiceover workspace', accept: { 'application/octet-stream': ['.vover'] } }] });
  } catch (e) { if (e.name === 'AbortError') return; }
  status('Saving the workspace…');
  try {
    const parts = [], blobs = [];
    const add = (name, blob, extra = {}) => { parts.push({ name, len: blob.size, ...extra }); blobs.push(blob); };
    for (const x of sources) if (!x.blank) add('src:' + x.id, x.file, { type: x.file.type, fname: x.file.name });
    for (const x of osources) add('osrc:' + x.id, x.file, { type: x.file.type, fname: x.file.name });
    if (hasTake()) add('take', new Blob([state.take.samples]));
    for (const t of takes) add('take:' + t.id, new Blob([t.samples]));
    const mus = await kv.get('music');
    if (mus?.file) add('music', mus.file, { type: mus.file.type, fname: mus.file.name });
    const head = {
      v: 1, sources: sources.map(({ id, name, dur, blank }) => ({ id, name, dur, blank })), project: JSON.stringify({ total: total(), clips, zooms, voiceFree, vsp, ovl }), osources: osources.map(({ id, name, dur }) => ({ id, name, dur })),
      script: scriptEl.value, marks: lsGet('marks'), fx: lsGet('fx'), takeRate: state.take?.rate, takeCounter,
      takes: takes.map(({ id, name, stars, at, rate, free }) => ({ id, name, stars, at, rate, free })), parts,
    };
    const enc = new TextEncoder().encode(JSON.stringify(head));
    const out = new Blob([WS_MAGIC, new Uint8Array(new Uint32Array([enc.length]).buffer), enc, ...blobs]);
    if (handle) await out.stream().pipeTo(await handle.createWritable());
    else Object.assign(document.createElement('a'), { href: URL.createObjectURL(out), download: 'workspace.vover' }).click();
    status(`Workspace saved (${(out.size / 1e6).toFixed(0)} MB). Use Open workspace to bring it back, on this computer or another.`);
  } catch (e) { status('Could not save the workspace: ' + e.message); }
}
async function openWorkspace(file) {
  if (!file) return;
  stopAll();
  try {
    const dec = new TextDecoder(), top = new Uint8Array(await file.slice(0, 11).arrayBuffer());
    if (dec.decode(top.slice(0, 7)) !== WS_MAGIC) return status('That is not a workspace file saved from here.');
    const hl = new DataView(top.buffer).getUint32(7, true), h = JSON.parse(dec.decode(await file.slice(11, 11 + hl).arrayBuffer()));
    if (sources.length && !confirm('Open this workspace? What is on screen now is replaced (save it first if you want to keep it).')) return;
    status('Opening the workspace…');
    const blobs = {}; let at = 11 + hl;
    for (const p of h.parts) { blobs[p.name] = { blob: file.slice(at, at + p.len, p.type || ''), p }; at += p.len; }
    // clear what is stored now, then store the workspace
    for (const x of (await kv.get('sources')) || []) kv.del('src-' + x.id);
    for (const x of (await kv.get('osources')) || []) kv.del('osrc-' + x.id);
    for (const x of ((await kv.get('takes'))?.list) || []) kv.del('take-' + x.id);
    for (const k of ['take', 'attempts', 'music', 'draft', 'video']) await kv.del(k);
    clearTimeout(takeTimer); takeTimer = 0; state.take = null; // a pending save of the old voice must not overwrite this one
    const fileOf = ({ blob, p }) => new File([blob], p.fname || 'file', { type: p.type || '' });
    await kv.set('sources', h.sources);
    for (const x of h.sources) if (!x.blank) await kv.set('src-' + x.id, { file: fileOf(blobs['src:' + x.id]) });
    await kv.set('osources', h.osources || []);
    for (const x of h.osources || []) await kv.set('osrc-' + x.id, { file: fileOf(blobs['osrc:' + x.id]) });
    if (blobs.take) await kv.set('take', { samples: new Float32Array(await blobs.take.blob.arrayBuffer()), rate: h.takeRate });
    for (const t of h.takes || []) if (blobs['take:' + t.id]) await kv.set('take-' + t.id, { samples: new Float32Array(await blobs['take:' + t.id].blob.arrayBuffer()) });
    await kv.set('takes', { n: h.takeCounter || 0, list: h.takes || [] });
    if (blobs.music) await kv.set('music', { file: fileOf(blobs.music) });
    const ls = (k, v) => { try { v == null ? localStorage.removeItem(k) : localStorage.setItem(k, v); } catch {} };
    ls('project', h.project); ls('script', h.script); ls('marks', h.marks); ls('fx', h.fx);
    location.reload();
  } catch (e) { status('Could not open that file: ' + e.message); }
}
$('saveWs').onclick = saveWorkspace;
$('openWs').onchange = (e) => { openWorkspace(e.target.files[0]); e.target.value = ''; };
$('addFile').onchange = (e) => { addVideo(e.target.files[0]); e.target.value = ''; };

// undo / redo: a snapshot is the clips, the videos and the recorded voice (the voice arrays are never changed in place, so keeping them is cheap)
const snap = () => ({ clips: JSON.stringify(clips), zooms: JSON.stringify(zooms), voiceFree, vsp: vsp.slice(), sources: sources.slice(), ovl: JSON.stringify(ovl), osources: osources.slice(), take: state.take ? { samples: state.take.samples, rate: state.take.rate } : null });
function checkpoint() { history.push(snap()); if (history.length > 15) history.shift(); future = []; updateUI(); }
function applySnap(sn) {
  const keepE = sources.length && loaded >= 0 ? toEdit(gNow()) : 0, was = sources[loaded];
  const sameTake = (state.take?.samples || null) === (sn.take?.samples || null), sameSources = sources.length === sn.sources.length && sources.every((x, i) => x === sn.sources[i]);
  clips = JSON.parse(sn.clips); zooms = JSON.parse(sn.zooms); voiceFree = !!sn.voiceFree; vsp = (sn.vsp || []).slice(); asel = null; ovl = JSON.parse(sn.ovl || '[]'); osources = (sn.osources || []).slice(); osel = null; syncMode(); zsel = null; pick = null; sources = sn.sources.slice(); cutStart = null;
  if (loaded >= sources.length || sources[loaded] !== was) loaded = -1;
  state.take = sn.take ? { ...sn.take } : null; mixCache = null;
  if (!sameTake) rebuildPeaks(state.take?.samples || new Float32Array(0));
  saveProject(); if (!sameSources) saveSources(); if (!sameTake) saveTake(); touched(); renderCuts(); renderZooms(); renderSections(); drawWave(); updateUI();
  if (loaded < 0 || clipIndexAt(gNow()) < 0) gSeek(snapG(loaded < 0 ? toSrc(keepE) : gNow()));
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

// ---------- edits that change only the video ----------
// Normally the voice belongs to the video: cutting a part of the video cuts the voice that goes with it. With "video only" the voice
// is laid out on the finished timeline instead, so it stays exactly where it is and edits to the video do not move or remove it.
// vt turns a position in the video into a position in the voice recording.
const vt = (g) => (voiceFree ? toEdit(g) : g);
const vInv = (t) => (voiceFree ? toSrc(t) : t);
const voiceSec = () => (hasTake() ? state.take.samples.length / state.take.rate : 0);
const overrunNote = () => ''; // the video now runs on to the end of the voice, so nothing is left out
function setTakeSamples(samples, rate) {
  state.take = { samples, rate }; state.attempts = {}; saveAttempts(); mixCache = null;
  rebuildPeaks(samples); saveTake(); touched();
}
// video and voice -> video only: the voice is re-laid onto the edited timeline, so it sounds exactly the same right now
function bakeVoice() {
  if (!hasTake()) return;
  const { samples, rate } = state.take;
  setTakeSamples(concat(segs().map((g) => {
    const from = Math.round(g.a * rate), raw = new Float32Array(Math.round((g.b - g.a) * rate));
    if (from < samples.length) raw.set(samples.subarray(from, from + raw.length));
    return stretch(raw, g.r);
  })), rate);
}
// video only -> video and voice: each clip takes the voice that is under it on the timeline back to where it came from
function unbakeVoice() {
  if (!hasTake()) return;
  const { samples, rate } = state.take, out = new Float32Array(Math.round(total() * rate));
  for (const g of segs()) {
    const from = Math.round(g.e0 * rate), piece = new Float32Array(Math.round(((g.b - g.a) / g.r) * rate));
    if (from < samples.length) piece.set(samples.subarray(from, from + piece.length));
    const back = stretch(piece, 1 / g.r), at = Math.round(g.a * rate);
    out.set(back.subarray(0, Math.max(0, Math.min(back.length, out.length - at))), at);
  }
  setTakeSamples(out, rate);
}
// The voice is either on its own track (the default: deleting or cutting video leaves the voice alone) or linked to the video.
function syncMode() { $('linkVoice').checked = !voiceFree; }
// the Add menu closes after a choice, or when you click elsewhere
for (const m of document.querySelectorAll('details.addmenu')) m.addEventListener('click', (e) => { if (e.target.closest('label, button')) setTimeout(() => (m.open = false), 0); });
document.addEventListener('pointerdown', (e) => { for (const m of document.querySelectorAll('details.addmenu')) if (!m.contains(e.target)) m.open = false; });
$('linkVoice').onchange = (e) => {
  const free = !e.target.checked;
  e.target.blur();
  if (!free && ovl.length) { syncMode(); return status('Delete the overlay clips first: linking ties everything to the main video, so it cannot hold overlays.'); }
  if (!canSeek()) { syncMode(); return status('Stop recording first.'); }
  if (free !== voiceFree) {
    stopPlay(); archiveTake(); checkpoint();
    if (free) bakeVoice(); else { unbakeVoice(); if (sources.some((x) => x.blank)) { dropGaps(); const n = Math.round(realTotal() * state.take.rate); if (hasTake() && state.take.samples.length > n) setTakeSamples(state.take.samples.slice(0, n), state.take.rate); gSeek(0); } }
    voiceFree = free;
  }
  asel = null; if (!voiceFree && selTrack !== 'video') selTrack = 'video';
  saveProject(); touched(); renderCuts(); renderSections(); drawWave(); renderTakes(); updateUI();
  status(free ? 'Voice and video are separate. Deleting or cutting video leaves your voice where it is.' : 'Voice linked to video. Cutting or deleting video also removes the voice under it. Your voice was moved back to match the video.');
};

// ---------- editing only the voice ----------
// The voice is a stretch of samples; the pieces are the parts of it that have sound, separated by silence or by a split.
// Cutting or deleting a piece blanks it, so the space stays; dragging a piece moves its samples, and it clings to nearby edges.
let pieceCache = null;
function pieces() {
  if (!hasTake()) return [];
  const { samples, rate } = state.take, key = vsp.join(',');
  if (pieceCache?.ref === samples && pieceCache.key === key) return pieceCache.list;
  const min = Math.round(rate * 0.03), spans = [], n = samples.length;
  let from = -1, last = -1;
  for (let i = 0; i < n; i++) {
    if (samples[i] !== 0) { if (from < 0) from = i; last = i; }
    else if (from >= 0 && i - last > min) { spans.push([from, last + 1]); from = -1; }
  }
  if (from >= 0) spans.push([from, last + 1]);
  const cuts = vsp.map((t) => Math.round(t * rate)), list = [], tiny = Math.round(rate * 0.02);
  for (const [a, b] of spans) {
    let lo = a;
    for (const c of cuts.filter((c) => c > a + tiny && c < b - tiny)) { list.push({ s: lo / rate, e: c / rate }); lo = c; }
    list.push({ s: lo / rate, e: b / rate });
  }
  pieceCache = { ref: samples, key, list };
  return list;
}
const pieceAt = (t) => pieces().find((p) => t >= p.s && t < p.e);
const chosenPiece = () => (asel && pieces().find((p) => Math.abs(p.s - asel.s) < 0.02)) || pieceAt(toEdit(gNow()));
function afterVoiceEdit() { saveProject(); drawWave(); updateUI(); }
function blankVoice(lo, hi) {
  const { samples, rate } = state.take, out = samples.slice();
  out.fill(0, Math.max(0, Math.round(lo * rate)), Math.min(out.length, Math.round(hi * rate)));
  setTakeSamples(out, rate);
  vsp = vsp.filter((t) => t < lo - 1e-4 || t > hi + 1e-4);
}
function voiceSplit(t) {
  const p = pieceAt(t);
  if (!p || t - p.s < 0.1 || p.e - t < 0.1) return status('Click inside a piece of the voice, away from its ends, to cut it.');
  checkpoint(); vsp = [...vsp, t].sort((a, b) => a - b); asel = null; afterVoiceEdit();
  status(`Split the voice at ${fmt(t)}. Click a piece, then drag it or press Delete.`);
}
function voiceDelete() {
  const p = chosenPiece();
  if (!p) return status('Click a piece of the voice first, or put the playhead on one.');
  checkpoint(); blankVoice(p.s, p.e); asel = null; afterVoiceEdit();
  status(`Deleted ${(p.e - p.s).toFixed(1)}s of voice and left the space. Undo brings it back.`);
}
function voiceMove(p, d) {
  const { samples, rate } = state.take, a = Math.round(p.s * rate), b = Math.round(p.e * rate), to = Math.max(0, a + Math.round(d * rate));
  const out = new Float32Array(Math.max(samples.length, to + (b - a))), piece = samples.slice(a, b);
  out.set(samples); out.fill(0, a, b); out.set(piece, to);
  setTakeSamples(out, rate);
  const dd = (to - a) / rate, to0 = p.s + dd, to1 = p.e + dd;
  const inside = vsp.filter((t) => t > p.s + 1e-4 && t < p.e - 1e-4).map((t) => t + dd);
  const outside = vsp.filter((t) => !(t >= p.s - 1e-4 && t <= p.e + 1e-4) && !(t > to0 && t < to1));
  vsp = [...outside, ...inside, to0, to1].sort((x, y) => x - y).filter((t, i, l) => !i || t - l[i - 1] > 1e-4);
  asel = { s: to0, e: to1 };
}
// where a piece being dragged by d lands: its edges cling to the edges of other pieces, the start of the recording and the end of the video
function magnet(p, d, tol) {
  const marks = [0, editedLen(), ...pieces().filter((o) => Math.abs(o.s - p.s) > 1e-6).flatMap((o) => [o.s, o.e])];
  d = Math.max(-p.s, d);
  let best = null;
  for (const edge of [p.s + d, p.e + d]) for (const q of marks) {
    const gap = Math.abs(q - edge);
    if (gap < tol && (!best || gap < best.gap)) best = { gap, adj: q - edge, at: q };
  }
  return best ? { d: Math.max(-p.s, d + best.adj), at: best.at } : { d, at: null };
}
let adrag = null;
function renderPieces() {
  const lane = $('alane');
  const on = voiceFree && hasTake() && !state.recording && extent() > 0;
  lane.hidden = !on;
  if (!on) { lane.innerHTML = ''; return; }
  const v = vr();
  lane.innerHTML = pieces().map((p, i) => {
    const sel = asel && Math.abs(p.s - asel.s) < 0.02;
    return `<div class="ablk${sel ? ' sel' : ''}" data-i="${i}" style="left:${pctE(p.s)}%;width:${((p.e - p.s) / v.len) * 100}%" title="Drag to move, Delete to remove"></div>`;
  }).join('');
}
$('alane').onpointerdown = (e) => {
  const lane = $('alane'), el = e.target.closest('.ablk');
  if (!el || !canSeek() || e.button) return;
  e.stopPropagation();
  const p = pieces()[+el.dataset.i];
  asel = { s: p.s, e: p.e }; setTrack('voice'); showEdit();
  lane.querySelectorAll('.ablk').forEach((b) => b.classList.toggle('sel', b === el));
  adrag = { p, el, i: +el.dataset.i, s0: vr().s, x0: e.clientX, perPx: vr().len / lane.getBoundingClientRect().width, d: 0, moved: false };
  addEventListener('pointermove', amove); addEventListener('pointerup', aup); addEventListener('pointercancel', aup);
};
function amove(e) {
  if (!adrag) return;
  const lane = $('alane');
  edgeTrack(e);
  const dx = e.clientX - adrag.x0;
  if (!adrag.moved && Math.abs(dx) < 4) return;
  adrag.moved = true;
  if (!edge) edgeStart(amove);
  const m = magnet(adrag.p, dx * adrag.perPx + (vr().s - adrag.s0), 10 * adrag.perPx);
  m.d = Math.min(m.d, 3600 - adrag.p.e); // a recording is kept in memory, so there is a limit of an hour
  adrag.d = m.d;
  const el = lane.querySelector(`[data-i="${adrag.i}"]`);
  el.classList.add('dragging');
  el.style.left = pctE(adrag.p.s + m.d) + '%';
  lane.querySelector('.drop')?.remove();
  if (m.at !== null) { const line = Object.assign(document.createElement('div'), { className: 'drop' }); line.style.left = pctE(m.at) + '%'; lane.append(line); }
}
function aup(e) {
  const lane = $('alane');
  removeEventListener('pointermove', amove); removeEventListener('pointerup', aup); removeEventListener('pointercancel', aup);
  const d = adrag; adrag = null; edgeStop();
  if (!d) return;
  lane.querySelector('.drop')?.remove();
  if (!d.moved || Math.abs(d.d) < 1e-3) { if (!d.moved) seekTo(toSrc(eAtX(e.clientX))); renderPieces(); return; }
  checkpoint(); voiceMove(d.p, d.d); afterVoiceEdit();
  status(`Moved the voice to ${fmt(asel.s)}.${overrunNote()}`);
}

const SRC_TINT = ['', 's1', 's2', 's3'];
function renderCuts() {
  syncTail();
  const v = vr(), list = segs(), k = curIdx(), pct = (e) => ((e - v.s) / v.len) * 100;
  $('strip').innerHTML = list.map((s, i) => {
    const w = ((s.b - s.a) / s.r / v.len) * 100;
    if (sources[s.src].blank) return `<div class="blk gap${i === k ? ' sel' : ''}" data-i="${i}" style="left:${pct(s.e0)}%;width:${w}%" title="Empty space. Click it and press Delete to close it, or drag a clip in"><span>${((s.b - s.a) / s.r).toFixed(1)}s</span></div>`;
    const label = `${i + 1}${s.r !== 1 ? ` · ${s.r}×` : ''}${sources.length > 1 ? ` · ${esc(sources[s.src].name)}` : ''}`;
    return `<div class="blk ${SRC_TINT[s.src % 4]}${i === k ? ' sel' : ''}" data-i="${i}" style="left:${pct(s.e0)}%;width:${w}%" title="${esc(sources[s.src]?.name || '')}"><span>${label}</span></div>`;
  }).join('');
  $('ostrip').innerHTML = ovl.map((c, i) => `<div class="blk ovl${i === selIdx() ? ' sel' : ''}" data-i="${i}" style="left:${pct(c.at)}%;width:${(olen(c) / v.len) * 100}%" title="${esc(osources[c.o]?.name || '')}"><span>${esc(osources[c.o]?.name || 'Overlay')}</span></div>`).join('');
  // a dot where a clip was split in two, a red line where something was cut out or clips from different places meet
  $('cuts').innerHTML = list.slice(1).map((s, i) => {
    const prev = list[i], joined = Math.abs(prev.b - s.a) < 1e-3 && prev.src === s.src && prev.r === s.r;
    return `<i class="${joined ? 'split' : ''}" style="left:${pct(s.e0)}%"></i>`;
  }).join('') + (cutStart === null ? '' : `<i class="pending" style="left:${pct(toEdit(cutStart))}%"></i>`)
    + zooms.map((z) => `<b class="zm${z === zsel ? ' sel' : ''}" style="left:${pct(toEdit(z.a))}%;width:${Math.max(0.5, ((toEdit(z.b) - toEdit(z.a)) / v.len) * 100)}%">🔍 ${z.k.toFixed(1)}×</b>`).join('');
  $('dur').textContent = fmt(editedLen());
  const gaps = voiceFree ? [] : gapsOf(), bar = $('cutbar');
  bar.hidden = !gaps.length && cutStart === null;
  bar.innerHTML = (cutStart !== null
    ? `<span>Cut starts at ${fmt(toEdit(cutStart))}. Move to where it ends, then press Cut again (Esc cancels).</span>`
    : gaps.map((g, i) => `<span>✂ ${(g.b - g.a).toFixed(1)}s removed</span><button class="btn ghost" data-restore="${i}">Restore</button>`).join(''))
    + (gaps.length ? `<span class="sub">Edited length ${fmt(editedLen())}</span>` : '');
  lastClipKey = '';
  drawWave(); renderMarks(); updateScroll(); updateUI();
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
  if (sources[s.src].blank) { $('clipInfo').textContent = `Empty space ${((s.b - s.a) / s.r).toFixed(1)}s · Delete closes it`; return; }
  $('clipInfo').textContent = `Clip ${k + 1} of ${clips.length} · ${((s.b - s.a) / s.r).toFixed(1)}s${voiceFree ? '' : ' · linked to your voice'}`;
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

// cuts the main video at timeline time e
function splitVideoAt(e) {
  const list = segs(), k = list.findIndex((g) => e > g.e0 + 0.05 && e < g.e0 + (g.b - g.a) / g.r - 0.05);
  if (k < 0) return status('Click inside a video clip to cut it there.');
  const c = clips[k], g = list[k].a + (e - list[k].e0) * list[k].r;
  checkpoint(); clips.splice(k, 1, { ...c, b: g }, { ...c, a: g }); commitEdit();
  status(`Cut the video at ${fmt(e)}. Click a part and press Delete to remove it, or drag it to move it.`);
}
function splitHere() {
  if (!canSeek()) return;
  const e = toEdit(gNow());
  if (voiceFree && selTrack === 'overlay') return splitOverlay(e);
  if (onVoice()) return voiceSplit(e);
  splitVideoAt(e);
}

// The Cut tool: while it is on, a click on a track cuts that track right where you click, as many times as you like.
// Click the video row to cut the video, the voice row to cut the voice, the overlay row to cut the overlay.
let razor = false;
function setRazor(on) {
  if (on && !canSeek()) return;
  razor = on;
  $('tbody').classList.toggle('razor', on);
  $('rline').hidden = true;
  updateUI();
  if (on) status('Cut tool on: click the video, voice or overlay row where you want to cut. Click Cut again or press Esc to stop.');
}
const toggleRazor = () => setRazor(!razor);
$('cut').onclick = toggleRazor;
const razorLine = (e) => { // a guide that follows the mouse along the row it would cut
  const r = $('tbody').getBoundingClientRect(), y = e.clientY - r.top, line = $('rline');
  let track = y < 30 ? 'overlay' : y < 60 ? 'video' : 'voice';
  if (track === 'voice' && !voiceFree) track = 'video';
  const top = track === 'overlay' ? 0 : track === 'video' ? 30 : 60, h = track === 'voice' ? r.height - 60 - 14 : 30;
  Object.assign(line.style, { left: e.clientX - r.left + 'px', top: top + 'px', height: h + 'px' });
  line.hidden = false;
};
timeline.addEventListener('pointermove', (e) => { if (razor) razorLine(e); });
timeline.addEventListener('pointerleave', () => { $('rline').hidden = true; });
timeline.addEventListener('pointerdown', (e) => {
  if (!razor || e.button) return;
  e.stopPropagation(); e.preventDefault(); // the click cuts; it does not drag, select or move the playhead
  if (!canSeek()) return;
  let track = trackAtY(e.clientY);
  if (track === 'voice' && !voiceFree) track = 'video';
  const t = eAtX(e.clientX);
  if (track === 'overlay') splitOverlay(t); else if (track === 'voice') voiceSplit(t); else splitVideoAt(t);
}, true);
function deleteClip() {
  if (!canSeek()) return;
  if (voiceFree && selTrack === 'overlay') return deleteOverlay();
  if (onVoice()) return voiceDelete();
  const k = curIdx();
  if (k < 0) return;
  const c = clips[k], at = toEdit(c.a);
  checkpoint();
  if (voiceFree) { // the space stays; deleting a gap itself closes it
    if (isBlankClip(c)) { clips.splice(k, 1); layout(realItems()); }
    else layout(realItems().filter((it) => !(it.c.a === c.a && it.c.b === c.b)));
  } else clips.splice(k, 1);
  commitEdit();
  if (!clips.length) { seekTo(0); return status(voiceFree ? 'The video is gone and your voice is kept. Click "+ Add video" to put a new video under it, or Undo (Ctrl+Z) to bring the old one back.' : 'Everything was deleted, voice included. Press Undo (Ctrl+Z) to bring it back.'); }
  seekTo(toSrc(Math.min(at, editedLen() - 0.01)));
  status(isBlankClip(c) ? 'Closed the gap.' : `Deleted the clip (${((c.b - c.a) / c.r).toFixed(1)}s).${voiceFree ? ' The space stays where it was; drag a clip into it, or click the space and press Delete to close it.' : ''}${overrunNote()}`);
}
function setClipSpeed(r) {
  if (!canSeek()) return;
  if (isBlankClip(clips[curIdx()])) return;
  if (onVoice() || (voiceFree && selTrack === 'overlay')) return status('Speed changes the video. Click a clip on the Video track first.');
  const k = curIdx();
  if (k < 0) return;
  checkpoint(); clips[k].r = r; commitEdit();
  status(r === 1 ? 'Clip back to normal speed.' : `Clip now plays at ${r}×. ${voiceFree ? 'Your voice is not changed.' : 'The voice is sped up to match when you export.'}${overrunNote()}`);
}
$('split').onclick = splitHere;
$('delClip').onclick = deleteClip;
$('clipSpeed').onchange = (e) => { setClipSpeed(+e.target.value); e.target.blur(); };

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
  if (e.button) return;
  const blk = e.target.closest('.blk');
  if (blk) { setTrack('video'); showEdit(); if (asel) { asel = null; renderPieces(); } } // Delete now acts on the video clip
  if (!blk || !canSeek()) return;
  e.stopPropagation();
  strip.setPointerCapture(e.pointerId);
  const i = +blk.dataset.i, c = clips[i], W = strip.getBoundingClientRect().width;
  const si = srcOf((c.a + c.b) / 2), joined = (o, j, side) => j !== i && srcOf((o.a + o.b) / 2) === si && Math.abs(side === 'r' ? o.a - c.b : o.b - c.a) < 1e-3;
  // a clip that was split from this one shares the edge, so it moves along with it (found now: it moves while dragging)
  sdrag = { i, c0: { ...c }, edge: edgeAt(blk, e.clientX), x0: e.clientX, perPx: vr().len / W, moved: false, saved: false, to: i,
    pr: clips.findIndex((o, j) => joined(o, j, 'r')), pl: clips.findIndex((o, j) => joined(o, j, 'l')) };
  if (voiceFree) { // clips stay where they are put: remember where every clip starts, and move or trim only this one
    const items0 = realItems(), me = items0.findIndex((it) => it.c.a === c.a && it.c.b === c.b);
    Object.assign(sdrag, { pr: -1, pl: -1, items0, me, at0: segs()[i].e0, len: (c.b - c.a) / c.r, s0: vr().s });
    if (me < 0) sdrag.edge = null; // an empty space is not dragged
  }
};
strip.onpointermove = (e) => {
  if (!sdrag) { const blk = e.target.closest?.('.blk'); strip.style.cursor = blk && edgeAt(blk, e.clientX) ? 'col-resize' : ''; return; }
  const dx = e.clientX - sdrag.x0;
  if (!sdrag.moved && Math.abs(dx) < 4) return;
  if (sdrag.items0 && sdrag.me < 0) return;
  sdrag.moved = true;
  if (!sdrag.saved) { checkpoint(); sdrag.saved = true; }
  if (sdrag.edge) (sdrag.items0 ? trimFree : trimEdge)(sdrag, dx * sdrag.perPx * sdrag.c0.r);
  else if (sdrag.items0) { edgeTrack(e); if (!edge) edgeStart(moveFree); moveFree(e); }
  else moveHint(e);
};
strip.onpointerup = strip.onpointercancel = (e) => {
  const d = sdrag; sdrag = null; edgeStop();
  if (!d) return;
  strip.querySelector('.drop')?.remove();
  if (!d.moved) { // a plain click puts the playhead there
    const r = strip.getBoundingClientRect();
    return seekTo(toSrc(eAtX(e.clientX, strip)));
  }
  if (d.edge) { commitEdit(); return; }
  if (d.items0) {
    if (d.newAt === undefined || Math.abs(d.newAt - d.at0) < 1e-3) return renderCuts();
    layout(d.items0.map((it, j) => ({ c: { ...it.c }, at: j === d.me ? d.newAt : it.at })));
    commitEdit(); seekTo(toSrc(d.newAt + 0.01));
    return status(`Moved the clip to ${fmt(d.newAt)}. The space it left stays empty.`);
  }
  if (d.to !== d.i) { const [c] = clips.splice(d.i, 1); clips.splice(d.to, 0, c); commitEdit(); status(`Moved the clip to position ${d.to + 1}.`); }
  else renderCuts();
};
strip.ondblclick = (e) => {
  const blk = document.elementsFromPoint(e.clientX, e.clientY).find((el) => el.classList?.contains('blk')); // the strip holds the pointer, so look at what is under it
  if (!blk) return;
  const s = segs()[+blk.dataset.i], len = Math.max(0.5, ((s.b - s.a) / s.r) * 1.2);
  setView(Math.max(0, s.e0 - len * 0.083), len);
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
// the same with clips that stay where they are put: trimming leaves space instead of pulling the next clip along
function trimFree(d, dg) {
  const it0 = d.items0[d.me], c0 = it0.c, s = sources[srcOf((c0.a + c0.b) / 2)];
  const others = d.items0.filter((_, j) => j !== d.me).map((o) => o.c);
  const items = d.items0.map((it) => ({ c: { ...it.c }, at: it.at })), it = items[d.me];
  if (d.edge === 'r') {
    const wall = Math.min(s.off + s.dur, ...others.filter((o) => o.a >= c0.b - 1e-6 && o.a < s.off + s.dur).map((o) => o.a));
    it.c.b = Math.max(c0.a + 0.1, Math.min(wall, c0.b + dg));
  } else {
    const wall = Math.max(s.off, ...others.filter((o) => o.b <= c0.a + 1e-6 && o.b > s.off).map((o) => o.b));
    it.c.a = Math.min(c0.b - 0.1, Math.max(wall, c0.a + dg));
    it.at = it0.at + (it.c.a - c0.a) / c0.r;
  }
  layout(items); renderCuts(); seekTo(d.edge === 'r' ? it.c.b - 0.01 : it.c.a);
  touched();
}
// dragging a clip anywhere: its edges cling to other clips, the start of the timeline and the edges of voice pieces
function moveFree(e) {
  const d = sdrag, tol = 10 * d.perPx;
  let at = Math.max(0, d.at0 + (e.clientX - d.x0) * d.perPx + (vr().s - d.s0)), snapAt = null;
  const marks = [0, ...d.items0.filter((_, j) => j !== d.me).flatMap((it) => [it.at, it.at + (it.c.b - it.c.a) / it.c.r]), ...pieces().flatMap((p) => [p.s, p.e])];
  let best = null;
  for (const edge of [at, at + d.len]) for (const q of marks) {
    const gap = Math.abs(q - edge);
    if (gap < tol && (!best || gap < best.gap)) best = { gap, adj: q - edge, q };
  }
  if (best) { at = Math.max(0, at + best.adj); snapAt = best.q; }
  d.newAt = at;
  const blk = strip.querySelector(`[data-i="${d.i}"]`);
  blk.classList.add('dragging'); blk.style.left = pctE(at) + '%';
  strip.querySelector('.drop')?.remove();
  if (snapAt !== null) { const line = Object.assign(document.createElement('div'), { className: 'drop' }); line.style.left = pctE(snapAt) + '%'; strip.append(line); }
}
// ---------- the Edit tab: controls for whatever is selected ----------
const showEdit = () => { if (!state.playing && !state.recording) setPanel('edit'); }; // not while you are reading the prompter
const inspOv = () => (selIdx() >= 0 ? ovl[selIdx()] : activeOv());
function syncInspector() {
  const onOv = voiceFree && selTrack === 'overlay', which = onOv ? 'overlay' : onVoice() ? 'voice' : 'video';
  document.querySelectorAll('[data-insp]').forEach((el) => { el.hidden = el.dataset.insp !== which; });
  if (document.querySelector('.panel[data-panel=edit]').hidden) return;
  const set = (id, v) => { const el = $(id), val = String(Math.round(v)); if (el !== document.activeElement && el.value !== val) el.value = val; };
  if (which === 'overlay') {
    const c = inspOv();
    for (const id of ['iOvW', 'iOvX', 'iOvY', 'iOvCl', 'iOvCt', 'iOvCr', 'iOvCb', 'iOvFill', 'iOvReset']) $(id).disabled = !c;
    $('inspOvInfo').textContent = c ? `${osources[c.o]?.name || 'Overlay'} · starts ${fmt(c.at)} · ${olen(c).toFixed(1)}s` : 'Click an overlay clip on the timeline.';
    if (c) { ovBoxOf(c); set('iOvW', c.w * 100); set('iOvX', c.x * 100); set('iOvY', c.y * 100); set('iOvCl', c.cl * 100); set('iOvCt', c.ct * 100); set('iOvCr', c.cr * 100); set('iOvCb', c.cb * 100); }
  } else if (which === 'voice') {
    const p = chosenPiece();
    $('inspVoiceInfo').textContent = !hasTake() ? 'No recording yet.' : p ? `Piece from ${fmt(p.s)} to ${fmt(p.e)} (${(p.e - p.s).toFixed(1)}s)` : 'Click a piece of the voice on the timeline.';
  } else {
    const k = curIdx(), g = k >= 0 ? segs()[k] : null;
    $('inspVidInfo').textContent = !g ? 'Click a clip on the timeline.' : sources[g.src].blank ? `Empty space · ${((g.b - g.a) / g.r).toFixed(1)}s. Delete closes it.` : `Clip ${k + 1} of ${clips.length} · ${sources[g.src].name} · ${((g.b - g.a) / g.r).toFixed(1)}s`;
  }
}
// moves one overlay setting, keeping the rest of the picture where it is (cropping reveals less of the same picture)
function ovApply(c, key, v) {
  ovBoxOf(c);
  if (key === 'w') c.w = Math.max(0.05, v);
  else if (key === 'x' || key === 'y') c[key] = v;
  else {
    const F = overlayFrame(), src = osources[c.o], vw = src?.vw || 16, vh = src?.vh || 9;
    const S = (c.w * F.w) / (1 - c.cl - c.cr), Sh = (S * vh) / vw, was = { cl: c.cl, ct: c.ct };
    const other = { cl: c.cr, cr: c.cl, ct: c.cb, cb: c.ct }[key];
    c[key] = Math.max(0, Math.min(0.95 - other, v));
    c.w = (S * (1 - c.cl - c.cr)) / F.w;
    c.x += ((c.cl - was.cl) * S) / F.w; c.y += ((c.ct - was.ct) * Sh) / F.h;
  }
}
let inspGesture = false;
for (const [id, key] of Object.entries({ iOvW: 'w', iOvX: 'x', iOvY: 'y', iOvCl: 'cl', iOvCt: 'ct', iOvCr: 'cr', iOvCb: 'cb' })) {
  $(id).addEventListener('input', () => {
    const c = inspOv(), v = +$(id).value / 100; // read before the undo step, which refreshes the sliders
    if (!c) return;
    if (!inspGesture) { checkpoint(); inspGesture = true; }
    ovApply(c, key, v);
    if (activeOv() === c) placeOverlay(c);
    touched();
  });
  $(id).addEventListener('change', () => { inspGesture = false; commitEdit(); });
}
$('iOvFill').onclick = () => { const c = inspOv(); if (c) ovTool('fill', c); };
$('iOvReset').onclick = () => { const c = inspOv(); if (c) ovTool('reset', c); };
$('iZoom').onclick = () => $('zoomAdd').click();

// ---------- right-click menu ----------
function hideCtx() { $('ctx').hidden = true; }
document.addEventListener('pointerdown', (e) => { if (!$('ctx').contains(e.target)) hideCtx(); }, true);
document.addEventListener('keydown', (e) => { if (e.key === 'Escape') hideCtx(); });
addEventListener('blur', hideCtx);
$('ctx').onclick = (e) => { const b = e.target.closest('button'); if (!b) return; const fn = $('ctx')._fns[+b.dataset.i]; hideCtx(); fn(); };
timeline.addEventListener('contextmenu', (e) => {
  e.preventDefault();
  if (!canSeek()) return;
  let track = trackAtY(e.clientY);
  if (track === 'voice' && !voiceFree) track = 'video';
  seekTo(toSrc(eAtX(e.clientX))); // the playhead goes where you clicked, so Split cuts there
  const piece = track === 'voice' ? pieceAt(eAtX(e.clientX)) : null, ob = track === 'overlay' ? e.target.closest('.blk') : null;
  if (piece) asel = { s: piece.s, e: piece.e }; else if (track === 'voice') asel = null;
  if (ob) osel = { o: ovl[+ob.dataset.i].o, a: ovl[+ob.dataset.i].a };
  setTrack(track, true); renderPieces(); renderCuts();
  const items = [['Split here', splitHere]];
  if (track === 'video') {
    const gap = isBlankClip(clips[curIdx()]);
    items.push([gap ? 'Close the gap' : 'Delete clip', deleteClip]);
    if (!gap) { items.push(null, ['Speed 0.5×', () => setClipSpeed(0.5)], ['Speed 1×', () => setClipSpeed(1)], ['Speed 2×', () => setClipSpeed(2)], null, ['Add zoom here', () => $('zoomAdd').click()]); }
  } else if (track === 'overlay') {
    items.push(['Delete overlay', deleteOverlay], null, ['Fill the picture', () => { const c = inspOv(); if (c) ovTool('fill', c); }], ['Reset size and position', () => { const c = inspOv(); if (c) ovTool('reset', c); }]);
  } else items.push(['Delete voice', voiceDelete]);
  const fns = [], html = items.map((it) => (it ? `<button data-i="${fns.push(it[1]) - 1}">${it[0]}</button>` : '<hr>')).join('');
  const m = $('ctx'); m._fns = fns; m.innerHTML = html; m.hidden = false;
  m.style.left = Math.min(e.clientX, innerWidth - m.offsetWidth - 8) + 'px'; m.style.top = Math.min(e.clientY, innerHeight - m.offsetHeight - 8) + 'px';
});

// ---------- the overlay track ----------
// A second video track above the main one. Its clips sit at times on the same timeline, play on top of the main video as a small window
// (size and corner are in Picture & text), and can be cut, split, moved and trimmed like any other clip. Their own sound is not used.
const olen = (c) => (c.b - c.a) / c.r;
const oEnd = () => ovl.reduce((m, c) => Math.max(m, c.at + olen(c)), 0);
const selIdx = () => (osel ? ovl.findIndex((c) => c.o === osel.o && Math.abs(c.a - osel.a) < 1e-3) : -1);
const saveOSources = () => kv.set('osources', osources.map(({ id, name, dur }) => ({ id, name, dur })));
function olayout(items) { // clips that overlap are pushed along rather than stacked
  let end = 0;
  ovl = items.slice().sort((x, y) => x.at - y.at).map((c) => { const at = Math.max(c.at, end); end = at + olen(c); return { ...c, at }; });
  layout(realItems()); // the main track gets empty space after it if an overlay runs past its end
  touched();
}
const asItems = () => ovl.map((c) => ({ ...c }));
async function addOverlay(file) {
  if (!file) return;
  if (!sources.length) return status('Add the main video first, then an overlay on top of it.');
  if (state.recording && !state.recPaused) return status('Stop recording first.');
  stopPlay();
  let switched = false;
  if (!voiceFree) { $('linkVoice').checked = false; $('linkVoice').dispatchEvent(new Event('change')); switched = voiceFree; } // overlays need the voice on its own track
  if (!voiceFree) return status('Overlays need the voice and video unlinked: untick "Link voice to video".');
  try {
    const { dur, url, vw, vh } = await probe(file), s = { id: crypto.randomUUID(), name: file.name, file, url, dur, vw, vh };
    checkpoint();
    osources.push(s);
    olayout([...asItems(), { o: osources.length - 1, a: 0, b: dur, r: 1, at: toEdit(gNow()) }]);
    osel = { o: osources.length - 1, a: 0 }; setTrack('overlay', true);
    kv.set('osrc-' + s.id, { file }); saveOSources();
    commitEdit(); updateUI();
    status(`${switched ? 'Unlinked the voice from the video, which overlays need. ' : ''}Added ${file.name} on the overlay track at the playhead. Drag it, trim its edges, split it (B) or delete it. Size and corner are in Picture & text.`);
  } catch { status('This browser cannot play that video. Try an MP4 (H.264) or WebM file.'); }
}
$('ovFile').onchange = (e) => { addOverlay(e.target.files[0]); e.target.value = ''; };
function splitOverlay(e) {
  const k = ovl.findIndex((c) => e > c.at + 0.15 && e < c.at + olen(c) - 0.15);
  if (k < 0) return status('Click inside an overlay clip, away from its ends, to cut it.');
  const c = ovl[k], m = c.a + (e - c.at) * c.r, items = asItems();
  checkpoint(); items.splice(k, 1, { ...c, b: m }, { ...c, a: m, at: e });
  olayout(items); osel = { o: c.o, a: m }; commitEdit();
  status(`Split the overlay at ${fmt(e)}. Click a part and press Delete, or drag it.`);
}
function deleteOverlay() {
  const e = toEdit(gNow()), k = selIdx() >= 0 ? selIdx() : ovl.findIndex((c) => e >= c.at && e < c.at + olen(c));
  if (k < 0) return status('Click an overlay clip first.');
  checkpoint(); olayout(asItems().filter((_, j) => j !== k)); osel = null; commitEdit();
  status('Deleted the overlay clip. The main video is untouched.');
}
let odrag = null;
$('ostrip').onpointerdown = (e) => {
  if (e.button) return;
  setTrack('overlay');
  const blk = e.target.closest('.blk'), strip = $('ostrip');
  if (!blk || !canSeek()) { updateUI(); return; } // empty space: the timeline just moves the playhead
  e.stopPropagation();
  strip.setPointerCapture(e.pointerId);
  const i = +blk.dataset.i, c = ovl[i];
  osel = { o: c.o, a: c.a }; showEdit();
  strip.querySelectorAll('.blk').forEach((b) => b.classList.toggle('sel', b === blk));
  odrag = { i, items0: asItems(), edge: edgeAt(blk, e.clientX), x0: e.clientX, perPx: vr().len / strip.getBoundingClientRect().width, moved: false, saved: false, s0: vr().s };
  updateUI();
};
$('ostrip').onpointermove = (e) => {
  const strip = $('ostrip');
  if (!odrag) { const blk = e.target.closest?.('.blk'); strip.style.cursor = blk && edgeAt(blk, e.clientX) ? 'col-resize' : ''; return; }
  edgeTrack(e);
  if (!odrag.moved && Math.abs(e.clientX - odrag.x0) < 4) return;
  if (!odrag.edge && !edge) edgeStart(omove);
  omove(e);
};
function omove(e) {
  const d = odrag, strip = $('ostrip');
  if (!d) return;
  const dx = (e.clientX - d.x0) * d.perPx + (d.edge ? 0 : vr().s - d.s0), c0 = d.items0[d.i];
  d.moved = true;
  if (!d.saved) { checkpoint(); d.saved = true; }
  const items = d.items0.map((c) => ({ ...c })), c = items[d.i];
  if (d.edge === 'r') c.b = Math.max(c0.a + 0.1, Math.min(osources[c0.o].dur, c0.b + dx * c0.r));
  else if (d.edge === 'l') { c.a = Math.max(0, Math.min(c0.b - 0.1, c0.a + dx * c0.r)); c.at = c0.at + (c.a - c0.a) / c0.r; osel = { o: c.o, a: c.a }; }
  else { // moving: edges cling to the main clips, voice pieces, other overlay clips and the start
    let at = Math.max(0, c0.at + dx), snapAt = null, best = null;
    const len = olen(c0), tol = 10 * d.perPx;
    const marks = [0, ...segs().flatMap((g) => [g.e0, g.e0 + (g.b - g.a) / g.r]), ...pieces().flatMap((q) => [q.s, q.e]), ...d.items0.filter((_, j) => j !== d.i).flatMap((o) => [o.at, o.at + olen(o)])];
    for (const edge of [at, at + len]) for (const q of marks) { const gap = Math.abs(q - edge); if (gap < tol && (!best || gap < best.gap)) best = { gap, adj: q - edge, q }; }
    if (best) { at = Math.max(0, at + best.adj); snapAt = best.q; }
    c.at = at; d.newAt = at;
    const blk = strip.querySelector(`[data-i="${d.i}"]`);
    blk.classList.add('dragging'); blk.style.left = pctE(at) + '%';
    strip.querySelector('.drop')?.remove();
    if (snapAt !== null) { const line = Object.assign(document.createElement('div'), { className: 'drop' }); line.style.left = pctE(snapAt) + '%'; strip.append(line); }
    d.items = items;
    return;
  }
  d.items = items; olayout(items); renderCuts(); touched();
}
$('ostrip').onpointerup = $('ostrip').onpointercancel = (e) => {
  const d = odrag, strip = $('ostrip'); odrag = null; edgeStop();
  if (!d) return;
  strip.querySelector('.drop')?.remove();
  if (!d.moved) { seekTo(toSrc(eAtX(e.clientX, strip))); return; }
  if (!d.edge && d.items) { olayout(d.items); osel = { o: d.items[d.i].o, a: d.items[d.i].a }; status(`Moved the overlay to ${fmt(d.items[d.i].at)}.`); }
  commitEdit();
};

// the overlay window in the player: a third video that follows the timeline
const ov = $('ovideo');
function overlayFrame() { // the part of the player the picture fills, in pixels
  const W = wrap.clientWidth, H = wrap.clientHeight, r = pictureRect();
  return ratioOf() === null && r ? { x: r.ox, y: r.oy, w: r.pw, h: r.ph } : { x: 0, y: 0, w: W, h: H };
}
// Where an overlay clip sits: x, y and w are fractions of the picture (w is its width), cl/ct/cr/cb are how much is cropped off each side.
// New clips start from the size and corner chosen in Picture & text.
function ovBoxOf(c) {
  if (c.w == null) {
    const F = overlayFrame(), fa = F.w && F.h ? F.w / F.h : 16 / 9, src = osources[c.o], aspect = (src?.vw || 16) / (src?.vh || 9);
    const size = +$('ovSize').value / 100, pos = $('ovPos').value, m = 0.03;
    let w = size, h = (w / aspect) * fa, x, y; // h is a fraction of the picture's height
    if (size >= 0.99) { const k = Math.min(1 / w, 1 / h); w *= k; h *= k; x = (1 - w) / 2; y = (1 - h) / 2; }
    else {
      x = pos.includes('l') ? m : pos === 'c' ? (1 - w) / 2 : 1 - w - m;
      y = pos.includes('t') ? m * fa : pos === 'c' ? (1 - h) / 2 : 1 - h - m * fa;
    }
    Object.assign(c, { x, y, w, cl: 0, ct: 0, cr: 0, cb: 0 });
  }
  return c;
}
const activeOv = () => { const e = toEdit(gNow()); return voiceFree ? ovl.find((x) => e >= x.at && e < x.at + olen(x)) : null; };
let ovCrop = false;
function placeOverlay(c) {
  const F = overlayFrame(), b = ovBoxOf(c), vw = ov.videoWidth || osources[c.o]?.vw || 16, vh = ov.videoHeight || osources[c.o]?.vh || 9;
  const w = b.w * F.w, h = (w * (vh * (1 - b.ct - b.cb))) / (vw * (1 - b.cl - b.cr));
  Object.assign($('ovbox').style, { left: F.x + b.x * F.w + 'px', top: F.y + b.y * F.h + 'px', width: w + 'px', height: h + 'px' });
  const full = w / (1 - b.cl - b.cr), fullH = (full * vh) / vw; // the whole picture, of which the box shows a part
  Object.assign(ov.style, { width: full + 'px', height: fullH + 'px', left: -b.cl * full + 'px', top: -b.ct * fullH + 'px' });
  $('ovbox').classList.toggle('crop', ovCrop);
  $('ovbox').classList.toggle('tools-in', F.y + b.y * F.h < 32); // near the top of the picture the buttons go inside the overlay so they are not cut off
}
function syncOverlay() {
  const e = toEdit(gNow()), c = activeOv(), box = $('ovbox');
  if (!c) { if (!box.hidden) { ov.pause(); box.hidden = true; } return; }
  const src = osources[c.o]?.url;
  if (!src) return;
  if (ov.dataset.o !== String(c.o)) { ov.dataset.o = String(c.o); ov.src = src; }
  box.hidden = false; placeOverlay(c);
  const playing = state.playing || (state.recording && !state.recPaused), want = c.a + (e - c.at) * c.r;
  if (Math.abs(ov.currentTime - want) > (playing ? 0.3 : 0.03)) ov.currentTime = want;
  ov.playbackRate = Math.min(16, (+$('rate').value || 1) * c.r);
  if (playing && ov.paused) ov.play().catch(() => {}); else if (!playing && !ov.paused) ov.pause();
}
// grab the overlay in the player: drag it to move, drag a corner to resize, switch on Crop and drag an edge to crop
let obox = null;
$('ovbox').onpointerdown = (e) => {
  const c = activeOv();
  if (!c || !canSeek() || e.button) return;
  e.stopPropagation(); e.preventDefault();
  const tool = e.target.closest('[data-t]')?.dataset.t;
  if (tool) return ovTool(tool, c);
  const F = overlayFrame(), b = { ...ovBoxOf(c) }, handle = e.target.closest('[data-h]')?.dataset.h || 'move';
  obox = { c, handle, x0: e.clientX, y0: e.clientY, b, F, moved: false };
  $('ovbox').setPointerCapture(e.pointerId);
  setTrack('overlay'); osel = { o: c.o, a: c.a }; showEdit(); renderCuts();
};
$('ovbox').onpointermove = (e) => {
  const d = obox;
  if (!d) return;
  const dx = e.clientX - d.x0, dy = e.clientY - d.y0;
  if (!d.moved && Math.hypot(dx, dy) < 3) return;
  if (!d.moved) { checkpoint(); d.moved = true; }
  const { c, b, F, handle } = d, src = osources[c.o], vw = src?.vw || 16, vh = src?.vh || 9;
  const cw = vw * (1 - b.cl - b.cr), ch = vh * (1 - b.ct - b.cb), boxH = (b.w * F.w * ch) / cw / F.h; // box height as a fraction of the picture
  if (handle === 'move') { c.x = Math.max(-b.w + 0.1, Math.min(0.9, b.x + dx / F.w)); c.y = Math.max(-boxH + 0.1, Math.min(0.9, b.y + dy / F.h)); }
  else if (handle.length === 2) { // a corner: scale around the opposite corner
    const k = Math.max(0.05 / b.w, 1 + ((handle.includes('r') ? dx : -dx) / (b.w * F.w)));
    c.w = Math.min(2, b.w * k);
    if (handle.includes('l')) c.x = b.x + b.w - c.w;
    if (handle.includes('t')) c.y = b.y + boxH - boxH * (c.w / b.w);
  } else { // an edge, in crop mode: the picture keeps its size and more or less of it shows
    const S = (b.w * F.w) / (1 - b.cl - b.cr), Sh = (S * vh) / vw;
    if (handle === 'l') { c.cl = Math.max(0, Math.min(1 - b.cr - 0.05, b.cl + dx / S)); c.x = b.x + ((c.cl - b.cl) * S) / F.w; }
    if (handle === 'r') c.cr = Math.max(0, Math.min(1 - b.cl - 0.05, b.cr - dx / S));
    if (handle === 't') { c.ct = Math.max(0, Math.min(1 - b.cb - 0.05, b.ct + dy / Sh)); c.y = b.y + ((c.ct - b.ct) * Sh) / F.h; }
    if (handle === 'b') c.cb = Math.max(0, Math.min(1 - b.ct - 0.05, b.cb - dy / Sh));
    c.w = (S * (1 - c.cl - c.cr)) / F.w;
  }
  placeOverlay(c); touched();
};
$('ovbox').onpointerup = $('ovbox').onpointercancel = () => { const d = obox; obox = null; if (d?.moved) commitEdit(); };
function ovTool(t, c) {
  if (t === 'crop') { ovCrop = !ovCrop; placeOverlay(c); return status(ovCrop ? 'Crop on: drag an edge of the overlay to crop it. Press Crop again to go back to resizing.' : 'Resize: drag a corner to make the overlay bigger or smaller.'); }
  checkpoint();
  if (t === 'reset') { c.w = null; ovBoxOf(c); status('Overlay back to its starting size and corner.'); }
  if (t === 'fill') { // as large as fits in the picture, whatever is left after cropping
    const F = overlayFrame(), src = osources[c.o], cw = (src?.vw || 16) * (1 - c.cl - c.cr), ch = (src?.vh || 9) * (1 - c.ct - c.cb), k = Math.min(F.w / cw, F.h / ch);
    c.w = (cw * k) / F.w; c.x = (1 - c.w) / 2; c.y = (1 - (ch * k) / F.h) / 2; status('Overlay fills the picture.');
  }
  placeOverlay(c); commitEdit();
}
// the size and corner in Picture & text are what new overlays start with; changing them resets the overlay under the playhead too
for (const id of ['ovSize', 'ovPos']) $(id).addEventListener('change', () => { const c = activeOv(); if (c) { checkpoint(); c.w = null; ovBoxOf(c); commitEdit(); } });

// dragging a clip: shows where it would land
function moveHint(e) {
  const x = eAtX(e.clientX, strip);
  const list = segs();
  let to = 0;
  list.forEach((s, j) => { if (j !== sdrag.i && s.e0 + (s.b - s.a) / s.r / 2 < x) to++; });
  sdrag.to = to;
  strip.querySelectorAll('.blk').forEach((b) => b.classList.toggle('dragging', +b.dataset.i === sdrag.i));
  strip.querySelector('.drop')?.remove();
  const rest = list.filter((_, j) => j !== sdrag.i);
  const at = to === 0 ? 0 : (rest[to - 1].e0 + (rest[to - 1].b - rest[to - 1].a) / rest[to - 1].r);
  const line = Object.assign(document.createElement('div'), { className: 'drop' });
  line.style.left = pctE(at) + '%';
  strip.append(line);
}

// ---------- zoom & pan ----------
// Where the picture sits inside the player (it can be letterboxed, or cropped to a vertical or square shape).
function pictureRect() {
  const W = video.clientWidth, H = video.clientHeight, vw = video.videoWidth, vh = video.videoHeight;
  if (!vw || !W) return null;
  const cover = coverMode(), k = cover ? Math.max(W / vw, H / vh) : Math.min(W / vw, H / vh);
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
  const key = [editVer, voiceFree, $('fade').value, $('mvol').value, $('duck').checked, music?.id, intro?.sec, outro?.sec].join('|');
  const hit = finalCache[cards];
  if (hit && hit.key === key && hit.base === base) return hit.audio;
  const rate = base.rate, list = segs(), joint = Math.round(rate * 0.01);
  const parts = voiceFree ? [] : list.map((g) => {
    const from = Math.round(g.a * rate), len = Math.round((g.b - g.a) * rate), raw = new Float32Array(len);
    if (from < base.samples.length) raw.set(base.samples.subarray(from, from + len));
    const out = stretch(raw, g.r);
    if (list.length > 1) for (let i = 0; i < Math.min(joint, out.length >> 1); i++) { const k = i / joint; out[i] *= k; out[out.length - 1 - i] *= k; } // no click where a cut joins
    return out;
  });
  const L = Math.round(editedLen() * rate);
  let v = voiceFree ? base.samples.slice(0, L) : concat(parts); // video only: the voice is already laid out on the finished timeline
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
const fxIds = ['denoise', 'norm', 'eq', 'deess', 'fade', 'mvol', 'duck', 'shape', 'shapeW', 'shapeH', 'fit', 'crop', 'caps', 'introText', 'introSec', 'outroText', 'outroSec', 'ovSize', 'ovPos'];
// The shape of the project: the video's own, or a chosen aspect ratio that the picture fills (edges cropped) or sits inside (bars).
function ratioOf() {
  const v = $('shape').value;
  if (v === 'original') return null;
  const [w, h] = v === 'custom' ? [+$('shapeW').value, +$('shapeH').value] : v.split(':').map(Number);
  return w > 0 && h > 0 ? w / h : null;
}
const coverMode = () => ratioOf() !== null && $('fit').value !== 'fit';
function applyShape() {
  const ar = ratioOf(), first = sources.find((x) => !x.blank), own = first?.vw && first?.vh ? first.vw / first.vh : video.videoWidth ? video.videoWidth / video.videoHeight : 16 / 9;
  wrap.style.setProperty('--ar', String(ar ?? own));
  wrap.classList.toggle('cover', coverMode());
  wrap.style.setProperty('--crop', $('crop').value + '%');
  $('customRow').hidden = $('shape').value !== 'custom';
  $('fitRow').hidden = ar === null;
  $('cropRow').hidden = !coverMode();
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
for (const id of ['shapeW', 'shapeH']) $(id).addEventListener('input', applyShape);
try {
  const f = JSON.parse(localStorage.getItem('fx') || 'null');
  if (f?.shape === 'vertical') f.shape = '9:16'; else if (f?.shape === 'square') f.shape = '1:1'; // saved before the ratio list existed
  if (f) for (const k of fxIds) if (k in f) { if ($(k).type === 'checkbox') $(k).checked = f[k]; else $(k).value = f[k]; }
} catch {}

// captions: the script's words spread over each section's time span
let capCache = null;
function captionList() {
  const key = sections.map((x) => x.start.toFixed(2)).join() + '|' + scriptEl.value.length + '|' + realTotal();
  if (capCache?.key !== key) capCache = { key, list: buildCaptions(sections, realTotal() || 0) };
  return capCache.list;
}
$('srt').onclick = () => {
  const lead = titleCard('intro')?.sec || 0;
  const lines = captionList().map((c) => ({ t0: toEdit(c.t0) + lead, t1: toEdit(c.t1) + lead, text: c.text })).filter((l) => l.t1 - l.t0 > 0.05);
  if (!lines.length) return status('Add a script first, there is nothing to caption.');
  Object.assign(document.createElement('a'), { href: URL.createObjectURL(new Blob([toSrt(lines)], { type: 'text/plain' })), download: 'captions.srt' }).click();
  status('Captions downloaded. Their timing follows your section start times, so use "Fit to my voice" for the best match.');
};

const RULER_STEPS = [0.05, 0.1, 0.2, 0.5, 1, 2, 5, 10, 15, 30, 60, 120, 300, 600];
function tlabel(t, step) { const m = Math.floor(t / 60), sec = t - m * 60; return `${m}:${sec.toFixed(step < 0.1 ? 2 : step < 1 ? 1 : 0).padStart(step < 0.1 ? 5 : step < 1 ? 4 : 2, '0')}`; }
function drawWave() {
  if (syncTail()) return renderCuts();
  const dpr = devicePixelRatio || 1;
  canvas.width = canvas.clientWidth * dpr;
  canvas.height = canvas.clientHeight * dpr;
  const g = canvas.getContext('2d'), W = canvas.width, H = canvas.height;
  g.clearRect(0, 0, W, H);
  const v = vr();
  if (!extent() || !W) { renderPieces(); return; }
  const perPx = v.len / W; // seconds of edited video per pixel
  if (ctx || peaks.length) {
    const rate = state.take?.rate || ctx?.sampleRate || 48000;
    g.fillStyle = voiceFree ? '#00000000' : '#ffb88e26';
    const vsec = (peaks.length * B) / rate, end = (((voiceFree ? vsec : toEdit(Math.min(total(), vsec))) - v.s) / v.len) * W;
    g.fillRect(0, 0, Math.max(0, Math.min(W, end)), H);
    g.fillStyle = '#f08a4b';
    for (let x = 0; x < W; x++) {
      const e = v.s + x * perPx, s0 = voiceFree ? e : toSrc(e), r = voiceFree ? 1 : speedAt(s0), b0 = Math.floor((s0 * rate) / B), b1 = Math.max(b0 + 1, Math.floor(((s0 + perPx * r) * rate) / B));
      if (b0 >= peaks.length) break;
      let mx = 0;
      for (let b = b0; b < b1 && b < peaks.length; b++) mx = Math.max(mx, peaks[b]);
      if (voiceFree && mx === 0) continue; // a gap is left empty
      const h = Math.max(2 * dpr, Math.min(1, mx * 1.6) * H * 0.9);
      g.fillRect(x, (H - h) / 2, 1, h);
    }
  }
  // time ruler along the bottom: marks every so often, with the interval chosen to suit the zoom
  const step = RULER_STEPS.find((q) => (q / perPx) / dpr >= 80) || 600;
  g.fillStyle = '#737373'; g.strokeStyle = '#00000026'; g.font = `${10 * dpr}px Inter, sans-serif`; g.textBaseline = 'bottom';
  for (let t = Math.ceil(v.s / step) * step; t < v.s + v.len; t += step) {
    const x = Math.round((t - v.s) / perPx);
    g.beginPath(); g.moveTo(x + 0.5, H - 14 * dpr); g.lineTo(x + 0.5, H); g.stroke();
    g.fillText(tlabel(t, step), x + 3 * dpr, H - 2 * dpr);
  }
  renderPieces();
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

const sectionEnd = (i) => (i + 1 < sections.length ? sections[i + 1].start : realTotal() || 0);
function sectionAt(t) { let i = 0; while (i + 1 < sections.length && t >= sections[i + 1].start - 1e-6) i++; return i; }

function spreadEvenly() {
  const words = sections.reduce((n, x) => n + x.n, 0) || 1;
  let seen = 0;
  for (const x of sections) { x.start = (realTotal() || 0) * (seen / words); seen += x.n; }
}
function saveMarks() { try { localStorage.setItem('marks', JSON.stringify({ n: sections.length, dur: realTotal(), starts: sections.map((x) => x.start) })); } catch {} }
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
const wordsPerSec = () => (realTotal() ? spans.length / realTotal() : 2.5);
function posAt(t) {
  if (!sections.length) return 0;
  const i = sectionAt(t), x = sections[i], len = sectionEnd(i) - x.start;
  const frac = len > 0 ? Math.max(0, Math.min(1, ((t - x.start) / len) * speed)) : 0;
  return x.w0 + frac * (x.n - 1);
}
function updateWpm() {
  $('wpm').textContent = spans.length && realTotal() ? `About ${Math.round(wordsPerSec() * speed * 60)} words per minute` : 'Add a script and a video to see the pace.';
}

function renderMarks() {
  const d = editedLen();
  $('marks').replaceChildren(...(d ? sections.slice(1).map((x, i) => Object.assign(document.createElement('i'), { style: `left:${pctE(toEdit(x.start))}%`, title: `Section ${i + 2}` })) : []));
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
  const lo = sections[i - 1].start + 0.1, hi = (i + 1 < sections.length ? sections[i + 1].start : realTotal()) - 0.1;
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
  picked.forEach((g, i) => (sections[i + 1].start = Math.max(sections[i].start + 0.1, vInv(g.end * sec - 0.15))));
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
    // The microphone must not miss anything while the next video loads. Where the voice carries straight on (one clip into the
    // next) the capture just keeps running; where the edit skips ahead, the new capture starts at once, before the video is ready.
    if (recLive && Math.abs((capStart + chunkLen) / ctx.sampleRate - vt(g)) > 0.1) { commitCapture(); beginCapture(true, vt(g)); }
    await gSeek(g);
    if (recLive) { // the voice kept running during the switch, so move the video on to where the voice has got to
      const want = vInv((capStart + chunkLen) / ctx.sampleRate);
      if (want - gNow() > 0.04 && clipIndexAt(want) === clipIndexAt(gNow())) await gSeek(want);
    }
    playK = clipIndexAt(gNow());
    if (state.playing) startVoice();
    if ((state.playing || recLive) && vPaused()) await vPlay().catch(() => {});
  } finally { jumping = false; }
}
for (const el of [video, spare]) el.onended = () => { if (el === video && (state.playing || (state.recording && !state.recPaused))) tick(); };

function tick() {
  const t = gNow();
  if (total()) {
    const e = toEdit(t), v = vr(), x = pctE(e);
    $('playhead').style.display = x < -0.3 || x > 100.3 ? 'none' : '';
    $('playhead').style.left = x + '%';
    // while playing or recording a zoomed timeline follows the playhead
    if ((state.playing || state.recording) && view.len && !scrubbing && (e > v.s + v.len * 0.97 || e < v.s)) setView(Math.max(0, e - v.len * 0.1), v.len);
  }
  $('cur').textContent = fmt(toEdit(t));
  if (!state.recording) updateRecLabel();
  // a section retake stops by itself at the end of its section
  if (state.recording && !state.recPaused && state.range && t >= state.range.end - 0.02) stopRecording();
  if (state.recording && !state.recPaused && !state.range && recLimit !== null && vt(t) >= recLimit - 0.02) { stopRecording(); status('Stopped: the next piece of voice starts here, and recording never goes over it.'); }
  if (state.playing) { // faster / slower parts of the video
    const want = Math.min(16, (+$('rate').value || 1) * speedAt(t));
    if (Math.abs(video.playbackRate - want) > 1e-3) video.playbackRate = want;
  }
  updateClip(); syncOverlay(); if (!document.querySelector('.panel[data-panel=edit]').hidden) syncInspector();
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
      const ahead = clips[k + 1]; // getting the next video ready in the other player before it is needed
      if (ahead && srcOf(ahead.a) !== loaded && t > clips[k].b - 3) prepare(srcOf(ahead.a), ahead.a);
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
const rangeEndIdx = () => (state.range ? Math.round(vt(state.range.end) * ctx.sampleRate) : null);

function beginCapture(quiet = false, at = null) {
  if (!quiet) checkpoint();
  video.playbackRate = 1; // the voice is recorded in real time, so the video must not run faster or slower
  capStart = Math.round((at ?? vt(gNow())) * ctx.sampleRate);
  const have = hasTake() ? state.take.samples : new Float32Array(0);
  base = have; // splice() copies from it, the take itself is untouched until the capture is committed
  const r = state.range;
  if (r && !('old' in r)) { // remember the audio this retake replaces, so it can be brought back
    const a = Math.round(vt(r.start) * ctx.sampleRate);
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

// Recording never goes over voice that is already there: it only starts in empty space and stops where the next piece begins.
let recLimit = null;
// the last moments of a piece count as its end, so a paused recording can carry on
function recBlocked() {
  const t = vt(gNow());
  if (hasTake() && pieces().some((p) => t >= p.s && t < p.e - 0.25)) { status('There is already voice here. Move the playhead into an empty space (or cut or delete that part of the voice first) to record.'); return true; }
  recLimit = hasTake() ? (pieces().find((p) => p.s > t)?.s ?? null) : null;
  return false;
}
async function startRecording(range = null) {
  if (!(stream?.active || (await initMic()))) return;
  await ctx.resume();
  stopPlay();
  if (editedLen() - toEdit(gNow()) < 0.2) { status('The playhead is at the end. Move it back to where you want to record from.'); return; }
  if (!range && recBlocked()) return;
  state.range = range;
  setTab('read');
  video.muted = true;
  for (let n = 3; n > 0; n--) {
    showCount(n);
    await new Promise((r) => setTimeout(r, 1000));
  }
  showCount(null);
  state.recording = true; state.recPaused = false; playK = curIdx();
  if (range) recLimit = null;
  beginCapture();
  await vPlay();
  status(range ? `Retaking section ${range.sec + 1}… it stops by itself at the end of the section.` : 'Recording… read the highlighted text. Press M when you start each new section.');
  updateUI();
}
function pauseRecording() {
  vPause();
  commitCapture();
  state.recPaused = true;
  status('Paused. Press Play to listen back, scrub to find your trim point, then Trim or Resume from there.');
  updateUI();
}
async function resumeRecording() {
  if (!state.range && recBlocked()) return;
  stopPlay();
  video.muted = true;
  await ctx.resume();
  state.recPaused = false; playK = curIdx();
  beginCapture();
  await vPlay();
  status('Recording…');
  updateUI();
}
function stopRecording() {
  const wasRange = !!state.range;
  stopPlay();
  vPause();
  if (!state.recPaused) commitCapture();
  if (!wasRange) archiveTake(); // a section retake is kept with the section instead
  video.playbackRate = +$('rate').value;
  state.recording = false; state.recPaused = false; state.range = null;
  video.muted = !$('hear').checked;
  status(`Take saved (${fmt(voiceFree ? voiceSec() : toEdit(voiceSec()))}). Play it back, record more from the playhead, or export.`);
  drawWave(); updateUI();
}
$('rec').onclick = () => (state.recording ? stopRecording() : startRecording());
$('pauseRec').onclick = () => (state.recPaused ? resumeRecording() : pauseRecording());

$('trim').onclick = () => {
  if (!hasTake()) return;
  const n = Math.round(vt(gNow()) * state.take.rate);
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
  stopPlay(); state.take = null; vsp = []; asel = null; mixCache = null; peaks = []; capturing = false; state.attempts = {};
  kv.del('take'); kv.del('attempts'); drawWave(); updateUI(); renderSections();
}
$('clear').onclick = () => { archiveTake(); checkpoint(); discardTake(); status('Take discarded.'); };

// ---------- takes ----------
// Every time you stop recording, the voice as it stands is kept here, so you can listen back, star the best one and switch to it.
let takeCounter = 0, listening = null;
const takesMeta = () => kv.set('takes', { n: takeCounter, list: takes.map(({ id, name, stars, at, rate, free }) => ({ id, name, stars, at, rate, free })) });
function archiveTake() {
  if (!hasTake() || takes.some((t) => t.samples === state.take.samples)) return;
  const t = { id: crypto.randomUUID(), name: `Take ${++takeCounter}`, samples: state.take.samples, rate: state.take.rate, stars: 0, at: Date.now(), free: voiceFree };
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
    if (!!t.free !== voiceFree) return status(`${t.name} was recorded with the voice ${t.free ? 'separate from' : 'linked to'} the video. Change "Link voice to video" to match first.`);
    stopPlay(); try { listenSrc?.stop(); } catch {} listening = null;
    checkpoint(); archiveTake();
    state.take = { samples: t.samples, rate: t.rate }; vsp = []; asel = null; mixCache = null;
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
  const g = gNow(), lines = buildCaptions(sections, realTotal(), Infinity);
  if (!lines.length) return status('Add a script first, so the app knows where each sentence starts.');
  let i = lines.findIndex((x) => g >= x.t0 && g < x.t1);
  if (i < 0) i = lines.length - 1;
  if (i > 0 && g - lines[i].t0 < 0.8) i--; // you had only just started this sentence, so redo the one before
  const from = lines[i];
  pauseRecording(); // puts the voice recorded so far away and pauses the video
  const np = nearestPause(vt(from.t0));
  let t0 = np == null ? from.t0 : vInv(np);
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
  await vPlay();
  updateUI();
}
function stopPlay() {
  if (!state.playing) return;
  stopVoice(); vPause(); video.playbackRate = +$('rate').value; state.playing = false; updateUI();
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
    state.take = { samples: mono, rate: buf.sampleRate }; vsp = []; asel = null; state.attempts = {}; mixCache = null; cleaned = null;
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
  if (syncTail()) renderCuts();
  // The save dialog has to open straight from the click, before any slow work.
  let handle = null;
  try { handle = await pickSaveTarget('voiceover.mp4'); } catch (e) { if (e.name === 'AbortError') return; }
  btn.disabled = true; btn.textContent = 'Exporting…';
  try {
    await ensureClean();
    const ratio = ratioOf(), captions = $('caps').checked ? captionList() : null, intro = titleCard('intro'), outro = titleCard('outro');
    // these edits are drawn onto every frame, so only a browser that can encode video can do them (the server only handles cuts)
    const heavy = !!(captions?.length || intro || outro || ratio !== null || zooms.length || !plainEdit());
    let blob = null, local = false, note = '';
    if ($('keep').checked) {
      if (heavy) throw new Error('Keeping the original audio cannot be combined with speed changes, moved clips, several videos, captions, titles zooms or cropping. Turn one off.');
      blob = await serverExport('Keeping the original audio needs the server.');
    } else {
      try {
        status('Exporting on this device…');
        const fx = { ratio, fit: $('fit').value, crop: $('crop').value / 100, captions, intro, outro, zooms };
        const r = await exportLocally({ sources: sources.map((x) => ({ file: x.file, off: x.off, blank: !!x.blank })), voice: finalAudio(true), overlay: ovl.length ? { clips: ovl.map((c) => ({ file: osources[c.o].file, a: c.a, b: c.b, at: c.at, box: { ...ovBoxOf(c) } })) } : null, segs: segs().map((g) => ({ src: g.src, a: g.a - sources[g.src].off, b: g.b - sources[g.src].off, r: g.r })), fx, saveHandle: handle, onProgress: (p) => (btn.textContent = `Exporting ${Math.round(p * 100)}%`) });
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
document.addEventListener('keyup', (e) => { if (e.code === 'Space' && !/TEXTAREA|INPUT|SELECT/.test(e.target.tagName)) e.preventDefault(); });
document.addEventListener('keydown', (e) => {
  if (/TEXTAREA|INPUT|SELECT/.test(e.target.tagName) || !state.file) return;
  const k = e.key.toLowerCase();
  if ((e.ctrlKey || e.metaKey) && (k === 'z' || k === 'y')) { e.preventDefault(); (k === 'y' || e.shiftKey ? redo : undo)(); return; }
  if (e.metaKey || e.ctrlKey) return;
  const cur = sectionAt(gNow());
  if (e.code === 'Space') { e.preventDefault(); e.target.blur?.(); state.recording && !state.recPaused ? $('pauseRec').click() : togglePlay(); } // a focused button must not also react to the space bar
  else if (k === 'r') $('rec').click();
  else if (k === 't') $('trim').click();
  else if (k === 'x') toggleRazor();
  else if (k === 'l') redoLine();
  else if (k === 'b') splitHere();
  else if (k === '+' || k === '=') zoomBy(1.6);
  else if (k === '-' || k === '_') zoomBy(1 / 1.6);
  else if (k === '0') setView(0, 0);
  else if (e.key === 'Delete' || e.key === 'Backspace') { e.preventDefault(); deleteClip(); }
  else if (e.key === 'Escape') setRazor(false);
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
    for (const m of meta) { if (m.blank) { sources.push({ id: m.id, name: m.name, blank: true, dur: m.dur, off: total() }); continue; } const rec = m.file ? { file: m.file } : await kv.get('src-' + m.id); if (rec?.file) await addSource(rec.file, m.id); }
  } catch { return status('This browser cannot play the saved video any more. Upload it again.'); }
  if (!sources.length) return;
  try { for (const m of (await kv.get('osources')) || []) { const rec = await kv.get('osrc-' + m.id); if (rec?.file) { const { dur, url, vw, vh } = await probe(rec.file); osources.push({ id: m.id, name: m.name, file: rec.file, url, dur, vw, vh }); } } } catch {}
  if (legacy) { kv.set('src-' + sources[0].id, { file: sources[0].file }); saveSources(); kv.del('video'); }
  clips = sources.filter((x) => !x.blank).map((x) => ({ a: x.off, b: x.off + x.dur, r: 1 }));
  let usedSaved = false;
  try { // the saved edit counts only if it still fits the videos
    const e = JSON.parse(localStorage.getItem('project') || 'null');
    if (e && Math.abs(e.total - total()) < 0.05 && Array.isArray(e.clips) && e.clips.every((c) => c.b > c.a && c.a >= 0 && c.b <= total() + 0.01)) { usedSaved = true; ovl = (e.ovl || []).filter((c) => osources[c.o]); clips = e.clips; zooms = (e.zooms || []).filter((z) => z.b > z.a); voiceFree = !!e.voiceFree; vsp = Array.isArray(e.vsp) ? e.vsp : []; syncMode(); }
  } catch {}
  if (!usedSaved) sources = sources.filter((x) => !x.blank);
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
