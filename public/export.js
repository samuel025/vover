// Builds the narrated MP4 on the user's own device. With no edits the original video is copied packet by packet
// (never re-encoded). With cuts or speed changes the frames are decoded and encoded again; with captions, title cards
// or a crop they are also drawn onto a canvas on the way. The finished audio is encoded and added as the only sound track.
import {
  ALL_FORMATS, AudioBufferSource, BlobSource, BufferTarget, CanvasSource, EncodedPacketSink, EncodedVideoPacketSource,
  Input, Mp4OutputFormat, Output, StreamTarget, VideoSampleSink, VideoSampleSource, canEncodeAudio, canEncodeVideo,
} from './vendor/mediabunny.mjs';

// Thrown when this device cannot do the job, so the caller can fall back to the server.
export class Unsupported extends Error {}

// codecs that play in ordinary MP4 players; anything else (e.g. VP8) goes through the server so it is converted to H.264
const MP4_SAFE = ['avc', 'hevc', 'vp9', 'av1'];
const AUDIO_CODECS = ['aac', 'opus']; // AAC plays everywhere; Opus is the fallback where AAC cannot be encoded
const SHAPES = { vertical: 9 / 16, square: 1 };

export const canSaveToDisk = () => typeof window.showSaveFilePicker === 'function';

// Opens the "save as" dialog. Must be called straight from the click, before any slow work.
export async function pickSaveTarget(name) {
  if (!canSaveToDisk()) return null;
  const handle = await window.showSaveFilePicker({ suggestedName: name, types: [{ description: 'MP4 video', accept: { 'video/mp4': ['.mp4'] } }] });
  return handle;
}

const even = (n) => Math.max(2, Math.floor(n / 2) * 2);

// Splits `text` into lines that fit `width`.
function wrap(g, text, width) {
  const lines = []; let line = '';
  for (const w of text.split(/\s+/)) {
    const t = line ? line + ' ' + w : w;
    if (line && g.measureText(t).width > width) { lines.push(line); line = w; } else line = t;
  }
  if (line) lines.push(line);
  return lines;
}

function drawTitle(g, W, H, text) {
  g.fillStyle = '#171717'; g.fillRect(0, 0, W, H);
  const size = Math.round(Math.min(W, H) * 0.09);
  g.font = `700 ${size}px Inter, system-ui, sans-serif`; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillStyle = '#fff';
  const lines = wrap(g, text, W * 0.8), gap = size * 1.25, top = H / 2 - ((lines.length - 1) * gap) / 2;
  lines.forEach((l, i) => g.fillText(l, W / 2, top + i * gap));
  g.fillStyle = '#ffb88e'; g.fillRect(W / 2 - size, top + ((lines.length - 1) * gap) / 2 + size * 1.1, size * 2, Math.max(3, size * 0.08));
}

function drawCaption(g, W, H, text) {
  const size = Math.round(Math.min(W, H) * 0.055);
  g.font = `600 ${size}px Inter, system-ui, sans-serif`; g.textAlign = 'center'; g.textBaseline = 'middle';
  const lines = wrap(g, text, W * 0.86), gap = size * 1.3, bottom = H - size * 1.4;
  lines.forEach((l, i) => {
    const y = bottom - (lines.length - 1 - i) * gap, w = g.measureText(l).width;
    g.fillStyle = '#000000b3'; g.fillRect(W / 2 - w / 2 - size * 0.4, y - size * 0.7, w + size * 0.8, size * 1.4);
    g.fillStyle = '#fff'; g.fillText(l, W / 2, y);
  });
}

// sources: [{ file, off }] the videos (off is where each starts in project time, which is how captions are timed).
// segs: the clips in timeline order, [{ src, a, b, r }] with a and b in seconds inside that video and r the speed.
// voice: finished audio, already edited and padded for any title cards.
// fx: { shape, crop, captions, intro: { text, sec }, outro: { text, sec } } (caption times are in project time).
export async function exportLocally({ sources, voice, segs, fx = {}, saveHandle, onProgress }) {
  if (!('AudioEncoder' in window)) throw new Unsupported('This browser cannot encode audio.');
  if (!segs.length) throw new Unsupported('There is nothing left in the timeline to export.');

  // open every video that is used
  const tracks = {};
  for (const k of new Set(segs.map((x) => x.src))) {
    const input = new Input({ source: new BlobSource(sources[k].file), formats: ALL_FORMATS });
    const video = await input.getPrimaryVideoTrack();
    if (!video) throw new Unsupported('No video track found.');
    tracks[k] = { video, duration: await video.computeDuration(), sink: null };
  }
  const first = tracks[segs[0].src];
  const multi = Object.keys(tracks).length > 1;

  const format = new Mp4OutputFormat({ fastStart: saveHandle ? false : 'in-memory' });
  const vcodec = await first.video.getCodec();
  if (!vcodec || !MP4_SAFE.includes(vcodec) || !format.getSupportedVideoCodecs().includes(vcodec)) throw new Unsupported(`MP4 cannot hold ${vcodec || 'this'} video without converting it.`);
  const decoderConfig = await first.video.getDecoderConfig();

  const intro = fx.intro?.sec > 0 ? fx.intro : null, outro = fx.outro?.sec > 0 ? fx.outro : null;
  const shape = SHAPES[fx.shape] ? fx.shape : 'original';
  const look = !!(fx.captions?.length || intro || outro || shape !== 'original'); // anything that has to be drawn onto the frames
  const same = !multi && segs.length === 1 && segs[0].r === 1 && segs[0].a < 1e-3 && Math.abs(segs[0].b - first.duration) < 0.02;
  const mode = look || multi ? 'canvas' : same ? 'copy' : 'samples';
  const content = segs.reduce((n, g) => n + (g.b - g.a) / g.r, 0);
  const lead = intro?.sec || 0, total = lead + content + (outro?.sec || 0);

  // output picture size comes from the first video; canvas mode crops or fits every frame into it
  const dw = first.video.displayWidth, dh = first.video.displayHeight;
  let outW = even(dw), outH = even(dh);
  if (shape !== 'original') {
    const A = SHAPES[shape];
    const ch = A < dw / dh ? dh : dw / A;
    outH = even(Math.min(ch, 1920)); outW = even(outH * A);
  }
  // where a frame of size (w, h) is taken from and drawn to
  const place = (w, h) => {
    if (shape !== 'original') {
      const A = outW / outH, p = { dx: 0, dy: 0, dW: outW, dH: outH, sx: 0, sy: 0, sw: w, sh: h };
      if (A < w / h) { p.sw = h * A; p.sx = (w - p.sw) * (fx.crop ?? 0.5); } else { p.sh = w / A; p.sy = (h - p.sh) / 2; }
      return p;
    }
    const k = Math.min(outW / w, outH / h), dW = w * k, dH = h * k;
    return { sx: 0, sy: 0, sw: w, sh: h, dx: (outW - dW) / 2, dy: (outH - dH) / 2, dW, dH };
  };
  const encW = mode === 'canvas' ? outW : await first.video.getCodedWidth(), encH = mode === 'canvas' ? outH : await first.video.getCodedHeight();
  const bitrate = Math.max(2e6, encW * encH * 4);

  let outCodec = vcodec;
  if (mode !== 'copy') {
    outCodec = null;
    for (const c of ['avc', 'vp9', 'av1']) {
      if (format.getSupportedVideoCodecs().includes(c) && await canEncodeVideo(c, { width: encW, height: encH, bitrate })) { outCodec = c; break; }
    }
    if (!outCodec) throw new Unsupported('This browser cannot encode video, which these edits need.');
  }

  let acodec;
  for (const c of AUDIO_CODECS) {
    if (await canEncodeAudio(c, { numberOfChannels: 1, sampleRate: voice.rate })) { acodec = c; break; }
  }
  if (!acodec) throw new Unsupported('This browser cannot encode audio.');

  const canvas = mode === 'canvas' ? new OffscreenCanvas(outW, outH) : null;
  const g = canvas?.getContext('2d');
  const writable = saveHandle ? await saveHandle.createWritable() : null;
  const target = writable ? new StreamTarget(writable) : new BufferTarget();
  const output = new Output({ format, target });
  const vsource = mode === 'copy' ? new EncodedVideoPacketSource(vcodec)
    : mode === 'canvas' ? new CanvasSource(canvas, { codec: outCodec, bitrate })
    : new VideoSampleSource({ codec: outCodec, bitrate });
  const asource = new AudioBufferSource({ codec: acodec, bitrate: 192_000 });
  output.addVideoTrack(vsource, mode === 'canvas' ? {} : { rotation: first.video.rotation });
  output.addAudioTrack(asource);
  await output.start();

  const copyVideo = async () => {
    let firstPacket = true;
    for await (const packet of new EncodedPacketSink(first.video).packets()) {
      await vsource.add(packet, firstPacket ? { decoderConfig } : undefined);
      firstPacket = false;
      onProgress?.(Math.min(1, packet.timestamp / first.duration));
    }
    vsource.close();
  };

  const encodeVideo = async () => {
    const caps = fx.captions || [];
    let outAt = lead, ci = 0;
    const card = async (text, from, sec) => {
      drawTitle(g, outW, outH, text);
      for (let t = 0; t < sec; t += 0.25) await vsource.add(from + t, Math.min(0.25, sec - t));
    };
    if (intro) await card(intro.text, 0, intro.sec);
    for (const seg of segs) {
      const tr = tracks[seg.src], { a, b, r } = seg, off = sources[seg.src].off;
      tr.sink ||= new VideoSampleSink(tr.video);
      const pl = mode === 'canvas' ? place(tr.video.displayWidth, tr.video.displayHeight) : null;
      for await (const s of tr.sink.samples(a, b)) {
        const rel = Math.max(0, s.timestamp - a) / r;
        if (mode === 'canvas') {
          if (multi || shape === 'original') { g.fillStyle = '#000'; g.fillRect(0, 0, outW, outH); }
          s.draw(g, pl.sx, pl.sy, pl.sw, pl.sh, pl.dx, pl.dy, pl.dW, pl.dH);
          const gt = off + s.timestamp; // captions are timed in project time, and clips can be played in any order
          if (!(caps[ci] && gt >= caps[ci].t0 && gt < caps[ci].t1)) ci = caps.findIndex((c) => gt >= c.t0 && gt < c.t1);
          if (ci >= 0 && caps[ci]) drawCaption(g, outW, outH, caps[ci].text);
          await vsource.add(outAt + rel, Math.max(s.duration / r, 0.001));
        } else {
          s.setTimestamp(outAt + rel); s.setDuration(s.duration / r);
          await vsource.add(s);
        }
        s.close();
        onProgress?.(Math.min(1, (outAt + rel) / total));
      }
      outAt += (b - a) / r;
    }
    if (outro) await card(outro.text, outAt, outro.sec);
    vsource.close();
  };

  // The audio is fed in 10 second pieces, then padded with silence to the end of the video.
  const encodeVoice = async () => {
    const { samples, rate } = voice;
    const len = Math.max(samples.length, Math.ceil(total * rate));
    const piece = rate * 10;
    for (let at = 0; at < len; at += piece) {
      const n = Math.min(piece, len - at);
      const buf = new AudioBuffer({ length: n, sampleRate: rate, numberOfChannels: 1 });
      if (at < samples.length) buf.copyToChannel(samples.subarray(at, Math.min(samples.length, at + n)), 0);
      await asource.add(buf);
    }
    asource.close();
  };

  try {
    await Promise.all([mode === 'copy' ? copyVideo() : encodeVideo(), encodeVoice()]);
    await output.finalize();
  } catch (e) {
    try { await output.cancel(); } catch {}
    try { await writable?.abort(); } catch {}
    throw e;
  }
  return { blob: saveHandle ? null : new Blob([target.buffer], { type: 'video/mp4' }), audioCodec: acodec };
}
