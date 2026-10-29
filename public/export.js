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

// segs: the kept parts of the video, [{ a, b, r }] in seconds with their speed. voice: finished audio, already edited and
// padded for any title cards. fx: { shape, crop, captions, intro: { text, sec }, outro: { text, sec } }.
export async function exportLocally({ file, voice, segs, fx = {}, saveHandle, onProgress }) {
  if (!('AudioEncoder' in window)) throw new Unsupported('This browser cannot encode audio.');
  const input = new Input({ source: new BlobSource(file), formats: ALL_FORMATS });
  const video = await input.getPrimaryVideoTrack();
  if (!video) throw new Unsupported('No video track found.');

  const format = new Mp4OutputFormat({ fastStart: saveHandle ? false : 'in-memory' });
  const vcodec = await video.getCodec();
  if (!vcodec || !MP4_SAFE.includes(vcodec) || !format.getSupportedVideoCodecs().includes(vcodec)) throw new Unsupported(`MP4 cannot hold ${vcodec || 'this'} video without converting it.`);
  const decoderConfig = await video.getDecoderConfig();
  const fullDuration = await video.computeDuration();

  const intro = fx.intro?.sec > 0 ? fx.intro : null, outro = fx.outro?.sec > 0 ? fx.outro : null;
  const shape = SHAPES[fx.shape] ? fx.shape : 'original';
  const look = !!(fx.captions?.length || intro || outro || shape !== 'original'); // anything that has to be drawn onto the frames
  const same = segs.length === 1 && segs[0].r === 1 && segs[0].a < 1e-3 && Math.abs(segs[0].b - fullDuration) < 0.02;
  const mode = look ? 'canvas' : same ? 'copy' : 'samples';
  const content = segs.reduce((n, s) => n + (s.b - s.a) / s.r, 0);
  const lead = intro?.sec || 0, total = lead + content + (outro?.sec || 0);

  // output picture size; canvas mode crops to the chosen shape
  const dw = video.displayWidth, dh = video.displayHeight;
  const crop = { sx: 0, sy: 0, sw: dw, sh: dh };
  let outW = even(dw), outH = even(dh);
  if (shape !== 'original') {
    const A = SHAPES[shape];
    if (A < dw / dh) { crop.sw = dh * A; crop.sx = (dw - crop.sw) * (fx.crop ?? 0.5); }
    else { crop.sh = dw / A; crop.sy = (dh - crop.sh) / 2; }
    outH = even(Math.min(crop.sh, 1920)); outW = even(outH * A);
  }
  const encW = mode === 'canvas' ? outW : await video.getCodedWidth(), encH = mode === 'canvas' ? outH : await video.getCodedHeight();
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
  output.addVideoTrack(vsource, mode === 'canvas' ? {} : { rotation: video.rotation });
  output.addAudioTrack(asource);
  await output.start();

  const copyVideo = async () => {
    let first = true;
    for await (const packet of new EncodedPacketSink(video).packets()) {
      await vsource.add(packet, first ? { decoderConfig } : undefined);
      first = false;
      onProgress?.(Math.min(1, packet.timestamp / fullDuration));
    }
    vsource.close();
  };

  const encodeVideo = async () => {
    const sink = new VideoSampleSink(video);
    const caps = fx.captions || [];
    let ci = 0, outAt = lead;
    const card = async (text, from, sec) => {
      drawTitle(g, outW, outH, text);
      for (let t = 0; t < sec; t += 0.25) await vsource.add(from + t, Math.min(0.25, sec - t));
    };
    if (intro) await card(intro.text, 0, intro.sec);
    for (const { a, b, r } of segs) {
      for await (const s of sink.samples(a, b)) {
        const rel = Math.max(0, s.timestamp - a) / r;
        if (mode === 'canvas') {
          s.draw(g, crop.sx, crop.sy, crop.sw, crop.sh, 0, 0, outW, outH);
          while (ci < caps.length && caps[ci].t1 <= s.timestamp) ci++; // captions are in video time, which only moves forward
          if (caps[ci] && s.timestamp >= caps[ci].t0) drawCaption(g, outW, outH, caps[ci].text);
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
