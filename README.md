# Voiceover Studio

Record a voiceover over any video in one browser tab. Upload a video, paste your script, read it from a teleprompter that scrolls with the video, then export an MP4 with your voice.

- Synced teleprompter with adjustable scroll speed, font size and mirror mode
- Record, pause, play back, trim the end and continue from any point
- Sections (a blank line in the script): retake one section on its own, keep earlier takes and switch back, and let the teleprompter follow your real pace
- Fullscreen teleprompter that you can run entirely from the keyboard
- Recordings are saved as you go, so a crashed or closed tab can be recovered, plus a live warning when the mic is too quiet or clipping
- Cut parts out of the video: press Cut (X) at the start, move the playhead, press it again at the end. Cuts are skipped in playback and removed from the export (the picture is re-encoded when there are cuts), and each one can be restored
- Save your recording as a WAV file and import it onto any video later (or a new one), then carry on recording from where it ends
- Zoom and pan: zoom into part of the picture for a few seconds, optionally sliding to another spot, easing in and out (preview and export)
- Voice tone presets (podcast, warm, bright) and a light or strong de-esser, applied to the recording non-destructively
- New project clears everything and gives a blank workspace
- Zoomable timeline with a time ruler: + / - buttons or keys, Ctrl + scroll, double-click a clip to zoom to it, scroll bar to move along, follows the playhead while playing
- Video-only edits: set "Edits change" to "video only" and cuts, deletes, moves and speed changes leave your recorded voice exactly where it is on the timeline (switching back re-attaches it to the video)
- Voice-only edits: set "Edits change" to "voice only" to cut, split and delete just the recording. Cuts leave silence (no ripple), the voice shows as pieces you can drag, and a piece snaps to the edges of its neighbours so gaps close cleanly
- A clip strip above the waveform: drag a clip's edge to trim it, drag a clip to move it, click to select it
- Combine several videos on one timeline and narrate across them (+ Add video, or drop more videos on the page)
- Takes: every finished recording is kept in a list you can listen to, star and switch between
- Redo line (L): while recording, jump back to the start of the sentence you are on and read it again
- Split the video into clips (B), delete a clip, change one clip's speed (voice speed follows, pitch kept), undo and redo (Ctrl+Z)
- Audio polish: background noise reduction, volume evening, voice fades, background music that dips while you speak, one click to cut long pauses
- Captions built from your script (shown in the preview, burned into the export, or downloaded as .srt), intro and outro title cards, vertical or square crop
- Splitting, moving clips, several videos, speed, zooms, captions, titles and cropping are done in the browser only (Chrome or Edge); the server fallback handles plain cuts of a single video but nothing else
- Waveform timeline you can scrub, playback speed, volume and sync nudge
- Your video, script and take survive a page refresh
- Export runs **in your browser** for most MP4 and MOV files: the video is never uploaded

## Run it

You need [Node.js](https://nodejs.org) 18 or newer. There is nothing to build and no packages to install.

```
git clone <this repo>
cd voiceover-studio
npm start
```

Open http://localhost:3000 (set another port with `PORT=3111 npm start`; on Windows PowerShell use `$env:PORT=3111; npm start`).

Microphone access needs a secure page. `localhost` counts as secure; anything else must use HTTPS.

## How export works

| Case | Where it runs |
| --- | --- |
| MP4 / MOV video (H.264, HEVC, VP9, AV1) | In your browser. The video is copied untouched and only your voice is encoded. Nothing is uploaded. |
| WebM and other formats | On the server with ffmpeg, which converts the video to H.264. |
| "Keep original audio as quiet background" | On the server with ffmpeg. |

In Chrome and Edge the export is written straight to a file you choose, so large videos work. Other browsers build the file in memory first, so very large videos can fail there.

If a browser cannot encode AAC audio (Chrome on Linux, for example) the voice is saved as Opus. Most players handle it; QuickTime and some older devices may not.

### Server fallback needs ffmpeg

The server cases above need `ffmpeg` and `ffprobe` on your PATH ([install ffmpeg](https://ffmpeg.org/download.html)). Without them the app still works for in-browser exports, and the server refuses the other cases with a clear message. The server prints a warning at startup if ffmpeg is missing.

### Server limits

Set these with environment variables. Defaults are in brackets.

| Variable | Meaning |
| --- | --- |
| `PORT` | Port to listen on (3000) |
| `MAX_VIDEO_MB` | Largest video the server accepts (1024) |
| `MAX_VOICE_MB` | Largest voice recording the server accepts (600) |
| `MAX_VIDEO_MIN` | Longest video the server accepts, in minutes (30) |
| `MAX_JOBS` | Exports running at once (1) |
| `MAX_QUEUE` | Exports allowed to wait before the server says it is busy (5) |
| `TTL_MIN` | Minutes before uploaded files are deleted (60) |
| `HOURLY_UPLOADS` / `HOURLY_EXPORTS` | Per visitor, per hour (20 / 15) |

These limits only apply to the server fallback. In-browser exports have no limit beyond your device.

## Browser support

Chrome and Edge are the best supported. Firefox and Safari need the browser's audio encoding features (WebCodecs) and have had less testing; where a feature is missing the export falls back to the server.

## Hosting

The `public` folder is a plain static site, so it can be hosted anywhere (GitHub Pages, Netlify, Vercel) and in-browser exports will work. The server fallback needs somewhere that can run Node with ffmpeg; serverless platforms such as Vercel cannot run it. On a static-only host, WebM files and "keep original audio" will show a "server not available" message.

## Project layout

```
server.js          Small Node server: static files plus the ffmpeg fallback
public/            The app (landing page, studio, teleprompter, recorder, export)
public/vendor/     mediabunny, the library that builds the MP4 in the browser
scripts/vendor.mjs Updates public/vendor (npm install, then npm run vendor)
```

## Licenses

Voiceover Studio is MIT licensed (see `LICENSE`). It includes [mediabunny](https://github.com/Vanilagy/mediabunny) under the MPL-2.0; its license is in `public/vendor/mediabunny.LICENSE`.
