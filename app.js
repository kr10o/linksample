  <script>
    const { createApp, ref, onMounted, onUnmounted } = Vue;

    // --- Configuration ---
    const STEPS = 32;
    const SCALE = ['C2', 'D2', 'F2', 'G2', 'A#2', 'C3', 'D3', 'F3', 'G3', 'A#3', 'C4', 'D4', 'F4', 'G4', 'A#4'];
    // Desaturated track palette — mid-lightness, low-saturation tones that sit
    // calmly on the near-black background rather than fighting it.
    const PALETTE = [
      'bg-[#9b6a6a]', // rosewood
      'bg-[#6a82a0]', // steel blue
      'bg-[#9a9166]', // muted gold
      'bg-[#6f9a7c]', // sage
      'bg-[#8a7aa0]', // dusty violet
      'bg-[#a07c92]', // mauve
      'bg-[#a0855f]', // amber-brown
      'bg-[#6a9a9a]'  // muted teal
    ];
    const ROOT_NOTE = 'C3';
    const ACCENT = '#6f8aaa';      // muted steel-blue for canvases
    const ACCENT_RGB = '90,116,147';

    // ============================================================
    //  Pure helpers (module scope)
    // ============================================================
    const NOTE_OFFSETS = { C: 0, 'C#': 1, D: 2, 'D#': 3, E: 4, F: 5, 'F#': 6, G: 7, 'G#': 8, A: 9, 'A#': 10, B: 11 };
    const noteToMidi = (note) => {
      const m = String(note).match(/^([A-G]#?)(-?\d+)$/);
      if (!m) return 60;
      return NOTE_OFFSETS[m[1]] + (parseInt(m[2], 10) + 1) * 12;
    };
    const semitonesFromRoot = (note) => noteToMidi(note) - noteToMidi(ROOT_NOTE);

    const writeVarLen = (value) => {
      let buffer = value & 0x7f;
      while ((value >>= 7) > 0) { buffer <<= 8; buffer |= ((value & 0x7f) | 0x80); }
      const out = [];
      while (true) { out.push(buffer & 0xff); if (buffer & 0x80) buffer >>= 8; else break; }
      return out;
    };

    // Build a Standard MIDI File (format 1) from the sequencer grid.
    const buildMidiFile = (tracksData, gridData, bpmVal) => {
      const PPQ = 128;
      const sixteenth = PPQ / 4;
      const bytes = [];
      const pushStr = (arr, str) => { for (let i = 0; i < str.length; i++) arr.push(str.charCodeAt(i) & 0xff); };
      const pushU32 = (arr, v) => arr.push((v >>> 24) & 0xff, (v >>> 16) & 0xff, (v >>> 8) & 0xff, v & 0xff);
      const pushU16 = (arr, v) => arr.push((v >> 8) & 0xff, v & 0xff);
      const pushMeta = (arr, type, dataBytes) => { arr.push(0x00, 0xff, type, ...writeVarLen(dataBytes.length), ...dataBytes); };

      const chunks = [];
      const tempo = [];
      const micros = Math.round(60000000 / bpmVal);
      tempo.push(0x00, 0xff, 0x51, 0x03, (micros >> 16) & 0xff, (micros >> 8) & 0xff, micros & 0xff);
      tempo.push(0x00, 0xff, 0x2f, 0x00);
      chunks.push(tempo);

      tracksData.forEach((track, i) => {
        const events = [];
        gridData[i].forEach((step, stepIdx) => {
          if (!step.active) return;
          const tick = stepIdx * sixteenth;
          const note = noteToMidi(step.note);
          events.push({ tick, on: true, note });
          events.push({ tick: tick + sixteenth, on: false, note });
        });
        if (events.length === 0) return;
        events.sort((a, b) => (a.tick - b.tick) || (a.on === b.on ? 0 : a.on ? 1 : -1));

        const data = [];
        const nameBytes = [];
        pushStr(nameBytes, track.name.slice(0, 60));
        pushMeta(data, 0x03, nameBytes);

        let prev = 0;
        events.forEach((ev) => {
          const delta = ev.tick - prev; prev = ev.tick;
          data.push(...writeVarLen(delta));
          if (ev.on) data.push(0x90, ev.note & 0x7f, 100);
          else data.push(0x80, ev.note & 0x7f, 0x00);
        });
        data.push(0x00, 0xff, 0x2f, 0x00);
        chunks.push(data);
      });

      pushStr(bytes, 'MThd'); pushU32(bytes, 6); pushU16(bytes, 1); pushU16(bytes, chunks.length); pushU16(bytes, PPQ);
      chunks.forEach((chunk) => {
        pushStr(bytes, 'MTrk'); pushU32(bytes, chunk.length);
        for (let k = 0; k < chunk.length; k++) bytes.push(chunk[k]);
      });
      return new Uint8Array(bytes);
    };

    const App = {
      setup() {
        const isAudioReady = ref(false);
        const isLoading = ref(false);
        const isPlaying = ref(false);
        const isRecording = ref(false);
        const bpm = ref(120);
        const swing = ref(0);
        const metronomeOn = ref(false);
        const playingStep = ref(0);
        const masterVolume = ref(-5);
        const selectedTrackIdx = ref(0);
        const loadStatus = ref('');

        const tracks = ref([]);
        const grid = ref([]);
        const trackParams = ref([]);
        const canvasRef = ref(null);
        const waveCanvasRef = ref(null);

        // Global effect parameters (drive the shared aux nodes)
        const fxParams = ref({
          revDecay: 2.5, revWet: 1,
          dlyFeed: 0.4,  dlyWet: 1,
          dstAmt: 0.6,   dstWet: 1,
          fltRate: 1,    fltWet: 1,
          choDepth: 0.5, choWet: 1,
          phaRate: 0.5,  phaWet: 1
        });

        // Audio engine globals (non-reactive)
        let players = [];
        let channels = [];
        let revSends = [], dlySends = [], choSends = [], phaSends = [], dstSends = [], fltSends = [];
        let analyzer = null;
        let metronome = null;
        let stepCount = 0;
        let animationFrame = null;
        let engineInitialized = false;
        let recorder = null;
        const trackPeaks = {};

        let reverbNode, delayNode, chorusNode, phaserNode, distortionNode, autoFilterNode;
        let waveDrag = null;
        let painting = false;
        let paintValue = true;

        const defaultParams = (vol = -5) => ({
          vol, pan: 0, mute: false, solo: false,
          revSend: -60, dlySend: -60, choSend: -60, phaSend: -60, dstSend: -60, fltSend: -60,
          sampleStart: 0, sampleEnd: 100, chopCount: 4
        });

        const fetchWithRetry = async (url, retries = 3) => {
          let lastErr;
          for (let attempt = 1; attempt <= retries; attempt++) {
            try {
              const res = await fetch(url, { cache: 'no-store' });
              if (!res.ok) throw new Error('HTTP ' + res.status);
              return res;
            } catch (e) {
              lastErr = e;
              if (attempt < retries) await new Promise((r) => setTimeout(r, 600 * attempt));
            }
          }
          throw lastErr;
        };

        const loadBuffer = (url) => new Promise((resolve) => {
          try {
            const buf = new Tone.ToneAudioBuffer(url, () => resolve(buf), () => resolve(null));
          } catch (e) { resolve(null); }
        });

        const computePeaks = (i, buffer) => {
          try {
            const ab = buffer.get ? buffer.get() : buffer;
            const data = ab.getChannelData(0);
            const samples = 260;
            const block = Math.max(1, Math.floor(data.length / samples));
            const peaks = [];
            for (let s = 0; s < samples; s++) {
              let min = 1, max = -1;
              const base = s * block;
              for (let j = 0; j < block; j++) {
                const v = data[base + j] || 0;
                if (v < min) min = v;
                if (v > max) max = v;
              }
              peaks.push([min, max]);
            }
            trackPeaks[i] = peaks;
          } catch (e) { trackPeaks[i] = null; }
        };

        const setupTrackNodes = (i, params, buffer) => {
          const channel = new Tone.Channel({ volume: params.vol, pan: params.pan }).connect(Tone.Destination);
          channel.mute = params.mute;
          channel.solo = params.solo;
          channels[i] = channel;

          revSends[i] = new Tone.Volume(params.revSend).connect(reverbNode);     channel.connect(revSends[i]);
          dlySends[i] = new Tone.Volume(params.dlySend).connect(delayNode);      channel.connect(dlySends[i]);
          choSends[i] = new Tone.Volume(params.choSend).connect(chorusNode);     channel.connect(choSends[i]);
          phaSends[i] = new Tone.Volume(params.phaSend).connect(phaserNode);     channel.connect(phaSends[i]);
          dstSends[i] = new Tone.Volume(params.dstSend).connect(distortionNode); channel.connect(dstSends[i]);
          fltSends[i] = new Tone.Volume(params.fltSend).connect(autoFilterNode); channel.connect(fltSends[i]);

          if (buffer) {
            players[i] = new Tone.Player(buffer);
            computePeaks(i, buffer);
          } else {
            players[i] = null;
          }
        };

        const triggerHit = (i, note, time) => {
          const player = players[i];
          if (!player || !player.loaded || !player.buffer) return;
          const buffer = player.buffer;
          const total = buffer.duration;
          const p = trackParams.value[i];

          let startSec = (Math.min(p.sampleStart, p.sampleEnd) / 100) * total;
          let endSec = (Math.max(p.sampleStart, p.sampleEnd) / 100) * total;
          if (endSec <= startSec) endSec = total;
          const windowDur = Math.max(0.02, endSec - startSec);
          const rate = Math.pow(2, semitonesFromRoot(note) / 12);

          try {
            const src = new Tone.ToneBufferSource(buffer).connect(channels[i]);
            src.playbackRate.value = rate;
            src.fadeOut = 0.005;
            src.start(time, startSec, windowDur);
            src.onended = () => { try { src.dispose(); } catch (e) {} };
          } catch (e) {}
        };

        const initializeAudio = async () => {
          if (engineInitialized || isLoading.value) return;
          isLoading.value = true;
          loadStatus.value = 'Starting audio context...';
          await Tone.start();

          let fetchedSamples = [];
          try {
            loadStatus.value = 'Fetching sample manifest...';
            const res = await fetchWithRetry('https://raw.githubusercontent.com/kr10o/linksample/refs/heads/main/samples.json');
            const rawText = await res.text();
            try {
              const parsedData = JSON.parse(rawText);
              if (Array.isArray(parsedData)) {
                parsedData.forEach((item) => {
                  if (item.name && item.link) fetchedSamples.push({ name: item.name, link: item.link });
                });
              }
            } catch (parseError) {
              console.warn('Strict JSON parsing failed. Attempting RegEx extraction...', parseError);
              const regexArray = /["']name["']\s*:\s*["']([^"']+)["']\s*,\s*["']link["']\s*:\s*["']([^"']+)["']/g;
              let match;
              while ((match = regexArray.exec(rawText)) !== null) {
                fetchedSamples.push({ name: match[1], link: match[2] });
              }
            }
          } catch (error) {
            console.error('Error fetching sample backend.', error);
            loadStatus.value = 'Manifest unreachable — launching empty session.';
          }

          const dynamicTracks = fetchedSamples.map((sample, index) => ({
            id: sample.name,
            name: sample.name.charAt(0).toUpperCase() + sample.name.slice(1),
            color: PALETTE[index % PALETTE.length],
            url: sample.link,
            offline: false
          }));

          tracks.value = dynamicTracks;
          grid.value = dynamicTracks.map(() => Array(STEPS).fill(null).map(() => ({ active: false, note: 'C3' })));
          trackParams.value = dynamicTracks.map(() => defaultParams(-5));

          const masterCompressor = new Tone.Compressor({ threshold: -20, ratio: 4, attack: 0.01, release: 0.25 });
          const masterLimiter = new Tone.Limiter(-1);
          analyzer = new Tone.Waveform(256);
          Tone.Destination.volume.value = masterVolume.value;
          Tone.Destination.chain(masterCompressor, masterLimiter, analyzer);

          // Aux effect buses (initialised from fxParams)
          reverbNode    = new Tone.Reverb(fxParams.value.revDecay).connect(Tone.Destination);
          delayNode     = new Tone.FeedbackDelay('8n', fxParams.value.dlyFeed).connect(Tone.Destination);
          chorusNode    = new Tone.Chorus(4, 2.5, fxParams.value.choDepth).connect(Tone.Destination).start();
          phaserNode    = new Tone.Phaser({ frequency: fxParams.value.phaRate, octaves: 5, baseFrequency: 1000 }).connect(Tone.Destination);
          distortionNode = new Tone.Distortion({ distortion: fxParams.value.dstAmt, oversample: '2x' }).connect(Tone.Destination);
          autoFilterNode = new Tone.AutoFilter({ frequency: fxParams.value.fltRate, baseFrequency: 200, octaves: 4 }).connect(Tone.Destination).start();

          metronome = new Tone.Synth({
            oscillator: { type: 'triangle' },
            envelope: { attack: 0.001, decay: 0.04, sustain: 0, release: 0.02 },
            volume: -8
          }).connect(Tone.Destination);

          for (let i = 0; i < dynamicTracks.length; i++) {
            loadStatus.value = `Loading samples (${i + 1}/${dynamicTracks.length})...`;
            let buffer = null;
            try { buffer = await loadBuffer(dynamicTracks[i].url); } catch (e) { buffer = null; }
            if (!buffer) {
              tracks.value[i].offline = true;
              console.warn('Sample offline:', dynamicTracks[i].name, dynamicTracks[i].url);
            }
            setupTrackNodes(i, trackParams.value[i], buffer);
          }

          Tone.Transport.bpm.value = bpm.value;

          Tone.Transport.scheduleRepeat((time) => {
            const currentStep = stepCount;

            // Swing: nudge off-beat (odd) 16ths later by up to half a step.
            let t = time;
            if (swing.value > 0 && currentStep % 2 === 1) {
              t += swing.value * Tone.Time('16n').toSeconds() * 0.5;
            }

            // Metronome click on quarter notes (accent on the bar's first step).
            if (metronomeOn.value && !isRecording.value && metronome && currentStep % 4 === 0) {
              try {
                metronome.triggerAttackRelease(currentStep === 0 ? 'C6' : 'G5', '32n', time, currentStep === 0 ? 0.9 : 0.5);
              } catch (e) {}
            }

            tracks.value.forEach((track, index) => {
              const stepData = grid.value[index][currentStep];
              if (stepData && stepData.active) triggerHit(index, stepData.note, t);
            });

            Tone.Draw.schedule(() => { playingStep.value = currentStep; }, time);
            stepCount = (currentStep + 1) % STEPS;
          }, '16n');

          engineInitialized = true;
          isAudioReady.value = true;
          isLoading.value = false;
          startVisualizers();
        };

        const startVisualizers = () => {
          const draw = () => {
            if (analyzer && canvasRef.value) {
              const canvas = canvasRef.value;
              const ctx = canvas.getContext('2d');
              const width = canvas.width, height = canvas.height;
              const values = analyzer.getValue();
              ctx.clearRect(0, 0, width, height);
              ctx.beginPath();
              ctx.lineJoin = 'round';
              ctx.lineWidth = 1.5;
              ctx.strokeStyle = ACCENT;
              for (let i = 0; i < values.length; i++) {
                const x = (i / (values.length - 1)) * width;
                const y = ((values[i] + 1) / 2) * height;
                if (i === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
              }
              ctx.stroke();
            }
            drawWaveform();
            animationFrame = requestAnimationFrame(draw);
          };
          draw();
        };

        const drawWaveform = () => {
          const canvas = waveCanvasRef.value;
          if (!canvas) return;
          const ctx = canvas.getContext('2d');
          const W = canvas.width, H = canvas.height, mid = H / 2;
          ctx.clearRect(0, 0, W, H);

          const idx = selectedTrackIdx.value;
          const peaks = trackPeaks[idx];
          if (!peaks) {
            ctx.fillStyle = '#52525b';
            ctx.font = '9px monospace';
            ctx.fillText(tracks.value[idx] && tracks.value[idx].offline ? 'OFFLINE — no sample' : 'No sample loaded', 8, mid + 3);
            return;
          }

          const p = trackParams.value[idx];
          const sx = (Math.min(p.sampleStart, p.sampleEnd) / 100) * W;
          const ex = (Math.max(p.sampleStart, p.sampleEnd) / 100) * W;
          const colW = Math.max(1, W / peaks.length);

          for (let x = 0; x < peaks.length; x++) {
            const px = (x / peaks.length) * W;
            const inRange = px >= sx && px <= ex;
            ctx.fillStyle = inRange ? ACCENT : '#3f3f46';
            const [min, max] = peaks[x];
            const y2 = mid + max * (mid - 1);
            const y1 = mid + min * (mid - 1);
            ctx.fillRect(px, y2, colW, Math.max(1, y1 - y2));
          }

          ctx.fillStyle = 'rgba(10,10,10,0.55)';
          ctx.fillRect(0, 0, sx, H);
          ctx.fillRect(ex, 0, W - ex, H);

          ctx.strokeStyle = 'rgba(154,145,102,0.5)';
          ctx.lineWidth = 1;
          for (let s = 1; s < p.chopCount; s++) {
            const cx = (s / p.chopCount) * W;
            ctx.beginPath(); ctx.moveTo(cx, 0); ctx.lineTo(cx, H); ctx.stroke();
          }

          ctx.fillStyle = '#6f9a7c'; ctx.fillRect(sx, 0, 2, H);
          ctx.fillStyle = '#9b6a6a'; ctx.fillRect(ex - 2, 0, 2, H);
        };

        const waveXToPct = (clientX) => {
          const canvas = waveCanvasRef.value;
          const rect = canvas.getBoundingClientRect();
          return Math.max(0, Math.min(100, ((clientX - rect.left) / rect.width) * 100));
        };
        const waveMouseDown = (e) => {
          const idx = selectedTrackIdx.value;
          if (!trackPeaks[idx]) return;
          const x = waveXToPct(e.clientX);
          const p = trackParams.value[idx];
          waveDrag = Math.abs(x - p.sampleStart) <= Math.abs(x - p.sampleEnd) ? 'start' : 'end';
          applyWaveDrag(x);
        };
        const applyWaveDrag = (x) => {
          if (!waveDrag) return;
          const p = trackParams.value[selectedTrackIdx.value];
          if (waveDrag === 'start') p.sampleStart = Math.min(x, p.sampleEnd - 1);
          else p.sampleEnd = Math.max(x, p.sampleStart + 1);
        };
        const onWindowMove = (e) => { if (waveDrag) applyWaveDrag(waveXToPct(e.clientX)); };
        const onWindowUp = () => { waveDrag = null; painting = false; };

        onMounted(() => {
          window.addEventListener('mousemove', onWindowMove);
          window.addEventListener('mouseup', onWindowUp);
        });
        onUnmounted(() => {
          if (animationFrame) cancelAnimationFrame(animationFrame);
          window.removeEventListener('mousemove', onWindowMove);
          window.removeEventListener('mouseup', onWindowUp);
          try { Tone.Transport.stop(); } catch (e) {}
        });

        const togglePlay = () => {
          if (!isPlaying.value) {
            if (Tone.context.state !== 'running') Tone.context.resume();
            Tone.Transport.start();
            isPlaying.value = true;
          } else {
            Tone.Transport.pause();
            isPlaying.value = false;
          }
        };

        const stopPlayback = () => {
          Tone.Transport.stop();
          stepCount = 0;
          playingStep.value = 0;
          isPlaying.value = false;
        };

        const previewSample = (i) => {
          if (Tone.context.state !== 'running') Tone.context.resume();
          triggerHit(i, ROOT_NOTE, Tone.now() + 0.02);
        };
        const previewSlice = (i, slice, total) => {
          const player = players[i];
          if (!player || !player.loaded || !player.buffer) return;
          if (Tone.context.state !== 'running') Tone.context.resume();
          const buffer = player.buffer;
          const dur = buffer.duration;
          const startSec = (slice / total) * dur;
          const windowDur = Math.max(0.02, (1 / total) * dur);
          try {
            const src = new Tone.ToneBufferSource(buffer).connect(channels[i]);
            src.fadeOut = 0.005;
            src.start(Tone.now() + 0.02, startSec, windowDur);
            src.onended = () => { try { src.dispose(); } catch (e) {} };
          } catch (e) {}
        };

        const chopToTracks = (trackIndex) => {
          const player = players[trackIndex];
          if (!player || !player.loaded) return alert('Sample not loaded for this track.');
          const count = Math.max(2, Math.min(16, Math.round(trackParams.value[trackIndex].chopCount)));
          const orig = tracks.value[trackIndex];
          const buffer = player.buffer;

          for (let s = 0; s < count; s++) {
            const start = (s / count) * 100;
            const end = ((s + 1) / count) * 100;
            const newTrack = {
              id: orig.id + '_chop' + s + '_' + Date.now(),
              name: orig.name + ' [' + (s + 1) + ']',
              color: orig.color, url: orig.url, offline: false
            };
            const newParams = defaultParams(trackParams.value[trackIndex].vol);
            newParams.pan = trackParams.value[trackIndex].pan;
            newParams.sampleStart = start;
            newParams.sampleEnd = end;
            const gridRow = Array(STEPS).fill(null).map(() => ({ active: false, note: 'C3' }));

            tracks.value.push(newTrack);
            grid.value.push(gridRow);
            trackParams.value.push(newParams);
            setupTrackNodes(tracks.value.length - 1, newParams, buffer);
          }
          selectedTrackIdx.value = tracks.value.length - count;
        };

        const duplicateTrack = (trackIndex) => {
          const origTrack = tracks.value[trackIndex];
          const newTrack = {
            id: origTrack.id + '_copy_' + Date.now(),
            name: origTrack.name + ' (Copy)',
            color: origTrack.color, url: origTrack.url, offline: origTrack.offline
          };
          const newGridRow = grid.value[trackIndex].map((s) => ({ ...s }));
          const newParams = { ...trackParams.value[trackIndex] };

          tracks.value.push(newTrack);
          grid.value.push(newGridRow);
          trackParams.value.push(newParams);

          if (engineInitialized) {
            const buffer = players[trackIndex] ? players[trackIndex].buffer : null;
            setupTrackNodes(tracks.value.length - 1, newParams, buffer);
          }
        };

        // --- Delete a track and tear down its audio nodes ---
        const deleteTrack = (trackIndex) => {
          if (trackIndex < 0 || trackIndex >= tracks.value.length) return;

          // Dispose this track's audio nodes.
          try { if (players[trackIndex]) players[trackIndex].dispose(); } catch (e) {}
          [channels, revSends, dlySends, choSends, phaSends, dstSends, fltSends].forEach((arr) => {
            try { if (arr[trackIndex]) arr[trackIndex].dispose(); } catch (e) {}
          });

          // Splice the matching index out of every parallel array.
          players.splice(trackIndex, 1);
          channels.splice(trackIndex, 1);
          revSends.splice(trackIndex, 1);
          dlySends.splice(trackIndex, 1);
          choSends.splice(trackIndex, 1);
          phaSends.splice(trackIndex, 1);
          dstSends.splice(trackIndex, 1);
          fltSends.splice(trackIndex, 1);

          tracks.value.splice(trackIndex, 1);
          grid.value.splice(trackIndex, 1);
          trackParams.value.splice(trackIndex, 1);

          // Index-keyed peaks have shifted — rebuild from the remaining players.
          Object.keys(trackPeaks).forEach((k) => { delete trackPeaks[k]; });
          for (let k = 0; k < players.length; k++) {
            if (players[k] && players[k].loaded && players[k].buffer) computePeaks(k, players[k].buffer);
          }

          if (selectedTrackIdx.value >= tracks.value.length) {
            selectedTrackIdx.value = Math.max(0, tracks.value.length - 1);
          }
        };

        const clearTrack = (i) => { grid.value[i].forEach((s) => { s.active = false; }); };
        const randomizeTrack = (i) => {
          grid.value[i].forEach((s) => {
            s.active = Math.random() < 0.3;
            if (s.active) s.note = SCALE[Math.floor(Math.random() * SCALE.length)];
          });
        };

        const exportAudio = async () => {
          if (!engineInitialized || isRecording.value) return;
          isRecording.value = true;
          recorder = new Tone.Recorder();
          Tone.Destination.connect(recorder);
          Tone.Transport.stop();
          stepCount = 0; playingStep.value = 0;
          recorder.start();
          Tone.Transport.start();
          isPlaying.value = true;

          const durationMs = STEPS * (15000 / bpm.value);
          setTimeout(async () => {
            Tone.Transport.stop();
            isPlaying.value = false;
            stepCount = 0; playingStep.value = 0;
            const recording = await recorder.stop();
            const url = URL.createObjectURL(recording);
            const anchor = document.createElement('a');
            anchor.download = 'BeatRoyale_Export.webm';
            anchor.href = url;
            anchor.click();
            URL.revokeObjectURL(url);
            isRecording.value = false;
            Tone.Destination.disconnect(recorder);
          }, durationMs + 2500);
        };

        const exportMidi = () => {
          const hasNotes = grid.value.some((row) => row.some((s) => s.active));
          if (!hasNotes) return alert('No active notes to export!');
          const data = buildMidiFile(tracks.value, grid.value, bpm.value);
          const blob = new Blob([data], { type: 'audio/midi' });
          const url = URL.createObjectURL(blob);
          const anchor = document.createElement('a');
          anchor.download = 'BeatRoyale_Export.mid';
          anchor.href = url;
          anchor.click();
          URL.revokeObjectURL(url);
        };

        const updateBpm = (e) => {
          const val = Number(e.target.value);
          bpm.value = val;
          if (engineInitialized) Tone.Transport.bpm.value = val;
        };
        const updateSwing = (e) => { swing.value = Number(e.target.value); };
        const toggleMetronome = () => { metronomeOn.value = !metronomeOn.value; };

        const updateMasterVol = (e) => {
          const val = Number(e.target.value);
          masterVolume.value = val;
          if (engineInitialized) Tone.Destination.volume.value = val;
        };

        const toggleStep = (trackIndex, stepIndex) => {
          grid.value[trackIndex][stepIndex].active = !grid.value[trackIndex][stepIndex].active;
        };
        // Click-and-drag painting across step cells.
        const startPaint = (trackIndex, stepIndex) => {
          if (isRecording.value) return;
          const cell = grid.value[trackIndex][stepIndex];
          paintValue = !cell.active;   // first cell sets the brush (on if it was off)
          cell.active = paintValue;
          painting = true;
        };
        const paintEnter = (trackIndex, stepIndex) => {
          if (!painting || isRecording.value) return;
          const cell = grid.value[trackIndex][stepIndex];
          if (cell.active !== paintValue) cell.active = paintValue;
        };
        const updateStepNote = (trackIndex, stepIndex, note) => {
          grid.value[trackIndex][stepIndex].note = note;
        };

        const handleParamChange = (trackIndex, param, value) => {
          const numValue = Number(value);
          trackParams.value[trackIndex][param] = numValue;
          if (!engineInitialized) return;
          if (param === 'vol') channels[trackIndex].volume.value = numValue;
          if (param === 'pan') channels[trackIndex].pan.value = numValue;
          if (param === 'revSend') revSends[trackIndex].volume.value = numValue;
          if (param === 'dlySend') dlySends[trackIndex].volume.value = numValue;
          if (param === 'choSend') choSends[trackIndex].volume.value = numValue;
          if (param === 'phaSend') phaSends[trackIndex].volume.value = numValue;
          if (param === 'dstSend') dstSends[trackIndex].volume.value = numValue;
          if (param === 'fltSend') fltSends[trackIndex].volume.value = numValue;
        };

        // --- Granular global FX parameter control ---
        const updateFx = (key, value) => {
          const v = Number(value);
          fxParams.value[key] = v;
          if (!engineInitialized) return;
          try {
            switch (key) {
              case 'revDecay': reverbNode.decay = v; if (reverbNode.generate) reverbNode.generate(); break;
              case 'revWet':   reverbNode.wet.value = v; break;
              case 'dlyFeed':  delayNode.feedback.value = v; break;
              case 'dlyWet':   delayNode.wet.value = v; break;
              case 'dstAmt':   distortionNode.distortion = v; break;
              case 'dstWet':   distortionNode.wet.value = v; break;
              case 'fltRate':  autoFilterNode.frequency.value = v; break;
              case 'fltWet':   autoFilterNode.wet.value = v; break;
              case 'choDepth': chorusNode.depth = v; break;
              case 'choWet':   chorusNode.wet.value = v; break;
              case 'phaRate':  phaserNode.frequency.value = v; break;
              case 'phaWet':   phaserNode.wet.value = v; break;
            }
          } catch (e) {}
        };

        const toggleMuteSolo = (trackIndex, type) => {
          trackParams.value[trackIndex][type] = !trackParams.value[trackIndex][type];
          if (!engineInitialized) return;
          if (type === 'mute') channels[trackIndex].mute = trackParams.value[trackIndex].mute;
          if (type === 'solo') channels[trackIndex].solo = trackParams.value[trackIndex].solo;
        };

        const getNoteIndex = (note) => Math.max(0, SCALE.indexOf(note));

        return {
          isAudioReady, isLoading, isPlaying, isRecording, bpm, swing, metronomeOn, playingStep, masterVolume, loadStatus,
          selectedTrackIdx, tracks, grid, trackParams, fxParams, canvasRef, waveCanvasRef,
          initializeAudio, togglePlay, stopPlayback, updateBpm, updateSwing, toggleMetronome, updateMasterVol,
          toggleStep, startPaint, paintEnter, updateStepNote, handleParamChange, updateFx, toggleMuteSolo, getNoteIndex,
          duplicateTrack, exportAudio, exportMidi,
          previewSample, previewSlice, chopToTracks, waveMouseDown,
          deleteTrack, clearTrack, randomizeTrack,
          STEPS, SCALE
        };
      },

      template: `
        <div v-if="!isAudioReady" class="h-screen w-screen flex flex-col items-center justify-center space-y-6 relative">
          <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-blue-400 animate-pulse w-10 h-10">
            <polyline points="22 12 18 12 15 21 9 3 6 12 2 12"></polyline>
          </svg>
          <h1 class="text-xl font-bold tracking-[0.3em] text-neutral-200">BEAT ROYALE <span class="text-blue-400">DAW</span></h1>
          <p class="text-neutral-500 max-w-sm text-center text-[10px]">
            Fetching exact sample mapping from JSON backend.
          </p>
          <button
            @click="initializeAudio"
            :disabled="isLoading"
            :class="[
              'px-5 py-2 rounded text-xs font-semibold transition-all shadow-[0_0_15px_rgba(90,116,147,0.2)]',
              isLoading ? 'bg-neutral-900 text-neutral-600 cursor-not-allowed' : 'bg-blue-600/90 hover:bg-blue-500 text-white'
            ]"
          >
            {{ isLoading ? 'Downloading Assets...' : 'Launch Engine' }}
          </button>
          <p v-if="isLoading" class="text-[9px] font-mono text-neutral-600 h-3">{{ loadStatus }}</p>
        </div>

        <div v-else class="h-screen w-screen flex flex-col relative bg-[#0a0a0a]">

          <!-- Top Transport Bar -->
          <header class="h-10 bg-[#0d0d0d] border-b border-neutral-800 flex items-center px-4 justify-between shrink-0">
            <div class="flex items-center gap-2 w-1/4">
              <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-blue-400 w-4 h-4">
                <rect width="20" height="14" x="2" y="3" rx="2"/><path d="M12 17v4"/><path d="M8 21h8"/><path d="m10 7 5 3-5 3Z"/>
              </svg>
              <h1 class="text-[10px] font-black tracking-[0.2em] text-neutral-200 hidden sm:block">
                BEAT <span class="text-blue-400">ROYALE</span>
              </h1>
            </div>

            <!-- Transport Controls -->
            <div class="flex items-center gap-1 bg-neutral-950 p-1 rounded border border-neutral-800 shadow-inner">
              <button @click="togglePlay" :disabled="isRecording" :class="['p-1 rounded flex items-center justify-center transition-all', isPlaying ? 'bg-blue-600 text-white shadow-[0_0_8px_rgba(90,116,147,0.5)]' : 'bg-neutral-900 text-neutral-400 hover:text-white', isRecording ? 'opacity-50' : '']">
                <svg viewBox="0 0 24 24" :fill="isPlaying ? 'currentColor' : 'none'" stroke="currentColor" stroke-width="2" class="w-3 h-3"><polygon points="6 3 20 12 6 21 6 3"></polygon></svg>
              </button>
              <button @click="stopPlayback" :disabled="isRecording" class="p-1 rounded bg-neutral-900 text-neutral-400 hover:text-white transition-colors disabled:opacity-50">
                <svg viewBox="0 0 24 24" fill="currentColor" stroke="currentColor" stroke-width="2" class="w-3 h-3"><rect width="18" height="18" x="3" y="3" rx="2"></rect></svg>
              </button>
              <div class="h-4 w-px bg-neutral-800 mx-1"></div>
              <div class="flex items-center gap-1 px-1">
                <span class="text-[8px] font-bold text-neutral-500 tracking-wider">BPM</span>
                <input type="number" :value="bpm" @input="updateBpm" :disabled="isRecording" class="w-8 bg-transparent text-white font-mono text-center text-[10px] focus:outline-none focus:text-blue-300 disabled:opacity-50" min="60" max="240" />
              </div>
              <div class="h-4 w-px bg-neutral-800 mx-1"></div>
              <button @click="toggleMetronome" title="Metronome" :class="['p-1 rounded transition-all', metronomeOn ? 'bg-blue-600 text-white shadow-[0_0_8px_rgba(90,116,147,0.5)]' : 'bg-neutral-900 text-neutral-400 hover:text-white']">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="w-3 h-3"><path d="m12 2 7 19H5L12 2z"/><line x1="12" y1="2" x2="17" y2="13"/></svg>
              </button>
              <div class="flex items-center gap-1 px-1" title="Swing / shuffle amount">
                <span class="text-[8px] font-bold text-neutral-500 tracking-wider">SWG</span>
                <input type="range" min="0" max="0.7" step="0.05" :value="swing" @input="updateSwing" class="w-10 h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-blue-400" />
              </div>
            </div>

            <div class="flex items-center gap-2 w-1/4 justify-end">
               <button @click="exportAudio" :disabled="isRecording || tracks.length === 0" class="hidden md:flex items-center gap-1 px-2 py-1 bg-neutral-900 hover:bg-neutral-800 text-neutral-400 hover:text-white rounded border border-neutral-800 transition-all text-[8px] font-bold uppercase tracking-wider disabled:opacity-50">
                  <svg v-if="isRecording" class="animate-spin w-2.5 h-2.5 text-red-400" xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24"><circle class="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" stroke-width="4"></circle><path class="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"></path></svg>
                  <svg v-else viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="w-2.5 h-2.5"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
                  {{ isRecording ? 'Rendering...' : 'Audio' }}
               </button>
               <button @click="exportMidi" :disabled="isRecording || tracks.length === 0" class="hidden md:flex items-center gap-1 px-2 py-1 bg-neutral-900 hover:bg-neutral-800 text-neutral-400 hover:text-white rounded border border-neutral-800 transition-all text-[8px] font-bold uppercase tracking-wider disabled:opacity-50">
                  <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="w-2.5 h-2.5"><path d="M9 18V5l12-2v13"/><circle cx="6" cy="18" r="3"/><circle cx="18" cy="16" r="3"/></svg>
                  MIDI
               </button>

               <div class="hidden lg:flex flex-col items-center mr-2 ml-2">
                  <canvas ref="canvasRef" width="60" height="14" class="bg-neutral-950 rounded-sm border border-neutral-800 shadow-inner" />
               </div>
              <div class="flex items-center gap-1.5 bg-[#0d0d0d] px-2 py-1 rounded border border-neutral-800">
                <svg v-if="masterVolume < -50" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" class="text-neutral-600 w-3 h-3"><polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"></polygon><line x1="23" x2="17" y1="9" y2="15"></line><line x1="17" x2="23" y1="9" y2="15"></line></svg>
                <svg v-else viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" class="text-neutral-400 w-3 h-3"><polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"></polygon><path d="M15.54 8.46a5 5 0 0 1 0 7.07"></path><path d="M19.07 4.93a10 10 0 0 1 0 14.14"></path></svg>
                <input type="range" min="-60" max="0" :value="masterVolume" @input="updateMasterVol" class="text-blue-400 w-12 h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer" />
              </div>
            </div>
          </header>

          <!-- Main Workspace -->
          <main class="flex-1 flex overflow-hidden p-3 relative">
            <div v-if="tracks.length === 0" class="text-neutral-500 text-xs italic w-full text-center mt-10">
                No tracks loaded — import a sample below or check your samples.json file.
            </div>

            <div v-else class="flex-1 flex overflow-y-auto overflow-x-hidden min-w-0">
               <!-- Sticky Track Headers -->
               <div class="w-36 shrink-0 flex flex-col gap-1.5 z-20 sticky left-0 bg-[#0a0a0a] pr-2 border-r border-neutral-800">
                  <div class="h-4 flex items-end pb-1 px-1 mb-2">
                     <span class="text-[8px] uppercase font-bold text-neutral-600 tracking-widest">Tracks</span>
                  </div>

                  <div v-for="(track, trackIndex) in tracks" :key="track.id" class="flex flex-col gap-1.5 group h-8 justify-center">
                     <div
                       @click="selectedTrackIdx = trackIndex"
                       :class="['w-full rounded border p-1 flex items-center justify-between cursor-pointer transition-colors', selectedTrackIdx === trackIndex ? 'bg-neutral-800 border-blue-500/40 shadow-sm' : 'bg-[#121212] border-neutral-800 hover:border-neutral-700']"
                     >
                       <div class="flex items-center gap-1.5 overflow-hidden">
                         <div :class="['w-1.5 h-1.5 rounded-full opacity-90 shrink-0', track.offline ? 'bg-neutral-600' : track.color]"></div>
                         <span :class="['font-semibold text-[10px] truncate', selectedTrackIdx === trackIndex ? 'text-white' : 'text-neutral-400']" :title="track.name">{{ track.name }}</span>
                         <span v-if="track.offline" class="text-[6px] font-bold uppercase text-red-400/80 border border-red-400/40 rounded px-0.5 shrink-0">off</span>
                       </div>
                       <div class="flex gap-0.5 shrink-0 items-center" @click.stop>
                         <button @click="duplicateTrack(trackIndex)" title="Duplicate Track" class="w-3.5 h-3.5 rounded text-neutral-500 hover:text-white transition-colors flex items-center justify-center mr-0.5">
                           <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="w-2.5 h-2.5"><rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path></svg>
                         </button>
                         <button @click="deleteTrack(trackIndex)" title="Delete Sample" class="w-3.5 h-3.5 rounded text-neutral-600 hover:text-red-400 transition-colors flex items-center justify-center mr-0.5">
                           <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="w-2.5 h-2.5"><path d="M3 6h18"/><path d="M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"/></svg>
                         </button>
                         <button @click="toggleMuteSolo(trackIndex, 'mute')" :class="['w-4 h-4 rounded text-[7px] font-bold transition-all flex items-center justify-center', trackParams[trackIndex].mute ? 'bg-red-500/20 text-red-400 border border-red-500/50' : 'bg-transparent text-neutral-600 hover:text-neutral-400 border border-transparent']">M</button>
                         <button @click="toggleMuteSolo(trackIndex, 'solo')" :class="['w-4 h-4 rounded text-[7px] font-bold transition-all flex items-center justify-center', trackParams[trackIndex].solo ? 'bg-yellow-500/20 text-yellow-400 border border-yellow-500/50' : 'bg-transparent text-neutral-600 hover:text-neutral-400 border border-transparent']">S</button>
                       </div>
                     </div>
                  </div>
               </div>

               <!-- Scrolling Grid + Pitch Lane -->
               <div class="flex flex-col gap-1.5 pl-2 relative flex-1 min-w-0">
                  <!-- Steps Header -->
                  <div class="flex gap-0.5 w-full mb-2 h-4">
                     <div v-for="(_, i) in STEPS" :key="i" class="flex-1 min-w-0 h-4 flex justify-center items-end relative">
                        <span :class="['text-[7px] font-mono font-bold', i % 4 === 0 ? 'text-neutral-500' : 'text-neutral-700', i === playingStep ? 'text-blue-300' : '']">
                           {{ i + 1 }}
                        </span>
                        <div v-if="i === playingStep" class="absolute bottom-0 w-full h-px bg-blue-500 shadow-[0_-1px_3px_rgba(90,116,147,0.8)]"></div>
                     </div>
                  </div>

                  <!-- Grid Rows -->
                  <div v-for="(track, trackIndex) in tracks" :key="'grid_'+track.id" class="flex gap-0.5 w-full h-8 items-center p-0.5 rounded border border-transparent select-none" :class="selectedTrackIdx === trackIndex ? 'bg-neutral-900/40' : ''">
                     <div v-for="(step, stepIndex) in grid[trackIndex]" :key="stepIndex" class="relative group/step flex-1 min-w-0" @mousedown.prevent="startPaint(trackIndex, stepIndex)" @mouseenter="paintEnter(trackIndex, stepIndex)">
                        <button
                           :disabled="isRecording"
                           :class="[
                           'w-full h-6 rounded-sm border transition-all duration-75 block',
                           step.active ? track.color + ' border-transparent shadow-[0_1px_4px_rgba(0,0,0,0.4)] opacity-90' : 'bg-neutral-950 border-neutral-800 hover:bg-neutral-800',
                           (stepIndex % 4 === 0 && !step.active) ? 'bg-neutral-900/60' : '',
                           (stepIndex === playingStep) ? 'ring-1 ring-white/40 z-10 scale-105' : '',
                           (stepIndex === playingStep && step.active) ? 'brightness-110 saturate-125' : '',
                           isRecording ? 'opacity-70 pointer-events-none' : ''
                           ]"
                        >
                           <div v-if="step.active" class="absolute inset-0 bg-gradient-to-b from-white/10 to-transparent rounded-sm pointer-events-none"></div>
                        </button>

                        <select
                           v-if="step.active && !isRecording"
                           :value="step.note"
                           @change="updateStepNote(trackIndex, stepIndex, $event.target.value)"
                           @click.stop
                           @mousedown.stop
                           class="absolute bottom-0 left-0 w-full text-[6px] text-center font-mono bg-black/80 text-white border-none outline-none appearance-none cursor-pointer rounded-b-sm opacity-0 group-hover/step:opacity-100 transition-opacity z-20"
                           style="text-align-last: center"
                        >
                           <option v-for="n in SCALE" :key="n" :value="n" class="bg-neutral-900">{{ n }}</option>
                        </select>

                        <span v-if="step.active" class="absolute inset-0 flex items-center justify-center text-[7px] font-bold text-black/60 font-mono pointer-events-none opacity-100 group-hover/step:opacity-0 transition-opacity">
                           {{ step.note.replace(/[0-9]/g, '') }}
                        </span>
                     </div>
                  </div>

                  <!-- Pitch Lane (relocated here, below the tracks) -->
                  <div class="mt-3 pt-2 border-t border-neutral-800 w-full">
                     <div class="text-[8px] font-bold text-neutral-500 uppercase tracking-wider mb-1 flex items-center gap-2">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="w-2.5 h-2.5"><path d="M9 18V5l12-2v13"/><circle cx="6" cy="18" r="3"/><circle cx="18" cy="16" r="3"/></svg>
                        <span>Pitch Lane — <span class="text-blue-300">{{ tracks[selectedTrackIdx]?.name }}</span></span>
                        <button @click="clearTrack(selectedTrackIdx)" class="px-1.5 py-0.5 rounded border border-neutral-800 bg-neutral-900 hover:bg-neutral-800 text-neutral-500 hover:text-white text-[7px] font-bold uppercase tracking-wider transition-colors">Clear</button>
                        <button @click="randomizeTrack(selectedTrackIdx)" class="px-1.5 py-0.5 rounded border border-neutral-800 bg-neutral-900 hover:bg-neutral-800 text-neutral-500 hover:text-blue-300 text-[7px] font-bold uppercase tracking-wider transition-colors">Rand</button>
                     </div>
                     <div class="flex gap-0.5 h-32 items-end w-full">
                        <div v-for="(step, stepIndex) in grid[selectedTrackIdx]" :key="'pitch_'+stepIndex" class="flex-1 min-w-0 flex flex-col items-center gap-1 h-full justify-end group/pitch">
                           <div :class="['relative w-full flex-1 flex flex-col justify-end bg-neutral-950 rounded-sm border overflow-hidden hover:border-neutral-600', stepIndex === playingStep ? 'border-blue-500/60' : 'border-neutral-800']">
                              <div
                                :class="['w-full rounded-sm transition-all duration-100', step.active ? tracks[selectedTrackIdx].color : 'bg-neutral-800']"
                                :style="{ height: Math.max(5, (getNoteIndex(step.note) / (SCALE.length - 1)) * 100) + '%', opacity: step.active ? 0.9 : 0.2 }"
                              ></div>
                              <input
                                type="range" min="0" :max="SCALE.length - 1" :value="getNoteIndex(step.note)"
                                @input="updateStepNote(selectedTrackIdx, stepIndex, SCALE[Number($event.target.value)])"
                                class="absolute inset-0 w-full h-full opacity-0 cursor-pointer appearance-none z-10"
                                style="writing-mode: bt-lr; -webkit-appearance: slider-vertical;"
                              />
                           </div>
                           <span :class="['text-[6px] font-mono', step.active ? 'text-neutral-400' : 'text-neutral-700']">{{ step.note }}</span>
                        </div>
                     </div>
                  </div>
               </div>
            </div>
          </main>

          <!-- Bottom Device Rack -->
          <footer class="h-64 bg-[#121212] border-t border-neutral-800 flex flex-col shrink-0 z-20">
            <div class="h-5 bg-neutral-950 border-b border-neutral-800 flex items-center px-3 gap-1">
              <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" class="text-neutral-600 w-2 h-2"><circle cx="12" cy="12" r="3"></circle><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1 0 2.83 2 2 0 0 1-2.83 0l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-2 2 2 2 0 0 1-2-2v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83 0 2 2 0 0 1 0-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1-2-2 2 2 0 0 1 2-2h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 0-2.83 2 2 0 0 1 2.83 0l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 2-2 2 2 0 0 1 2 2v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 0 2 2 0 0 1 0 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 2 2 2 2 0 0 1-2 2h-.09a1.65 1.65 0 0 0-1.51 1z"></path></svg>
              <span v-if="tracks.length > 0" class="text-[8px] font-bold text-neutral-500 uppercase tracking-widest">Device Rack: <span class="text-blue-300">{{ tracks[selectedTrackIdx]?.name }}</span></span>
              <span v-else class="text-[8px] font-bold text-neutral-500 uppercase tracking-widest">No Tracks Loaded</span>
            </div>

            <div v-if="tracks.length > 0" class="flex-1 flex overflow-hidden">
              <!-- Mixer -->
              <div class="w-32 border-r border-neutral-800 p-2 flex flex-col gap-2 bg-[#0d0d0d] shrink-0">
                <div class="text-[8px] font-bold text-neutral-500 uppercase tracking-wider flex items-center gap-1">
                  <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" class="w-2 h-2"><line x1="21" x2="14" y1="4" y2="4"></line><line x1="10" x2="3" y1="4" y2="4"></line><line x1="21" x2="12" y1="12" y2="12"></line><line x1="8" x2="3" y1="12" y2="12"></line><line x1="21" x2="16" y1="20" y2="20"></line><line x1="12" x2="3" y1="20" y2="20"></line><line x1="14" x2="14" y1="2" y2="6"></line><line x1="8" x2="8" y1="10" y2="14"></line><line x1="16" x2="16" y1="18" y2="22"></line></svg>
                  Mixer
                </div>
                <div class="space-y-2">
                  <div class="flex items-center justify-between">
                    <span class="text-[7px] font-mono text-neutral-600 uppercase">Vol</span>
                    <input type="range" min="-60" max="10" :value="trackParams[selectedTrackIdx].vol" @input="handleParamChange(selectedTrackIdx, 'vol', $event.target.value)" class="w-14 h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-blue-400" />
                    <span class="text-[7px] font-mono text-neutral-500 w-4 text-right">{{ trackParams[selectedTrackIdx].vol.toFixed(0) }}</span>
                  </div>
                  <div class="flex items-center justify-between">
                    <span class="text-[7px] font-mono text-neutral-600 uppercase">Pan</span>
                    <input type="range" min="-1" max="1" step="0.1" :value="trackParams[selectedTrackIdx].pan" @input="handleParamChange(selectedTrackIdx, 'pan', $event.target.value)" class="w-14 h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-emerald-400" />
                    <span class="text-[7px] font-mono text-neutral-500 w-4 text-right">{{ trackParams[selectedTrackIdx].pan.toFixed(1) }}</span>
                  </div>
                </div>
              </div>

              <!-- Sampler: Waveform + Trim + Chop -->
              <div class="w-72 border-r border-neutral-800 p-2 flex flex-col gap-1.5 bg-[#0d0d0d] shrink-0">
                <div class="text-[8px] font-bold text-neutral-500 uppercase tracking-wider flex items-center justify-between gap-1">
                  <span class="flex items-center gap-1">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" class="w-2 h-2"><path d="M2 12h2l2-7 4 18 3-11 2 4h7"/></svg>
                    Sampler
                  </span>
                  <button @click="previewSample(selectedTrackIdx)" title="Audition trimmed sample" class="flex items-center gap-1 px-1.5 py-0.5 bg-neutral-900 hover:bg-neutral-800 text-neutral-400 hover:text-white rounded border border-neutral-800 text-[7px] font-bold uppercase tracking-wider">
                    <svg viewBox="0 0 24 24" fill="currentColor" class="w-2 h-2"><polygon points="6 3 20 12 6 21 6 3"></polygon></svg>
                    Play
                  </button>
                </div>

                <canvas
                  ref="waveCanvasRef" width="272" height="46"
                  @mousedown="waveMouseDown"
                  class="wave-canvas bg-neutral-950 rounded-sm border border-neutral-800 w-full shadow-inner select-none"
                ></canvas>

                <div class="grid grid-cols-2 gap-x-3 gap-y-1">
                  <div class="flex flex-col gap-0.5">
                    <div class="flex justify-between"><span class="text-[7px] font-mono text-[#6f9a7c] uppercase">Start</span><span class="text-[7px] font-mono text-neutral-500">{{ trackParams[selectedTrackIdx].sampleStart.toFixed(0) }}%</span></div>
                    <input type="range" min="0" max="100" step="0.5" :value="trackParams[selectedTrackIdx].sampleStart" @input="handleParamChange(selectedTrackIdx, 'sampleStart', Math.min($event.target.value, trackParams[selectedTrackIdx].sampleEnd - 1))" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-[#6f9a7c]" />
                  </div>
                  <div class="flex flex-col gap-0.5">
                    <div class="flex justify-between"><span class="text-[7px] font-mono text-[#9b6a6a] uppercase">End</span><span class="text-[7px] font-mono text-neutral-500">{{ trackParams[selectedTrackIdx].sampleEnd.toFixed(0) }}%</span></div>
                    <input type="range" min="0" max="100" step="0.5" :value="trackParams[selectedTrackIdx].sampleEnd" @input="handleParamChange(selectedTrackIdx, 'sampleEnd', Math.max($event.target.value, trackParams[selectedTrackIdx].sampleStart + 1))" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-[#9b6a6a]" />
                  </div>
                </div>

                <div class="flex items-center gap-1.5 pt-0.5 border-t border-neutral-800/60 mt-0.5">
                  <span class="text-[7px] font-mono text-[#9a9166] uppercase tracking-wider">Chop</span>
                  <input type="range" min="2" max="16" step="1" :value="trackParams[selectedTrackIdx].chopCount" @input="handleParamChange(selectedTrackIdx, 'chopCount', $event.target.value)" class="flex-1 h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-[#9a9166]" />
                  <span class="text-[7px] font-mono text-neutral-500 w-3 text-right">{{ trackParams[selectedTrackIdx].chopCount }}</span>
                  <button @click="chopToTracks(selectedTrackIdx)" title="Slice into separate tracks" class="px-1.5 py-0.5 bg-[#9a9166]/15 hover:bg-[#9a9166]/25 text-[#b3a878] rounded border border-[#9a9166]/40 text-[7px] font-bold uppercase tracking-wider transition-colors">
                    Slice →
                  </button>
                </div>
                <div class="flex flex-wrap gap-0.5">
                  <button v-for="s in trackParams[selectedTrackIdx].chopCount" :key="s"
                    @click="previewSlice(selectedTrackIdx, s - 1, trackParams[selectedTrackIdx].chopCount)"
                    class="flex-1 min-w-[14px] h-3.5 rounded-sm bg-neutral-900 hover:bg-[#9a9166]/25 border border-neutral-800 text-[6px] font-mono text-neutral-500 hover:text-[#b3a878] transition-colors">
                    {{ s }}
                  </button>
                </div>
              </div>

              <!-- Aux Sends -->
              <div class="w-56 border-r border-neutral-800 p-2 flex flex-col gap-1.5 bg-[#0d0d0d] shrink-0">
                <div class="text-[8px] font-bold text-neutral-500 uppercase tracking-wider flex items-center gap-1">
                  <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" class="w-2 h-2"><path d="M5 16v2"/><path d="M19 16v2"/><rect width="20" height="8" x="2" y="8" rx="2"/><path d="M18 9h.01"/><path d="M8 8v6"/><path d="M16 11.5v3"/><path d="M12 11.5v3"/><path d="M16 5c-4.48-1.5-11.45.69-14 4"/></svg>
                  Aux Sends
                </div>
                <div class="grid grid-cols-2 gap-x-3 gap-y-1.5">
                  <div class="flex flex-col gap-0.5">
                    <div class="flex justify-between"><span class="text-[7px] font-mono text-neutral-600 uppercase">Reverb</span><span class="text-[7px] font-mono text-neutral-500">{{ trackParams[selectedTrackIdx].revSend <= -60 ? '-∞' : trackParams[selectedTrackIdx].revSend.toFixed(0) }}</span></div>
                    <input type="range" min="-60" max="0" :value="trackParams[selectedTrackIdx].revSend" @input="handleParamChange(selectedTrackIdx, 'revSend', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-purple-400" />
                  </div>
                  <div class="flex flex-col gap-0.5">
                     <div class="flex justify-between"><span class="text-[7px] font-mono text-neutral-600 uppercase">Delay</span><span class="text-[7px] font-mono text-neutral-500">{{ trackParams[selectedTrackIdx].dlySend <= -60 ? '-∞' : trackParams[selectedTrackIdx].dlySend.toFixed(0) }}</span></div>
                    <input type="range" min="-60" max="0" :value="trackParams[selectedTrackIdx].dlySend" @input="handleParamChange(selectedTrackIdx, 'dlySend', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-pink-400" />
                  </div>
                  <div class="flex flex-col gap-0.5">
                     <div class="flex justify-between"><span class="text-[7px] font-mono text-neutral-600 uppercase">Chorus</span><span class="text-[7px] font-mono text-neutral-500">{{ trackParams[selectedTrackIdx].choSend <= -60 ? '-∞' : trackParams[selectedTrackIdx].choSend.toFixed(0) }}</span></div>
                    <input type="range" min="-60" max="0" :value="trackParams[selectedTrackIdx].choSend" @input="handleParamChange(selectedTrackIdx, 'choSend', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-indigo-400" />
                  </div>
                  <div class="flex flex-col gap-0.5">
                     <div class="flex justify-between"><span class="text-[7px] font-mono text-neutral-600 uppercase">Phaser</span><span class="text-[7px] font-mono text-neutral-500">{{ trackParams[selectedTrackIdx].phaSend <= -60 ? '-∞' : trackParams[selectedTrackIdx].phaSend.toFixed(0) }}</span></div>
                    <input type="range" min="-60" max="0" :value="trackParams[selectedTrackIdx].phaSend" @input="handleParamChange(selectedTrackIdx, 'phaSend', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-orange-400" />
                  </div>
                  <div class="flex flex-col gap-0.5">
                     <div class="flex justify-between"><span class="text-[7px] font-mono text-neutral-600 uppercase">Drive</span><span class="text-[7px] font-mono text-neutral-500">{{ trackParams[selectedTrackIdx].dstSend <= -60 ? '-∞' : trackParams[selectedTrackIdx].dstSend.toFixed(0) }}</span></div>
                    <input type="range" min="-60" max="0" :value="trackParams[selectedTrackIdx].dstSend" @input="handleParamChange(selectedTrackIdx, 'dstSend', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-rose-400" />
                  </div>
                  <div class="flex flex-col gap-0.5">
                     <div class="flex justify-between"><span class="text-[7px] font-mono text-neutral-600 uppercase">Filter</span><span class="text-[7px] font-mono text-neutral-500">{{ trackParams[selectedTrackIdx].fltSend <= -60 ? '-∞' : trackParams[selectedTrackIdx].fltSend.toFixed(0) }}</span></div>
                    <input type="range" min="-60" max="0" :value="trackParams[selectedTrackIdx].fltSend" @input="handleParamChange(selectedTrackIdx, 'fltSend', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-cyan-400" />
                  </div>
                </div>
              </div>

              <!-- FX Rack: granular global effect parameters -->
              <div class="flex-1 p-2 overflow-hidden bg-neutral-900/50 min-w-[280px] flex flex-col">
                 <div class="text-[8px] font-bold text-neutral-500 uppercase tracking-wider mb-1.5 flex items-center gap-1 shrink-0">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" class="w-2 h-2"><circle cx="12" cy="12" r="3"/><path d="M12 1v6m0 6v10M4.2 4.2l4.2 4.2m7.2 7.2 4.2 4.2M1 12h6m6 0h10"/></svg>
                    FX Rack — Global Effect Parameters
                 </div>
                 <div class="grid grid-cols-3 grid-rows-2 gap-2 flex-1 min-h-0">

                    <div class="bg-neutral-950/60 rounded border border-neutral-800 p-1.5 flex flex-col gap-1 justify-center min-h-0">
                      <span class="text-[7px] font-bold uppercase tracking-wider text-purple-400/80">Reverb</span>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Decay</span><span class="text-[6px] font-mono text-neutral-500">{{ fxParams.revDecay.toFixed(1) }}s</span></div>
                        <input type="range" min="0.1" max="10" step="0.1" :value="fxParams.revDecay" @change="updateFx('revDecay', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-purple-400" />
                      </div>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Return</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.revWet*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="1" step="0.01" :value="fxParams.revWet" @input="updateFx('revWet', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-purple-400" />
                      </div>
                    </div>

                    <div class="bg-neutral-950/60 rounded border border-neutral-800 p-1.5 flex flex-col gap-1 justify-center min-h-0">
                      <span class="text-[7px] font-bold uppercase tracking-wider text-pink-400/80">Delay</span>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Fbk</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.dlyFeed*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="0.95" step="0.01" :value="fxParams.dlyFeed" @input="updateFx('dlyFeed', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-pink-400" />
                      </div>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Return</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.dlyWet*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="1" step="0.01" :value="fxParams.dlyWet" @input="updateFx('dlyWet', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-pink-400" />
                      </div>
                    </div>

                    <div class="bg-neutral-950/60 rounded border border-neutral-800 p-1.5 flex flex-col gap-1 justify-center min-h-0">
                      <span class="text-[7px] font-bold uppercase tracking-wider text-rose-400/80">Drive</span>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Amt</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.dstAmt*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="1" step="0.01" :value="fxParams.dstAmt" @change="updateFx('dstAmt', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-rose-400" />
                      </div>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Return</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.dstWet*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="1" step="0.01" :value="fxParams.dstWet" @input="updateFx('dstWet', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-rose-400" />
                      </div>
                    </div>

                    <div class="bg-neutral-950/60 rounded border border-neutral-800 p-1.5 flex flex-col gap-1 justify-center min-h-0">
                      <span class="text-[7px] font-bold uppercase tracking-wider text-cyan-400/80">Filter</span>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Rate</span><span class="text-[6px] font-mono text-neutral-500">{{ fxParams.fltRate.toFixed(1) }}Hz</span></div>
                        <input type="range" min="0.1" max="8" step="0.1" :value="fxParams.fltRate" @input="updateFx('fltRate', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-cyan-400" />
                      </div>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Return</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.fltWet*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="1" step="0.01" :value="fxParams.fltWet" @input="updateFx('fltWet', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-cyan-400" />
                      </div>
                    </div>

                    <div class="bg-neutral-950/60 rounded border border-neutral-800 p-1.5 flex flex-col gap-1 justify-center min-h-0">
                      <span class="text-[7px] font-bold uppercase tracking-wider text-indigo-400/80">Chorus</span>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Depth</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.choDepth*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="1" step="0.01" :value="fxParams.choDepth" @input="updateFx('choDepth', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-indigo-400" />
                      </div>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Return</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.choWet*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="1" step="0.01" :value="fxParams.choWet" @input="updateFx('choWet', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-indigo-400" />
                      </div>
                    </div>

                    <div class="bg-neutral-950/60 rounded border border-neutral-800 p-1.5 flex flex-col gap-1 justify-center min-h-0">
                      <span class="text-[7px] font-bold uppercase tracking-wider text-orange-400/80">Phaser</span>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Rate</span><span class="text-[6px] font-mono text-neutral-500">{{ fxParams.phaRate.toFixed(1) }}Hz</span></div>
                        <input type="range" min="0.1" max="10" step="0.1" :value="fxParams.phaRate" @input="updateFx('phaRate', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-orange-400" />
                      </div>
                      <div class="flex flex-col gap-0.5">
                        <div class="flex justify-between"><span class="text-[6px] font-mono text-neutral-600 uppercase">Return</span><span class="text-[6px] font-mono text-neutral-500">{{ (fxParams.phaWet*100).toFixed(0) }}%</span></div>
                        <input type="range" min="0" max="1" step="0.01" :value="fxParams.phaWet" @input="updateFx('phaWet', $event.target.value)" class="w-full h-1 bg-neutral-800 rounded-lg appearance-none cursor-pointer text-orange-400" />
                      </div>
                    </div>

                 </div>
              </div>
            </div>
          </footer>
        </div>
      `
    };

    createApp(App).mount('#app');

    // ----- PWA: register the service worker (offline support) -----
    if ('serviceWorker' in navigator) {
      // Inject a minimal app manifest so the DAW is installable.
      try {
        const dir = location.pathname.replace(/[^/]*$/, '');
        const icon = 'data:image/svg+xml,' + encodeURIComponent(
          '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 512 512"><rect width="512" height="512" rx="96" fill="#0a0a0a"/><polyline points="470 256 384 256 320 448 192 64 128 256 42 256" fill="none" stroke="#6f8aaa" stroke-width="28" stroke-linecap="round" stroke-linejoin="round"/></svg>'
        );
        const manifest = {
          name: 'BEAT ROYALE DAW', short_name: 'BeatRoyale',
          start_url: location.pathname, scope: dir,
          display: 'standalone', background_color: '#0a0a0a', theme_color: '#0a0a0a',
          icons: [{ src: icon, sizes: '512x512', type: 'image/svg+xml', purpose: 'any maskable' }]
        };
        const link = document.createElement('link');
        link.rel = 'manifest';
        link.href = 'data:application/manifest+json,' + encodeURIComponent(JSON.stringify(manifest));
        document.head.appendChild(link);
      } catch (e) {}

      window.addEventListener('load', () => {
        navigator.serviceWorker.register('./service-worker.js').catch((err) => {
          console.warn('Service worker registration failed (needs https/localhost):', err);
        });
      });
    }
  </script>
