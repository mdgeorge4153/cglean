// Forwards pointer events to Lean and displays the SVG that Lean renders.
import createModule from './dist/cglean.mjs';

const M = await createModule();
M.ccall('cglean_init', null, [], []);

const down   = M.cwrap('cglean_js_pointer_down', null, ['number', 'number']);
const move   = M.cwrap('cglean_js_pointer_move', null, ['number', 'number']);
const up     = M.cwrap('cglean_js_pointer_up', null, []);
const render = M.cwrap('cglean_js_render', 'string', []);
const showExact    = M.cwrap('cglean_js_show_exact', null, ['number']);
const setRecording = M.cwrap('cglean_js_set_recording', null, ['number']);
const useSynthetic = M.cwrap('cglean_js_use_synthetic_trace', null, []);
const traceSize    = M.cwrap('cglean_js_trace_size', 'number', []);
const replay       = M.cwrap('cglean_js_replay', 'string', ['number']);

const svg = document.getElementById('canvas');

// Converts a pointer event's screen position to SVG user units.
function svgPoint(e) {
  const p = new DOMPoint(e.clientX, e.clientY).matrixTransform(svg.getScreenCTM().inverse());
  return [p.x, p.y];
}

function redraw() { svg.innerHTML = render(); }

svg.addEventListener('pointerdown', e => {
  e.preventDefault();   // otherwise a drag can select text, and the next press drags that
  svg.setPointerCapture(e.pointerId);
  down(...svgPoint(e));
  redraw();
});
svg.addEventListener('pointermove', e => { move(...svgPoint(e)); redraw(); });
svg.addEventListener('pointerup', () => { up(); redraw(); });
svg.addEventListener('pointercancel', () => { up(); redraw(); });

redraw();

// Benchmark controls (index.html; hidden when embedded in the blueprint).

const $ = id => document.getElementById(id);

function showTrace() {
  $('trace').textContent = `${traceSize()} events`;
}

$('exact').addEventListener('change', e => { showExact(e.target.checked ? 1 : 0); redraw(); });

$('record').addEventListener('click', e => {
  const on = e.target.textContent.startsWith('Record');
  setRecording(on ? 1 : 0);
  e.target.textContent = on ? 'Stop recording' : 'Record a drag';
  showTrace();
});

$('synthetic').addEventListener('click', () => {
  useSynthetic();
  $('record').textContent = 'Record a drag';
  showTrace();
});

// Runs the trace `reps` times in each arithmetic, in alternating rounds, and
// keeps each one's fastest round: browsers coarsen timers (to 5–100 µs), so
// only totals over many replays mean anything.
$('replay').addEventListener('click', () => {
  const reps = Math.max(1, Number($('reps').value) || 1);
  const rounds = 3;
  const events = traceSize();
  $('results').textContent = 'running…';
  setTimeout(() => {
    const best = { exact: Infinity, filtered: Infinity }, end = {};
    for (const [name, flag] of [['exact', 1], ['filtered', 0]]) end[name] = replay(flag); // warm up
    for (let r = 0; r < rounds; r++) {
      for (const [name, flag] of [['exact', 1], ['filtered', 0]]) {
        const t0 = performance.now();
        for (let i = 0; i < reps; i++) replay(flag);
        best[name] = Math.min(best[name], performance.now() - t0);
      }
    }
    const line = name => {
      const ms = best[name] / reps;
      return `${name.padEnd(9)} ${ms.toFixed(3).padStart(9)} ms per replay  ` +
             `${(1000 * ms / Math.max(events, 1)).toFixed(2).padStart(8)} µs per event`;
    };
    $('results').textContent =
      `${events} events, ${reps} replays, best of ${rounds} rounds\n` +
      `${line('exact')}\n${line('filtered')}\n` +
      `filtered / exact: ${(best.filtered / best.exact).toFixed(2)}\n` +
      (end.exact === end.filtered ? `both end at ${end.exact}`
                                  : `DISAGREE: exact ${end.exact}, filtered ${end.filtered}`);
  }, 0);
});

showTrace();
