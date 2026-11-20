// Forwards pointer events to Lean and displays the SVG that Lean renders.
// After each drag, replays it in exact and in filtered arithmetic, and shows
// how long each took.
import createModule from './dist/cglean.mjs';

const M = await createModule();
M.ccall('cglean_init', null, [], []);

const down      = M.cwrap('cglean_js_pointer_down', null, ['number', 'number']);
const move      = M.cwrap('cglean_js_pointer_move', null, ['number', 'number']);
const up        = M.cwrap('cglean_js_pointer_up', null, []);
const render    = M.cwrap('cglean_js_render', 'string', []);
const traceSize = M.cwrap('cglean_js_trace_size', 'number', []);
const replay    = M.cwrap('cglean_js_replay', 'string', ['number']);

const svg = document.getElementById('canvas');
const results = document.getElementById('results');

// Converts a pointer event's screen position to SVG user units.
function svgPoint(e) {
  const p = new DOMPoint(e.clientX, e.clientY).matrixTransform(svg.getScreenCTM().inverse());
  return [p.x, p.y];
}

function redraw() { svg.innerHTML = render(); }

// Milliseconds per replay of the last drag. Browsers coarsen timers (to
// 5–100 µs), so replays are repeated until they take at least 20 ms.
function timeReplay(exact) {
  for (let reps = 1; ; reps *= 2) {
    const t0 = performance.now();
    for (let i = 0; i < reps; i++) replay(exact);
    const dt = performance.now() - t0;
    if (dt >= 20) return dt / reps;
  }
}

function compare() {
  const events = traceSize();
  if (events === 0) return;   // the press missed the dot
  const end = { exact: replay(1), filtered: replay(0) };   // also warms up
  // Alternating rounds, keeping each one's best, to even out noise.
  const best = { exact: Infinity, filtered: Infinity };
  for (let r = 0; r < 3; r++) {
    best.exact = Math.min(best.exact, timeReplay(1));
    best.filtered = Math.min(best.filtered, timeReplay(0));
  }
  const us = ms => (1000 * ms / events).toFixed(1).padStart(7);
  results.textContent =
    `Last drag, ${events} events, replayed:\n` +
    `  exact    ${us(best.exact)} µs per event\n` +
    `  filtered ${us(best.filtered)} µs per event  (${(best.filtered / best.exact).toFixed(2)}×)\n` +
    (end.exact === end.filtered ? '' : `DISAGREE: exact ${end.exact}, filtered ${end.filtered}\n`);
}

function release() {
  up();
  redraw();
  if (traceSize() > 0) {
    results.textContent = 'Timing the drag…';
    setTimeout(compare, 0);   // let the page repaint first
  }
}

svg.addEventListener('pointerdown', e => {
  e.preventDefault();   // otherwise a drag can select text, and the next press drags that
  svg.setPointerCapture(e.pointerId);
  down(...svgPoint(e));
  redraw();
});
svg.addEventListener('pointermove', e => { move(...svgPoint(e)); redraw(); });
svg.addEventListener('pointerup', release);
svg.addEventListener('pointercancel', release);

redraw();
