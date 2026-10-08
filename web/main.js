// Forwards pointer events to Lean and displays the SVG that Lean renders.
import createModule from './dist/cglean.mjs';

const M = await createModule();
M.ccall('cglean_init', null, [], []);

const down   = M.cwrap('cglean_js_pointer_down', null, ['number', 'number']);
const move   = M.cwrap('cglean_js_pointer_move', null, ['number', 'number']);
const up     = M.cwrap('cglean_js_pointer_up', null, []);
const render = M.cwrap('cglean_js_render', 'string', []);

const svg = document.getElementById('canvas');

// Converts a pointer event's screen position to SVG user units.
function svgPoint(e) {
  const p = new DOMPoint(e.clientX, e.clientY).matrixTransform(svg.getScreenCTM().inverse());
  return [p.x, p.y];
}

function redraw() { svg.innerHTML = render(); }

svg.addEventListener('pointerdown', e => {
  svg.setPointerCapture(e.pointerId);
  down(...svgPoint(e));
  redraw();
});
svg.addEventListener('pointermove', e => { move(...svgPoint(e)); redraw(); });
svg.addEventListener('pointerup', () => { up(); redraw(); });

redraw();
