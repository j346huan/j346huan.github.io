import { svg, math } from './slide-utils.js';

export function createClassGroupDiagram() {
  const node = svg('svg', { width: 250, height: 330, viewBox: '0 0 250 330', overflow: 'visible' });
  const defs = svg('defs');
  node.append(defs);
  const strokes = [], curveStrokes = [], labels = [];
  const curves = svg('g');
  let count = 0;
  const id = 'class-group-' + Math.random().toString(36).slice(2);
  const clamp = value => Math.max(0, Math.min(1, value));

  function path(d, dash = '', color = '#111', width = 1.3, target = node) {
    const maskId = id + '-' + count++;
    const mask = svg('mask', { id: maskId, maskUnits: 'userSpaceOnUse', x: 0, y: 0, width: 250, height: 330 });
    const pen = svg('path', { d, fill: 'none', stroke: '#fff', 'stroke-width': width + 2, pathLength: 1, 'stroke-dasharray': 1 });
    mask.append(pen);
    defs.append(mask);
    target.append(svg('path', { d, fill: 'none', stroke: color, 'stroke-width': width, 'stroke-dasharray': dash, 'stroke-linecap': 'round', mask: 'url(#' + maskId + ')' }));
    (target === curves ? curveStrokes : strokes).push(pen);
  }

  function label(tex, x, y, size = 22) {
    const item = math(tex, size);
    item.setAttribute('x', x - Number(item.getAttribute('width')) / 2);
    item.setAttribute('y', y - Number(item.getAttribute('height')) / 2);
    node.append(item);
    labels.push(item);
    return item;
  }

  path('M 20 70 A 105 34 0 1 0 230 70 A 105 34 0 1 0 20 70', '5 4');
  path('M 39 255 A 86 28 0 1 0 211 255 A 86 28 0 1 0 39 255', '5 4');
  path('M 85 70 L 125 255 M 165 70 L 125 255', '4 5', '#aaa', 1, curves);
  path('M 85 70 L 165 70', '', '#111', 1.3, curves);
  path('M 99 50 L 151 90', '', '#111', 1.3, curves);
  path('M 99 90 L 151 50', '', '#111', 1.3, curves);
  const point = svg('circle', { cx: 125, cy: 255, r: 2.8, fill: '#111' });
  node.append(point);
  labels.push(point);
  label('V_\\alpha', 182, 85);
  label('\\operatorname{Spec}\\mathcal O_{Y,\\eta_\\alpha}^{h}', 125, 302, 20);
  label('\\Big\\downarrow', 54, 166, 37);
  label('\\tau_\\alpha', 77, 167);

  function draw(progress = 1) {
    for (const pen of strokes) pen.setAttribute('stroke-dashoffset', 1 - clamp(progress));
    for (const item of labels) item.setAttribute('opacity', clamp((progress - 0.45) / 0.55));
  }

  function drawCurves(progress = 1) {
    for (const pen of curveStrokes) pen.setAttribute('stroke-dashoffset', 1 - clamp(progress));
  }

  draw();
  drawCurves();
  return { node, draw, curves, drawCurves };
}

export function createClassGroupArrow() {
  const width = 14, height = 34;
  const node = svg('svg', { width, height, viewBox: '0 0 14 34', overflow: 'visible' });
  const shaft = svg('path', { d: 'M 7 1 C 1 4 1 6 7 9 C 13 12 13 14 7 17 C 1 20 1 22 7 25 L 7 31', fill: 'none', stroke: 'currentColor', 'stroke-width': 1.3, 'stroke-linecap': 'round', pathLength: 1, 'stroke-dasharray': 1 });
  const head = svg('path', { d: 'M 3.5 27 L 7 31 L 10.5 27', fill: 'none', stroke: 'currentColor', 'stroke-width': 1.3, 'stroke-linecap': 'round', 'stroke-linejoin': 'round' });
  node.append(shaft, head);
  function draw(progress = 1) {
    progress = Math.max(0, Math.min(1, progress));
    shaft.setAttribute('stroke-dashoffset', 1 - progress);
    head.setAttribute('opacity', Math.max(0, (progress - 0.85) / 0.15));
  }
  draw();
  return { node, width, height, draw };
}
