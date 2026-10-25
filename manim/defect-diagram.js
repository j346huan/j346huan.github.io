import { svg, math } from './slide-utils.js';

const red = '#b8202f', pale = '#df9da5';
const clamp = value => Math.max(0, Math.min(1, value));
const ease = value => value * value * (3 - 2 * value);
const mix = (a, b, t) => a + (b - a) * t;
const path = (points, closed = false) => points.map((point, i) => (i ? 'L' : 'M') + point.join(',')).join(' ') + (closed ? 'Z' : '');

export function createDefectDiagram(parent) {
  const node = svg('svg', { width: 866, height: 553, viewBox: '0 0 866 553' });
  node.style.cssText = 'position:absolute;left:0;top:0;overflow:visible;pointer-events:none'; parent.append(node);
  const lower = svg('g'), surface = svg('path', { fill: '#fff', stroke: red, 'stroke-width': 1.4 });
  const orbit = svg('ellipse', { fill: 'none', stroke: pale, 'stroke-width': 1.1 });
  const puncture = svg('ellipse', { rx: 2.4, ry: 1.8, fill: '#fff', stroke: red, 'stroke-width': 1.1 });
  const point = svg('circle', { r: 2.8, fill: '#000' }); lower.append(surface, orbit, puncture, point); node.append(lower);
  const connectors = [0, 1].map(() => svg('line', { stroke: '#888', 'stroke-width': 1.1, 'stroke-dasharray': '5 5' }));
  const upper = svg('g'); node.append(upper);
  const surfaceFaces = svg('g'), faces = Array.from({ length: 96 }, () => svg('path', { fill: '#fff', stroke: '#fff', 'stroke-width': .35 }));
  surfaceFaces.append(...faces); upper.append(surfaceFaces);
  const hiddenBorder = svg('path', { fill: 'none', stroke: red, 'stroke-opacity': .48, 'stroke-width': 1.2, 'stroke-dasharray': '4 3', 'stroke-linejoin': 'round' });
  const visibleBorder = svg('path', { fill: 'none', stroke: red, 'stroke-width': 1.4, 'stroke-linejoin': 'round' });
  const seams = svg('g'), hiddenSeam = hiddenBorder.cloneNode(), visibleSeam = visibleBorder.cloneNode(); seams.append(hiddenSeam, visibleSeam); upper.append(hiddenBorder, visibleBorder, seams);
  const liftPath = svg('path', { fill: 'none', stroke: pale, 'stroke-width': 1.1 }); upper.append(liftPath);
  upper.append(...connectors);
  const fibers = [svg('ellipse'), svg('ellipse')];
  fibers.forEach(fiber => { fiber.setAttribute('fill', '#ededed'); fiber.setAttribute('stroke', '#000'); fiber.setAttribute('stroke-width', 1.25); upper.append(fiber); });
  const lowerDot = svg('circle', { r: 3.1, fill: red }), upperDot = svg('circle', { r: 3.1, fill: red }); node.append(lowerDot, upperDot);
  const labels = {};
  for (const [key, latex, size] of [['base', 'U_\\alpha', 23.8], ['divisor', 'D_i', 23.8], ['point', 'x', 23.8], ['fiber', 'E_x', 23.8], ['map', 'f', 23.8], ['arrow', '\\Big\\downarrow', 35]]) {
    const label = math(latex, size); node.append(label); labels[key] = label;
  }
  const place = (label, x, y) => { label.setAttribute('x', x - Number(label.getAttribute('width')) / 2); label.setAttribute('y', y - Number(label.getAttribute('height')) / 2); };
  const config = { compact: 0, fiber: 0, spiral: 0, loop: false };
  let metrics, frame = 0, running = false, disposed = false, started = 0, progress = 0;
  const spatial = (radius, theta) => {
    const { x, hole, upperY, width, ry, pitch } = metrics, depth = radius * Math.sin(theta), height = pitch * theta / (2 * Math.PI);
    return [x + hole + radius * Math.cos(theta), upperY + depth * ry / width + pitch / 2 - height, depth + height * ry / width];
  };
  const helix = (radius, theta) => spatial(radius, theta).slice(0, 2);
  const samples = (radius, from = 0, to = 2 * Math.PI, count = 96) => Array.from({ length: count + 1 }, (_, i) => helix(radius, mix(from, to, i / count)));
  function drawSurface(spiral) {
    const { width } = metrics, innerRadius = width * .18 * spiral, first = -Math.PI / 2, last = 5 * Math.PI / 2;
    const triangles = [], ordered = [];
    const triangle = points => {
      const xs = points.map(point => point[0]), ys = points.map(point => point[1]);
      triangles.push({ points, left: Math.min(...xs), right: Math.max(...xs), top: Math.min(...ys), bottom: Math.max(...ys) });
    };
    faces.forEach((face, i) => {
      const a = mix(first, last, i / faces.length), b = mix(first, last, (i + 1) / faces.length);
      const points = [spatial(innerRadius, a), spatial(width, a), spatial(width, b), spatial(innerRadius, b)];
      face.setAttribute('d', path(points.map(point => point.slice(0, 2)), true));
      ordered.push({ face, depth: points.reduce((sum, point) => sum + point[2], 0) / 4 });
      triangle([points[0], points[1], points[2]]); triangle([points[0], points[2], points[3]]);
    });
    ordered.sort((a, b) => a.depth - b.depth).forEach(({ face }) => surfaceFaces.append(face));
    const hidden = point => triangles.some(({ points: [a, b, c], left, right, top, bottom }) => {
      if (point[0] < left - .01 || point[0] > right + .01 || point[1] < top - .01 || point[1] > bottom + .01) return false;
      const denominator = (b[1] - c[1]) * (a[0] - c[0]) + (c[0] - b[0]) * (a[1] - c[1]);
      if (Math.abs(denominator) < .0001) return false;
      const u = ((b[1] - c[1]) * (point[0] - c[0]) + (c[0] - b[0]) * (point[1] - c[1])) / denominator;
      const v = ((c[1] - a[1]) * (point[0] - c[0]) + (a[0] - c[0]) * (point[1] - c[1])) / denominator, w = 1 - u - v;
      return u >= -.001 && v >= -.001 && w >= -.001 && a[2] * u + b[2] * v + c[2] * w > point[2] + .45;
    });
    const borders = ['', ''];
    const trace = (points, output = borders) => {
      let previous = -1;
      for (let i = 1; i < points.length; i++) {
        const a = points[i - 1], b = points[i], middle = a.map((value, axis) => (value + b[axis]) / 2), layer = hidden(middle) ? 1 : 0;
        if (layer !== previous) output[layer] += 'M' + a.slice(0, 2).join(',');
        output[layer] += 'L' + b.slice(0, 2).join(','); previous = layer;
      }
    };
    trace(Array.from({ length: 257 }, (_, i) => spatial(width, mix(first, last, i / 256))));
    if (spiral > .001) {
      trace(Array.from({ length: 257 }, (_, i) => spatial(innerRadius, mix(first, last, i / 256))));
    }
    const ends = ['', ''];
    for (const angle of [first, last]) trace(Array.from({ length: 33 }, (_, i) => spatial(mix(innerRadius, width, i / 32), angle)), ends);
    visibleSeam.setAttribute('d', ends[0]); hiddenSeam.setAttribute('d', ends[1]); seams.style.opacity = String(spiral);
    visibleBorder.setAttribute('d', borders[0]); hiddenBorder.setAttribute('d', borders[1]);
  }
  function drawPoints() {
    const { x, hole, lowerY, radius, orbitY } = metrics, angle = progress * 2 * Math.PI;
    lowerDot.setAttribute('cx', x + hole + radius * Math.cos(angle)); lowerDot.setAttribute('cy', lowerY + 2 + orbitY * Math.sin(angle));
    const lifted = helix(radius, angle); upperDot.setAttribute('cx', lifted[0]); upperDot.setAttribute('cy', lifted[1]);
  }
  function render() {
    const compact = clamp(config.compact), fiber = clamp(config.fiber), spiral = clamp(config.spiral);
    const x = mix(433, 110, compact), width = mix(174, 92, compact), upperY = mix(122, 130, compact), lowerY = mix(386, 345, compact);
    const ry = mix(54, 32, compact), hole = mix(-10, -6, compact), radius = width * .55, orbitY = width * .18, pitch = mix(108, 58, compact) * spiral;
    const fiberX = x + hole + radius, fiberRX = mix(30, 17, compact), fiberRY = mix(10, 6.5, compact);
    metrics = { x, width, upperY, lowerY, ry, hole, radius, orbitY, pitch };
    lower.setAttribute('transform', 'translate(' + x + ',' + lowerY + ')');
    surface.setAttribute('d', 'M' + (-width) + ',-34 C' + (-width / 3) + ',-58 ' + (width / 3) + ',-10 ' + width + ',-34 L' + width + ',38 C' + (width / 3) + ',62 ' + (-width / 3) + ',14 ' + (-width) + ',38 Z');
    orbit.setAttribute('cx', hole); orbit.setAttribute('cy', 2); orbit.setAttribute('rx', radius); orbit.setAttribute('ry', orbitY); orbit.style.opacity = config.loop ? '1' : '0';
    puncture.setAttribute('cx', hole); puncture.setAttribute('cy', 2); point.setAttribute('cx', hole + radius); point.setAttribute('cy', 2);
    drawSurface(spiral);
    liftPath.setAttribute('d', path(samples(radius))); liftPath.style.opacity = config.loop ? String(spiral) : '0';
    fibers.forEach((disk, i) => { disk.setAttribute('cx', fiberX); disk.setAttribute('cy', upperY + pitch * (i ? -.5 : .5)); disk.setAttribute('rx', fiberRX); disk.setAttribute('ry', fiberRY); disk.style.opacity = String(fiber * (i ? spiral : 1)); });
    connectors.forEach((line, i) => {
      line.setAttribute('x1', fiberX); line.setAttribute('y1', lowerY + 2); line.setAttribute('x2', fiberX + (i ? 1 : -1) * fiberRX); line.setAttribute('y2', upperY - pitch / 2); line.style.opacity = String(fiber);
    });
    place(labels.base, x - width + 24, lowerY + 68); place(labels.divisor, x + hole - width + 36, upperY - ry - 24);
    labels.base.style.opacity = labels.divisor.style.opacity = String(1 - compact);
    place(labels.point, fiberX + 16, lowerY + 15);
    place(labels.fiber, x + hole + width + 18, upperY + 3); labels.fiber.style.opacity = String(fiber);
    const arrowX = x - mix(52, 28, compact), arrowY = (upperY + lowerY) / 2;
    place(labels.arrow, arrowX, arrowY); place(labels.map, arrowX + 22, arrowY);
    lowerDot.style.opacity = config.loop ? '1' : '0'; upperDot.style.opacity = config.loop ? String(fiber) : '0'; drawPoints();
  }
  function tick(now) {
    if (!running || disposed) return;
    const t = (now - started) % 9000;
    progress = t < 500 ? 0 : t < 4500 ? ease((t - 500) / 4000) : t < 5000 ? 1 : 1 - ease((t - 5000) / 4000);
    drawPoints(); frame = requestAnimationFrame(tick);
  }
  function set(values = {}) {
    if (disposed) return;
    Object.assign(config, values);
    if (config.loop && !running) { running = true; started = performance.now(); progress = 0; frame = requestAnimationFrame(tick); }
    else if (!config.loop && running) { running = false; cancelAnimationFrame(frame); frame = 0; progress = 0; }
    render();
  }
  set();
  return { node, set, centerY() { const top = upper.getBBox().y, base = surface.getBBox(); return (top + metrics.lowerY + base.y + base.height) / 2; }, dispose() { disposed = true; running = false; cancelAnimationFrame(frame); node.remove(); } };
}
