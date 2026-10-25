import { svg, math, mathAt } from './slide-utils.js';

export function createSeedConstructionDiagram(parent) {
  const node = svg('svg', { width: 866, height: 370, viewBox: '0 0 866 370', overflow: 'visible' });
  node.style.cssText = 'display:block;overflow:visible';
  parent?.append(node);
  const red = '#c4162b';
  const clamp = x => Math.max(0, Math.min(1, x));
  const lerp = (a, b, t) => a + (b - a) * t;
  const path = (group, d, color = '#111', dash = '', width = 1.35) => {
    const p = svg('path', { d, fill: 'none', stroke: color, 'stroke-width': width, 'stroke-linecap': 'round', 'stroke-linejoin': 'round', 'stroke-dasharray': dash });
    group.append(p);
    return p;
  };
  const group = target => { const g = svg('g'); (target || node).append(g); return g; };
  const label = (target, tex, x, y, size = 22, color = '#111') => {
    const item = mathAt(target, tex, x, y, size);
    item.style.color = color;
    return item;
  };
  const circle = (target, x, y, r, fill = '#111') => { const c = svg('circle', { cx: x, cy: y, r, fill }); target.append(c); return c; };
  const arrow = (target, x1, y1, x2, y2, dashed = false) => {
    const g = group(target), length = Math.hypot(x2 - x1, y2 - y1), size = 23.8;
    g.setAttribute('transform', 'translate(' + x1 + ' ' + y1 + ') rotate(' + Math.atan2(y2 - y1, x2 - x1) * 180 / Math.PI + ')');
    const a = math('\\xrightarrow{\\hspace{' + Math.max(0, (length / size - .589) / .7071) + 'em}}', size);
    const width = a.viewBox.baseVal.width;
    a.setAttribute('viewBox', '0 -510 ' + width + ' 520');
    a.setAttribute('height', 520 * size / 1000);
    a.setAttribute('x', 0); a.setAttribute('y', -260 * size / 1000);
    a.querySelector('[data-mml-node="mpadded"]')?.remove();
    if (dashed) {
      const shaft = a.querySelector('[data-mml-node="mo"] > svg');
      const segment = svg('path', { d: 'M 0 250 H ' + (width - 400), stroke: 'currentColor', 'stroke-width': 48, 'stroke-dasharray': '170 140', fill: 'none' });
      shaft.replaceWith(segment);
    }
    g.append(a); return g;
  };
  const boundary = 'M 0 12 H 260 V 180 H 0 Z';
  const patch = 'M 48 38 H 234 C 206 62 234 130 206 154 H 20 C 48 130 20 62 48 38 Z';
  const original = group();
  path(original, boundary);
  label(original, '\\mathbb P^5', 27, 32);
  path(original, 'M 56 95 H 210');
  label(original, 'L', 205, 78);
  const originalY = group(original);
  path(originalY, patch, red);
  label(originalY, 'Y', 223, 164, 22, red);

  const blown = group();
  const ambient = group(blown);
  path(ambient, boundary);
  label(ambient, '\\operatorname{Bl}_L\\mathbb P^5', 78, 25);
  const transformY = group(blown);
  path(transformY, patch, red);
  label(transformY, '\\operatorname{Bl}_L Y', 88, 56, 21, red);
  const restricted = group(blown);
  path(restricted, 'M 40 22 H 255 C 222 50 255 129 222 157 H 7 C 40 129 7 50 40 22 Z');
  label(restricted, '\\operatorname{Bl}_L Y', 70, 5);
  const exceptional = group(blown);
  path(exceptional, 'M 48 89 H 220');
  const labelL = label(exceptional, 'L', 200, 72);
  const labelExc = label(exceptional, '\\operatorname{Exc}(\\pi)', 199, 77, 18);
  const fibers = group(exceptional);
  for (const side of [-1, 1]) {
    for (const [index, offset] of [8, 16, 24, 32].entries()) {
      const x = 130 + side * (offset + 29 * Math.cos(Math.PI * 5 / 18)), dy = 29 * Math.sin(Math.PI * 5 / 18);
      path(fibers, 'M ' + x + ' ' + (120 - dy) + ' A 29 29 0 0 ' + (side > 0 ? 1 : 0) + ' ' + x + ' ' + (120 + dy)).setAttribute('opacity', [.72, .5, .3, .15][index]);
    }
  }
  fibers.append(svg('circle', { cx: 130, cy: 120, r: 29, fill: 'none', stroke: 'currentColor', 'stroke-width': 1.35 }));
  path(fibers, 'M 101 120 A 29 10 0 0 0 159 120', 'currentColor');
  path(fibers, 'M 101 120 A 29 10 0 0 1 159 120', 'currentColor', '3 4');
  for (const p of fibers.querySelectorAll('path')) p.setAttribute('stroke', 'currentColor');
  circle(exceptional, 130, 89, 2.7);
  const fiberP3 = label(blown, '\\mathbb P^3', 130, 163, 18, red);
  const crossH = path(blown, 'M 42 110 H 223', red, '2 5', 1.65);
  const crossV = path(blown, 'M 130 28 V 133', red, '2 5', 1.65);
  const fiberPoint = circle(blown, 130, 110, 2.8, red);
  const blowArrow = group();
  arrow(blowArrow, 0, 0, 94, 0);
  label(blowArrow, '\\pi', 47, -17);

  const base = group();
  base.append(svg('circle', { cx: 0, cy: 0, r: 59, fill: '#fff', stroke: '#111', 'stroke-width': 1.35 }));
  const equator = group(base);
  path(equator, 'M -59 0 A 59 18 0 0 0 59 0');
  path(equator, 'M -59 0 A 59 18 0 0 1 59 0', '#111', '3 5');
  label(base, '\\mathbb P^3', 67, 37, 22);
  const curve = group(base);
  const curvePath = 'M -36 28 C -6 28 6 -28 36 -28';
  const curvePoint = t => { const u = 1 - t; return [-36*u*u*u - 18*u*u*t + 18*u*t*t + 36*t*t*t, 28*u*u*u + 84*u*u*t - 84*u*t*t - 28*t*t*t]; };
  path(curve, curvePath);
  label(curve, 'C', 20, 5, 21);
  const zs = [.18, .48, .82].map(curvePoint);
  const generalPoint = curvePoint(.65);
  for (const [x, y] of zs) path(curve, `M ${x - 3.2} ${y - 3.2} L ${x + 3.2} ${y + 3.2} M ${x + 3.2} ${y - 3.2} L ${x - 3.2} ${y + 3.2}`, '#111', '', 1.5);
  label(curve, 'Z', -29, 43, 18);
  const basePoint = circle(base, 3, -16, 3, red);
  const projectionLeft = group();
  const projectionRight = group();
  const projectionSingle = group();
  arrow(projectionLeft, 267, 209, 365, 251);
  label(projectionLeft, '\\rho\\circ\\pi', 286, 245, 20);
  arrow(projectionRight, 581, 209, 489, 251, true);
  label(projectionRight, '\\rho', 573, 244, 21);
  arrow(projectionSingle, 0, 0, 0, 40);
  label(projectionSingle, '\\rho\\circ\\pi', 44, 25, 20);
  const formula = group();
  const equation = label(formula, 'E(\\operatorname{Bl}_L Y)=(E(\\mathbb P^3)-12)E(\\mathbb P^1)+12E(\\mathbb P^2).', 590, 170, 23.8);
  equation.setAttribute('x', 861 - Number(equation.getAttribute('width')));

  function state(step) {
    return {
      ox: step < 2 ? 303 : 522, oy: step < 2 ? 55 : 3, original: step < 6 ? 1 : 0,
      originalY: step === 1 || step === 3 ? 1 : 0,
      bx: step < 6 ? 84 : step < 11 ? 303 : 59, by: step < 6 ? 3 : 15,
      blown: step >= 2 ? 1 : 0, ambient: step < 6 ? 1 : 0,
      transformY: step === 3 ? 1 : 0, restricted: step >= 6 ? 1 : 0,
      redFiber: step === 2 ? 1 : 0, fiberP3: step === 2 ? 1 : 0,
      arrow: step >= 2 && step < 6 ? 1 : 0,
      base: step >= 4 ? 1 : 0, baseX: step < 11 ? 433 : 189, baseY: 296,
      doubleProjection: step >= 4 && step < 6 ? 1 : 0,
      singleProjection: step >= 6 ? 1 : 0, equator: step < 7 ? 1 : 0,
      curve: step >= 7 ? 1 : 0,
      crossH: [5, 8, 10].includes(step) ? 1 : 0,
      crossV: [5, 9, 10].includes(step) ? 1 : 0,
      point: [5, 8, 9, 10].includes(step) ? 1 : 0,
      pointX: step === 8 ? generalPoint[0] : step === 9 ? -21 : step === 10 ? zs[1][0] : 3,
      pointY: step === 8 ? generalPoint[1] : step === 9 ? -24 : step === 10 ? zs[1][1] : -16,
      formula: step === 11 ? 1 : 0
    };
  }
  const opacity = (element, value) => element.setAttribute('opacity', value);
  function set(step) {
    step = Math.max(0, Math.min(11, step));
    const index = Math.floor(step), t = step - index;
    const a = state(index), b = state(Math.min(11, index + 1));
    const s = Object.fromEntries(Object.keys(a).map(k => [k, lerp(a[k], b[k], t)]));
    original.setAttribute('transform', `translate(${s.ox} ${s.oy})`);
    blown.setAttribute('transform', `translate(${s.bx} ${s.by})`);
    opacity(original, s.original);
    opacity(originalY, s.originalY);
    opacity(blown, s.blown);
    opacity(ambient, s.ambient);
    opacity(transformY, s.transformY);
    opacity(restricted, s.restricted);
    opacity(labelL, 1 - s.restricted);
    opacity(labelExc, s.restricted);
    fibers.style.color = `rgb(${Math.round(17 + 179 * s.redFiber)},${Math.round(17 + 5 * s.redFiber)},${Math.round(17 + 26 * s.redFiber)})`;
    opacity(fiberP3, s.fiberP3);
    opacity(crossH, s.crossH);
    opacity(crossV, s.crossV);
    opacity(fiberPoint, s.point);
    blowArrow.setAttribute('transform', 'translate(384 95)');
    opacity(blowArrow, s.arrow);
    base.setAttribute('transform', `translate(${s.baseX} ${s.baseY})`);
    opacity(base, s.base);
    opacity(equator, s.equator);
    opacity(curve, s.curve);
    opacity(basePoint, s.point);
    basePoint.setAttribute('cx', s.pointX);
    basePoint.setAttribute('cy', s.pointY);
    opacity(projectionLeft, s.doubleProjection);
    opacity(projectionRight, s.doubleProjection);
    projectionSingle.setAttribute('transform', `translate(${s.baseX} 188)`);
    opacity(projectionSingle, s.singleProjection);
    opacity(formula, s.formula);
  }
  set(0);
  return { node, set, dispose() { node.remove(); } };
}
