import { svg, math, mathAt } from './slide-utils.js';

const clamp = value => Math.max(0, Math.min(1, value));
const red = '#c40000';

function pen(node) {
  const paths = [...node.querySelectorAll('path')].map(path => {
    const length = path.getTotalLength();
    path.style.cssText = 'stroke:currentColor;stroke-width:16;stroke-linecap:round;stroke-linejoin:round;stroke-dasharray:' + length;
    return { path, length };
  });
  return alpha => {
    const progress = clamp(alpha) * (1 + Math.max(0, paths.length - 1) * .022);
    node.style.visibility = alpha > 0 ? 'visible' : 'hidden';
    paths.forEach(({ path, length }, index) => {
      const value = clamp(progress - index * .022);
      path.style.strokeDashoffset = String(length * (1 - clamp(value / .75)));
      path.style.strokeOpacity = value > 0 && value < 1 ? '1' : '0';
      path.style.fillOpacity = String(clamp((value - .75) / .25));
    });
    node.querySelectorAll('rect').forEach(rect => {
      rect.style.transformBox = 'fill-box';
      rect.style.transformOrigin = 'center';
      rect.style.transform = 'scaleX(' + clamp(alpha) + ')';
    });
  };
}

function surface(resolved) {
  const group = svg('g', { fill: 'none', stroke: '#000', 'stroke-width': 1.7, 'stroke-linecap': 'round', 'stroke-linejoin': 'round', transform: 'translate(0 90) scale(.76)' });
  const side = resolved
    ? 'M-62 -90 C-40 -56 -22 -25 -22 0 C-22 25 -40 56 -62 90 M62 -90 C40 -56 22 -25 22 0 C22 25 40 56 62 90'
    : 'M-62 -90 L0 0 L-62 90 M62 -90 L0 0 L62 90';
  const fill = resolved
    ? 'M-62 -90 C-40 -56 -22 -25 -22 0 C-22 25 -40 56 -62 90 L62 90 C40 56 22 25 22 0 C22 -25 40 -56 62 -90 Z'
    : 'M-62 -90 L0 0 L-62 90 L62 90 L0 0 L62 -90 Z';
  group.append(svg('path', { d: fill, fill: '#fff', stroke: 'none' }), svg('path', { d: side }));
  group.append(svg('ellipse', { cx: 0, cy: -90, rx: 62, ry: 14, fill: '#fff' }));
  group.append(svg('path', { d: 'M-62 90 A62 14 0 0 1 62 90', 'stroke-dasharray': '5 5' }));
  group.append(svg('path', { d: 'M-62 90 A62 14 0 0 0 62 90' }));
  if (resolved) {
    group.append(svg('path', { d: 'M-22 0 A22 8 0 0 1 22 0', stroke: red, 'stroke-width': 2, 'stroke-dasharray': '4 4' }));
    group.append(svg('path', { d: 'M-22 0 A22 8 0 0 0 22 0', stroke: red, 'stroke-width': 2 }));
  } else group.append(svg('circle', { cx: 0, cy: 0, r: 4.5, fill: red, stroke: 'none' }));
  return group;
}

function label(parent, prefix, descriptions) {
  const group = svg('g', { fill: '#000', stroke: 'none' });
  const first = math(prefix, 22), firstWidth = Number(first.getAttribute('width'));
  first.setAttribute('y', 188 - Number(first.getAttribute('height')) / 2);
  group.append(first);
  const parts = descriptions.map(text => {
    if (!text) return { width: 0, write() {} };
    const node = math('\\ \\text{' + text + '}', 21);
    node.setAttribute('y', 188 - Number(node.getAttribute('height')) / 2);
    group.append(node);
    return { node, width: Number(node.getAttribute('width')), write: pen(node) };
  });
  parent.append(group);
  const prefixWrite = pen(first);
  return (from, to = from, alpha = 1, reveal = 1) => {
    const width = parts[from].width + (parts[to].width - parts[from].width) * alpha;
    first.setAttribute('x', -(firstWidth + width) / 2);
    prefixWrite(reveal);
    parts.forEach((part, index) => {
      part.node?.setAttribute('x', (firstWidth - width) / 2);
      part.write(reveal * (from === to ? +(index === to) : index === from ? 1 - clamp(alpha * 2) : index === to ? clamp(alpha * 2 - 1) : 0));
    });
  };
}

export function createConjectureDiagram() {
  const element = svg('svg', { viewBox: '0 0 864 218', width: 864, height: 218, role: 'img', 'aria-label': 'Crepant resolutions by varieties and stacks' });
  element.style.cssText = 'display:block;width:864px;height:218px;overflow:visible;color:#000;pointer-events:none';
  const source = svg('g', { transform: 'translate(252 0)', 'data-source': '' });
  const target = svg('g', { 'data-target': '' });
  const arrow = svg('g', { 'data-arrow': '' });
  const resolved = surface(true), singular = surface(false);
  source.append(resolved);
  target.append(singular);
  const x = mathAt(source, 'X', 0, 188, 22);
  const targetLabel = label(target, 'Y', ['', 'quotient singularity', 'log-terminal singularity']);
  const saddle = svg('g', { transform: 'translate(0 90)', fill: 'none', stroke: '#000', 'stroke-width': 1.25, 'stroke-linecap': 'round', 'stroke-linejoin': 'round' });
  const project = (u, v) => [67 * (u + .55 * v), 25 * (u - v) - 12 * (u * u - v * v)];
  const curve = (u, v, du, dv) => Array.from({ length: 25 }, (_, index) => project(u + du * index / 24, v + dv * index / 24));
  const path = points => points.map(([a, b], index) => (index ? 'L' : 'M') + a + ' ' + b).join(' ');
  const perimeter = [...curve(-1, -1, 2, 0), ...curve(1, -1, 0, 2), ...curve(1, 1, -2, 0), ...curve(-1, 1, 0, -2)];
  const outline = svg('path', { d: path(perimeter) + 'Z' });
  saddle.append(outline);
  const length = outline.getTotalLength();
  outline.style.strokeDasharray = String(length);
  const point = svg('circle', { cx: 0, cy: 0, r: 3.2, fill: red, stroke: 'none' });
  const dots = [-11, -20, -29].map(cy => svg('circle', { cx: 0, cy, r: 1.7, fill: red, stroke: 'none' }));
  const stabilizer = svg('path', { d: 'M0 -5 V-52', stroke: red, 'stroke-width': 2, 'stroke-dasharray': '5 5' });
  saddle.append(stabilizer, ...dots, point);
  source.append(saddle);
  const sourceLabelGroup = svg('g');
  source.append(sourceLabelGroup);
  const sourceLabel = label(sourceLabelGroup, '\\mathcal{X}', ['Deligne-Mumford stack', 'Artin stack']);
  const arrowWrite = pen(mathAt(arrow, '\\xrightarrow{\\quad\\text{crepant}\\quad}', 432, 90, 23));
  element.append(source, arrow, target);

  function shape(alpha, artin = 0) {
    outline.style.strokeDashoffset = String(length * (1 - clamp(alpha * 1.3)));
    outline.style.visibility = alpha ? 'visible' : 'hidden';
    point.setAttribute('r', 3.2 * clamp(alpha * 2));
    dots.forEach((dot, index) => dot.setAttribute('r', 1.7 * clamp(alpha * 2 - index * .15) * (1 - artin)));
    stabilizer.style.visibility = artin ? 'visible' : 'hidden';
    stabilizer.setAttribute('d', 'M0 -5 V' + (-5 - 47 * artin));
  }

  function center(alpha) {
    const value = clamp(alpha);
    source.style.opacity = '0';
    arrow.style.opacity = '0';
    target.setAttribute('transform', 'translate(' + (612 - 180 * value) + ' 0)');
    targetLabel(0, 1, value);
  }

  function resolve(alpha) {
    const value = clamp(alpha);
    source.style.opacity = '1';
    arrow.style.opacity = '1';
    resolved.style.display = x.style.display = 'none';
    saddle.style.display = sourceLabelGroup.style.display = '';
    target.setAttribute('transform', 'translate(' + (432 + 180 * value) + ' 0)');
    targetLabel(1);
    sourceLabel(0, 0, 1, value);
    shape(value);
    arrowWrite(clamp(value * 1.2 - .2));
  }

  function artin(alpha) {
    const value = clamp(alpha);
    resolve(1);
    sourceLabel(0, 1, value);
    targetLabel(1, 2, value);
    shape(1, value);
  }

  function state(mode) {
    source.style.opacity = '1';
    arrow.style.opacity = '1';
    target.style.opacity = '1';
    if (mode === 'dm') { resolve(1); return; }
    if (mode === 'artin') { artin(1); return; }
    resolved.style.display = x.style.display = '';
    saddle.style.display = sourceLabelGroup.style.display = 'none';
    arrowWrite(1);
    target.setAttribute('transform', 'translate(612 0)');
    targetLabel(0);
    if (mode === 'yasuda') center(1);
  }

  state('batyrev');
  return { element, source, arrow, state, center, resolve, artin };
}
