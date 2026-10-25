import { svg, mathAt } from './slide-utils.js';

let serial = 0;
const clamp = value => Math.max(0, Math.min(1, value));

export function createBlades() {
  const element = svg('svg', { viewBox: '0 0 960 720', width: 960, height: 720, role: 'img', 'aria-label': 'Two reflected Hodge blades extending to positive and negative degrees' });
  element.style.cssText = 'position:absolute;inset:0;overflow:visible;pointer-events:none;color:#000';
  const defs = svg('defs');
  element.append(defs);
  const labels = [], outlines = [];
  const levels = Array.from({ length: 6 }, () => {
    const group = svg('g');
    element.append(group);
    return { group, glyphs: [], dots: [], clips: [] };
  });
  const row = (level, x, y, values, gap = 120) => values.forEach((value, index) => {
    const right = x > 480;
    const latex = value.replace(/^h/, right ? 'h_{\\mathrm{st}}' : 'g_{\\mathrm{st}}');
    const node = mathAt(level.group, latex, x + (index - (values.length - 1) / 2) * gap, y, 21);
    labels.push({ node, y, right });
    const paths = [...node.querySelectorAll('path')];
    paths.forEach((path, index) => {
      const length = path.getTotalLength();
      path.style.cssText = 'stroke:currentColor;stroke-width:16;stroke-linecap:round;stroke-linejoin:round;stroke-dasharray:' + length;
      level.glyphs.push({ path, length, index, count: paths.length });
    });
  });
  const dots = (level, x, y, direction) => [-1, 0, 1].forEach(index => {
    const cy = y + direction * index * 7;
    const dot = svg('circle', { cx: x + index * 7, cy });
    level.group.append(dot);
    level.dots.push(dot);
    labels.push({ node: dot, y: cy, right: x > 480 });
  });
  const edges = (level, points, up) => {
    const id = 'hodge-blade-' + ++serial;
    const clip = svg('clipPath', { id, clipPathUnits: 'userSpaceOnUse' });
    const rect = svg('rect', { x: 0, width: 960 });
    clip.append(rect);
    defs.append(clip);
    const group = svg('g', { fill: 'none', stroke: '#c4c4c4', 'stroke-width': 1.1, 'clip-path': 'url(#' + id + ')' });
    level.group.prepend(group);
    outlines.push({ node: group, right: !up });
    points.forEach(([x1, y1, x2, y2, dashed]) => {
      const path = svg('path', { d: 'M ' + x1 + ' ' + y1 + ' L ' + x2 + ' ' + y2 });
      if (dashed) path.setAttribute('stroke-dasharray', '2 6');
      group.append(path);
    });
    const ys = points.flatMap(point => [point[1], point[3]]);
    level.clips.push({ rect, top: Math.min(...ys) - 1, height: Math.max(...ys) - Math.min(...ys) + 2, up });
  };
  const leftY = [553, 510, 466, 411, 362, 303, 258];
  const rightY = leftY.map(y => 811 - y);
  const width = index => index < 3 ? (553 - leftY[index]) * 161 / 142 : 161;
  levels.forEach((level, index) => {
    const left = [-1, 1].map(side => [250 + side * width(index), leftY[index], 250 + side * width(index + 1), leftY[index + 1], index === 5]);
    const right = [-1, 1].map(side => [710 + side * width(index), rightY[index], 710 + side * width(index + 1), rightY[index + 1], index === 5]);
    edges(level, left, true);
    edges(level, right, false);
  });
  row(levels[0], 250, 531, ['h^{0,0}']);
  row(levels[0], 710, 280, ['h^{n,n}']);
  row(levels[1], 250, 489, ['h^{1,0}', 'h^{0,1}'], 98);
  row(levels[1], 710, 322, ['h^{n,n-1}', 'h^{n-1,n}'], 98);
  dots(levels[2], 166.5, 448, 1);
  dots(levels[2], 333.5, 448, -1);
  dots(levels[2], 626.5, 363, -1);
  dots(levels[2], 793.5, 363, 1);
  row(levels[3], 250, 402, ['h^{n,0}', '\\cdots', 'h^{0,n}']);
  row(levels[3], 710, 409, ['h^{n,0}', '\\cdots', 'h^{0,n}']);
  row(levels[4], 250, 353, ['h^{n+1,1}', '\\cdots', 'h^{1,n+1}']);
  row(levels[4], 710, 458, ['h^{n-1,-1}', '\\cdots', 'h^{-1,n-1}']);
  row(levels[5], 250, 302, ['\\vdots', '\\vdots', '\\vdots']);
  row(levels[5], 710, 509, ['\\vdots', '\\vdots', '\\vdots']);

  function reveal(progress) {
    levels.forEach((level, index) => {
      const alpha = clamp(progress * levels.length - index);
      level.group.style.visibility = alpha ? 'visible' : 'hidden';
      level.glyphs.forEach(({ path, length, index, count }) => {
        const value = clamp(alpha * (1 + (count - 1) * .022) - index * .022);
        path.style.strokeDashoffset = String(length * (1 - clamp(value / .75)));
        path.style.strokeOpacity = value > 0 && value < 1 ? '1' : '0';
        path.style.fillOpacity = String(clamp((value - .75) / .25));
      });
      level.dots.forEach(dot => dot.setAttribute('r', 1.1 * alpha));
      const eased = alpha * alpha * (3 - 2 * alpha);
      level.clips.forEach(({ rect, top, height, up }) => {
        rect.setAttribute('y', top + (up ? height * (1 - eased) : 0));
        rect.setAttribute('height', height * eased);
      });
    });
  }

  function compare(progress) {
    const alpha = clamp(progress), flip = Math.cos(Math.PI * alpha);
    labels.forEach(({ node, y, right }) => {
      const dx = (right ? -230 : 230) * alpha;
      const dy = right ? (405.5 - y) * (1 - flip) : 0;
      node.setAttribute('transform', 'translate(' + dx + ' ' + dy + ')');
    });
    outlines.forEach(({ node, right }) => {
      const dx = (right ? -230 : 230) * alpha;
      node.setAttribute('transform', 'matrix(1 0 0 ' + (right ? flip : 1) + ' ' + dx + ' ' + (right ? 405.5 * (1 - flip) : 0) + ')');
    });
  }

  reveal(0);
  compare(0);
  return { element, reveal, compare };
}
