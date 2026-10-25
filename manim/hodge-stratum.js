import { svg, math } from './slide-utils.js';

export function createDiamond(parent, options = {}) {
  const config = { x: 0, y: 0, n: 6, unit: 24, color: '#b8202f', vertices: true, detail: 'none', omissions: true, opacity: .1, dimension: 'n', size: 19, label: '', accent: null, extraPoints: [], ...options };
  const group = svg('g');
  const fill = svg('polygon', { stroke: 'none', fill: 'currentColor' });
  const border = svg('path', { fill: 'none', stroke: 'currentColor', 'stroke-width': 1.2 });
  const dots = svg('g', { fill: 'currentColor' });
  const labels = svg('g');
  const omitted = svg('g', { fill: 'currentColor', opacity: .55 });
  const center = svg('g');
  const accentBorder = svg('path', { fill: 'none', 'stroke-width': 1.2 });
  group.append(fill, border, dots, omitted, labels, center, accentBorder);
  parent.append(group);
  const markers = Array.from({ length: 18 }, () => { const dot = svg('circle', { r: 2.1 }); dots.append(dot); return dot; });
  const ellipses = Array.from({ length: 9 }, () => { const dot = svg('circle', { r: 1.3 }); omitted.append(dot); return dot; });
  let labelKey = '', centerKey = '', glyphs = [];
  const local = (p, q) => [(q - p) * config.unit, -(p + q) * config.unit];
  const position = (node, x, y) => { node.setAttribute('x', x - Number(node.getAttribute('width')) / 2); node.setAttribute('y', y - Number(node.getAttribute('height')) / 2); };
  function render() {
    const { x, y, n, unit, color, vertices, detail, omissions, opacity, dimension, size, label, accent, extraPoints } = config;
    group.setAttribute('transform', 'translate(' + x + ',' + y + ')');
    group.style.color = color;
    const corners = [[n, n], [0, n], [0, 0], [n, 0]].map(([p, q]) => local(p, q));
    fill.setAttribute('points', corners.map(point => point.join(',')).join(' '));
    fill.setAttribute('fill-opacity', opacity);
    const inset = vertices ? Math.min(23, unit * n * .27) : 0;
    const edges = corners.map((a, index) => {
      const b = corners[(index + 1) % 4], length = Math.hypot(b[0] - a[0], b[1] - a[1]);
      const dx = (b[0] - a[0]) * inset / length, dy = (b[1] - a[1]) * inset / length;
      return 'M' + (a[0] + dx) + ',' + (a[1] + dy) + 'L' + (b[0] - dx) + ',' + (b[1] - dy);
    });
    border.setAttribute('d', edges.join(' '));
    accentBorder.setAttribute('d', accent ? edges.filter((_, i) => accent.edges.includes(i)).join(' ') : '');
    accentBorder.setAttribute('stroke', accent?.color || color);
    const pointColor = (p, q) => accent?.test(p, q) ? accent.color : 'inherit';
    const key = dimension + ':' + size;
    if (labelKey !== key) {
      labelKey = key;
      labels.replaceChildren();
      glyphs = [dimension + ',' + dimension, '0,' + dimension, '0,0', dimension + ',0'].map(pair => {
        const node = math('h_c^{' + pair + '}', size); labels.append(node); return node;
      });
    }
    glyphs.forEach((node, index) => position(node, ...corners[index]));
    labels.style.visibility = vertices ? 'inherit' : 'hidden';
    const points = [[n, n], [0, n], [0, 0], [n, 0]];
    if (detail !== 'none') {
      if (detail === 'full') for (let p = 0; p < 3; p++) for (let q = 0; q < 3; q++) { if (p || q) points.push([n - p, n - q]); }
      else points.push([n - 1, n], [n, n - 1]);
      points.push([0, n - 1], [1, n], [1, 0], [0, 1], [n - 1, 0], [n, 1]);
    }
    points.push(...extraPoints);
    while (markers.length < points.length) { const dot = svg('circle', { r: 2.1 }); dots.append(dot); markers.push(dot); }
    markers.forEach((dot, index) => {
      const value = points[index];
      dot.style.visibility = !vertices && value ? 'inherit' : 'hidden';
      if (value) { dot.style.color = pointColor(...value); const [dx, dy] = local(...value); dot.setAttribute('cx', dx); dot.setAttribute('cy', dy); }
    });
    const starts = [[n - 1, n - 2, 0, -.4], [n - 2, n - 1, -.4, 0], [n - 2, n - 2, -.3, -.3]];
    ellipses.forEach((dot, index) => {
      dot.style.visibility = !vertices && detail === 'full' && omissions ? 'inherit' : 'hidden';
      const [p, q, dp, dq] = starts[Math.floor(index / 3)], k = index % 3 + 1;
      dot.style.color = pointColor(p + k * dp, q + k * dq);
      const [dx, dy] = local(p + k * dp, q + k * dq);
      dot.setAttribute('cx', dx); dot.setAttribute('cy', dy);
    });
    if (centerKey !== label + ':' + size) {
      centerKey = label + ':' + size;
      center.replaceChildren();
      if (label) center.append(math(label, size));
    }
    if (center.firstChild) position(center.firstChild, 0, -n * unit);
  }
  render();
  return { group, set(values) { Object.assign(config, values); render(); }, point(p, q) { const [x, y] = local(p, q); return { x: config.x + x, y: config.y + y }; }, dispose() { group.remove(); } };
}

let bracePaths;
export function createBrace(parent, { color = '#000', size = 24 } = {}) {
  if (!bracePaths) {
    const source = math('\\left.\\rule{0pt}{5em}\\right\\}', size);
    bracePaths = ['23AB', '23AC', '23AD'].map(code => source.querySelector('[data-c="' + code + '"]').getAttribute('d'));
  }
  const group = svg('g', { role: 'img', 'aria-label': '\\}', fill: 'currentColor' });
  group.style.color = color;
  const stems = [svg('rect'), svg('rect')];
  const caps = bracePaths.map(d => svg('path', { d }));
  group.append(...stems, ...caps);
  parent.append(group);
  let width = 0;
  return {
    group,
    get width() { return width; },
    set(x, top, bottom) {
      const height = Math.max(0, bottom - top), scale = Math.min(size / 1000, height / 3000);
      const cap = 750 * scale, middle = (top + bottom) / 2, origin = x - 150 * scale;
      width = 602 * scale;
      [top + cap, middle + cap, bottom].forEach((y, i) => caps[i].setAttribute('transform', 'translate(' + origin + ',' + y + ') scale(' + scale + ',' + -scale + ')'));
      [[top + cap, middle - cap], [middle + cap, bottom - cap]].forEach(([a, b], i) => {
        stems[i].setAttribute('x', origin + 397 * scale);
        stems[i].setAttribute('y', a - .2);
        stems[i].setAttribute('width', 108 * scale);
        stems[i].setAttribute('height', Math.max(0, b - a) + .4);
      });
    },
    dispose() { group.remove(); }
  };
}
