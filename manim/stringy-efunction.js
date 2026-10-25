import { svg, math, motion } from './slide-utils.js';

const red = '#b8202f';
const clamp = value => Math.max(0, Math.min(1, value));

function place(parent, latex, x, y, size = 23.8) {
  const node = math(latex, size);
  node.setAttribute('x', String(x - Number(node.getAttribute('width')) / 2));
  node.setAttribute('y', String(y - Number(node.getAttribute('height')) / 2));
  parent.append(node);
  return node;
}

function discrepancies(node) {
  node.querySelectorAll('path[data-c="1D44E"]').forEach(path => {
    const group = path.closest('g[data-mml-node="msub"]') || path.parentNode;
    group.style.color = red;
  });
}

function textBlock(parent, markup, top) {
  const node = document.createElement('div');
  node.style.cssText = 'position:absolute;left:47px;right:47px;top:' + top + 'px;font:23.8px/1.35 Beamer,serif;color:#000;text-align:left';
  node.innerHTML = markup;
  node.querySelectorAll('[data-math]').forEach(item => item.replaceChildren(math(item.dataset.math)));
  parent.append(node);
  return node;
}

function writable(node) {
  const paths = [...node.querySelectorAll('path')].map(path => {
    const length = path.getTotalLength();
    path.style.stroke = 'currentColor';
    path.style.strokeWidth = '16';
    path.style.strokeLinecap = 'round';
    path.style.strokeLinejoin = 'round';
    path.style.strokeDasharray = String(length);
    return { path, length };
  });
  paths.bars = [...node.querySelectorAll('rect')];
  paths.bars.forEach(bar => { bar.style.transformBox = 'fill-box'; bar.style.transformOrigin = 'center'; });
  return paths;
}

function write(paths, alpha) {
  paths.bars.forEach(bar => { bar.style.transform = 'scaleX(' + clamp(alpha) + ')'; });
  const progress = clamp(alpha) * (1 + Math.max(0, paths.length - 1) * .022);
  paths.forEach(({ path, length }, index) => {
    const value = clamp(progress - index * .022);
    path.style.strokeDashoffset = String(length * (1 - clamp(value / .75)));
    path.style.strokeOpacity = value > 0 && value < 1 ? '1' : '0';
    path.style.fillOpacity = String(clamp((value - .75) / .25));
  });
}

export function createEFunction(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;inset:0;pointer-events:none';
  slide.append(body);
  const stage = svg('svg', { viewBox: '0 0 960 720', width: 960, height: 720 });
  stage.style.cssText = 'position:absolute;inset:0;overflow:visible;color:#000';
  body.append(stage);
  const intro = textBlock(body, String.raw`Let <span data-math="f:X\to Y"></span> be a resolution with exceptional divisors <span data-math="D_i"></span>. Turns out to get the adjustment we want, we only need <em>discrepancies</em> <span style="color:#b8202f" data-math="a_i"></span>.`, 251);
  const canonical = svg('g');
  stage.append(canonical);
  discrepancies(place(canonical, String.raw`K_X=f^*K_Y+\sum_i a_iD_i`, 480, 424, 28));
  const formula = svg('g');
  stage.append(formula);
  const pieces = [
    String.raw`E_{\mathrm{st}}(Y)=`,
    String.raw`\sum_{J\subseteq I}`,
    String.raw`E(`,
    String.raw`D_J^\circ`,
    String.raw`)`,
    String.raw`\prod_{j\in J}`,
    String.raw`\frac{uv-1}{(uv)^{a_j+1}-1}`
  ].map(value => math(value, 28));
  const gaps = [8, 8, 0, 0, 9, 9, 0];
  const widths = pieces.map(node => Number(node.getAttribute('width')));
  let x = (960 - widths.reduce((sum, width, index) => sum + width + gaps[index], 0)) / 2;
  const positions = [];
  pieces.forEach((node, index) => {
    const [, viewTop, , viewHeight] = node.getAttribute('viewBox').split(/\s+/).map(Number);
    const scale = Number(node.getAttribute('height')) / viewHeight;
    node.setAttribute('x', String(x));
    node.setAttribute('y', String(311 + viewTop * scale));
    positions.push({ x, width: widths[index], top: 311 + viewTop * scale, height: Number(node.getAttribute('height')) });
    formula.append(node);
    x += widths[index] + gaps[index];
  });
  discrepancies(pieces[6]);
  const term = positions[3], fraction = positions[6];
  const anchor = term.x + term.width / 2;
  const fractionX = fraction.x + fraction.width / 2;
  const highlight = svg('g', { fill: 'none', stroke: '#000', 'stroke-width': 1.5 });
  highlight.append(svg('path', { d: 'M ' + anchor + ' ' + (term.top + term.height + 5) + ' V 390' }));
  stage.append(highlight);
  const callout = svg('g');
  callout.append(svg('rect', { x: 226, y: 0, width: 508, height: 252, rx: 3, fill: '#fff', stroke: '#000', 'stroke-width': 1.5 }));
  stage.append(callout);
  const diagram = svg('svg', { x: 238, y: 7, width: 484, height: 236, viewBox: '120 0 510 252', overflow: 'visible' });
  callout.append(diagram);
  const project = (x, y, z) => [348 + 88 * x + 58 * y, 127 + 25 * x - 38 * y - 72 * z];
  const bounds = [1.5, 1.3, .85], eye = [58, -88, 4794 / 72];
  const planes = [
    [[0,-1.3,-.85],[0,1.3,-.85],[0,1.3,.85],[0,-1.3,.85]],
    [[-1.5,0,-.85],[1.5,0,-.85],[1.5,0,.85],[-1.5,0,.85]],
    [[-1.5,-1.3,0],[1.5,-1.3,0],[1.5,1.3,0],[-1.5,1.3,0]]
  ];
  for (const plane of planes) diagram.append(svg('polygon', {
    points: plane.map(point => project(...point).join(',')).join(' '),
    fill: '#ececec', 'fill-opacity': .45, stroke: 'none'
  }));
  function edge(a, b, color = '#222222', width = 1.5, dashed = false) {
    const delta = b.map((value, i) => value - a[i]), cuts = [0, 1];
    const cut = (value, slope) => {
      if (Math.abs(slope) < 1e-9) return;
      const t = -value / slope;
      if (t > 1e-7 && t < 1 - 1e-7) cuts.push(t);
    };
    for (let k = 0; k < 3; k++) {
      cut(a[k], delta[k]);
      for (let j = 0; j < 3; j++) if (j !== k) {
        const value = a[j] - a[k] * eye[j] / eye[k];
        const slope = delta[j] - delta[k] * eye[j] / eye[k];
        cut(value - bounds[j], slope);
        cut(value + bounds[j], slope);
      }
    }
    cuts.sort((a, b) => a - b);
    const at = t => a.map((value, i) => value + delta[i] * t);
    const p = project(...a), q = project(...b), length = Math.hypot(q[0] - p[0], q[1] - p[1]);
    for (let i = 1; i < cuts.length; i++) {
      if (cuts[i] - cuts[i - 1] < 1e-7) continue;
      const midpoint = at((cuts[i - 1] + cuts[i]) / 2);
      let layers = 0;
      for (let k = 0; k < 3; k++) {
        const t = -midpoint[k] / eye[k];
        if (t > 1e-7 && midpoint.every((value, j) => j === k || Math.abs(value + t * eye[j]) <= bounds[j] + 1e-7)) layers++;
      }
      const tint = color.match(/[a-f\d]{2}/gi).map(value => Math.round(236 + (parseInt(value, 16) - 236) * .55 ** layers));
      const start = project(...at(cuts[i - 1])), end = project(...at(cuts[i]));
      const line = svg('line', {
        x1: start[0], y1: start[1], x2: end[0], y2: end[1],
        stroke: 'rgb(' + tint.join(',') + ')', 'stroke-width': width, 'data-layers': layers
      });
      if (dashed) {
        line.setAttribute('stroke-dasharray', '5 4');
        line.setAttribute('stroke-dashoffset', -length * cuts[i - 1]);
      }
      diagram.append(line);
    }
  }
  for (const plane of planes) plane.forEach((point, i) => edge(point, plane[(i + 1) % 4]));
  edge([0,0,-.85], [0,0,.85], '#222222', 1.5, true);
  edge([-1.5,0,0], [1.5,0,0], red, 3);
  place(diagram, 'D_i', 594, 117);
  place(diagram, 'D_j', 194, 38);
  place(diagram, 'D_k', 460, 22);
  const closedLabel = place(diagram, 'D_{ij}', 530, 184);
  const openLabel = place(diagram, 'D_{ij}^{\\circ}', 530, 184);
  closedLabel.style.color = openLabel.style.color = red;
  const openBox = openLabel.getAttribute('viewBox').split(/\s+/).map(Number);
  const openScale = Number(openLabel.getAttribute('width')) / openBox[2];
  const closedBox = closedLabel.getAttribute('viewBox').split(/\s+/).map(Number);
  const closedScale = Number(closedLabel.getAttribute('width')) / closedBox[2];
  const labelY = Number(closedLabel.getAttribute('y')) - closedBox[1] * closedScale + openBox[1] * openScale;
  openLabel.setAttribute('y', labelY);

  const circleGlyph = openLabel.querySelector('path[data-c="2218"]').parentNode;
  const circlePaths = writable(circleGlyph);
  openLabel.querySelectorAll('path').forEach(path => { if (!circleGlyph.contains(path)) path.style.visibility = 'hidden'; });
  const labelX = Number(closedLabel.getAttribute('x'));
  const labelTargetX = Number(openLabel.getAttribute('x'));
  function label(alpha) {
    closedLabel.setAttribute('x', labelX + (labelTargetX - labelX) * alpha);
    openLabel.setAttribute('x', labelX + (labelTargetX - labelX) * alpha);

    write(circlePaths, alpha);
  }
  const point = svg('circle', { cx: 348, cy: 127, r: 6, fill: '#fff', stroke: red, 'stroke-width': 2.4 });
  diagram.append(point);
  const labels = [...diagram.querySelectorAll('.math-svg')];
  const explanation = svg('g');
  stage.append(explanation);
  const braceY = fraction.top + fraction.height + 8;
  const brace = math('\\underbrace{\\hspace{' + fraction.width / 28 + 'em}}', 28);
  brace.setAttribute('x', fractionX - Number(brace.getAttribute('width')) / 2);
  brace.setAttribute('y', braceY);
  explanation.append(brace);
  const bracePaths = writable(brace);
  const polynomial = place(explanation, String.raw`\frac{1}{(uv)^{a_j}+(uv)^{a_j-1}+\cdots+1}`, fractionX, 405, 27);
  const projective = place(explanation, String.raw`\frac{1}{E(\mathbb P^{a_j})}`, fractionX, 405, 29);
  const polyPaths = writable(polynomial), projectivePaths = writable(projective);
  const rational = textBlock(body, String.raw`In general, <span data-math="E_{\mathrm{st}}(Y)"></span> is a rational function, we can expand it in <span data-math="\mathbb Z[\![u,v]\!]"></span> as a power series or <span data-math="\mathbb Z(\!(u^{-1},v^{-1})\!)"></span> as a Laurent series.`, 413);
  const properties = textBlock(body, '<ul style="margin:0;padding-left:29px"><li style="padding-left:3px;margin-bottom:17px">Independent of resolution.</li><li style="padding-left:3px">Compatible with product.</li></ul>', 572);
  properties.style.cssText = 'margin-top:18px';
  rational.append(properties);
  properties.querySelectorAll('li').forEach(item => item.style.setProperty('color', '#000'));
  const animation = motion();
  const tween = (seconds, update) => animation.run(seconds, value => update(value * value * (3 - 2 * value)));
  let previous = -1, serial = 0, disposed = false;
  const show = (node, visible) => { node.style.display = visible ? '' : 'none'; };
  const fade = node => {
    node.style.opacity = '0';
    show(node, true);
    return tween(.3, value => { node.style.opacity = String(value); });
  };
  const fadeOut = (...nodes) => tween(.25, value => {
    nodes.forEach(node => { node.style.opacity = String(1 - value); });
  });
  function render(step) {
    intro.style.top = (step < 2 ? 251 : 143) + 'px';
    show(canonical, step === 1);
    canonical.style.opacity = '1';
    show(formula, step >= 2);
    formula.style.opacity = '1';
    show(highlight, step === 3 || step === 4);
    highlight.style.opacity = '1';
    pieces[3].style.color = step === 3 || step === 4 ? red : '#000';
    show(callout, step === 3 || step === 4);
    callout.setAttribute('transform', 'translate(0 390)');
    labels.forEach(node => { node.style.opacity = '1'; });
    show(point, step === 4);
    point.setAttribute('r', '6');
    show(openLabel, step === 4);
    show(closedLabel, true);
    label(step === 4 ? 1 : 0);
    show(explanation, step === 6 || step === 7);
    explanation.style.opacity = '1';
    polynomial.style.opacity = '1';
    show(polynomial, step === 6);
    show(projective, step === 7);
    write(bracePaths, 1);
    write(polyPaths, 1);
    write(projectivePaths, 1);
    show(rational, step >= 8);
    rational.style.opacity = '1';
    show(properties, step >= 9);
    slide.dataset.step = String(step);
  }
  render(0);
  return {
    animated: true,
    async play(step = 0) {
      if (disposed) return;
      step = Math.max(0, Math.min(9, step));
      const from = previous === step ? step - 1 : previous;
      previous = step;
      const token = ++serial;
      animation.cancel();
      render(step);
      if (from === 1 && step === 2) {
        show(canonical, true);
        show(formula, false);
        intro.style.top = '251px';
        if (!await fadeOut(canonical)) return;
        if (disposed || token !== serial) return;
        show(canonical, false);
        if (!await tween(.85, value => { intro.style.top = (251 - 108 * value) + 'px'; })) return;
        if (disposed || token !== serial) return;
        await fade(formula);
      } else if (from === 2 && step === 3) {
        await tween(.75, value => callout.setAttribute('transform', 'translate(0 390) scale(1 ' + Math.max(.001, value) + ')'));
      } else if (from === 3 && step === 4) {
        await tween(.9, value => {
          point.setAttribute('r', String(6 * value));
          label(value);
        });
      } else if (from === 4 && step === 5) {
        render(4);
        if (!await fadeOut(...labels)) return;
        if (disposed || token !== serial) return;
        await tween(.65, value => {
          callout.setAttribute('transform', 'translate(0 390) scale(1 ' + Math.max(.001, 1 - value) + ')');
          highlight.style.opacity = String(1 - value);
        });
      } else if (from === 5 && step === 6) {
        polynomial.style.opacity = '0';
        if (!await tween(.65, value => write(bracePaths, value))) return;
        if (disposed || token !== serial) return;
        await fade(polynomial);
      } else if (from === 6 && step === 7) {
        show(polynomial, true);
        await tween(1.15, value => {
          write(polyPaths, clamp(1 - value * 2.15));
          write(projectivePaths, clamp((value - .4) / .6));
        });
      } else if (from === 7 && step === 8) {
        render(7);
        if (!await fadeOut(explanation)) return;
        if (disposed || token !== serial) return;
        show(explanation, false);
        await fade(rational);
      }
      if (!disposed && token === serial) render(step);
    },
    dispose() {
      disposed = true;
      serial++;
      animation.dispose();
      body.remove();
    }
  };
}
