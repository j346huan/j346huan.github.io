import { svg, math, typeset, motion } from './slide-utils.js';
import { createDiamond, createBrace } from './hodge-stratum.js';

const redColor = '#b8202f', blackColor = '#202020';
const mix = (from, to, t) => '#' + [1, 3, 5].map(i => Math.round(parseInt(from.slice(i, i + 2), 16) * (1 - t) + parseInt(to.slice(i, i + 2), 16) * t).toString(16).padStart(2, '0')).join('');
const ease = x => x * x * (3 - 2 * x);
const m = latex => '<span data-math="' + latex + '"></span>';

export function createStrataPositivity(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;top:139px;width:866px;height:540px;color:#000';
  slide.append(body);
  const entries = [];
  const column = 350, width = 516;
  function text(parent, html, x, y, span, first, last = Infinity, font = 23) {
    const node = document.createElement('div');
    node.innerHTML = html;
    node.style.cssText = 'position:absolute;left:' + x + 'px;top:' + y + 'px;width:' + span + 'px;font-size:' + font + 'px;line-height:1.35';
    typeset(node);
    parent.append(node);
    entries.push({ node, first, last });
    return node;
  }
  function formula(parent, latex, y, first, last = Infinity, size = 23, x = 14, span = width - 28) {
    const node = math(latex, size);
    const w = Number(node.getAttribute('width')), h = Number(node.getAttribute('height'));
    const scale = Math.min(1, span / w);
    node.setAttribute('width', w * scale); node.setAttribute('height', h * scale);
    node.style.cssText += ';position:absolute;left:' + (x + (span - w * scale) / 2) + 'px;top:' + y + 'px';
    parent.append(node);
    entries.push({ node, first, last });
    return node;
  }
  function box(y) {
    const node = document.createElement('div');
    node.style.cssText = 'position:absolute;left:' + column + 'px;top:' + y + 'px;width:' + width + 'px;border:1px solid #000;box-sizing:border-box;overflow:hidden';
    body.append(node);
    return node;
  }
  const introduction = text(body, 'Some terms depend only on the ' + m('0') + '-stratum ' + m('D_{\\varnothing}^{\\circ}=X\\setminus D\\cong Y_{\\mathrm{reg}}') + '.', 62, 190, 742, 0, 1, 23.8);
  const a = box(0), b = box(80), c = box(160);
  const titleA = text(a, '<strong>Trivial case:</strong>', 14, 12, 220, 2);
  const canonical = text(a, 'For canonical singularities, ' + m('a_i\\geq0') + ', so', 14, 60, width - 28, 2, 3);
  const topRow = formula(a, 'h_{\\mathrm{st}}^{p,n}(Y)=h_c^{p,n}(X\\setminus D).', 132, 2, 3);
  const inclusion = formula(a, 'E(X\\setminus D)=E(X)+\\sum_{J\\ne\\varnothing}(-1)^{|J|}E(D_J)', 192, 3, 3, 21);
  const dimension = text(a, 'Since ' + m('\\dim D\\lt n') + ',', 14, 273, width - 28, 3, 3);
  const positive = formula(a, 'h_c^{p,n}(X\\setminus D)=h^{p,n}(X)\\geq0.', 316, 3, 3);
  const summaryA = formula(a, 'h_{\\mathrm{st}}^{p,n}(Y)\\geq0.', 14, 4, Infinity, 23, 164, width - 178);
  const terminal = text(b, 'Replace ' + m('Y') + ' by a crepant terminal model. Then ' + m('a_i\\geq1') + ', so', 14, 16, width - 28, 5, 6);
  const terminalRow = formula(b, 'h_{\\mathrm{st}}^{p,n-1}(Y)=h_c^{p,n-1}(X\\setminus D).', 116, 5, 6);
  const titleB = text(b, '<strong>Olano 2021:</strong>', 14, 188, 210, 6);
  const olanoRow = formula(b, 'h_c^{p,n-1}(X\\setminus D)\\geq0.', 233, 6, 6);
  const summaryB = formula(b, 'h_{\\mathrm{st}}^{p,n-1}(Y)\\geq0.', 14, 7, Infinity, 23, 164, width - 178);
  const large = text(c, 'If all ' + m('a_i') + ' are large enough, Poincaré duality gives non-negativity, assuming polynomiality.', 14, 16, width - 28, 8, 10, 21);
  const titleC = text(c, '<strong>Schepers–Veys 2007:</strong>', 14, 112, width - 28, 9, Infinity, 22);
  const schepers = text(c, m('h_{\\mathrm{st}}^{p,q}(Y)\\geq0') + ' for isolated singularities if ' + m('E_{\\mathrm{st}}(Y)') + ' is polynomial and', 14, 154, width - 28, 9, 10, 21);
  const threshold = formula(c, 'a_i>\\left\\lfloor\\frac{n-4}{2}\\right\\rfloor.', 229, 9, 10, 23);
  const threefold = text(c, '<ul style="margin:0;padding-left:23px"><li>This proves non-negativity for threefolds, assuming polynomiality.</li></ul>', 14, 290, width - 28, 10, 10, 19);
  const summaryC = formula(c, 'a_i>\\left\\lfloor\\frac{n-4}{2}\\right\\rfloor.', 13, 11, Infinity, 22, 256, width - 270);
  const fourfold = text(body, 'For a fourfold with polynomial ' + m('E_{\\mathrm{st}}(Y)') + ', it remains to show <span style="color:' + redColor + '">' + m('h_{\\mathrm{st}}^{2,2}(Y)\\geq0') + '</span>.', column, 264, width, 12, Infinity, 23);
  const final = formula(body, '\\begin{aligned}h_{\\mathrm{st}}^{2,2}(Y)&=h_c^{2,2}(X\\setminus D)+\\sum_{a_i=1}h_c^{\\mathrm{top}}(D_i^\\circ)\\\\&=h_c^{2,2}(X\\setminus D)+c,\\end{aligned}', 374, 13, Infinity, 23, column, width);
  const count = text(body, 'where ' + m('c') + ' is the number of discrepancy-1 divisors.', column, 481, width, 13, Infinity, 23);
  const canvas = svg('svg', { viewBox: '0 0 866 540', width: 866, height: 540 });
  canvas.style.cssText = 'position:absolute;left:0;top:0;overflow:visible;pointer-events:none';
  body.prepend(canvas);
  const black = createDiamond(canvas, { n: 7, unit: 20, color: '#202020', vertices: false, detail: 'full', opacity: .075 });
  const fill = black.group.firstChild, fills = svg('g'), upperShade = svg('polygon', { fill: redColor, 'fill-opacity': .12 });
  fill.replaceWith(fills); fills.append(fill, upperShade);
  const layerGrid = svg('g', { stroke: redColor, 'stroke-opacity': .26, 'stroke-width': .8 });
  const gridLines = [svg('line'), svg('line')]; layerGrid.append(...gridLines); fills.append(layerGrid);
  const red = createDiamond(canvas, { n: 6, unit: 20, vertices: false, detail: 'short', opacity: .1 });
  const brace = createBrace(canvas, { color: redColor });
  const label = math('a_i', 22), labelOne = math('=1', 22);
  const baseline = node => -node.viewBox.baseVal.y * Number(node.getAttribute('height')) / node.viewBox.baseVal.height;
  const labelOffset = baseline(label) - baseline(labelOne);
  label.style.color = labelOne.style.color = redColor;
  const focus = svg('g');
  focus.append(svg('circle', { r: 8, fill: 'none', stroke: redColor, 'stroke-width': 1.6 }), svg('circle', { r: 2.1, fill: redColor }));
  canvas.append(label, labelOne, focus);
  const timeline = motion();
  let step = -1, revision = 0, disposed = false;
  const display = (node, visible) => { node.style.display = visible ? '' : 'none'; node.style.opacity = '1'; };
  const heights = next => [next < 3 ? 215 : next < 4 ? 377 : 64, next < 6 ? 188 : next < 7 ? 292 : 64, next < 9 ? 114 : next < 10 ? 285 : next < 11 ? 357 : 78];
  const layout = next => ({ x: next < 2 ? 433 : 150, y: next < 2 ? 345 : 346, n: next >= 12 ? 4 : 7, unit: next >= 12 ? 28 : 20, shift: next >= 9 && next < 12 ? 3 : 1, omissions: next < 12, finite: next >= 12 ? 1 : 0, neutral: next >= 2 ? 1 : 0, shade: next >= 9 && next < 12 ? 1 : 0, top: next >= 12 || next >= 2 && next < 5 ? 1 : 0, second: next >= 12 || next >= 5 && next < 8 ? 1 : 0, upper: next >= 9 && next < 12 ? 1 : 0, grid: next >= 12 || next >= 5 && next < 8 ? 1 : 0 });
  function geometry(config) {
    const { x, y, n, unit, shift, omissions, finite, neutral, shade, top, second, upper, grid } = config;
    const shiftedColor = mix(redColor, blackColor, neutral);
    brace.group.style.color = label.style.color = labelOne.style.color = shiftedColor;
    upperShade.setAttribute('points', '0,' + (-2 * n * unit) + ' ' + (-n * unit) + ',' + (-n * unit) + ' ' + (n * unit) + ',' + (-n * unit));
    upperShade.style.opacity = String(shade);
    layerGrid.style.opacity = String(grid);
    [[n - 1, 0, n - 1, n], [0, n - 1, n, n - 1]].forEach(([p0, q0, p1, q1], i) => {
      const line = gridLines[i]; line.setAttribute('x1', (q0 - p0) * unit); line.setAttribute('y1', -(p0 + q0) * unit); line.setAttribute('x2', (q1 - p1) * unit); line.setAttribute('y2', -(p1 + q1) * unit);
    });
    const accent = { color: mix(blackColor, redColor, neutral * (top + upper)), edges: [0, 3], test: () => false };
    black.set({ x, y, n, unit, omissions: finite < 1, accent, extraPoints: omissions ? [] : [[n - 1, 1], [1, n - 1]] });
    red.set({ color: shiftedColor, x, y: y + 2 * unit * shift, n: n - 1, unit, omissions: finite < 1, extraPoints: omissions ? [] : [[1, 1], [1, n - 2], [n - 2, 1], [n - 2, n - 2]] });
    [black.group.children[2], black.group.children[3]].forEach(group => [...group.children].forEach(dot => {
      const dx = Number(dot.getAttribute('cx')) / unit, dy = -Number(dot.getAttribute('cy')) / unit, p = (dy - dx) / 2, q = (dy + dx) / 2;
      const edge = Math.abs(p - n) < .001 || Math.abs(q - n) < .001;
      const inner = Math.abs(p - n + 1) < .001 || Math.abs(q - n + 1) < .001;
      const weight = Math.min(1, top * edge + second * inner + upper * (p + q >= n - .001));
      dot.style.color = mix(blackColor, redColor, neutral * weight);
    }));
    [[black, 18], [red, 12]].forEach(([diamond, firstExtra]) => {
      [...diamond.group.children[2].children].forEach((dot, i) => { dot.style.opacity = String(i < firstExtra ? 1 : finite); });
      diamond.group.children[3].style.opacity = String(1 - finite);
    });
    const from = y - 2 * (n - 1) * unit, to = from + 2 * unit * shift, bx = x + n * unit + 10;
    brace.set(bx, from, to);
    const point = black.point(2, 2);
    focus.setAttribute('transform', 'translate(' + point.x + ',' + point.y + ')');
    label.setAttribute('x', bx + brace.width + 7);
    label.setAttribute('y', (from + to - Number(label.getAttribute('height'))) / 2);
    labelOne.setAttribute('x', bx + brace.width + 9 + Number(label.getAttribute('width')));
    labelOne.setAttribute('y', Number(label.getAttribute('y')) + labelOffset);
  }
  function reveal(diamond, alpha) {
    const [fill, border, dots, omitted] = diamond.group.children;
    const length = border.getTotalLength();
    border.style.strokeDasharray = String(length);
    border.style.strokeDashoffset = String(length * (1 - alpha));
    fill.style.opacity = String(alpha);
    dots.style.opacity = String(alpha);
    omitted.style.opacity = String(alpha);
  }
  function state(next) {
    entries.forEach(({ node, first, last }) => display(node, next >= first && next <= last));
    [a, b, c].forEach((node, i) => { display(node, next >= [2, 5, 8][i]); node.style.height = heights(next)[i] + 'px'; });
    titleB.style.top = next < 7 ? '188px' : '12px';
    titleC.style.top = next < 11 ? '112px' : '14px';
    introduction.style.top = next ? '458px' : '190px';
    display(canvas, next >= 1);
    [black.group, red.group, brace.group, label].forEach(node => display(node, next >= 1));
    display(labelOne, next >= 12); display(focus, next >= 12);
    [topRow, positive, summaryA].forEach(node => { node.style.color = next < 5 || next >= 12 ? redColor : '#000'; });
    [terminalRow, olanoRow, summaryB].forEach(node => { node.style.color = next >= 12 || next >= 5 && next < 8 ? redColor : '#000'; });
    [schepers, threshold, summaryC].forEach(node => { node.style.color = next >= 9 && next < 12 ? redColor : '#000'; });
    geometry(layout(next));
    reveal(black, 1); reveal(red, 1);
  }
  const fade = (run, nodes, incoming = false) => run(.25, alpha => nodes.forEach(node => { node.style.opacity = String(incoming ? ease(alpha) : 1 - ease(alpha)); }));
  const interpolate = (from, to, alpha) => {
    const value = ease(alpha), result = { ...to };
    for (const key of ['x', 'y', 'n', 'unit', 'shift', 'finite', 'neutral', 'shade', 'top', 'second', 'upper', 'grid']) result[key] = from[key] + (to[key] - from[key]) * value;
    return result;
  };
  async function expand(previous, next, index, incoming, run) {
    state(next);
    incoming.forEach(node => { node.style.opacity = '0'; });
    const panel = [a, b, c][index], from = heights(previous)[index], to = heights(next)[index];
    if (!await run(.4, alpha => { panel.style.height = from + (to - from) * ease(alpha) + 'px'; })) return;
    await fade(run, incoming, true);
  }
  async function collapse(previous, next, index, title, fromY, toY, outgoing, incoming, run) {
    state(previous);
    if (!await fade(run, outgoing)) return;
    state(next);
    incoming.style.opacity = '0';
    const panel = [a, b, c][index], from = heights(previous)[index], to = heights(next)[index];
    if (!await run(.7, alpha => {
      const t = ease(alpha);
      panel.style.height = from + (to - from) * t + 'px';
      title.style.top = fromY + (toY - fromY) * t + 'px';
    })) return;
    await fade(run, [incoming], true);
  }
  async function animate(previous, next, run) {
    if (next === 1) {
      state(0);
      if (!await run(.65, alpha => {
        const t = ease(alpha);
        introduction.style.top = 190 + 268 * t + 'px';
      })) return;
      display(canvas, true);
      geometry({ ...layout(1), shift: 0 });
      display(black.group, true); reveal(black, 0);
      if (!await run(.75, alpha => reveal(black, alpha))) return;
      display(red.group, true); reveal(red, 0);
      if (!await run(.65, alpha => reveal(red, alpha))) return;
      display(brace.group, true);
      if (!await run(.75, alpha => geometry({ ...layout(1), shift: ease(alpha) }))) return;
      display(label, true);
      await fade(run, [label], true);
    } else if (next === 2) {
      state(previous);
      if (!await fade(run, [introduction])) return;
      state(next); a.style.opacity = '0';
      if (!await run(.75, alpha => geometry(interpolate(layout(previous), layout(next), alpha)))) return;
      await fade(run, [a], true);
    } else if (next === 3) await expand(previous, next, 0, [inclusion, dimension, positive], run);
    else if (next === 4) await collapse(previous, next, 0, titleA, 12, 12, [canonical, topRow, inclusion, dimension, positive], summaryA, run);
    else if (next === 5 || next === 8) {
      state(next);
      await run(.5, alpha => {
        geometry(interpolate(layout(previous), layout(next), alpha));
        const t = ease(alpha);
        (next === 5 ? summaryA : summaryB).style.color = mix(redColor, '#000000', t);
        if (next === 5) terminalRow.style.color = mix('#000000', redColor, t);
      });
    } else if (next === 6) await expand(previous, next, 1, [titleB, olanoRow], run);
    else if (next === 7) await collapse(previous, next, 1, titleB, 188, 12, [terminal, terminalRow, olanoRow], summaryB, run);
    else if (next === 9) {
      state(next); [titleC, schepers, threshold].forEach(node => { node.style.opacity = '0'; });
      if (!await run(.9, alpha => {
        geometry(interpolate(layout(previous), { ...layout(next), upper: 0, shade: 0 }, alpha));
        c.style.height = heights(previous)[2] + (heights(next)[2] - heights(previous)[2]) * ease(alpha) + 'px';
      })) return;
      if (!await run(.3, alpha => geometry({ ...layout(next), upper: ease(alpha), shade: ease(alpha) }))) return;
      await fade(run, [titleC, schepers, threshold], true);
    } else if (next === 10) await expand(previous, next, 2, [threefold], run);
    else if (next === 11) await collapse(previous, next, 2, titleC, 112, 14, [large, schepers, threshold, threefold], summaryC, run);
    else if (next === 12) {
      state(next); fourfold.style.opacity = '0'; labelOne.style.opacity = '0'; focus.style.opacity = '0';
      if (!await run(.9, alpha => {
        geometry(interpolate(layout(previous), layout(next), alpha));
        summaryA.style.color = summaryB.style.color = mix('#000000', redColor, ease(alpha));
      })) return;
      await fade(run, [fourfold, labelOne, focus], true);
    } else state(next);
  }
  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      next = Math.max(0, Math.min(13, Number(next) || 0));
      const previous = step, token = ++revision;
      timeline.cancel(); step = next; slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (previous >= 0 && next === previous + 1) await animate(previous, next, run); else state(next);
      if (!disposed && token === revision) state(next);
    },
    dispose() { disposed = true; revision++; timeline.dispose(); body.remove(); }
  };
}
