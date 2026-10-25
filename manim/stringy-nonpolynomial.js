import { svg, math, typeset, motion } from './slide-utils.js';
import { createNonpolynomialDiagram } from './nonpolynomial-diagram.js';

const red = '#b8202f';
const clamp = x => Math.max(0, Math.min(1, x));
const ease = x => x * x * (3 - 2 * x);
const m = latex => '<span data-math="' + latex + '"></span>';

const baseline = node => -node.viewBox.baseVal.y * Number(node.getAttribute('height')) / node.viewBox.baseVal.height;

function ink(node) {
  const paths = [...node.querySelectorAll('path')].map(path => {
    const length = path.getTotalLength();
    path.style.stroke = 'currentColor'; path.style.strokeWidth = '16';
    path.style.strokeLinecap = 'round'; path.style.strokeLinejoin = 'round'; path.style.strokeDasharray = String(length);
    return { path, length };
  });
  return value => paths.forEach(({ path, length }, i) => {
    const t = clamp(value * (1 + paths.length * .002) - i * .002);
    path.style.strokeDashoffset = String(length * (1 - clamp(t / .75)));
    path.style.strokeOpacity = t > 0 && t < 1 ? '1' : '0';
    path.style.fillOpacity = String(clamp((t - .7) / .3));
  });
}

export function createNonpolynomial(slide) {
  const seed = slide.dataset.number === '19';
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;top:139px;width:866px;height:553px;color:#000;font-size:23px;line-height:1.35';
  slide.append(body);
  const diagram = createNonpolynomialDiagram(body);
  const theorem = document.createElement('div');
  theorem.style.cssText = 'position:absolute;left:0;width:866px;box-sizing:border-box;border:1px solid #000;padding:12px 16px;font-style:italic';
  const introduction = document.createElement('div');
  introduction.innerHTML = '<strong style="font-style:normal">Theorem (H.-Satriano).</strong> Let ' + m('(n,p,q)\\in\\mathbb{Z}_{\\geq0}^{3}') + '. Then ' + m('h_{\\mathrm{st}}^{p,q}(Y)\\geq0') + ' for all projective<br>Gorenstein canonical ' + m('n') + '-folds ' + m('Y') + ' ';
  typeset(introduction); theorem.append(introduction);
  const finalLine = document.createElement('span'); finalLine.style.whiteSpace = 'nowrap';
  const qualifier = document.createElement('span'); qualifier.style.cssText = 'position:relative;display:inline-block';
  const ifWord = math('\\textit{if}', 23), iffWords = math('\\textit{if and only if}', 23);
  qualifier.style.height = ifWord.getAttribute('height') + 'px'; qualifier.style.verticalAlign = ifWord.style.verticalAlign;
  ifWord.style.display = 'block';
  iffWords.style.cssText += ';position:absolute;left:0;top:' + (baseline(ifWord) - baseline(iffWords)) + 'px;color:' + red;
  qualifier.append(ifWord, iffWords); finalLine.append(qualifier, document.createTextNode(' at least one of the following holds:'));
  introduction.append(finalLine);
  const iffInk = ink(iffWords);
  const list = svg('svg', { width: 832, height: 84, viewBox: '0 0 832 84' });
  list.style.cssText = 'display:block;overflow:visible;margin-top:8px'; theorem.append(list); body.append(theorem);
  const conditions = ['\\min(p,q)\\leq1', '(p,q)=(2,2)', '|p-q|\\geq n-1', '\\{p,q\\}=\\{2,n\\}', 'n\\leq2'];
  const rows = conditions.map((latex, i) => {
    const group = svg('g'), row = [0, 1, 0, 1, 2][i], column = i === 2 || i === 3 ? 416 : 0;
    group.append(svg('circle', { cx: column + 10, cy: 15 + 28 * row, r: 2.5, fill: '#000' }));
    const node = math(latex, 23); node.setAttribute('x', column + 32); node.setAttribute('y', 15 + 28 * row - Number(node.getAttribute('height')) / 2);
    group.append(node); list.append(group); return group;
  });
  let example;
  if (seed) {
    example = document.createElement('div');
    example.style.cssText = 'position:absolute;left:0;top:365px;width:866px;box-sizing:border-box;border:1px solid #000;padding:12px 16px;font-style:italic';
    example.innerHTML = '<strong style="font-style:normal">Theorem.</strong> There exists a 5-dimensional projective Gorenstein terminal variety ' + m('Y') + ' where ' + m('E_{\\mathrm{st}}(Y;u,v)') + ' is a polynomial, but';
    const equation = document.createElement('div');
    equation.style.cssText = 'margin-top:10px;text-align:center';
    const left = math('h_{\\mathrm{st}}^{2,3}(Y)'), right = math('h_{\\mathrm{st}}^{3,2}(Y)');
    left.style.color = red; right.style.color = red;
    equation.append(left, math('\\;=\\;'), right, math('\\;=-1.'));
    example.append(equation); typeset(example); body.append(example);
  }
  const timeline = motion();
  let step = -1, revision = 0, disposed = false, current;
  const interpolate = (a, b, t) => Object.fromEntries(Object.keys(b).map(key => [key, a[key] + (b[key] - a[key]) * t]));
  function pose(next) {
    const stage = seed ? 6 : next;
    const value = {
      x: 433, bottom: 404, n: 8, unit: 17,
      edge: stage >= 2 ? 1 : 0, point: stage >= 3 ? 1 : 0, side: stage >= 4 ? 1 : 0, pair: stage >= 5 ? 1 : 0, surface: 0,
      top: stage ? 365 : 210, height: [0, 0, 28, 56, 56, 56, 84, 84][stage], margin: stage >= 2 ? 8 : 0, iff: stage === 7 ? 1 : 0,
      diagramAlpha: stage ? 1 : 0,
      ...Object.fromEntries(rows.map((_, i) => ['row' + i, i + 1 < stage ? 1 : 0]))
    };
    if (seed) Object.assign(value, { pointRed: next === 1 ? 1 : 0, rowRed: next === 1 ? 1 : 0, counterexamples: next === 2 ? 1 : 0, finite: next === 3 ? 1 : 0, theoremAlpha: next === 3 ? 0 : 1, exampleAlpha: next === 3 ? 1 : 0 });
    return value;
  }
  function paint(value) {
    current = value;
    const { x, bottom, n, unit, edge, point, side, pair, surface } = value;
    theorem.style.top = value.top + 'px';
    const a = Number(ifWord.getAttribute('width')), b = Number(iffWords.getAttribute('width'));
    qualifier.style.width = a + (b - a) * ease(clamp(value.iff / .4)) + 'px';
    ifWord.style.opacity = String(1 - ease(clamp(value.iff / .35)));
    iffInk(ease(clamp((value.iff - .4) / .6)));
    const height = Math.max(.001, value.height);
    list.setAttribute('height', height); list.setAttribute('viewBox', '0 0 832 ' + height);
    list.style.marginTop = value.margin + 'px';
    rows.forEach((row, i) => { row.style.opacity = String(value['row' + i]); });
    diagram.node.style.opacity = String(value.diagramAlpha);
    diagram.set({ x, bottom, n, unit, edge, point, side, pair, surface, ...(seed ? { pointRed: value.pointRed, counterexamples: value.counterexamples, finite: value.finite } : {}) });
    if (seed) {
      const color = 'rgb(' + [184,32,47].map(c => Math.round(c * value.rowRed)).join(',') + ')';
      rows[1].style.color = color; rows[1].firstElementChild.setAttribute('fill', color);
      theorem.style.opacity = String(value.theoremAlpha); theorem.style.visibility = value.theoremAlpha > 0 ? 'visible' : 'hidden';
      example.style.opacity = String(value.exampleAlpha); example.style.visibility = value.exampleAlpha > 0 ? 'visible' : 'hidden';
    }
  }
  async function animate(next, run) {
    const start = { ...current }, target = pose(next);
    if (seed) {
      const move = async (from, to, seconds) => await run(seconds, alpha => paint(interpolate(from, to, ease(alpha))));
      if (next === 1) {
        const point = { ...target, rowRed: 0 };
        if (!await move(start, point, .65)) return;
        await move(point, target, .35);
      } else if (next === 2) {
        const neutral = { ...target, counterexamples: 0 };
        if (!await move(start, neutral, .4)) return;
        await move(neutral, target, .85);
      } else {
        const hidden = { ...start, theoremAlpha: 0 };
        if (!await move(start, hidden, .3)) return;
        const diagram = { ...target, exampleAlpha: 0 };
        if (!await move(hidden, diagram, 1.1)) return;
        await move(diagram, target, .3);
      }
      return;
    }
    const delayed = ['diagramAlpha', ...rows.map((_, i) => 'row' + i)].filter(key => start[key] === 0 && target[key] > 0);
    if (!await run(next === 6 ? .35 : next === 1 ? .8 : .7, alpha => {
      const value = interpolate(start, target, ease(alpha));
      delayed.forEach(key => { value[key] = start[key]; });
      paint(value);
    })) return;
    if (delayed.length) {
      const settled = { ...current };
      await run(.25, alpha => paint(interpolate(settled, target, ease(alpha))));
    }
  }
  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      next = Math.max(0, Math.min(seed ? 3 : 7, Number(next) || 0));
      const previous = step, token = ++revision;
      timeline.cancel(); step = next; slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (previous >= 0 && next === previous + 1) await animate(next, run); else paint(pose(next));
      if (!disposed && token === revision) paint(pose(next));
    },
    dispose() { disposed = true; revision++; timeline.dispose(); diagram.dispose(); body.remove(); }
  };
}
