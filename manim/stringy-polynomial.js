import { svg, math, typeset, motion } from './slide-utils.js';
import { createBrace } from './hodge-stratum.js';
import { createPolynomialDiagram } from './polynomial-diagram.js';

const blue = '#3333b3', red = '#b8202f';
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

export function createPolynomial(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;top:139px;width:866px;height:553px;color:#000;font-size:23px;line-height:1.35';
  slide.append(body);
  const diagram = createPolynomialDiagram(body);
  const theorem = document.createElement('div');
  theorem.style.cssText = 'position:absolute;left:0;top:150px;width:866px;box-sizing:border-box;border:1px solid #000;padding:12px 16px;font-style:italic';
  const introduction = document.createElement('div');
  introduction.innerHTML = '<strong style="font-style:normal">Theorem (H.-Satriano).</strong> Let ' + m('(n,p,q)\\in\\mathbb{Z}_{\\geq0}^{3}') + '. Then ' + m('h_{\\mathrm{st}}^{p,q}(Y)\\geq0') + ' for all projective Gorenstein canonical ' + m('Y') + ' of dimension ' + m('n') + ' with polynomial ' + m('E_{\\mathrm{st}}(Y;u,v)');
  typeset(introduction); theorem.append(introduction);
  const finalLine = document.createElement('div'); finalLine.style.whiteSpace = 'nowrap';
  const qualifier = document.createElement('span'); qualifier.style.cssText = 'position:relative;display:inline-block';
  const ifWord = math('\\textit{if}', 23), iffWords = math('\\textit{if and only if}', 23);
  qualifier.style.height = ifWord.getAttribute('height') + 'px'; qualifier.style.verticalAlign = ifWord.style.verticalAlign;
  ifWord.style.display = 'block';
  iffWords.style.cssText += ';position:absolute;left:0;top:' + (baseline(ifWord) - baseline(iffWords)) + 'px;color:' + red;
  qualifier.append(ifWord, iffWords); finalLine.append(qualifier, document.createTextNode(' at least one of the following holds:'));
  introduction.append(finalLine);
  const iffInk = ink(iffWords);
  const list = svg('svg', { width: 832, height: 128, viewBox: '0 0 832 128' });
  list.style.cssText = 'display:block;overflow:visible;margin-top:8px';
  theorem.append(list); body.append(theorem);
  const first = svg('g'), second = svg('g'); list.append(first, second);
  function put(parent, latex, x, y, reference = null) {
    const node = math(latex, 23);
    node.setAttribute('x', x);
    node.setAttribute('y', reference ? Number(reference.getAttribute('y')) + baseline(reference) - baseline(node) : y - Number(node.getAttribute('height')) / 2);
    parent.append(node); return node;
  }
  const prefixes = ['\\min(p,q)', '\\max(p,q)'].map((value, i) => {
    first.append(svg('circle', { cx: 10, cy: 17 + 32 * i, r: 2.5, fill: blue }));
    return put(first, value, 32, 17 + 32 * i);
  });
  const tails = [['=0', '=n'], ['\\leq1', '\\geq n-1']].map(values => values.map((value, i) => put(first, value, 38 + Number(prefixes[i].getAttribute('width')), 0, prefixes[i])));
  const pens = tails.map(pair => pair.map(ink));
  const brace = createBrace(first, { size: 23 }); brace.set(300, 0, 64);
  const trivial = put(first, '\\text{trivial case}', 330, 32), olano = put(first, '\\text{Olano 2021}', 330, 32);
  olano.style.color = blue;
  const olanoInk = ink(olano);
  trivial.style.color = '#000';
  ['(p,q)=(2,2)', '(p,q)=(n-2,n-2)'].forEach((value, i) => {
    second.append(svg('circle', { cx: 10, cy: 81 + 32 * i, r: 2.5, fill: blue }));
    put(second, value, 32, 81 + 32 * i);
  });
  second.style.color = red;
  const specialBrace = createBrace(second, { color: red, size: 23 }); specialBrace.set(345, 64, 128);
  const specialName = put(second, '\\text{H.-Satriano}', 375, 96);
  const consequence = document.createElement('div');
  consequence.style.cssText = 'position:absolute;left:425px;top:93px;width:410px;box-sizing:border-box;border:1px solid #000;padding:12px 16px;overflow:hidden;font-style:italic';
  consequence.innerHTML = '<strong style="font-style:normal">Corollary</strong> Batyrev’s conjecture holds for ' + m('n\\leq4') + '.';
  typeset(consequence); body.append(consequence);
  const bullets = [...list.querySelectorAll('circle')];
  const timeline = motion();
  let step = -1, revision = 0, disposed = false, current;
  const mix = (a, b, t) => a + (b - a) * t;
  const interpolate = (a, b, t) => Object.fromEntries(Object.keys(b).map(key => [key, mix(a[key], b[key], t)]));
  function pose(next) {
    const width = 410, oldWidth = consequence.style.width;
    consequence.style.width = width + 'px';
    const oldHeight = consequence.style.height;
    consequence.style.height = 'auto';
    const corollaryHeight = consequence.offsetHeight;
    consequence.style.width = oldWidth; consequence.style.height = oldHeight;
    const top = next ? 285 : 150;
    return {
      x: next >= 5 ? 225 : 433, y: 122, n: next === 5 ? 4 : 8, unit: next === 5 ? 30 : 18,
      band: next >= 3 ? 2 : 1, bandAlpha: next >= 2 ? 1 : 0,
      special: next >= 4 ? 1 : 0, complete: next === 5 ? 1 : 0,
      top, height: next >= 4 ? 128 : next >= 2 ? 64 : 0, margin: next >= 2 ? 8 : 0,
      listAlpha: next >= 2 ? 1 : 0, diagramAlpha: next > 0 ? 1 : 0,
      oldAlpha: next < 3 ? 1 : 0, newInk: next >= 3 ? 1 : 0, color: next >= 3 ? 1 : 0,
      secondAlpha: next >= 4 ? 1 : 0, consequenceAlpha: next >= 5 ? 1 : 0,
      corollaryLeft: 425, corollaryTop: 93,
      corollaryWidth: width, corollaryHeight,
      braceAlpha: next === 6 ? 0 : 1, neutral: next === 6 ? 1 : 0, iff: next === 6 ? 1 : 0
    };
  }
  function paint(value) {
    current = value;
    const { x, y, n, unit, band, bandAlpha, special, complete, neutral } = value;
    theorem.style.top = value.top + 'px';
    const height = Math.max(.001, value.height);
    list.setAttribute('height', height); list.setAttribute('viewBox', '0 0 832 ' + height);
    list.style.marginTop = value.margin + 'px'; list.style.opacity = String(value.listAlpha);
    diagram.node.style.opacity = String(value.diagramAlpha); diagram.set({ x, y, n, unit, band, bandAlpha, special, complete, neutral });
    const color = 'rgb(' + [51, 51, 179].map(channel => Math.round(channel * value.color * (1 - value.neutral))).join(',') + ')';
    first.style.color = color; brace.group.style.color = color; olano.style.color = color;
    second.style.color = 'rgb(' + [184, 32, 47].map(channel => Math.round(channel * (1 - value.neutral))).join(',') + ')';
    brace.group.style.opacity = specialBrace.group.style.opacity = olano.style.opacity = specialName.style.opacity = String(value.braceAlpha);
    bullets.forEach(dot => dot.setAttribute('fill', 'rgb(' + [51, 51, 179].map(channel => Math.round(channel * (1 - value.neutral))).join(',') + ')'));
    qualifier.style.width = mix(Number(ifWord.getAttribute('width')), Number(iffWords.getAttribute('width')), ease(clamp(value.iff / .4))) + 'px';
    ifWord.style.opacity = String(1 - ease(clamp(value.iff / .35)));
    iffInk(ease(clamp((value.iff - .4) / .6)));
    tails[0].forEach(node => { node.style.opacity = String(value.oldAlpha); }); trivial.style.opacity = String(value.oldAlpha * value.braceAlpha);
    pens[1].forEach(write => write(value.newInk)); olanoInk(value.newInk);
    second.style.opacity = String(value.secondAlpha);
    consequence.style.opacity = String(value.consequenceAlpha);
    consequence.style.left = value.corollaryLeft + 'px'; consequence.style.top = value.corollaryTop + 'px';
    consequence.style.width = value.corollaryWidth + 'px'; consequence.style.height = value.corollaryHeight + 'px';
  }
  pens[0].forEach(write => write(1));
  async function animate(next, run) {
    if (next === 6) {
      const tween = (target, seconds) => { const start = { ...current }; return run(seconds, alpha => paint(interpolate(start, target, ease(alpha)))); };
      if (!await tween({ ...current, braceAlpha: 0 }, .25)) return;
      const target = pose(next);
      if (!await tween({ ...target, iff: current.iff }, 1.1)) return;
      await tween(target, .7);
      return;
    }
    const start = { ...current }, target = pose(next), duration = next === 5 ? 1.1 : next === 3 ? .95 : .75;
    const delayed = ['listAlpha', 'diagramAlpha', 'secondAlpha', 'consequenceAlpha'].filter(key => start[key] === 0 && target[key] > 0);
    if (!await run(duration, alpha => {
      const value = interpolate(start, target, ease(alpha));
      delayed.forEach(key => { value[key] = start[key]; });
      value.oldAlpha = mix(start.oldAlpha, target.oldAlpha, ease(clamp(alpha * duration / .22)));
      if (target.newInk > start.newInk) {
        const delay = start.oldAlpha > 0 ? .27 : 0;
        value.newInk = mix(start.newInk, target.newInk, ease(clamp((alpha * duration - delay) / (duration - delay))));
      }
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
      next = Math.max(0, Math.min(6, Number(next) || 0));
      const previous = step, token = ++revision;
      timeline.cancel(); step = next; slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (previous >= 0 && next === previous + 1) await animate(next, run); else paint(pose(next));
      if (!disposed && token === revision) paint(pose(next));
    },
    dispose() { disposed = true; revision++; timeline.dispose(); diagram.dispose(); body.remove(); }
  };
}
