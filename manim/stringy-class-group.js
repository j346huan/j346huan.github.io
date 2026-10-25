import { svg, math, typeset, motion } from './slide-utils.js';
import { createClassGroupDiagram, createClassGroupArrow } from './stringy-class-group-diagram.js';

const red = '#b8202f';
const ease = t => t * t * (3 - 2 * t);
const clamp = t => Math.max(0, Math.min(1, t));
const m = tex => '<span data-math="' + tex + '"></span>';
const marked = tex => '<span data-highlight>' + m(tex) + '</span>';

export function createClassGroup(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;top:139px;width:866px;height:553px;color:#000';
  const scene = svg('svg', { width: 866, height: 553, viewBox: '0 0 866 553', overflow: 'visible' });
  scene.style.position = 'absolute';
  body.append(scene);
  slide.append(body);
  const items = {};
  function formula(key, tex, r = 0) {
    const content = math(tex), node = svg('g', { 'data-term': key });
    node.append(content); scene.append(node);
    const width = Number(content.getAttribute('width')), height = Number(content.getAttribute('height'));
    const paths = [...content.querySelectorAll('path')].map(path => [path, path.getTotalLength()]);
    items[key] = { node, content, width, height, base: -content.viewBox.baseVal.y * height / content.viewBox.baseVal.height, r,
      write(amount) {
        paths.forEach(([path, length]) => {
          path.style.stroke = 'currentColor'; path.style.strokeWidth = '14'; path.style.strokeLinecap = 'round';
          path.style.strokeDasharray = String(length); path.style.strokeDashoffset = String(length * (1 - clamp(amount / .7)));
          path.style.strokeOpacity = amount > 0 && amount < 1 ? '1' : '0'; path.style.fillOpacity = String(clamp((amount - .7) / .3));
        });
      }
    };
  }
  function text(key, html, width = 866) {
    const node = document.createElement('div');
    node.dataset.term = key;
    node.style.cssText = 'position:absolute;left:0;top:0;width:' + width + 'px;font:23.8px/1.35 Beamer,serif';
    node.innerHTML = html; typeset(node); body.append(node);
    const measure = node.cloneNode(true);
    measure.style.position = 'fixed'; measure.style.top = '-2000px'; measure.style.visibility = 'hidden';
    document.body.append(measure);
    const height = measure.getBoundingClientRect().height;
    measure.remove();
    items[key] = { node, width, height, base: 0, r: 0, text: true, write() {} };
  }
  const O = '\\mathcal O_{Y,\\eta_\\alpha}', rank = '\\operatorname{rank}\\operatorname{Cl}(' + O + '^{\\mathrm h})';
  const Cl = '\\operatorname{Cl}_Y^{\\mathrm{\\acute{e}t}}|_{U_\\alpha}\\otimes\\mathbb Q';
  formula('lhs', 'h^{2,2}_{\\mathrm{st}}(Y)'); formula('ge', '\\geq'); formula('c', 'c'); formula('minus', '-');
  formula('sum', '\\sum_\\alpha'); formula('topDelta', '\\delta_\\alpha', 1);
  formula('rank', rank, 1); formula('delta', '\\delta_\\alpha', 1); formula('equal', '=');
  text('recall', 'Recall ' + m('\\delta_\\alpha') + ' is the dimension of the monodromy-invariant part of the stalk ' + marked('(\\mathcal D_\\alpha)_x') + ', with');
  formula('stalkDimension', '\\dim{(\\mathcal D_\\alpha)_x}=\\dim\\frac{\\operatorname{Weil}(U_x)_\\mathbb Q}{\\operatorname{Cart}(U_x)_\\mathbb Q}\\quad\\text{on an analytic nbhd.}');
  formula('analyticSequence', '0\\longrightarrow\\mathcal V_\\alpha^{01}\\longrightarrow\\mathcal V_\\alpha^2\\longrightarrow{\\mathcal D_\\alpha}\\longrightarrow0');
  text('bingener', 'Bingener–Flenner (1984) give the following étale analogue:');
  formula('divisors', '\\bigoplus_{D_i\\text{ over }U_\\alpha}(f_i^\\circ)_*^{\\mathrm{\\acute{e}t}}\\mathbb Q');
  formula('pic', '\\operatorname{Pic}_{X/Y}^{\\mathrm{\\acute{e}t}}|_{U_\\alpha}\\otimes\\mathbb Q');
  formula('cl', Cl); formula('zero', '0');
  for (let i = 0; i < 3; i++) formula('arrow' + i, '\\longrightarrow');
  formula('clBrace', '\\underbrace{\\phantom{' + Cl + '}}');
  items.clBrace.content.querySelectorAll('[data-mml-node="mphantom"]').forEach(node => node.remove());
  formula('clLabel', '\\mathcal D_\\alpha^{\\mathrm{\\acute{e}t}}');
  text('generic', 'Let ' + m('\\eta_\\alpha') + ' be the generic point of ' + m('C_\\alpha') + '. Then');
  formula('etSections', 'H^0(U_\\alpha,{\\mathcal D_\\alpha^{\\mathrm{\\acute{e}t}}})');
  formula('anSections', 'H^0(U_\\alpha,{\\mathcal D_\\alpha^{\\mathrm{an}}})');
  formula('etStalk', '(\\mathcal D_\\alpha^{\\mathrm{\\acute{e}t}})_{\\overline\\eta_\\alpha}^{\\pi_1^{\\mathrm{\\acute{e}t}}(U_\\alpha,\\overline\\eta_\\alpha)}');
  formula('anStalk', '(\\mathcal D_\\alpha)_x^{\\pi_1(U_\\alpha,x)}');
  formula('classInvariants', '(\\operatorname{Cl}(' + O + '^{\\mathrm{sh}})\\otimes\\mathbb Q)^{\\operatorname{Gal}_\\alpha}');
  for (let i = 0; i < 4; i++) formula('cong' + i, '\\cong');
  text('galois', 'where ' + marked('\\operatorname{Gal}_\\alpha') + ' is the absolute Galois group of ' + m('\\mathbb C(C_\\alpha)') + '.');
  for (const key of ['classDown', 'anDown']) {
    const arrow = createClassGroupArrow(), node = svg('g', { 'data-term': key });
    node.append(arrow.node); scene.append(node);
    items[key] = { node, width: arrow.width, height: arrow.height, base: 0, r: 0, write: arrow.draw };
  }
  const narrow = 574;
  text('failure', '<span style="color:' + red + '">' + m(rank) + '</span> measures the failure of ' + m(O + '^{\\mathrm h}') + ' to be <span style="white-space:nowrap">' + m('\\mathbb Q') + '-factorial</span>.', narrow);
  text('smallModel', 'Lyu–Murayama (2026) provide a small ' + m('\\mathbb Q') + '-factorial model', narrow);
  formula('model', '\\tau_\\alpha:V_\\alpha\\longrightarrow\\operatorname{Spec}' + O + '^{\\mathrm h}');
  text('curveCount', 'At least <span style="color:' + red + '">' + m(rank) + '</span> exceptional curves are contracted to the closed point.', narrow);
  text('blowup', 'Blow up each exceptional curve to get a divisorial valuation ' + m('F_{\\alpha,i}') + '. Each has discrepancy 1 and corresponds to a discrepancy-1 divisor over ' + m('U_\\alpha') + '.', narrow);
  formula('finalSum', '\\sum_\\alpha'); formula('finalRank', rank, 1);
  formula('le0', '\\leq'); formula('curves', '\\#\\{\\text{exceptional curves}\\}'); formula('le1', '\\leq'); formula('finalC', 'c');
  function mark(key, node, first, last) {
    (items[key].marks ??= []).push({ node, first, last });
  }
  for (const [key, first, last] of [['stalkDimension',2,3], ['analyticSequence',2,4], ['etSections',4,4], ['anSections',4,4]]) {
    const root = items[key].content.querySelector('[data-mml-node="math"]');
    mark(key, [...root.children].find(node => node.querySelector('[data-c="44"]')), first, last);
  }
  mark('recall', items.recall.node.querySelector('[data-highlight]'), 2, 3);
  mark('galois', items.galois.node.querySelector('[data-highlight]'), 6, 6);
  for (const key of ['etStalk', 'anStalk', 'classInvariants']) {
    const root = items[key].content.querySelector('[data-mml-node="math"]');
    const power = [...root.children].findLast(node => ['msup', 'msubsup'].includes(node.dataset.mmlNode));
    mark(key, power.children[1], key === 'classInvariants' ? 6 : 5, 6);
  }
  const diagram = createClassGroupDiagram(), diagramGroup = svg('g', { 'data-term': 'diagram' });
  diagramGroup.append(diagram.node); scene.append(diagramGroup);
  items.diagram = { node: diagramGroup, width: 250, height: 330, base: 0, r: 0, write: diagram.draw };
  diagram.curves.dataset.term = 'exceptionalGeometry'; scene.append(diagram.curves);
  items.exceptionalGeometry = { node: diagram.curves, width: 250, height: 330, base: 0, r: 0, write: diagram.drawCurves };
  const box = svg('rect', { fill: 'none', stroke: '#000', 'stroke-width': 1.1 });
  const boxGroup = svg('g', { 'data-term': 'box' }); boxGroup.append(box); scene.prepend(boxGroup);
  items.box = { node: boxGroup, width: 0, height: 0, base: 0, r: 0, write() {} };
  const put = (state, key, x, y) => state.set(key, { x, y, r: items[key].r });
  const center = (state, key, y, middle = 433) => put(state, key, middle - items[key].width / 2, y);
  function row(state, keys, y, gap = 7, start = 0, width = 866) {
    let x = start + (width - keys.reduce((sum, key) => sum + items[key].width, 0) - gap * (keys.length - 1)) / 2;
    keys.forEach(key => { put(state, key, x, y); x += items[key].width + gap; });
  }
  function layout(step) {
    const state = new Map(), end = step >= 9 ? 'rank' : 'topDelta';
    const top = ['lhs', 'ge', 'c', 'minus', 'sum', end];
    row(state, top, 44, 7, step >= 10 ? 292 : 0, step >= 10 ? narrow : 866);
    const left = state.get('lhs').x - 17, right = state.get(end).x + items[end].width + 17;
    state.set('box', { x: left, y: 3, w: right - left, h: 78 });
    if (step >= 2 && step <= 3) {
      put(state, 'recall', 0, 112); center(state, 'stalkDimension', 223); center(state, 'analyticSequence', 291);
    }
    if (step === 3) put(state, 'bingener', 0, 340);
    if (step >= 3 && step <= 7) {
      const y = step === 3 ? 426 : 198;
      row(state, ['divisors', 'arrow0', 'pic', 'arrow1', 'cl', 'arrow2', 'zero'], y);
      const point = state.get('cl'), middle = point.x + items.cl.width / 2;
      center(state, 'clBrace', y, middle);
      center(state, 'clLabel', y - items.clBrace.base + items.clBrace.height + 25, middle);
    }
    if (step >= 4 && step <= 7) {
      center(state, 'analyticSequence', 121);
      put(state, 'generic', 0, 278);
      const comparison = step === 4 ? ['etSections', 'cong1', 'anSections'] : step === 5 ? ['etStalk', 'cong0', 'etSections', 'cong1', 'anSections', 'cong2', 'anStalk'] : ['classInvariants', 'cong3', 'etStalk', 'cong0', 'etSections', 'cong1', 'anSections', 'cong2', 'anStalk'];
      row(state, comparison, 358, step >= 6 ? 5 : 9);
      if (step >= 6) put(state, 'galois', 0, step === 7 ? 486 : 430);
      if (step === 7) {
        for (const [source, arrow, target] of [['classInvariants', 'classDown', 'rank'], ['anSections', 'anDown', 'delta']]) {
          const middle = state.get(source).x + items[source].width / 2;
          center(state, arrow, 385, middle); center(state, target, 452, middle);
        }
      }
    }
    if (step === 8) row(state, ['rank', 'equal', 'delta'], 280, 18);
    if (step >= 10) {
      put(state, 'diagram', 0, 104);
      if (step === 10) {
        let y = 102;
        put(state, 'failure', 292, y); y += items.failure.height + 13;
        put(state, 'smallModel', 292, y); y += items.smallModel.height + 39;
        center(state, 'model', y, 579);
      } else {
        put(state, 'exceptionalGeometry', 0, 104);
        center(state, 'model', 150, 579);
        put(state, 'curveCount', 292, 190);
        const y = 190 + items.curveCount.height + 27;
        if (step >= 12) put(state, 'blowup', 292, y);
        if (step === 13) row(state, ['finalSum', 'finalRank', 'le0', 'curves', 'le1', 'finalC'], y + items.blowup.height + 63, 7, 292, narrow);
      }
    }
    state.forEach((point, key) => {
      point.r = key === 'topDelta' && step >= 7 ? 0 : key === 'clLabel' ? Number(step <= 4) : items[key].r;
      (items[key].marks || []).forEach(({ first, last }, i) => { point['m' + i] = Number(step >= first && step <= last); });
    });
    return state;
  }
  const states = Array.from({ length: 13 }, (_, i) => layout(i + 1));
  function position(key, point) {
    const item = items[key], y = point.y - item.base;
    if (item.text) item.node.style.transform = 'translate(' + point.x + 'px,' + y + 'px)';
    else item.node.setAttribute('transform', 'translate(' + point.x + ',' + y + ')');
    const color = amount => 'rgb(' + [184,32,47].map(c => Math.round(c * amount)).join(',') + ')';
    item.node.style.color = color(point.r ?? item.r);
    (item.marks || []).forEach(({ node }, i) => { node.style.color = color(point['m' + i] || 0); });
    if (key === 'box') { box.setAttribute('width', point.w); box.setAttribute('height', point.h); }
  }
  function show(key, amount) {
    items[key].node.style.opacity = String(amount); items[key].node.style.visibility = amount > 0 ? 'visible' : 'hidden';
  }
  function display(state) {
    Object.entries(items).forEach(([key, item]) => {
      show(key, state.has(key) ? 1 : 0); item.write(1);
      if (state.has(key)) position(key, state.get(key));
    });
  }
  async function transition(before, after, run, draw = false) {
    const leaving = [...before.keys()].filter(key => !after.has(key));
    const common = [...after.keys()].filter(key => before.has(key));
    const entering = [...after.keys()].filter(key => !before.has(key));
    if (leaving.length && !await run(.3, t => leaving.forEach(key => show(key, 1 - ease(t))))) return false;
    const moved = common.some(key => Object.keys(after.get(key)).some(property => after.get(key)[property] !== before.get(key)[property]));
    if (moved && !await run(.75, t => common.forEach(key => {
      const a = before.get(key), b = after.get(key), point = {};
      Object.keys(b).forEach(property => { point[property] = a[property] + (b[property] - a[property]) * ease(t); });
      position(key, point);
    }))) return false;
    entering.forEach(key => { position(key, after.get(key)); items[key].write(1); });
    if (draw) {
      const ink = entering.filter(key => !items[key].text && key !== 'box');
      if (ink.length && !await run(.75, t => ink.forEach(key => { show(key, 1); items[key].write(t); }))) return false;
      const rest = entering.filter(key => !ink.includes(key));
      if (rest.length && !await run(.3, t => rest.forEach(key => show(key, ease(t))))) return false;
    } else if (moved || leaving.length) {
      if (entering.length && !await run(.3, t => entering.forEach(key => show(key, ease(t))))) return false;
    } else entering.forEach(key => show(key, 1));
    display(after);
    return true;
  }
  const timeline = motion();
  let step = -1, revision = 0, disposed = false;
  display(new Map());
  return {
    animated: true,
    async play(value = 0) {
      if (disposed) return;
      const next = Math.max(0, Math.min(12, Number(value) || 0)), previous = step, token = ++revision;
      timeline.cancel(); step = next; slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (previous >= 0 && next === previous + 1) {
        const before = states[previous], after = states[next];
        display(before);
        if (next === 8) {
          const aligned = new Map(before);
          aligned.delete('equal'); aligned.delete('delta');
          put(aligned, 'rank', after.get('rank').x, 150);
          if (!await transition(before, aligned, run)) return;
          const cleared = new Map(aligned); cleared.delete('topDelta');
          if (!await transition(aligned, cleared, run)) return;
          await transition(cleared, after, run);
        } else await transition(before, after, run, [6,7,9,10].includes(next));
      } else display(states[next]);
      if (!disposed && token === revision) display(states[next]);
    },
    dispose() { disposed = true; revision++; timeline.dispose(); body.remove(); }
  };
}
