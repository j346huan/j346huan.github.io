import { typeset, motion } from './slide-utils.js';
import { createSeedConstructionDiagram } from './seed-construction-diagram.js';
import { createSeedConstructionBlades } from './seed-construction-blades.js';

const m = latex => '<span data-math="' + latex + '"></span>';
const ease = x => x * x * (3 - 2 * x);
const mix = (a, b, t) => a + (b - a) * t;

export function createSeedConstruction(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;top:145px;width:866px;height:550px;color:#000;font:23px/1.3 Beamer,serif';
  slide.append(body);
  const geometry = createSeedConstructionDiagram(body), blades = createSeedConstructionBlades(body);
  for (const item of [geometry.node, blades.node]) Object.assign(item.style, { position: 'absolute', left: '0', top: '0' });
  const rows = {};
  function row(key, html, bullet = true, width = 866) {
    const node = document.createElement('div');
    node.style.cssText = 'position:absolute;left:0;top:0;box-sizing:border-box;width:' + width + 'px;' + (bullet ? 'padding-left:24px' : '');
    node.innerHTML = (bullet ? '<span style="position:absolute;left:4px;color:#3333b3">•</span>' : '') + html;
    typeset(node); body.append(node); rows[key] = node;
  }
  row('define', 'Define ' + m('Y') + ' in ' + m('\\mathbb P^5_{[s:t:x_0:\\dots:x_3]}') + ', with ' + m('L=V(x_0,\\dots,x_3)') + '.');
  row('choose', 'Take ' + m('Y=V(sq_0(x)+tq_1(x)+c(x))') + ', where ' + m('q_0,q_1') + ' are quadratic and ' + m('c') + ' is cubic.');
  row('equation', m('Y=V(sq_0(x)+tq_1(x)+c(x))') + '<span data-punctuation>.</span>');
  row('loci', m('C=V(q_0,q_1),\\quad Z=V(q_0,q_1,c)') + '.', false);
  for (const key of ['equation', 'loci']) Object.assign(rows[key].style, { width: 'max-content', whiteSpace: 'nowrap' });
  const punctuation = rows.equation.querySelector('[data-punctuation]');
  row('blowup', 'Blow up ' + m('\\mathbb P^5') + ' along ' + m('L') + ': at each point add a copy of ' + m('\\mathbb P^3') + '.');
  row('resolve', 'This resolves ' + m('Y') + ', which is singular along ' + m('L') + '.');
  row('map', 'To compute discrepancy, consider ' + m('\\operatorname{Bl}_L\\mathbb P^5\\longrightarrow\\mathbb P^3') + '.');
  row('fiber', 'The fiber at each ' + m('x\\in\\mathbb P^3') + ' is a copy of ' + m('\\mathbb P^2') + '.');
  row('restrict', 'Restrict to ' + m('\\operatorname{Bl}_L Y\\longrightarrow\\mathbb P^3') + '.');
  row('vary', 'Fibers vary over ' + m('\\mathbb P^3') + ' at ' + m('C=V(q_0,q_1)') + ' and ' + m('Z=V(q_0,q_1,c)') + '.');
  row('exceptional', 'At ' + m('x\\in C\\setminus Z') + ', get exceptional fiber ' + m('\\mathbb P^1') + '.');
  row('strict', 'At ' + m('x\\in\\mathbb P^3\\setminus C') + ', get strict transform fiber ' + m('\\mathbb P^1') + '.');
  row('special', 'At ' + m('x\\in Z') + ' (12 such points), get special fiber ' + m('\\mathbb P^2') + '.');
  row('compute', 'Now the class of the resolution of ' + m('Y') + ', that of the exceptional divisor and its discrepancy are easy to compute.');
  row('fourfold', m('Y') + ' is a 4-fold with negative stringy Hodge numbers, but ' + m('E_{\\mathrm{st}}(Y)') + ' is not a polynomial.', true, 410);
  row('product', 'Take ' + m("Y'=Y\\times\\mathbb P^1") + '.', true, 410);
  row('fivefold', 'Then ' + m("Y'") + ' is a 5-fold with negative stringy Hodge numbers and polynomial ' + m("E_{\\mathrm{st}}(Y')") + '.', true, 410);
  const timeline = motion();
  let current, step = -1, revision = 0, disposed = false;
  function pose(next) {
    const state = { geometry: next < 12 ? 1 : 0, blades: next >= 12 ? 1 : 0, geometryStep: Math.min(next, 11), bladeStep: Math.max(0, next - 12) };
    Object.keys(rows).forEach(key => { state[key] = 0; state[key + 'X'] = 0; state[key + 'Y'] = 380; });
    const sequences = [ ['define'], ['define','choose'], ['blowup'], ['blowup','resolve'], ['map'], ['map','fiber'], ['restrict'], ['restrict','vary'], ['exceptional'], ['exceptional','strict'], ['special'], ['compute'] ];
    if (next < 12) {
      let y = 380;
      if (next >= 2) {
        state.equation = 1; state.equationY = y;
        if (next >= 8) { state.loci = 1; state.lociX = rows.equation.offsetWidth + 9; state.lociY = y; }
        y += Math.max(rows.equation.offsetHeight, next >= 8 ? rows.loci.offsetHeight : 0) + 9;
      }
      for (const key of sequences[next]) { state[key] = 1; state[key + 'Y'] = y; y += rows[key].offsetHeight + 7; }
    } else if (next >= 15) {
      let y = 110;
      for (const key of ['fourfold', ...(next >= 16 ? ['product'] : []), ...(next >= 17 ? ['fivefold'] : [])]) {
        state[key] = 1; state[key + 'X'] = 456; state[key + 'Y'] = y; y += rows[key].offsetHeight + 20;
      }
    }
    return state;
  }
  function paint(value) {
    current = value;
    punctuation.textContent = value.loci > 0 ? ',' : '.';
    geometry.node.style.opacity = String(value.geometry); geometry.node.style.visibility = value.geometry > 0 ? 'visible' : 'hidden';
    blades.node.style.opacity = String(value.blades); blades.node.style.visibility = value.blades > 0 ? 'visible' : 'hidden';
    geometry.set(value.geometryStep); blades.set(value.bladeStep);
    for (const [key, node] of Object.entries(rows)) {
      node.style.opacity = String(value[key]); node.style.visibility = value[key] > 0 ? 'visible' : 'hidden';
      node.style.transform = 'translate(' + value[key + 'X'] + 'px,' + value[key + 'Y'] + 'px)';
    }
  }
  async function animate(next, run) {
    const target = pose(next);
    const move = async (end, seconds) => {
      const start = { ...current };
      return run(seconds, t => paint(Object.fromEntries(Object.keys(end).map(key => [key, mix(start[key], end[key], ease(t))]))));
    };
    const removing = { ...current };
    Object.keys(rows).forEach(key => { if (!target[key]) removing[key] = 0; });
    if (next === 12) removing.geometry = 0;
    if (!await move(removing, .25)) return;
    const diagram = { ...target };
    Object.keys(rows).forEach(key => { if (!current[key] && target[key]) diagram[key] = 0; });
    if (!await move(diagram, next === 17 ? 2.5 : next === 14 ? 1.5 : next >= 12 ? 1.05 : .75)) return;
    await move(target, .25);
  }
  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      next = Math.max(0, Math.min(17, Number(next) || 0));
      const previous = step, token = ++revision; timeline.cancel(); step = next; slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (previous >= 0 && next === previous + 1) await animate(next, run); else paint(pose(next));
      if (!disposed && token === revision) paint(pose(next));
    },
    dispose() { disposed = true; revision++; timeline.dispose(); geometry.dispose(); blades.dispose(); body.remove(); }
  };
}
