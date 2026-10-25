import { svg, math, typeset, motion } from './slide-utils.js';
import { createDefectDiagram } from './defect-diagram.js';

const red = '#b8202f';
const ease = t => t * t * (3 - 2 * t);
const m = value => '<span data-math="' + value + '"></span>';
const base = node => -node.viewBox.baseVal.y * Number(node.getAttribute('height')) / node.viewBox.baseVal.height;
const width = node => Number(node.getAttribute('width'));
const show = (node, value) => { node.style.opacity = String(value); node.style.visibility = value > 0 ? 'visible' : 'hidden'; };
const place = (node, x, y) => { node.setAttribute('x', x); node.setAttribute('y', y - base(node)); };

export function createDefect(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;top:139px;width:866px;height:553px;color:#000;font-size:23px;line-height:1.35';
  slide.append(body);
  const scene = svg('svg', { width: 866, height: 553, viewBox: '0 0 866 553' });
  scene.style.cssText = 'position:absolute;inset:0;overflow:visible;pointer-events:none';
  body.append(scene);
  const diagram = createDefectDiagram(scene);
  function text(html, y, bullet = false) {
    const node = document.createElement('div');
    node.style.cssText = 'position:absolute;left:240px;top:' + y + 'px;width:626px';
    node.innerHTML = bullet ? '<ul style="margin:0;padding-left:25px"><li>' + html + '</li></ul>' : html;
    typeset(node); body.append(node); return node;
  }
  const generic = text('Let ' + m('E_x=f^{-1}(x)') + '. Generically ' + m('E_x') + ' is an SNC surface.', 24, true);
  const local = text('The local defect at ' + m('x') + ' is', 55, true);
  const localFinal = text('The local defect at ' + m('x') + ' is ' + m('\\sigma(x)=') + '<span data-link-dimension style="margin:0 8px">' + m('h^2(L_x)') + '</span>.', 55, true);
  const neighbourhood = text('where ' + m('U_x') + ' is an analytic neighbourhood of ' + m('x') + ' in a general 3-fold linear slice.', 173);
  neighbourhood.style.left = '265px'; neighbourhood.style.width = '601px';
  const extra = text('<ul style="margin:0;padding-left:25px"><li>Globalize these sequences to local systems on <span style="color:' + red + '">' + m('U_\\alpha') + '</span>.</li><li style="margin-top:8px">' + m('\\mathcal D_\\alpha') + ' is related to ' + m('\\sigma(x)') + ' by monodromy <span style="color:' + red + '">' + m('G_\\alpha') + '</span>.</li></ul>', 239);
  const [globalize, monodromy] = extra.querySelectorAll('li');
  const summary = text('<ul style="margin:0;padding-left:25px"><li style="margin-bottom:8px">The local defect at ' + m('x') + ' is ' + m('\\sigma(x)=h^2(L_x)') + '.</li><li style="margin-bottom:8px">The defect local system is ' + m('\\mathcal D_\\alpha') + '.</li><li style="white-space:nowrap">The global defect on <span style="color:' + red + '">' + m('U_\\alpha') + '</span> is ' + m('H^0(\\mathcal D_\\alpha)=\\sigma(x)^{G_\\alpha}') + '.</li></ul>', 276.5);
  summary.style.transform = 'translateY(-50%)';
  [...summary.querySelectorAll('[data-mml-node="msup"]')].at(-1).lastElementChild.setAttribute('fill', red);
  const layer = svg('svg', { width: 626, height: 350, viewBox: '0 0 626 350' });
  layer.style.cssText = 'position:absolute;left:240px;top:0;overflow:visible;pointer-events:none'; body.append(layer);
  function term(latex, x = 0, y = 0, size = 23.8) {
    const node = math(latex, size); place(node, x, y); layer.append(node); return node;
  }
  const quotient = term('\\dim\\bigl(\\operatorname{Weil}(U_x)_{\\mathbb Q}/\\operatorname{Cart}(U_x)_{\\mathbb Q}\\bigr)');
  const olano = ['\\sigma(x)', '=', 'h^{1,1}(E_x^{[1]})', '-', 'h^0(E_x^{[2]})', '-', 'h^0(E_x^{[1]})'].map(value => term(value));
  const citation = term('\\text{(Olano 2021)}');
  const total = olano.reduce((sum, node) => sum + width(node), 0) + 6 * 5;
  let x = (626 - total - 18 - width(citation)) / 2;
  const positions = olano.map(node => { const point = [x, 137]; place(node, ...point); x += width(node) + 5; return point; });
  place(citation, x + 13, 137);
  const quotientX = (626 - width(olano[0]) - width(olano[1]) - width(quotient) - 10) / 2;
  const quotientPositions = [[quotientX, 137], [quotientX + width(olano[0]) + 5, 137]];
  place(quotient, quotientPositions[1][0] + width(olano[1]) + 5, 137);
  const linkEqual = term('=', positions[1][0], 189);
  const linkDimension = term('h^2(L_x)', positions[2][0], 189);
  const laza = term('\\text{(Friedman–Laza 2024)}', positions[2][0] + width(linkDimension) + 18, 189);
  const entries = [
    ['0','\\longrightarrow','H^2(E_x)','\\longrightarrow','H^2(E_x^{[1]})','\\longrightarrow','H^2(E_x^{[2]})','\\longrightarrow','0'],
    ['0','\\longrightarrow','H_4(E_x)(-3)','\\longrightarrow','H^2(E_x)','\\longrightarrow','H^2(L_x)','\\longrightarrow','0'],
    ['0','\\longrightarrow','\\mathcal V_\\alpha^2','\\longrightarrow','\\mathcal V_\\alpha^{21}','\\longrightarrow','\\mathcal V_\\alpha^{22}','\\longrightarrow','0'],
    ['0','\\longrightarrow','\\mathcal V_\\alpha^{01}','\\longrightarrow','\\mathcal V_\\alpha^2','\\longrightarrow','\\mathcal D_\\alpha','\\longrightarrow','0']
  ].map(row => row.map(value => term(value)));
  function sequenceLayout(rows) {
    const sizes = rows[0].map((_, index) => Math.max(...rows.map(row => width(row[index]))));
    const columns = [];
    let x = (626 - sizes.reduce((sum, size) => sum + size, 0) - 48) / 2;
    sizes.forEach(size => { columns.push(x + size / 2); x += size + 6; });
    return rows.map((row, ri) => row.map((node, ci) => [columns[ci] - width(node) / 2, ri % 2 ? 204 : 142]));
  }
  const sequencePositions = sequenceLayout(entries), compactPositions = sequenceLayout(entries.slice(2));
  const movers = [[olano[2], entries[0][4]], [olano[4], entries[0][6]], [olano[6], entries[1][2]], [linkDimension, entries[1][6]]];
  const boxes = [localFinal.querySelector('[data-link-dimension] .math-svg'), entries[1][6]].map(target => {
    const bounds = target.viewBox.baseVal, scale = width(target) / bounds.width;
    const box = svg('rect', {
      x: bounds.x - 5 / scale, y: bounds.y - 4 / scale,
      width: bounds.width + 10 / scale, height: bounds.height + 8 / scale,
      fill: 'none', stroke: red, 'stroke-width': 1.4 / scale, pathLength: 1, 'stroke-dasharray': 1
    });
    target.prepend(box); return box;
  });
  function mark(value) {
    boxes.forEach(box => {
      box.setAttribute('stroke-dashoffset', String(1 - value)); show(box, value > 0 ? 1 : 0);
    });
  }
  const nodes = [generic, local, localFinal, neighbourhood, globalize, monodromy, summary, quotient, ...olano, citation, linkEqual, linkDimension, laza, ...entries.flat(), ...boxes];
  const timeline = motion();
  let step = -1, revision = 0, disposed = false;
  let diagramState = { compact: 0, fiber: 0, spiral: 0, loop: false };
  const diagramSet = patch => { diagramState = { ...diagramState, ...patch }; diagram.set(diagramState); summary.style.top = diagram.centerY() + 'px'; };

  function state(next) {
    nodes.forEach(node => show(node, 0));
    diagramSet({ compact: next >= 1 ? 1 : 0, fiber: next >= 1 ? 1 : 0, spiral: next >= 7 ? 1 : 0, loop: next >= 7 });
    olano.forEach((node, i) => place(node, ...positions[i]));
    place(linkDimension, positions[2][0], 189);
    entries.forEach((row, ri) => row.forEach((node, ci) => place(node, ...(next >= 6 && ri >= 2 ? compactPositions[ri - 2][ci] : sequencePositions[ri][ci]))));
    if (next >= 1 && next < 8) show(generic, 1);
    if (next >= 2 && next < 5) show(local, 1);
    if (next === 2) {
      [quotient, neighbourhood, olano[0], olano[1]].forEach(node => show(node, 1));
      quotientPositions.forEach((point, i) => place(olano[i], ...point));
    }
    if (next >= 3 && next < 5) [...olano, citation].forEach(node => show(node, 1));
    if (next === 4) [linkEqual, linkDimension, laza].forEach(node => show(node, 1));
    if (next >= 5 && next < 8) {
      show(localFinal, 1);
      entries.slice(next >= 6 ? 2 : 0, next >= 6 ? 4 : 2).flat().forEach(node => show(node, 1));
    }
    if (next === 5) mark(1);
    if (next >= 6 && next < 8) show(globalize, 1);
    if (next === 7) show(monodromy, 1);
    if (next === 8) show(summary, 1);
  }
  const fade = (run, list, incoming, seconds = .3) => run(seconds, t => list.forEach(node => show(node, incoming ? ease(t) : 1 - ease(t))));
  async function moveDiagram(run, patch, seconds = .8) {
    const start = { ...diagramState };
    return run(seconds, t => diagramSet(Object.fromEntries(Object.entries(patch).map(([key, value]) => [key, start[key] + (value - start[key]) * ease(t)]))));
  }
  async function replaceTerms(run, pairs) {
    if (!await fade(run, pairs.map(([from]) => from), false, .3)) return false;
    return fade(run, pairs.map(([, to]) => to), true, .35);
  }
  async function animate(next, run) {
    if (next === 1) {
      if (!await moveDiagram(run, { compact: 1 })) return;
      if (!await moveDiagram(run, { fiber: 1 }, .6)) return;
      await fade(run, [generic], true);
    } else if (next === 2) {
      state(next);
    } else if (next === 3) {
      if (!await fade(run, [quotient, neighbourhood], false)) return;
      if (!await run(.7, t => quotientPositions.forEach((start, i) => place(olano[i], start[0] + (positions[i][0] - start[0]) * ease(t), start[1] + (positions[i][1] - start[1]) * ease(t))))) return;
      await fade(run, [...olano.slice(2), citation], true);
    } else if (next === 4) {
      [linkEqual, linkDimension, laza].forEach(node => show(node, 1));
    } else if (next === 5) {
      if (!await fade(run, [olano[0], olano[1], olano[3], olano[5], citation, linkEqual, laza, local], false)) return;
      const starts = movers.map(([from]) => [Number(from.getAttribute('x')), Number(from.getAttribute('y')) + base(from)]);
      const ends = movers.map(([from, to]) => [Number(to.getAttribute('x')) + (width(to) - width(from)) / 2, Number(to.getAttribute('y')) + base(to)]);
      if (!await run(.85, t => movers.forEach(([node], i) => place(node, starts[i][0] + (ends[i][0] - starts[i][0]) * ease(t), starts[i][1] + (ends[i][1] - starts[i][1]) * ease(t))))) return;
      if (!await replaceTerms(run, movers)) return;
      const held = new Set(movers.map(([, node]) => node));
      if (!await fade(run, [localFinal, ...entries.slice(0, 2).flat().filter(node => !held.has(node))], true)) return;
      await run(.5, t => mark(ease(t)));
    } else if (next === 6) {
      if (!await fade(run, boxes, false)) return;
      const pairs = [];
      for (let row = 0; row < 2; row++) for (const column of [2, 4, 6]) pairs.push([entries[row][column], entries[row + 2][column]]);
      if (!await replaceTerms(run, pairs)) return;
      entries.slice(0, 2).flat().forEach(node => show(node, 0));
      entries.slice(2).flat().forEach(node => show(node, 1));
      if (!await run(.65, t => entries.slice(2).forEach((row, ri) => row.forEach((node, ci) => {
        const start = sequencePositions[ri + 2][ci], end = compactPositions[ri][ci];
        place(node, start[0] + (end[0] - start[0]) * ease(t), end[1]);
      })))) return;
      await fade(run, [globalize], true);
    } else if (next === 7) {
      if (!await moveDiagram(run, { spiral: 1 }, 1.1)) return;
      diagramSet({ loop: true });
      await fade(run, [monodromy], true);
    } else if (next === 8) {
      if (!await fade(run, [generic, localFinal, ...entries.slice(2).flat(), globalize, monodromy], false)) return;
      await fade(run, [summary], true);
    }
  }
  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      next = Math.max(0, Math.min(8, Number(next) || 0));
      const previous = step, token = ++revision;
      timeline.cancel(); step = next; slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (previous >= 0 && next === previous + 1) { state(previous); await animate(next, run); }
      else state(next);
      if (!disposed && token === revision) state(next);
    },
    dispose() { disposed = true; revision++; timeline.dispose(); diagram.dispose(); body.remove(); }
  };
}
