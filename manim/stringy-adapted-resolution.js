import { svg, math, typeset, motion } from './slide-utils.js';

const red = '#b8202f';
const clamp = x => Math.max(0, Math.min(1, x));
const ease = x => x * x * (3 - 2 * x);
const m = value => '<span data-math="' + value + '"></span>';
const baseline = node => -node.viewBox.baseVal.y * Number(node.getAttribute('height')) / node.viewBox.baseVal.height;

function ink(node) {
  const paths = [...node.querySelectorAll('path')].map(path => {
    const length = path.getTotalLength();
    path.style.stroke = 'currentColor'; path.style.strokeWidth = '16';
    path.style.strokeLinecap = 'round'; path.style.strokeLinejoin = 'round'; path.style.strokeDasharray = String(length);
    return { path, length };
  });
  return value => paths.forEach(({ path, length }, i) => {
    const t = clamp(value * (1 + paths.length * .003) - i * .003);
    path.style.strokeDashoffset = String(length * (1 - clamp(t / .75)));
    path.style.strokeOpacity = t > 0 && t < 1 ? '1' : '0';
    path.style.fillOpacity = String(clamp((t - .7) / .3));
  });
}

export function createAdaptedResolution(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;top:139px;width:866px;height:553px;color:#000;font-size:23px;line-height:1.35';
  slide.append(body);
  const theorem = document.createElement('div');
  theorem.style.cssText = 'position:absolute;left:0;top:0;width:866px;height:72px;box-sizing:border-box;border:1px solid #000';
  const theoremCanvas = svg('svg', { width: 866, height: 72, viewBox: '0 0 866 72' });
  theoremCanvas.style.overflow = 'visible';
  const theoremIntro = math('\\textbf{Theorem.}\\quad\\textit{For projective Gorenstein canonical }Y,', 23.8), theoremResult = math('h_{\\mathrm{st}}^{2,2}(Y)\\geq0.', 23.8);
  theoremCanvas.append(theoremIntro, theoremResult); theorem.append(theoremCanvas); body.append(theorem);
  const equation = svg('svg', { width: 866, height: 180, viewBox: '0 0 866 180' });
  equation.style.cssText = 'position:absolute;left:0;top:112px;overflow:visible'; body.append(equation);
  const terms = ['h_{\\mathrm{st}}^{2,2}(Y)=h_c^{2,2}(', 'X\\setminus D', ')+c'].map(value => math(value, 27));
  const total = terms.reduce((sum, node) => sum + Number(node.getAttribute('width')), 0) + 4;
  let tx = (866 - total) / 2;
  terms.forEach((node, i) => { node.setAttribute('x', tx); node.setAttribute('y', 43 - baseline(node)); equation.append(node); tx += Number(node.getAttribute('width')) + (i ? 0 : 2); });
  const variable = terms[1], brace = math('\\underbrace{\\phantom{X\\setminus D}}', 27);
  brace.setAttribute('x', Number(variable.getAttribute('x')) + (Number(variable.getAttribute('width')) - Number(brace.getAttribute('width'))) / 2);
  brace.setAttribute('y', 43 - baseline(brace)); equation.append(brace);
  const bracePen = ink(brace), mixed = math('\\text{mixed Hodge structure}', 21);
  mixed.setAttribute('x', Number(variable.getAttribute('x')) + (Number(variable.getAttribute('width')) - Number(mixed.getAttribute('width'))) / 2);
  mixed.setAttribute('y', Number(brace.getAttribute('y')) + Number(brace.getAttribute('height')) + 8); equation.append(mixed);
  const panel = document.createElement('div');
  panel.style.cssText = 'position:absolute;left:0;top:88px;width:866px;height:461px;box-sizing:border-box;border:1px solid #000;overflow:hidden';
  const heading = document.createElement('div'); heading.textContent = 'Adapted resolution';
  heading.style.cssText = 'position:absolute;left:16px;top:12px;font-weight:bold'; panel.append(heading); body.append(panel);
  const diagram = svg('svg', { width: 866, height: 461, viewBox: '0 0 866 461' });
  diagram.style.cssText = 'position:absolute;left:0;top:0;overflow:hidden;pointer-events:none'; panel.append(diagram);
  const defs = svg('defs'), gradient = svg('linearGradient', { id: 'adapted-diagram-fade', gradientUnits: 'userSpaceOnUse', x1: 0, y1: 42, x2: 0, y2: 451 });
  [[0, 0], [.04, 1], [.96, 1], [1, 0]].forEach(([offset, opacity]) => gradient.append(svg('stop', { offset, 'stop-color': '#fff', 'stop-opacity': opacity })));
  const mask = svg('mask', { id: 'adapted-diagram-mask', maskUnits: 'userSpaceOnUse', x: 0, y: 0, width: 866, height: 461 });
  mask.append(svg('rect', { x: 0, y: 0, width: 866, height: 461, fill: 'url(#adapted-diagram-fade)' })); defs.append(gradient, mask); diagram.append(defs);
  const scene = svg('g', { mask: 'url(#adapted-diagram-mask)' }); diagram.append(scene);
  const lower = svg('g'); scene.append(lower);
  const surface = svg('path', { d: 'M-150,-38 C-92,-72 82,-70 148,-26 L126,55 C34,83 -88,70 -155,29 Z', fill: 'none', stroke: '#000', 'stroke-width': 1.2 });
  const curve = svg('path', { d: 'M-83.984,-36.032 C-22,-47.36 30,-30.4 50,0 C93,38 128,32 129,0 C130,-35 98,-45 50,0 C6.8,30.96 -40.5472,39.1104 -84.949888,37.51488', fill: 'none', stroke: red, 'stroke-width': 2.1, pathLength: 1, 'stroke-dasharray': 1 });
  lower.append(surface, curve);
  const label = (parent, latex, x, y, size = 23.8, color = '#000') => {
    const node = math(latex, size); node.setAttribute('x', x - Number(node.getAttribute('width')) / 2); node.setAttribute('y', y - Number(node.getAttribute('height')) / 2); node.style.color = color; parent.append(node); return node;
  };
  const yLabel = label(lower, 'Y', 60, 52);
  const singular = label(lower, '\\operatorname{Sing}(Y)', -65, 5, 23.8, red);
  const component = label(lower, 'C_\\alpha', -65, 5, 23.8, red);
  const openLabel = label(lower, 'U_\\alpha', -65, 5, 23.8, red);
  const singularPen = ink(singular), componentPen = ink(component), openPen = ink(openLabel);
  const hole = (x, y) => { const node = svg('circle', { cx: x, cy: y, r: 0, fill: '#fff', stroke: red, 'stroke-width': 1.6 }); lower.append(node); return node; };
  const nodeHole = hole(50, 0), projectedHole = hole(-19.625, -37.625);
  const upper = svg('g'); scene.append(upper);
  upper.append(svg('path', { d: 'M-153,-61 C-83,-90 74,-89 151,-48 L143,91 C63,121 -84,111 -155,73 Z', fill: 'none', stroke: '#000', 'stroke-width': 1.2 }));
  const cx = -19.625;
  const planes = [[[cx - 65, -49], [cx + 65, -1], [cx + 65, 82], [cx - 65, 34]], [[cx - 62, 2], [cx + 62, -52], [cx + 62, 31], [cx - 62, 85]]];
  planes.forEach(points => upper.append(svg('polygon', { points: points.map(point => point.join(',')).join(' '), fill: red, 'fill-opacity': .16, stroke: red, 'stroke-opacity': .75, 'stroke-width': 1.2 })));
  upper.append(svg('line', { x1: cx, y1: -25, x2: cx, y2: 58, stroke: red, 'stroke-width': 2.1 }));
  const xLabel = label(upper, 'X', 95, 56), dLabel = label(upper, 'D', cx - 95, 25, 23.8, red);
  const arrow = label(scene, '\\Big\\downarrow', 350, 251, 36), arrowPen = ink(arrow), fLabel = label(scene, 'f', 373, 248);
  const extension = svg('line', { stroke: red, 'stroke-width': 1.6, 'stroke-dasharray': '5 5' }); scene.append(extension);
  const slice = svg('g'); lower.append(slice);
  slice.append(svg('polygon', { points: '-80.098875,-54.156875 -26.098875,-30.156875 -26.098875,77.843125 -80.098875,53.843125', fill: '#c4cdd6', 'fill-opacity': .42, stroke: '#59646e', 'stroke-width': 1.2 }));
  slice.append(svg('circle', { cx: -53.098875, cy: 36.843125, r: 3, fill: '#000' }));
  label(slice, 'x', -31.098875, 52.843125, 23.8);
  lower.append(openLabel);
  const right = document.createElement('div'); right.style.cssText = 'position:absolute;left:400px;top:58px;width:450px'; panel.append(right);
  const paragraph = html => { const node = document.createElement('div'); node.innerHTML = html; node.style.marginBottom = '14px'; typeset(node); right.append(node); return node; };
  const terminal = paragraph('Assume ' + m('Y') + ' is terminal, so<div style="text-align:center;margin-top:12px">' + m('\\operatorname{codim}\\operatorname{Sing}(Y)\\geq3') + '.</div>');
  const componentText = paragraph('Let ' + m('C_\\alpha') + ' be any codimension-3 component of ' + m('\\operatorname{Sing}(Y)') + '.');
  const openText = paragraph('Take an open subset ' + m('U_\\alpha') + ' such that:');
  const list = document.createElement('ul'); list.style.cssText = 'margin:0;padding-left:23px'; right.append(list);
  const bullets = [m('f') + ' is smooth and proper over ' + m('U_\\alpha') + ';', 'Any ' + m('r') + '-stratum over ' + m('U_\\alpha') + ' dominates ' + m('C_\\alpha') + ';', 'A general 3-fold linear slice restricts to a log-resolution of a terminal 3-fold.'].map(html => {
    const node = document.createElement('li'); node.innerHTML = html; node.style.marginBottom = '9px'; typeset(node); list.append(node); return node;
  });
  const conclusion = paragraph('The locus we throw away has codim ' + m('\\geq4') + ' and will not contribute negatively to ' + m('h_{\\mathrm{st}}^{2,2}') + '.');
  conclusion.style.marginTop = '12px';
  const defect = paragraph('The negative contributions of ' + m('h_{\\mathrm{st}}^{2,2}') + ' come from <em>defect</em> of each component ' + m('C_\\alpha') + '.');
  const localDefect = paragraph('The resolution adapted to <span style="color:' + red + '">' + m('U_\\alpha') + '</span> helps relate the defect on ' + m('C_\\alpha') + ' to the <em>local defect</em> of a 3-fold slice at ' + m('x\\in C_\\alpha') + '.');
  const timeline = motion();
  let step = -1, revision = 0, disposed = false, current;
  const visibility = (node, value) => { node.style.opacity = String(value); node.style.visibility = value > 0 ? 'visible' : 'hidden'; };
  const textVisibility = (node, value) => { node.style.display = value > 0 ? '' : 'none'; node.style.opacity = String(value); };
  const pose = next => ({
    equation: next >= 1 && next < 3 ? 1 : 0, brace: next >= 2 ? 1 : 0, mixed: next >= 2 ? 1 : 0,
    panel: next >= 3 ? 1 : 0, surface: next >= 3 ? 1 : 0, curve: next >= 3 ? 1 : 0, lowerX: next < 4 ? 433 : 185, lowerY: next >= 12 ? 205 : next < 6 ? 265 : 340,
    yLabel: next >= 3 && next < 6 ? 1 : 0, singular: next >= 3 && next < 5 ? 1 : 0, component: next === 5 ? 1 : 0,
    upper: next >= 6 && next < 12 ? 1 : 0, arrow: next >= 6 && next < 12 ? 1 : 0, upperLabels: next >= 6 && next < 12 ? 1 : 0,
    terminal: next >= 4 && next < 7 ? 1 : 0, componentText: next >= 5 && next < 7 ? 1 : 0, openText: next >= 7 && next < 12 ? 1 : 0,
    first: next >= 8 && next < 12 ? 1 : 0, second: next >= 9 && next < 12 ? 1 : 0, third: next >= 10 && next < 12 ? 1 : 0,
    nodeHole: next >= 8 ? 1 : 0, projectedHole: next >= 9 ? 1 : 0, extension: next === 9 ? 1 : 0, slice: next === 10 || next >= 13 ? 1 : 0,
    openLabel: next >= 11 ? 1 : 0, conclusion: next === 11 ? 1 : 0, defect: next >= 12 ? 1 : 0, localDefect: next >= 13 ? 1 : 0
  });
  function paint(value) {
    current = value;
    const introWidth = Number(theoremIntro.getAttribute('width'));
    theoremIntro.setAttribute('x', 18); theoremIntro.setAttribute('y', 37 - baseline(theoremIntro));
    theoremResult.setAttribute('x', 30 + introWidth); theoremResult.setAttribute('y', 37 - baseline(theoremResult));
    visibility(equation, value.equation); bracePen(value.brace); visibility(mixed, value.mixed); visibility(panel, value.panel);
    lower.setAttribute('transform', 'translate(' + value.lowerX + ',' + value.lowerY + ')');
    visibility(surface, value.surface); visibility(curve, value.curve); curve.setAttribute('stroke-dashoffset', String(1 - value.curve));
    visibility(yLabel, value.yLabel); singularPen(value.singular); componentPen(value.component); openPen(value.openLabel);
    upper.setAttribute('transform', 'translate(' + value.lowerX + ',130)'); visibility(upper, value.upper);
    visibility(xLabel, value.upperLabels); visibility(dLabel, value.upperLabels); arrowPen(value.arrow); visibility(fLabel, value.upperLabels);
    nodeHole.setAttribute('r', 3.5 * value.nodeHole); visibility(nodeHole, value.nodeHole);
    projectedHole.setAttribute('r', 3.5 * value.projectedHole); visibility(projectedHole, value.projectedHole);
    extension.setAttribute('x1', value.lowerX + cx); extension.setAttribute('x2', value.lowerX + cx);
    extension.setAttribute('y1', 188); extension.setAttribute('y2', 188 + (value.lowerY - 37.625 - 188) * value.extension); visibility(extension, value.extension);
    visibility(slice, value.slice);
    [[terminal, value.terminal], [componentText, value.componentText], [openText, value.openText], [bullets[0], value.first], [bullets[1], value.second], [bullets[2], value.third], [conclusion, value.conclusion], [defect, value.defect], [localDefect, value.localDefect]].forEach(([node, amount]) => textVisibility(node, amount));
  }
  async function animate(next, run) {
    const target = pose(next);
    const move = async (patch, seconds) => { const start = { ...current }, end = { ...current, ...patch }; return run(seconds, alpha => { const t = ease(alpha); paint(Object.fromEntries(Object.keys(end).map(key => [key, start[key] + (end[key] - start[key]) * t]))); }); };
    if (next === 1) paint(target);
    else if (next === 2) { if (!await move({ brace: 1 }, .55)) return; await move({ mixed: 1 }, .25); }
    else if (next === 3) {
      if (!await move({ equation: 0 }, .25)) return;
      if (!await move({ panel: 1 }, .25)) return;
      if (!await move({ surface: 1, curve: 1 }, .7)) return;
      await move({ yLabel: 1, singular: 1 }, .35);
    } else if (next === 4) { if (!await move({ lowerX: target.lowerX }, .7)) return; await move({ terminal: 1 }, .25); }
    else if (next === 5) {
      if (!await move({ singular: 0 }, .25)) return;
      if (!await move({ component: 1 }, .35)) return;
      await move({ componentText: 1 }, .25);
    } else if (next === 6) {
      if (!await move({ component: 0, yLabel: 0 }, .25)) return;
      if (!await move({ lowerY: target.lowerY }, .6)) return;
      if (!await move({ upper: 1, arrow: 1 }, .65)) return;
      await move({ upperLabels: 1 }, .25);
    } else if (next === 7) {
      if (!await move({ terminal: 0, componentText: 0 }, .25)) return;
      await move({ openText: 1 }, .25);
    } else if (next === 8) { if (!await move({ nodeHole: 1 }, .4)) return; await move({ first: 1 }, .25); }
    else if (next === 9) {
      if (!await move({ extension: 1 }, .6)) return;
      if (!await move({ projectedHole: 1 }, .3)) return;
      await move({ second: 1 }, .25);
    } else if (next === 10) {
      if (!await move({ extension: 0 }, .25)) return;
      if (!await move({ slice: 1 }, .55)) return;
      await move({ third: 1 }, .25);
    } else if (next === 11) {
      if (!await move({ slice: 0 }, .3)) return;
      if (!await move({ openLabel: 1 }, .4)) return;
      await move({ conclusion: 1 }, .25);
    } else if (next === 12) {
      if (!await move({ upper: 0, arrow: 0, upperLabels: 0, openText: 0, first: 0, second: 0, third: 0, conclusion: 0 }, .3)) return;
      if (!await move({ lowerY: target.lowerY }, .65)) return;
      await move({ defect: 1 }, .25);
    } else if (next === 13) {
      if (!await move({ slice: 1 }, .55)) return;
      await move({ localDefect: 1 }, .25);
    }
  }
  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      next = Math.max(0, Math.min(13, Number(next) || 0));
      const previous = step, token = ++revision; timeline.cancel(); step = next; slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (previous >= 0 && next === previous + 1) await animate(next, run); else paint(pose(next));
      if (!disposed && token === revision) paint(pose(next));
    },
    dispose() { disposed = true; revision++; timeline.dispose(); body.remove(); }
  };
}
