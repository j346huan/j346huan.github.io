import { svg, math, motion } from './slide-utils.js';

const red = '#b8202f';
const ease = t => t * t * (3 - 2 * t);
const clamp = t => Math.max(0, Math.min(1, t));

export function createDefectBound(slide) {
  const scene = svg('svg', { width: 866, height: 553, viewBox: '0 0 866 553' });
  scene.style.cssText = 'position:absolute;left:47px;top:139px;overflow:visible;color:#000';
  slide.append(scene);
  const items = {};
  function add(key, latex, r = 0, label = false, size = 23.8) {
    const node = math(latex, size);
    node.dataset.term = key;
    scene.append(node);
    const phantom = node.querySelector('[data-mml-node="mphantom"]');
    let hole = 0;
    for (let part = phantom; part && part !== node; part = part.parentElement) {
      const transform = part.transform?.baseVal.consolidate()?.matrix;
      if (transform) hole = transform.a * hole + transform.e;
    }
    hole *= size / 1000;
    node.querySelectorAll('[data-mml-node="mphantom"]').forEach(part => part.remove());
    const width = Number(node.getAttribute('width')), height = Number(node.getAttribute('height'));
    const paths = [...node.querySelectorAll('path')].map(path => [path, path.getTotalLength()]);
    items[key] = { node, width, height, hole, base: -node.viewBox.baseVal.y * height / node.viewBox.baseVal.height, r, label,
      write(amount) {
        paths.forEach(([path, length], i) => {
          const t = clamp(amount * (1 + paths.length * .002) - i * .002);
          path.style.stroke = 'currentColor'; path.style.strokeWidth = '14'; path.style.strokeLinecap = 'round';
          path.style.strokeDasharray = String(length); path.style.strokeDashoffset = String(length * (1 - clamp(t / .7)));
          path.style.strokeOpacity = t > 0 && t < 1 ? '1' : '0'; path.style.fillOpacity = String(clamp((t - .7) / .3));
        });
      }
    };
  }
  const U = 'Y_{\\mathrm{reg}}', S = '\\operatorname{Sing}(Y)', IC = '\\operatorname{IC}_Y';
  const h = i => 'h^{2,2}(H^' + i + '(' + U + '))';
  const boundary = 'h^{n-2,n-2}(H^{n-4}(' + S + ',' + IC + '))';
  add('lhs', 'h^{2,2}_{\\mathrm{st}}(Y)'); add('eq', '='); add('ge', '\\geq');
  add('smooth', 'h^{2,2}(X)', 1); add('divisors', 'h^{1,1}(D^{[1]})', 1); add('intersections', 'h^0(D^{[2]})', 1);
  add('minus', '-', 1); add('plus', '+', 1); add('plusC', '+'); add('c', 'c');
  add('olano', '\\text{(Olano 2021)}', 0, true);
  ['H^{0,0}(D^{[2]})','H^{1,1}(D^{[1]})','H^{2,2}(X)'].forEach((tex, i) => add('complex' + i, tex, 1));
  for (let i = 0; i < 2; i++) add('complexArrow' + i, '\\longrightarrow', 1);
  add('down', '\\Downarrow', 1);
  for (let i = 2; i <= 4; i++) {
    add('coh' + i, '(H^' + i + '(' + U + '))^{2,2}', 1);
    add('h' + i, h(i), 1);
  }
  add('dual4', 'H^4(' + U + ')^\\vee', 1); add('dual3', 'H^3(' + U + ')^\\vee', 1);
  add('ihDual4', '\\operatorname{IH}^4(Y)^\\vee'); add('ihDual3', '\\operatorname{IH}^3(Y)^\\vee');
  add('localBoundary', 'H^{n-4}(' + S + ',' + IC + ')(n)');
  for (let i = 0; i < 4; i++) add('localArrow' + i, '\\longrightarrow');
  add('compare4', h(4), 1); add('compare3', h(3), 1);
  add('compareMinus', '-', 1); add('compareGe', '\\geq', 1);
  add('boundary', boundary, 1); add('boundMinus', '-', 1);
  add('intersection', 'h^{2,2}(\\operatorname{IH}^4(Y))', 1);
  const conversions = [
    ['dual4', 'compare4', 'H^4(' + U + ')', 'h^{2,2}'],
    ['dual3', 'compare3', 'H^3(' + U + ')', 'h^{2,2}'],
    ['ihDual4', 'intersection', '\\operatorname{IH}^4(Y)', 'h^{2,2}'],
    ['localBoundary', 'boundary', 'H^{n-4}(' + S + ',' + IC + ')', 'h^{n-2,n-2}']
  ];
  conversions.forEach(([, target, core, coefficient]) => {
    add(target + 'Core', core, 1);
    add(target + 'Shell', coefficient + '(\\phantom{' + core + '})', 1);
  });
  add('chainLhs', boundary, 1);
  add('chain0', 'h^{n-4}(' + S + ',' + IC + ')', 1);
  add('chain1', 'h^{2n-6}(' + S + ',\\mathcal H^{-n+2}(' + IC + '|_{' + S + '}))', 1);
  add('chain2', '\\sum_\\alpha h_c^{2n-6}(U_\\alpha,\\mathcal D_\\alpha)', 1);
  add('chain3', '\\sum_\\alpha h^0(U_\\alpha,\\mathcal D_\\alpha)', 1);
  add('sum', '\\sum_\\alpha\\delta_\\alpha', 1);
  for (let i = 0; i < 5; i++) add('relation' + i, i < 2 ? '\\leq' : '=', 1);
  add('spectral', '\\text{Spectral sequence: }H^p(\\mathcal H^q)\\Rightarrow H^{p+q}', 0, true, 21);
  add('slice', '\\text{Localization to }U_\\alpha\\text{ and a threefold slice:}', 0, true, 21);
  add('sliceIdentity', '\\mathcal H^{-n+2}(' + IC + ')_x\\cong\\mathcal H^{-1}(\\operatorname{IC}_{Z_x})_x', 0, true, 21);
  add('duality', '\\text{Poincar}\\acute{\\text{e}}\\text{ duality}', 0, true, 21);
  function outline(key, width, height, base = 0) {
    const node = svg('rect', { width, height, fill: 'none', stroke: '#000', 'stroke-width': 1.1 });
    node.dataset.term = key;
    scene.prepend(node);
    const length = 2 * (width + height);
    items[key] = { node, width, height, base, r: 0, write(amount) {
      node.setAttribute('stroke-dasharray', length); node.setAttribute('stroke-dashoffset', length * (1 - amount));
    } };
  }
  function box(key, target) {
    const item = items[target];
    outline(key, item.width + 12, item.height + 10, item.base + 5);
  }
  box('h2Box', 'h2'); box('intersectionBox', 'intersection');
  const complexKeys = ['complex0','complexArrow0','complex1','complexArrow1','complex2'];
  const localKeys = ['dual4','localArrow0','ihDual4','localArrow1','localBoundary','localArrow2','dual3','localArrow3','ihDual3'];
  function brace(key, keys, latex, captions, r) {
    add(key, '\\underbrace{\\phantom{' + latex + '}}', r);
    const width = keys.reduce((w, id) => w + items[id].width, 0) + 10 * (keys.length - 1);
    items[key].width = width;
    items[key].node.setAttribute('width', width);
    items[key].node.setAttribute('preserveAspectRatio', 'none');
    captions.forEach((caption, i) => add(key + 'Label' + i, caption, 1, true, 21));
  }
  brace('weightBrace', complexKeys, 'H^{0,0}(D^{[2]})\\longrightarrow H^{1,1}(D^{[1]})\\longrightarrow H^{2,2}(X)', [
    '\\text{Weight spectral sequence}', '(2,2)\\text{ part of row }4'
  ], 1);
  brace('localBrace', localKeys, 'H^4(' + U + ')^\\vee\\to\\operatorname{IH}^4(Y)^\\vee\\to H^{n-4}(' + S + ',' + IC + ')(n)\\to H^3(' + U + ')^\\vee\\to\\operatorname{IH}^3(Y)^\\vee', [
    '\\text{Localization triangle for }Y=' + U + '\\cup ' + S,
    '\\text{with Poincar}\\acute{\\text{e}}\\text{ duality}'
  ], 0);
  add('cBrace', '\\underbrace{\\phantom{\\quad c\\quad}}');
  add('sumBrace', '\\underbrace{\\phantom{\\sum_\\alpha\\delta_\\alpha}}');
  add('cLabel', '\\text{discrepancy-1}', 0, true, 21);
  add('sumLabel', '\\text{defect}', 0, true, 21);
  const put = (state, key, x, y, r = items[key].r) => state.set(key, { x, y, r });
  const center = (state, key, y, x = 433, r = items[key].r) => put(state, key, x - items[key].width / 2, y, r);
  function row(state, keys, y, gap = 10) {
    const width = keys.reduce((w, id) => w + items[id].width, 0) + gap * (keys.length - 1);
    let x = (866 - width) / 2;
    keys.forEach(key => { put(state, key, x, y); x += items[key].width + gap; });
  }
  function boxed(state, key, target) {
    const point = state.get(target); put(state, key, point.x - 6, point.y);
  }
  function under(state, key, targets) {
    const first = state.get(targets[0]), last = state.get(targets.at(-1));
    const x = (first.x + last.x + items[targets.at(-1)].width) / 2, y = first.y;
    center(state, key, y, x);
    const bottom = y - items[key].base + items[key].height;
    center(state, key + 'Label0', bottom + 24, x);
    center(state, key + 'Label1', bottom + 51, x);
  }
  function layout(step) {
    const state = new Map();
    if (step <= 4) {
      row(state, ['lhs','eq','smooth','minus','divisors','plus','intersections','plusC','c'], 70);
      if (step === 1) put(state, 'olano', 866 - items.olano.width, 70);
    } else if (step === 5) {
      row(state, ['lhs','eq','h4','minus','h3','plus','h2','plusC','c'], 70);
      state.get('h2').r = 0; state.get('plus').r = 0;
      boxed(state, 'h2Box', 'h2');
    } else if (step <= 8) {
      row(state, ['lhs','ge','h4','minus','h3','plusC','c'], 70);
    } else if (step === 9) {
      row(state, ['lhs','ge','intersection','boundMinus','boundary','plusC','c'], 70);
      state.get('intersection').r = 0;
      boxed(state, 'intersectionBox', 'intersection');
    } else if (step <= 15) {
      row(state, ['lhs','ge','boundMinus','boundary','plusC','c'], 70);
    } else if (step === 16) {
      row(state, ['lhs','ge','boundMinus','sum','plusC','c'], 70);
      state.get('boundMinus').r = 0; state.get('sum').r = 0;
    } else {
      const keys = ['lhs','ge','c','boundMinus','sum'];
      const widths = keys.map(key => Math.max(items[key].width, items[key + 'Label']?.width || 0));
      let x = (866 - widths.reduce((total, width) => total + width, 0) - 48) / 2;
      keys.forEach((key, i) => { center(state, key, 0, x + widths[i] / 2, 0); x += widths[i] + 12; });
      for (const key of ['c','sum']) {
        const middle = state.get(key).x + items[key].width / 2, brace = items[key + 'Brace'];
        center(state, key + 'Brace', 0, middle);
        center(state, key + 'Label', brace.height - brace.base + 24, middle);
      }
      const top = Math.min(...[...state].map(([key, point]) => point.y - items[key].base));
      const bottom = Math.max(...[...state].map(([key, point]) => point.y - items[key].base + items[key].height));
      state.forEach(point => { point.y += (553 - top - bottom) / 2; });
    }
    if (step === 2 || step === 3) {
      row(state, complexKeys, 205); under(state, 'weightBrace', complexKeys);
      if (step === 3) {
        center(state, 'down', 300);
        for (let i = 2; i <= 4; i++) {
          const key = 'complex' + (i - 2), point = state.get(key);
          center(state, 'coh' + i, 332, point.x + items[key].width / 2);
        }
      }
    }
    if (step === 4) row(state, ['coh2','coh3','coh4'], 230, 65);
    if (step === 7) {
      row(state, localKeys, 235); under(state, 'localBrace', localKeys);
    }
    if (step === 8) row(state, ['compare4','compareMinus','compare3','compareGe','intersection','boundMinus','boundary'], 235, 6);
    if (step >= 11 && step <= 15) {
      const rhs = ['chain0','chain1','chain2','chain3','sum'];
      const width = items.chainLhs.width + 42 + Math.max(...rhs.map(key => items[key].width));
      const x = (866 - width) / 2, right = x + items.chainLhs.width + 42;
      put(state, 'chainLhs', x, 193);
      for (let i = 0; i <= step - 11; i++) {
        const r = i === step - 11 ? 1 : 0;
        put(state, 'relation' + i, right - 32, 193 + i * 53, r);
        put(state, rhs[i], right, 193 + i * 53, r);
      }
      if (step === 12) put(state, 'spectral', right - 32, 294);
      if (step === 13) { put(state, 'slice', right - 32, 347); put(state, 'sliceIdentity', right - 32, 381); }
      if (step === 14) put(state, 'duality', right - 32, 405);
    }
    return state;
  }
  const snapshots = Array.from({ length: 17 }, (_, i) => layout(i + 1));
  const last = snapshots.at(-1);
  const left = Math.min(...[...last].map(([key, point]) => point.x));
  const right = Math.max(...[...last].map(([key, point]) => point.x + items[key].width));
  const top = Math.min(...[...last].map(([key, point]) => point.y - items[key].base));
  const bottom = Math.max(...[...last].map(([key, point]) => point.y - items[key].base + items[key].height));
  outline('finalBox', right - left + 40, bottom - top + 36);
  put(last, 'finalBox', left - 20, top - 18);
  function position(key, point) {
    const item = items[key];
    item.node.setAttribute('x', point.x); item.node.setAttribute('y', point.y - item.base);
    item.node.style.color = point.r === 1 ? red : 'rgb(' + [184,32,47].map(c => Math.round(c * point.r)).join(',') + ')';
  }
  function show(key, opacity) {
    const node = items[key].node;
    node.style.opacity = String(opacity); node.style.visibility = opacity > 0 ? 'visible' : 'hidden';
  }
  function display(state) {
    Object.entries(items).forEach(([key, item]) => {
      show(key, state.has(key) ? 1 : 0); item.write(1);
      if (state.has(key)) position(key, state.get(key));
    });
  }
  function interpolate(key, a, b, t, arc = 0) {
    position(key, { x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t + arc * Math.sin(Math.PI * t), r: a.r + (b.r - a.r) * t });
  }
  async function transition(before, after, run, { write = true, arc = {}, collapse = [] } = {}) {
    const leaving = [...before.keys()].filter(key => !after.has(key));
    const common = [...after.keys()].filter(key => before.has(key));
    const incoming = [...after.keys()].filter(key => !before.has(key));
    if (leaving.length && !await run(.3, t => leaving.forEach(key => {
      show(key, 1 - ease(t));
      if (collapse.includes(key)) {
        const a = before.get(key); interpolate(key, a, { ...a, x: 433 - items[key].width / 2 }, ease(t));
      }
    }))) return false;
    const moving = common.some(key => {
      const a = before.get(key), b = after.get(key); return a.x !== b.x || a.y !== b.y || a.r !== b.r;
    });
    if (moving && !await run(.7, t => common.forEach(key => interpolate(key, before.get(key), after.get(key), ease(t), arc[key] || 0)))) return false;
    incoming.forEach(key => { position(key, after.get(key)); items[key].write(write && !items[key].label ? 0 : 1); });
    const formulas = incoming.filter(key => !items[key].label), labels = incoming.filter(key => items[key].label);
    if (formulas.length) {
      if (write) {
        if (!await run(.65, t => formulas.forEach(key => { show(key, 1); items[key].write(t); }))) return false;
      } else if (!await run(.3, t => formulas.forEach(key => show(key, ease(t))))) return false;
    }
    if (labels.length) {
      if (moving || leaving.length || formulas.length) {
        if (!await run(.3, t => labels.forEach(key => show(key, ease(t))))) return false;
      } else labels.forEach(key => show(key, 1));
    }
    display(after);
    return true;
  }
  const timeline = motion();
  let step = -1, revision = 0, disposed = false;
  async function animate(previous, next, run) {
    const before = snapshots[previous], after = snapshots[next];
    if (next === 4) {
      const aligned = new Map(before);
      [4,3,2].forEach(i => center(aligned, 'coh' + i, 178, after.get('h' + i).x + items['h' + i].width / 2));
      if (!await transition(before, aligned, run, { arc: { coh2: 44, coh4: -44 } })) return;
      const dimensions = new Map(aligned);
      for (let i = 2; i <= 4; i++) { dimensions.delete('coh' + i); put(dimensions, 'h' + i, after.get('h' + i).x, 178, 1); }
      if (!await transition(aligned, dimensions, run)) return;
      await transition(dimensions, after, run);
    } else if (next === 7) {
      const unbraced = new Map(before);
      ['localBrace','localBraceLabel0','localBraceLabel1'].forEach(key => unbraced.delete(key));
      if (!await transition(before, unbraced, run)) return;
      const terms = new Map(unbraced);
      ['localArrow0','localArrow1','localArrow2','localArrow3','ihDual3'].forEach(key => terms.delete(key));
      if (!await transition(unbraced, terms, run)) return;
      const aligned = new Map(terms);
      conversions.forEach(([source, target]) => put(aligned, source, after.get(target).x + items[target + 'Shell'].hole, after.get(target).y, 1));
      if (!await transition(terms, aligned, run, { arc: { dual3: -52, ihDual4: 20, localBoundary: 20 } })) return;
      const cores = new Map(aligned);
      conversions.forEach(([source, target]) => {
        const key = target + 'Core', point = aligned.get(source);
        cores.delete(source); put(cores, key, point.x, point.y, 1);
        position(key, cores.get(key)); items[key].write(1); show(key, 1);
      });
      if (!await run(.3, t => conversions.forEach(([source]) => show(source, 1 - ease(t))))) return;
      display(cores);
      const wrapped = new Map(cores);
      conversions.forEach(([, target]) => {
        const point = after.get(target); put(wrapped, target + 'Shell', point.x, point.y, 1);
      });
      if (!await transition(cores, wrapped, run)) return;
      const dimensions = new Map(after);
      ['compareMinus','compareGe','boundMinus'].forEach(key => dimensions.delete(key));
      display(dimensions);
      await transition(dimensions, after, run);
    } else if (next === 8) {
      const aligned = new Map(before);
      ['compare4','compareMinus','compare3','compareGe'].forEach(key => aligned.delete(key));
      ['intersection','boundMinus','boundary'].forEach(key => put(aligned, key, after.get(key).x, 175, 1));
      if (!await transition(before, aligned, run)) return;
      await transition(aligned, after, run);
    } else if (next === 15) {
      const aligned = new Map(before);
      ['chainLhs','chain0','chain1','chain2','chain3',...Array.from({ length: 5 }, (_, i) => 'relation' + i)].forEach(key => aligned.delete(key));
      center(aligned, 'sum', 168, before.get('boundary').x + items.boundary.width / 2, 1);
      if (!await transition(before, aligned, run)) return;
      await transition(aligned, after, run);
    } else if (next === 16) {
      const annotated = new Map(after); annotated.delete('finalBox');
      if (!await transition(before, annotated, run, { arc: { c: -27, sum: 22, boundMinus: 22 } })) return;
      await transition(annotated, after, run);
    } else {
      await transition(before, after, run, {
        collapse: next === 3 ? [...complexKeys, 'weightBrace','weightBraceLabel0','weightBraceLabel1','down'] : []
      });
    }
  }
  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      next = Math.max(0, Math.min(16, Number(next) || 0));
      const previous = step, token = ++revision;
      timeline.cancel(); step = next; slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (previous >= 0 && next === previous + 1) { display(snapshots[previous]); await animate(previous, next, run); }
      else display(snapshots[next]);
      if (!disposed && token === revision) display(snapshots[next]);
    },
    dispose() { disposed = true; revision++; timeline.dispose(); scene.remove(); }
  };
}
