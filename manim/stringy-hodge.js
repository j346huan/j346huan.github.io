import { svg, math, typeset, motion } from './slide-utils.js';
import { createBlades } from './hodge-blades.js';

const clamp = value => Math.max(0, Math.min(1, value));
const ease = value => value * value * (3 - 2 * value);

export function createHodge(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;inset:0;color:#000';
  body.innerHTML = '<div data-expansions style="position:absolute;left:47px;right:47px;top:246px"><p style="margin:0">There are two ways to expand:</p></div><ul data-coefficients style="position:absolute;left:47px;right:47px;top:405px;margin:0;padding-left:29px"><li style="margin-bottom:17px">If <span data-math="E_{\\mathrm{st}}(Y)"></span> is a polynomial, then the expansion does not matter.</li><li style="margin-bottom:17px">Otherwise, setting <span data-math="h_{\\mathrm{st}}^{p,q}(Y)"></span> to be <span data-math="c_{p,q}"></span> will yield different values depending on expansion.</li><li>A priori, the two expansions yield unrelated coefficients, but Poincaré duality shows they in fact give reflected coefficients.</li></ul><ul data-symmetries style="position:absolute;left:47px;right:47px;top:610px;margin:0;padding-left:29px"><li>Hodge symmetry, Poincaré duality, and Mirror symmetry for certain Calabi–Yau mirrors. <a href="https://arxiv.org/pdf/alg-geom/9509009" target="_blank" rel="noopener noreferrer" style="color:#3333b3;font-size:19px">[Batyrev–Borisov]</a></li></ul>';
  const stage = svg('svg', { viewBox: '0 0 960 720', width: 960, height: 720 });
  stage.style.cssText = 'position:absolute;inset:0;overflow:visible;pointer-events:none';
  body.prepend(stage);
  slide.append(body);
  typeset(body);
  const formula = svg('g', { 'data-formula': '' });
  stage.append(formula);
  const old = ['E(X;u,v)', '=', '\\sum_{p,q}(-1)^{p+q}', 'h^{p,q}(X)', 'u^pv^q', '\\text{for smooth }X.'];
  const current = ['E_{\\mathrm{st}}(Y;u,v)', '=', '\\sum_{p,q}(-1)^{p+q}', 'c_{p,q}', 'u^pv^q', '\\text{for singular }Y.'];
  const gaps = [8, 8, 3, 3, 20, 0];
  const changed = [0, 3, 5];
  const parts = current.map((latex, index) => {
    const node = math(latex);
    if (index === 3) node.style.color = '#b8202f';
    formula.append(node);
    return node;
  });
  const before = parts.map((node, index) => {
    if (!changed.includes(index)) return node;
    const previous = math(old[index]);
    if (index === 3) previous.style.color = '#b8202f';
    formula.append(previous);
    return previous;
  });
  function layout(nodes) {
    const widths = nodes.map(node => Number(node.getAttribute('width')));
    let x = (960 - widths.reduce((sum, width, index) => sum + width + gaps[index], 0)) / 2;
    return widths.map((width, index) => {
      const position = x;
      x += width + gaps[index];
      return position;
    });
  }
  const hodge = math('h_{\\mathrm{st}}^{p,q}(Y)');
  hodge.style.color = '#b8202f';
  formula.append(hodge);
  const finalParts = parts.map((node, index) => index === 3 ? hodge : node);
  const starts = layout(before), ends = layout(parts), finalPositions = layout(finalParts);
  function place(node, x) {
    const box = node.getAttribute('viewBox').split(/\s+/).map(Number);
    node.setAttribute('x', x);
    node.setAttribute('y', 186 + box[1] * Number(node.getAttribute('width')) / box[2]);
  }
  function ink(node) {
    return [...node.querySelectorAll('path')].map(path => {
      const length = path.getTotalLength();
      path.style.stroke = 'currentColor';
      path.style.strokeWidth = '16';
      path.style.strokeLinecap = 'round';
      path.style.strokeLinejoin = 'round';
      path.style.strokeDasharray = String(length);
      return { path, length };
    });
  }
  const redrawn = [3, 5];
  const oldInk = redrawn.map(index => ink(before[index]));
  const newInk = redrawn.map(index => ink(parts[index]));
  const hodgeInk = ink(hodge);
  const sourcePrefix = before[0].querySelector('[data-mml-node="math"]');
  const targetPrefix = parts[0].querySelector('[data-mml-node="math"]');
  const prefixGroups = [...targetPrefix.children];
  const offset = node => Number(node.getAttribute('transform')?.match(/translate\(([-\d.]+)/)?.[1] || 0);
  const shared = [1, 3, 4, 5, 6, 7].map(index => ({
    node: prefixGroups[index], from: offset(sourcePrefix.children[index]), to: offset(prefixGroups[index])
  }));
  const sourceVariable = sourcePrefix.children[2].cloneNode(true);
  targetPrefix.append(sourceVariable);
  const targetVariable = prefixGroups[2];
  const variableFrom = offset(sourceVariable), variableTo = offset(targetVariable);
  const variableInk = [ink(sourceVariable), ink(targetVariable)];
  const subscriptInk = ink(prefixGroups[0].children[1]);

  function prefix(alpha) {
    const position = ease(alpha);
    shared.forEach(({ node, from, to }) => node.setAttribute('transform', 'translate(' + (from + (to - from) * position) + ',0)'));
    for (const node of [sourceVariable, targetVariable]) node.setAttribute('transform', 'translate(' + (variableFrom + (variableTo - variableFrom) * position) + ',0)');
    sourceVariable.style.visibility = alpha < 1 ? 'visible' : 'hidden';
    targetVariable.style.visibility = alpha > 0 ? 'visible' : 'hidden';
    write(variableInk[0], 1 - alpha * 2.4);
    write(variableInk[1], (alpha - .35) / .65);
    write(subscriptInk, alpha);
    parts[0].setAttribute('aria-label', alpha === 0 ? old[0] : current[0]);
  }
  function write(paths, amount) {
    const progress = clamp(amount) * (1 + (paths.length - 1) * .015);
    paths.forEach(({ path, length }, index) => {
      const value = clamp(progress - index * .015);
      path.style.strokeDashoffset = String(length * (1 - clamp(value / .7)));
      path.style.strokeOpacity = value > 0 && value < 1 ? '1' : '0';
      path.style.fillOpacity = String(clamp((value - .7) / .3));
    });
  }
  const expansions = body.querySelector('[data-expansions]');
  const cases = math('\\frac{uv-1}{(uv)^{a+1}-1}=\\begin{cases}(1-uv)+(uv)^{a+1}(1-uv)+(uv)^{2(a+1)}(1-uv)+\\cdots\\\\(uv)^{-(a+1)}(uv-1)+(uv)^{-2(a+1)}(uv-1)+(uv)^{-3(a+1)}(uv-1)+\\cdots\\end{cases}', 23.8);
  cases.style.cssText += ';display:block;max-width:866px;height:auto;margin:21px auto 0';
  expansions.append(cases);
  const coefficients = body.querySelector('[data-coefficients]');
  const symmetries = body.querySelector('[data-symmetries]');
  const blades = createBlades();
  body.append(blades.element);
  const timeline = motion();
  let step = -1, revision = 0, loop = 0, disposed = false;

  function state(next) {
    for (const node of [expansions, coefficients]) node.style.opacity = '1';
    expansions.style.visibility = next >= 2 && next < 6 ? 'visible' : 'hidden';
    coefficients.style.visibility = next >= 3 && next < 6 ? 'visible' : 'hidden';
    [...coefficients.children].forEach((item, index) => {
      item.style.visibility = next >= index + 3 && next < 6 ? 'visible' : 'hidden';
      item.style.opacity = '1';
    });
    symmetries.style.visibility = next === 7 ? 'visible' : 'hidden';
    blades.element.style.visibility = next >= 6 ? 'visible' : 'hidden';
    blades.reveal(next >= 6 ? 1 : 0);
    blades.compare(0);
    hodge.style.visibility = next >= 4 ? 'visible' : 'hidden';
    place(hodge, finalPositions[3]);
    parts.forEach((node, index) => {
      node.style.visibility = (next > 0 || !changed.includes(index)) && !(index === 3 && next >= 4) ? 'visible' : 'hidden';
      place(node, next === 0 ? starts[index] : next >= 4 ? finalPositions[index] : ends[index]);
      if (changed.includes(index)) {
        before[index].style.visibility = next === 0 ? 'visible' : 'hidden';
        place(before[index], starts[index]);
      }
    });
    before[0].style.visibility = 'hidden';
    parts[0].style.visibility = 'visible';
    prefix(next === 0 ? 0 : 1);
    oldInk.forEach(paths => write(paths, 1));
    newInk.forEach(paths => write(paths, 1));
    write(hodgeInk, 1);
  }

  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      const previous = step, token = ++revision;
      timeline.cancel();
      cancelAnimationFrame(loop);
      step = next;
      slide.dataset.step = String(next);
      if (next === 6 && (previous === 5 || previous === 6)) {
        if (previous === 5) {
          state(previous);
          if (!await timeline.run(.25, alpha => {
            for (const node of [expansions, coefficients]) node.style.opacity = String(1 - ease(alpha));
          })) return;
          if (disposed || token !== revision) return;
        }
        state(next);
        await timeline.run(2.8, alpha => blades.reveal(alpha));
        if (!disposed && token === revision) state(next);
        return;
      }
      state(next);
      if (next === 7) {
        const start = performance.now();
        function tick(now) {
          if (disposed || token !== revision) return;
          const time = ((now - start) / 1000) % 4.6;
          const amount = time < .5 ? 0 : time < 2.3 ? (time - .5) / 1.8 : time < 2.8 ? 1 : 1 - (time - 2.8) / 1.8;
          blades.compare(ease(amount));
          loop = requestAnimationFrame(tick);
        }
        loop = requestAnimationFrame(tick);
        return;
      }
      if (next === 4 && (previous === 3 || previous === 4)) {
        const item = coefficients.children[1];
        item.style.visibility = 'hidden';
        item.style.opacity = '0';
        parts[3].style.visibility = 'visible';
        if (!await timeline.run(1.1, alpha => {
          const position = ease(alpha);
          parts.forEach((node, index) => place(node, ends[index] + (finalPositions[index] - ends[index]) * position));
          place(hodge, ends[3] + (finalPositions[3] - ends[3]) * position);
          write(newInk[0], 1 - alpha * 2.4);
          write(hodgeInk, (alpha - .35) / .65);
        })) return;
        if (disposed || token !== revision) return;
        parts[3].style.visibility = 'hidden';
        item.style.visibility = 'visible';
        await timeline.run(.25, alpha => { item.style.opacity = String(ease(alpha)); });
        if (!disposed && token === revision) state(next);
        return;
      }
      if (next !== 1 || previous < 0 || previous > 1) return;
      redrawn.forEach(index => { before[index].style.visibility = 'visible'; });
      await timeline.run(1.3, alpha => {
        const position = ease(alpha);
        parts.forEach((node, index) => {
          const x = starts[index] + (ends[index] - starts[index]) * position;
          place(node, x);
          if (changed.includes(index)) place(before[index], x);
        });
        prefix(alpha);
        oldInk.forEach(paths => write(paths, 1 - alpha * 2.4));
        newInk.forEach(paths => write(paths, (alpha - .35) / .65));
      });
      if (!disposed && token === revision) state(next);
    },
    dispose() {
      disposed = true;
      timeline.dispose();
      cancelAnimationFrame(loop);
      body.remove();
    }
  };
}
