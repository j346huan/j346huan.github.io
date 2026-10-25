import { svg, math, typeset, motion } from './slide-utils.js';

export function createProperties(slide) {
  const root = document.createElement('div');
  root.style.cssText = 'position:absolute;inset:0;color:#000';
  root.innerHTML = '<p data-intro style="position:absolute;left:47px;right:47px;top:144px;margin:0">For a smooth projective <span data-math="n"></span>-fold, Hodge numbers form a Hodge diamond and satisfy the following properties.</p><ul data-properties style="position:absolute;left:47px;right:47px;top:480px;margin:0;padding-left:29px"><li data-property="1" style="margin-bottom:14px"><b>Hodge symmetry:</b> <span data-math="h^{p,q}=h^{q,p}"></span>.</li><li data-property="2" style="margin-bottom:14px"><b>Poincaré duality:</b> <span data-math="h^{p,q}=h_c^{n-p,n-q}"></span>.</li><li data-property="3"><b>Mirror symmetry:</b> <span data-math="h^{p,q}(X)=h^{n-p,q}(X^\\vee)"></span>.</li></ul><p data-explanation style="position:absolute;left:47px;right:47px;margin:0">Sometimes the <span data-math="E"></span>-function, the generating function of these Hodge numbers, is easier to manipulate than the Hodge diamond.</p><div data-general-properties style="position:absolute;left:47px;right:47px;top:405px"><ul style="margin:0;padding-left:29px"><li style="margin-bottom:20px"><b>Compatible with stratification:</b> <span data-math="E(X)=E(U)+E(Z)"></span>.</li><li><b>Compatible with fibration:</b> <span data-math="E(F\\times X)=E(F)E(X)"></span>.</li></ul></div>';
  const drawing = svg('svg', { viewBox: '0 0 960 720', width: 960, height: 720, 'aria-label': 'Hodge diamond and Hodge polynomial' });
  drawing.style.cssText = 'position:absolute;inset:0;overflow:visible;pointer-events:none';
  root.prepend(drawing);
  slide.append(root);
  typeset(root);
  const intro = root.querySelector('[data-intro]');
  const properties = root.querySelector('[data-properties]');
  const explanation = root.querySelector('[data-explanation]');
  const generalProperties = root.querySelector('[data-general-properties]');
  const entries = [], timeline = motion();
  let step = -1, revision = 0, loop = 0, disposed = false;

  function inline(parent, latex, x = 0) {
    const node = math(latex);
    const box = node.getAttribute('viewBox').split(/\s+/).map(Number);
    const width = Number(node.getAttribute('width'));
    node.setAttribute('x', String(x));
    node.setAttribute('y', String(box[1] * width / box[2]));
    parent.append(node);
    return { node, width };
  }

  for (let q = 0; q < 4; q++) for (let p = 0; p < 4; p++) {
    const group = svg('g', { 'data-hodge': p + ',' + q });
    const label = inline(group, 'h^{' + p + ',' + q + '}');
    label.node.setAttribute('x', String(-label.width / 2));
    const extras = svg('g');
    group.append(extras);
    if (p || q) {
      const sign = inline(extras, (p + q) % 2 ? '-' : '+');
      sign.node.setAttribute('x', String(-label.width / 2 - sign.width - 5));
    }
    const factor = (p ? 'u' + (p > 1 ? '^' + p : '') : '') + (q ? 'v' + (q > 1 ? '^' + q : '') : '');
    if (factor) inline(extras, factor, label.width / 2 + 4);
    drawing.append(group);
    entries.push({ p, q, group, extras, x: 480 + (p - q) * 90, y: 335 + (p + q - 3) * 35, scale: 1 });
  }
  const prefix = svg('g', { transform: 'translate(53 265)' });
  const prefixWidth = inline(prefix, 'E(X;u,v)=').width;
  drawing.append(prefix);
  const general = math('\\sum_{p,q}(-1)^{p+q}h^{p,q}(X)u^pv^q');
  const generalWidth = Number(general.getAttribute('width'));
  const generalHeight = Number(general.getAttribute('height'));
  const generalX = (960 - prefixWidth - 14 - generalWidth) / 2;
  general.setAttribute('x', String(generalX + prefixWidth + 14));
  general.setAttribute('y', String(205 - generalHeight / 2));
  const generalBox = general.getAttribute('viewBox').split(/\s+/).map(Number);
  const generalY = 205 - generalHeight / 2 - generalBox[1] * generalWidth / generalBox[2];
  drawing.append(general);
  const paths = [...general.querySelectorAll('path')].map(path => {
    const length = path.getTotalLength();
    path.setAttribute('stroke', '#000');
    path.setAttribute('stroke-width', '18');
    path.setAttribute('stroke-linecap', 'round');
    path.setAttribute('stroke-linejoin', 'round');
    path.style.strokeDasharray = String(length);
    return { path, length };
  });

  function write(alpha) {
    const progress = alpha * (1 + Math.max(0, paths.length - 1) * .025);
    paths.forEach(({ path, length }, index) => {
      const value = Math.max(0, Math.min(1, progress - index * .025));
      path.style.strokeDashoffset = String(length * (1 - Math.min(1, value / .7)));
      path.style.strokeOpacity = value > 0 && value < 1 ? '1' : '0';
      path.style.fillOpacity = String(Math.max(0, (value - .7) / .3));
    });
  }

  function place(entry, x, y, scale = 1) {
    Object.assign(entry, { x, y, scale });
    entry.group.setAttribute('transform', 'translate(' + x + ' ' + y + ') scale(' + scale + ')');
  }

  function position(entry, expanded = false) {
    return expanded ? [235 + entry.p * 176, generalY + entry.q * 46] : [480 + (entry.p - entry.q) * 90, 335 + (entry.p + entry.q - 3) * 35];
  }

  function state(next) {
    for (const node of [intro, properties, explanation]) node.style.opacity = '1';
    prefix.setAttribute('transform', 'translate(' + (next >= 5 ? generalX : 53) + ' ' + generalY + ')');
    intro.style.visibility = next < 4 ? 'visible' : 'hidden';
    properties.style.visibility = next < 4 ? 'visible' : 'hidden';
    properties.querySelectorAll('[data-property]').forEach(item => item.style.visibility = next < 4 && Number(item.dataset.property) <= next ? 'visible' : 'hidden');
    explanation.style.visibility = next >= 4 ? 'visible' : 'hidden';
    explanation.style.top = (next === 4 ? 390 : 275) + 'px';
    generalProperties.style.visibility = next === 6 ? 'visible' : 'hidden';
    prefix.style.visibility = next >= 4 ? 'visible' : 'hidden';
    prefix.style.opacity = '1';
    general.style.visibility = next >= 5 ? 'visible' : 'hidden';
    write(1);
    entries.forEach(entry => {
      entry.group.style.visibility = next < 5 ? 'visible' : 'hidden';
      entry.group.style.opacity = '1';
      entry.extras.style.visibility = next === 4 ? 'visible' : 'hidden';
      entry.extras.style.opacity = '1';
      place(entry, ...position(entry, next >= 4));
    });
  }

  const ease = alpha => alpha * alpha * (3 - 2 * alpha);
  const animate = (seconds, update) => timeline.run(seconds, alpha => update(ease(alpha)));

  function turn(amount) {
    const offset = ease(amount);
    entries.forEach(entry => {
      const x = entry.p - entry.q, y = entry.p + entry.q - 3, radius = Math.abs(x) + Math.abs(y);
      const phase = x >= 0 && y <= 0 ? x / radius : x >= 0 ? 1 + y / radius : y >= 0 ? 2 - x / radius : 3 - y / radius;
      const value = (phase + offset) % 4, edge = Math.floor(value), along = value - edge;
      const points = [[along, along - 1], [1 - along, along], [-along, 1 - along], [along - 1, -along]];
      place(entry, 480 + points[edge][0] * radius * 90, 335 + points[edge][1] * radius * 35);
    });
  }

  function repeat(update, token) {
    const start = performance.now();
    function tick(now) {
      if (disposed || token !== revision) return;
      const time = ((now - start) / 1000) % 4.6;
      update(time < .5 ? 0 : time < 2.3 ? (time - .5) / 1.8 : time < 2.8 ? 1 : 1 - (time - 2.8) / 1.8);
      loop = requestAnimationFrame(tick);
    }
    loop = requestAnimationFrame(tick);
  }

  function flip(axis, token) {
    repeat(amount => {
      const factor = Math.cos(Math.PI * ease(amount));
      entries.forEach(entry => {
        const [x, y] = position(entry);
        place(entry, 480 + (x - 480) * (axis === 'vertical' ? factor : 1), 335 + (y - 335) * (axis === 'horizontal' ? factor : 1));
      });
    }, token);
  }

  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      const previous = step, token = ++revision;
      const start = entries.map(entry => next === 4 && previous === 4 ? [...position(entry), 1] : [entry.x, entry.y, entry.scale]);
      timeline.cancel();
      cancelAnimationFrame(loop);
      step = next;
      slide.dataset.step = String(next);
      if (next === 4 && previous >= 0 && previous < 4) {
        const opacity = [intro, properties].map(node => Number(node.style.opacity));
        await animate(.25, alpha => [intro, properties].forEach((node, index) => {
          node.style.opacity = String(opacity[index] * (1 - alpha));
        }));
        if (token !== revision || disposed) return;
      }
      state(next);
      if (next < 4 && (previous === 1 || previous === 2)) {
        entries.forEach((entry, index) => place(entry, ...start[index]));
        await animate(.5, alpha => entries.forEach((entry, index) => {
          const [x, y] = position(entry), initial = start[index];
          place(entry, initial[0] + (x - initial[0]) * alpha, initial[1] + (y - initial[1]) * alpha, initial[2] + (1 - initial[2]) * alpha);
        }));
        if (token !== revision || disposed) return;
      }
      if (next === 1 || next === 2) return flip(next === 1 ? 'vertical' : 'horizontal', token);
      if (next === 3) return repeat(turn, token);
      if (next === 4 && previous >= 0 && previous <= 4) {
        explanation.style.visibility = 'hidden';
        explanation.style.opacity = '0';
        prefix.style.opacity = '0';
        entries.forEach((entry, index) => { place(entry, ...start[index]); entry.extras.style.opacity = '0'; });
        await animate(1.7, alpha => {
          entries.forEach((entry, index) => {
            const [x, y] = position(entry, true), initial = start[index];
            place(entry, initial[0] + (x - initial[0]) * alpha, initial[1] + (y - initial[1]) * alpha, initial[2] + (1 - initial[2]) * alpha);
            entry.extras.style.opacity = String(alpha);
          });
          prefix.style.opacity = String(alpha);
        });
        if (token !== revision || disposed) return;
        explanation.style.visibility = 'visible';
        await animate(.35, alpha => { explanation.style.opacity = String(alpha); });
      } else if (next === 5 && (previous === 4 || previous === 5)) {
        entries.forEach(entry => { entry.group.style.visibility = 'visible'; entry.extras.style.visibility = 'visible'; });
        prefix.style.visibility = 'visible';
        write(0);
        explanation.style.top = '390px';
        await animate(1.5, alpha => {
          entries.forEach(entry => {
            const [x, y] = position(entry, true);
            place(entry, x + (generalX + prefixWidth + 14 + generalWidth * .68 - x) * alpha, y + (generalY - y) * alpha, 1 - .35 * alpha);
            entry.group.style.opacity = String(1 - alpha);
          });
          prefix.setAttribute('transform', 'translate(' + (53 + (generalX - 53) * alpha) + ' ' + generalY + ')');
          explanation.style.top = (390 - 115 * alpha) + 'px';
          write(alpha);
        });
        if (token !== revision || disposed) return;
        state(next);
      }
    },
    dispose() {
      disposed = true;
      revision++;
      cancelAnimationFrame(loop);
      timeline.dispose();
      root.remove();
    }
  };
}
