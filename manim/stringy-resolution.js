import { svg, mathAt, typeset, motion } from './slide-utils.js';

export function createResolution(slide) {
  const animation = motion();
  const diagram = svg('svg', { viewBox: '0 0 960 420', width: 960, height: 420, 'aria-label': 'Successive resolutions of a singular cone' });
  diagram.style.cssText = 'position:absolute;left:0;top:0;width:960px;height:420px;overflow:visible;pointer-events:none';
  const labels = [];

  function surface(resolved, label) {
    const group = svg('g', { fill: 'none', stroke: '#000', 'stroke-width': 1.7, 'stroke-linecap': 'round', 'stroke-linejoin': 'round' });
    const side = resolved
      ? 'M-62 -90 C-40 -56 -22 -25 -22 0 C-22 25 -40 56 -62 90 M62 -90 C40 -56 22 -25 22 0 C22 25 40 56 62 90'
      : 'M-62 -90 L0 0 L-62 90 M62 -90 L0 0 L62 90';
    const fill = resolved
      ? 'M-62 -90 C-40 -56 -22 -25 -22 0 C-22 25 -40 56 -62 90 L62 90 C40 56 22 25 22 0 C22 -25 40 -56 62 -90 Z'
      : 'M-62 -90 L0 0 L-62 90 L62 90 L0 0 L62 -90 Z';
    group.append(svg('path', { d: fill, fill: '#fff', stroke: 'none' }));
    group.append(svg('path', { d: side }));
    group.append(svg('ellipse', { cx: 0, cy: -90, rx: 62, ry: 14, fill: '#fff' }));
    group.append(svg('path', { d: 'M-62 90 A62 14 0 0 1 62 90', 'stroke-dasharray': '5 5' }));
    group.append(svg('path', { d: 'M-62 90 A62 14 0 0 0 62 90' }));
    if (resolved) {
      group.append(svg('path', { d: 'M-22 0 A22 8 0 0 1 22 0', stroke: '#c40000', 'stroke-width': 2, 'stroke-dasharray': '4 4' }));
      group.append(svg('path', { d: 'M-22 0 A22 8 0 0 0 22 0', stroke: '#c40000', 'stroke-width': 2 }));
    } else group.append(svg('circle', { cx: 0, cy: 0, r: 4.5, fill: '#c40000', stroke: 'none' }));
    const labelGroup = svg('g', { stroke: 'none', fill: '#000' });
    group.append(labelGroup);
    labels.push(mathAt(labelGroup, label, 0, 120, 27));
    diagram.append(group);
    return group;
  }

  function arrow(label) {
    const group = svg('g');
    labels.push(mathAt(group, '\\xrightarrow{\\displaystyle\\quad ' + label + '\\quad}', 0, 0, 25));
    diagram.append(group);
    return group;
  }

  const y = surface(false, 'Y'), x = surface(true, 'X'), prime = surface(true, "X'");
  const point = svg('circle', { cx: 8, cy: 7.45, r: 4, fill: '#c40000', stroke: 'none' });
  x.append(point);
  prime.append(svg('circle', { cx: 8, cy: 7.45, r: 8, fill: '#fff', stroke: '#c40000', 'stroke-width': 2 }));
  const f = arrow('f'), fp = arrow("f'");
  const text = document.createElement('div');
  text.className = 'resolution-content';
  text.style.cssText = 'position:absolute;left:47px;right:47px;top:425px;color:#000;font:23.8px/1.35 Beamer,serif;text-align:left';
  const contents = [
    'We want Hodge theoretic information of singular <span data-math="Y"></span>. But intersection cohomology is not enough for us because we want mirror symmetry.',
    'Take a resolution <span data-math="f:X\\to Y"></span>, and consider the Hodge numbers of <span data-math="X"></span>.',
    'We can not just use <span data-math="h^{p,q}(X)"></span> directly, because another resolution <span data-math="X\'\\to Y"></span> can have different Hodge numbers.',
    'The resolutions are birational maps, so degeneration of exceptional locus is causing problem.',
    'Need some adjustment for the contribution of exceptional locus.'
  ];
  const items = contents.map(content => {
    const item = document.createElement('div');
    item.style.cssText = 'position:absolute;left:0;right:0;top:0;padding-left:29px;opacity:0';
    item.innerHTML = '<span style="position:absolute;left:7px;top:0;color:#3333b3">•</span>' + content;
    text.append(item);
    return item;
  });
  slide.append(diagram, text);
  let disposed = false, step = -1, revision = 0, heights = [], state;
  const ready = Promise.all([...labels, typeset(text)]).then(() => {
    heights = items.map(item => item.offsetHeight);
  });
  const lerp = (a, b, t) => a + (b - a) * t;

  function target(next) {
    const positions = [0, heights[0] + 14, heights[0] + heights[1] + 28, heights[2] + 20, heights[2] + heights[3] + 40];
    if (next >= 3) positions[2] = 0;
    return {
      centers: [next === 0 ? 480 : next === 1 ? 655 : 755, next < 2 ? 305 : 480, 205],
      visible: [1, +(next >= 1), +(next >= 2)],
      point: +(next >= 2),
      opacity: [+ (next < 3), +(next >= 1 && next < 3), +(next >= 2), +(next >= 3), +(next >= 4)],
      positions
    };
  }

  function render(value) {
    state = value;
    [y, x, prime].forEach((group, index) => {
      group.setAttribute('transform', 'translate(' + value.centers[index] + ' 260)');
      group.setAttribute('opacity', value.visible[index]);
    });
    point.setAttribute('opacity', value.point);
    [[f, value.centers[1], value.centers[0], value.visible[1]], [fp, value.centers[2], value.centers[1], value.visible[2]]].forEach(([arrow, left, right, opacity]) => {
      arrow.setAttribute('opacity', opacity);
      arrow.setAttribute('transform', 'translate(' + ((left + right) / 2) + ' 248)');
    });
    items.forEach((item, index) => {
      item.style.opacity = value.opacity[index];
      item.style.transform = 'translateY(' + value.positions[index] + 'px)';
    });
  }
  diagram.style.opacity = '0';

  return {
    animated: true,
    async play(next = 0) {
      const token = ++revision;
      animation.cancel();
      await ready;
      if (disposed || token !== revision) return;
      const previous = step, destination = target(next), replay = next === previous && next > 0;
      step = next;
      slide.dataset.step = String(next);
      diagram.style.opacity = '1';
      if (next === 4) { render(destination); return; }
      if (replay) render(target(next - 1));
      if (!state || !replay && next !== previous + 1) { render(destination); return; }
      let source = state;
      if (next === 3) {
        const faded = await animation.run(.25, progress => {
          const alpha = progress * progress * (3 - 2 * progress);
          render({ ...source, opacity: source.opacity.map((value, index) => index < 2 ? value * (1 - alpha) : value) });
        });
        if (!faded || disposed || token !== revision) return;
        source = state;
      }
      const finished = await animation.run(.85, progress => {
        const alpha = progress * progress * (3 - 2 * progress);
        render({
          centers: source.centers.map((value, index) => lerp(value, destination.centers[index], alpha)),
          visible: source.visible.map((value, index) => lerp(value, destination.visible[index], alpha)),
          point: lerp(source.point, destination.point, alpha),
          positions: source.positions.map((value, index) => lerp(value, destination.positions[index], alpha)),
          opacity: source.opacity.map((value, index) => index === next ? 0 : lerp(value, destination.opacity[index], alpha))
        });
      });
      if (!finished || disposed || token !== revision) return;
      await animation.run(.25, progress => {
        const alpha = progress * progress * (3 - 2 * progress);
        render({ ...destination, opacity: destination.opacity.map((value, index) => index === next ? alpha : value) });
      });
    },
    dispose() {
      if (disposed) return;
      disposed = true;
      revision++;
      animation.dispose();
      diagram.remove();
      text.remove();
    }
  };
}
