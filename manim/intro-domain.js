import { mathjax, TeX, SVG, liteAdaptor, RegisterHTMLHandler } from './vendor/MathJaxBundle-DRYv6mR0.js';

const adaptor = liteAdaptor();
RegisterHTMLHandler(adaptor);
const math = mathjax.document('', {
  InputJax: new TeX({ packages: ['base', 'ams'] }),
  OutputJax: new SVG({ fontCache: 'none' })
});
const namespace = 'http://www.w3.org/2000/svg';
const scale = .0238, gap = 5.95;
const cache = new Map();
const clamp = value => Math.max(0, Math.min(1, value));

function token(latex) {
  if (!cache.has(latex)) {
    const result = math.convert(latex, { display: false });
    const svg = new DOMParser().parseFromString(adaptor.outerHTML(result), 'image/svg+xml').querySelector('svg');
    const [, top, width, height] = svg.getAttribute('viewBox').split(/\s+/).map(Number);
    svg.setAttribute('width', String(width * scale));
    svg.setAttribute('height', String(height * scale));
    svg.setAttribute('y', String(27 + top * scale));
    svg.style.cssText = 'overflow:visible;color:#000';
    cache.set(latex, svg);
  }
  return cache.get(latex).cloneNode(true);
}

function write(paths, alpha) {
  const progress = clamp(alpha) * (1 + Math.max(0, paths.length - 1) * .045);
  paths.forEach(({ path, length }, index) => {
    const value = clamp(progress - index * .045);
    path.style.strokeDashoffset = String(length * (1 - clamp(value / .7)));
    path.style.strokeOpacity = value > 0 && value < 1 ? '1' : '0';
    path.style.fillOpacity = String(clamp((value - .7) / .3));
  });
}

export function createDomain(container) {
  const original = container.innerHTML;
  const svg = document.createElementNS(namespace, 'svg');
  svg.setAttribute('viewBox', '0 0 866 38');
  svg.setAttribute('width', '866');
  svg.setAttribute('height', '38');
  svg.setAttribute('role', 'img');
  svg.style.cssText = 'display:block;width:100%;height:38px;overflow:visible;color:#000';
  const nodes = ['\\text{smooth}', '\\text{singular}', '\\text{projective complex variety}', 'X', 'Y', '\\text{of dimension}', 'n', '\\text{.}'].map(token);
  svg.append(...nodes);
  container.replaceChildren(svg);
  const changing = [0, 1, 3, 4].map(index => [...nodes[index].querySelectorAll('path')].map(path => {
    const length = path.getTotalLength();
    path.setAttribute('fill', '#000');
    path.setAttribute('stroke', '#000');
    path.setAttribute('stroke-width', '18');
    path.setAttribute('stroke-linecap', 'round');
    path.setAttribute('stroke-linejoin', 'round');
    path.style.strokeDasharray = String(length);
    return { path, length };
  }));
  const widths = nodes.map(node => Number(node.getAttribute('width')));
  const layouts = [false, true].map(singular => {
    const order = [singular ? 1 : 0, 2, singular ? 4 : 3, 5, 6, 7];
    const width = order.reduce((sum, index) => sum + widths[index], 0) + 4 * gap;
    let x = (866 - width) / 2;
    const positions = [];
    order.forEach((index, position) => {
      positions[index] = x;
      x += widths[index] + (position < 4 ? gap : 0);
    });
    positions[singular ? 0 : 1] = positions[singular ? 1 : 0];
    positions[singular ? 3 : 4] = positions[singular ? 4 : 3];
    return positions;
  });
  let disposed = false;

  function transition(progress, from = false, to = true) {
    if (disposed) return;
    const alpha = clamp(progress);
    const amount = Number(from) + (Number(to) - Number(from)) * alpha;
    nodes.forEach((node, index) => node.setAttribute('x', String(layouts[0][index] + (layouts[1][index] - layouts[0][index]) * amount)));
    const smooth = clamp((.5 - amount) * 2), singular = clamp((amount - .5) * 2);
    write(changing[0], smooth);
    write(changing[1], singular);
    write(changing[2], smooth);
    write(changing[3], singular);
    container.dataset.kind = amount < .5 ? 'smooth' : 'singular';
    container.dataset.variety = amount < .5 ? 'X' : 'Y';
    svg.setAttribute('aria-label', container.dataset.kind + ' projective complex variety ' + container.dataset.variety + ' of dimension n.');
  }

  transition(0);
  return {
    set(singular) { transition(Number(singular)); },
    transition,
    dispose() {
      disposed = true;
      container.innerHTML = original;
      delete container.dataset.kind;
      delete container.dataset.variety;
    }
  };
}
