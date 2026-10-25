import './vendor/mathjax-double-struck.js';
import { mathjax, TeX, SVG, liteAdaptor, RegisterHTMLHandler } from './vendor/MathJaxBundle-DRYv6mR0.js';

const answers = {
  h: ['Hodge numbers', 'h^{p,q}(X)'],
  e: ['Euler characteristic', '\\chi(X)'],
  k: ['Kodaira dimension', '\\kappa(X)'],
  f: ['Fundamental group', '\\pi_1(X)'],
  c: ['Chern numbers', 'c_n(X)'],
  b: ['Betti numbers', 'b_n(X)'],
  i: ['Intersection cohomology', 'h^{p,q}(\\mathrm{IH}^k(Y,\\mathbb C))'],
  s: ['Stringy Hodge numbers', 'h_{\\mathrm{st}}^{p,q}(Y)']
};
const adaptor = liteAdaptor();
RegisterHTMLHandler(adaptor);
const math = mathjax.document('', {
  InputJax: new TeX({ packages: ['base', 'ams', 'newcommand', 'configmacros'] }),
  OutputJax: new SVG({ fontCache: 'none' })
});
const cache = new Map();
const clamp = value => Math.max(0, Math.min(1, value));

function render(key) {
  if (!cache.has(key)) {
    const [label, formula] = answers[key];
    const result = math.convert('\\begin{gathered}\\text{' + label + '}\\\\[.35em]' + formula + '\\end{gathered}', { display: true });
    const svg = new DOMParser().parseFromString(adaptor.outerHTML(result), 'image/svg+xml').querySelector('svg');
    const [, , width, height] = svg.getAttribute('viewBox').split(/\s+/).map(Number);
    const scale = Math.min(420 / width, 85 / height, .024);
    svg.setAttribute('width', String(width * scale));
    svg.setAttribute('height', String(height * scale));
    svg.setAttribute('role', 'img');
    svg.setAttribute('aria-label', label);
    svg.style.cssText = 'display:block;margin:auto;max-width:100%;overflow:visible;color:#000';
    svg.querySelectorAll('path').forEach(path => {
      path.setAttribute('fill', '#000');
      path.setAttribute('stroke', '#000');
      path.setAttribute('stroke-width', '18');
      path.setAttribute('stroke-linecap', 'round');
      path.setAttribute('stroke-linejoin', 'round');
      path.style.fillOpacity = '0';
      path.style.strokeOpacity = '0';
    });
    cache.set(key, svg);
  }
  return cache.get(key).cloneNode(true);
}

export function createAnswers(container) {
  let paths = [], version = 0, amount = 0, erasedFrom = 0, disposed = false;

  function write(alpha) {
    amount = clamp(alpha);
    const progress = amount * (1 + Math.max(0, paths.length - 1) * .045);
    paths.forEach(({ path, length }, index) => {
      const value = clamp(progress - index * .045);
      path.style.strokeDashoffset = String(length * (1 - clamp(value / .7)));
      path.style.strokeOpacity = value > 0 && value < 1 ? '1' : '0';
      path.style.fillOpacity = String(clamp((value - .7) / .3));
    });
  }

  function clear() {
    version++;
    paths = [];
    container.replaceChildren();
  }

  return {
    async prepare(key) {
      if (disposed || !answers[key]) return;
      const current = ++version;
      const svg = await Promise.resolve(render(key));
      if (disposed || current !== version) return;
      container.replaceChildren(svg);
      paths = [...svg.querySelectorAll('path')].map(path => {
        const length = path.getTotalLength();
        path.style.strokeDasharray = String(length);
        return { path, length };
      });
      write(0);
    },
    write,
    erase(alpha) { if (alpha === 0) erasedFrom = amount; write(erasedFrom * (1 - alpha)); },
    clear,
    dispose() { disposed = true; clear(); }
  };
}
