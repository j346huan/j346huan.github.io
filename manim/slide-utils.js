import './vendor/mathjax-double-struck.js';
import { mathjax, TeX, SVG, liteAdaptor, RegisterHTMLHandler } from './vendor/MathJaxBundle-DRYv6mR0.js';
import { VGroup, UpdateFromAlphaFunc } from './vendor/manim-web.js';

const adaptor = liteAdaptor();
RegisterHTMLHandler(adaptor);
const renderer = mathjax.document('', {
  InputJax: new TeX({ packages: ['base', 'ams', 'newcommand', 'configmacros'] }),
  OutputJax: new SVG({ fontCache: 'none' })
});
const cache = new Map();

export function svg(tag, attributes = {}) {
  const node = document.createElementNS('http://www.w3.org/2000/svg', tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, value);
  return node;
}

export function math(latex, size = 23.8) {
  const key = size + ':' + latex;
  if (!cache.has(key)) {
    const result = renderer.convert(latex, { display: true });
    const node = new DOMParser().parseFromString(adaptor.outerHTML(result), 'image/svg+xml').querySelector('svg');
    const [, top, width, height] = node.getAttribute('viewBox').split(/\s+/).map(Number);
    const scale = size / 1000;
    node.setAttribute('width', width * scale);
    node.setAttribute('height', height * scale);
    node.setAttribute('class', 'math-svg');
    node.setAttribute('role', 'img');
    node.setAttribute('aria-label', latex);
    node.style.cssText = 'display:inline-block;overflow:visible;color:inherit;vertical-align:' + -(top + height) * scale + 'px';
    cache.set(key, node);
  }
  return cache.get(key).cloneNode(true);
}

export function mathAt(parent, latex, x, y, size = 23.8) {
  const node = math(latex, size);
  node.setAttribute('x', x - Number(node.getAttribute('width')) / 2);
  node.setAttribute('y', y - Number(node.getAttribute('height')) / 2);
  parent.append(node);
  return node;
}

export function typeset(root) {
  root.querySelectorAll('[data-math]').forEach(node => node.replaceChildren(math(node.dataset.math, Number(node.dataset.size) || 23.8)));
}

export function motion() {
  const anchor = new VGroup();
  const jobs = new Set();
  let frame = 0, disposed = false;

  function tick(now) {
    frame = 0;
    for (const job of [...jobs]) {
      try {
        const progress = Math.min(1, (now - job.start) / (job.animation.duration * 1000));
        job.animation.interpolate(progress);
        if (progress === 1) {
          job.animation.finish();
          jobs.delete(job);
          job.resolve(true);
        }
      } catch (error) {
        jobs.delete(job);
        job.reject(error);
      }
    }
    if (jobs.size) frame = requestAnimationFrame(tick);
  }

  function cancel() {
    cancelAnimationFrame(frame);
    frame = 0;
    for (const job of jobs) job.resolve(false);
    jobs.clear();
  }

  return {
    run(seconds, update) {
      if (disposed) return Promise.resolve(false);
      const animation = new UpdateFromAlphaFunc(anchor, (_, alpha) => update(alpha), { duration: seconds, rateFunc: alpha => alpha });
      animation.begin();
      animation.interpolate(0);
      return new Promise((resolve, reject) => {
        jobs.add({ animation, start: performance.now(), resolve, reject });
        if (!frame) frame = requestAnimationFrame(tick);
      });
    },
    cancel,
    dispose() {
      cancel();
      disposed = true;
      anchor.dispose();
    }
  };
}
