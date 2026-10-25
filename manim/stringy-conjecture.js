import { math, typeset, motion } from './slide-utils.js';
import { createConjectureDiagram } from './conjecture-diagram.js';

const ease = value => value * value * (3 - 2 * value);
const clamp = value => Math.max(0, Math.min(1, value));

export function createConjecture(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;right:47px;top:139px';
  body.innerHTML = '<ul data-intro style="margin:0;padding-left:29px"><li style="margin-bottom:18px"><strong>Non-negativity:</strong> <span data-math="h^{p,q}(X)\\geq 0"></span> for smooth projective <span data-math="X"></span> because <span data-math="H^i(X)"></span> has pure Hodge structure, so <span data-math="h^{p,q}(X)=\\dim (H^k(X))^{p,q}"></span>.</li><li>If <span data-math="Y"></span> is projective but singular, can we have <span data-math="h_{\\mathrm{st}}^{p,q}\\geq 0"></span>?</li></ul><div data-conjecture style="border:1px solid #000;padding:12px 16px;font-style:italic;margin-top:25px"><strong style="font-style:normal">Conjecture (Batyrev)</strong> Let <span data-math="X"></span> be a complex projective variety with Gorenstein canonical singularities. If <span data-math="E_{\\mathrm{st}}(X;u,v)"></span> is polynomial, then<div data-display data-math="h_{\\mathrm{st}}^{p,q}(X)\\geq 0\\qquad\\text{for all }p,q."></div></div><div data-results style="position:relative;border:1px solid #000;margin-top:16px;height:408px;box-sizing:border-box"><div data-name style="position:absolute;left:16px;top:13px"></div><ul data-batyrev style="position:absolute;left:20px;right:20px;top:256px;margin:0;padding-left:29px"><li>Cohomology of <span data-math="X"></span> carries pure Hodge structure, and<div data-display data-math="h_{\\mathrm{st}}^{p,q}(Y)=h^{p,q}(X)\\geq0."></div></li></ul><ul data-yasuda style="position:absolute;left:20px;right:20px;top:256px;margin:0;padding-left:29px"><li>Orbifold cohomology of <span data-math="\\mathcal{X}"></span> carries pure Hodge structure, and<div data-display data-math="h_{\\mathrm{st}}^{p,q}(Y)=h^{p,q}_{\\mathrm{orb}}(\\mathcal{X})\\geq0."></div></li></ul><ul data-cohomology style="position:absolute;left:20px;right:20px;top:256px;margin:0;padding-left:29px"><li>H.-Satriano-Usatine (2026) define stringy cohomology for Artin stacks,<div data-display data-math="h_{\\mathrm{st}}^{p,q}(Y)=h^{p,q}_{\\mathrm{st}}(\\mathcal{X})."></div><ul data-warning style="margin:8px 0 0;padding-left:27px;font-size:20px"><li><span style="color:#b8202f">Warning:</span> This does not prove non-negativity because we gave a mixed Hodge structure.</li></ul></li></ul></div>';
  slide.append(body);
  typeset(body);
  body.querySelectorAll('[data-display]').forEach(node => {
    node.style.textAlign = 'center';
    if (!node.style.position) node.style.marginTop = '8px';
  });
  const intro = body.querySelector('[data-intro]');
  const conjecture = body.querySelector('[data-conjecture]');
  const results = body.querySelector('[data-results]');
  const batyrev = body.querySelector('[data-batyrev]');
  const yasuda = body.querySelector('[data-yasuda]');
  const cohomology = body.querySelector('[data-cohomology]');
  const warning = body.querySelector('[data-warning]');
  const heading = body.querySelector('[data-name]');
  const names = ['Batyrev 1998', 'Yasuda 2004', 'Satriano-Usatine 2024'].map(name => {
    const node = math('\\textbf{' + name + '}');
    node.style.cssText += ';position:absolute;left:0;top:0';
    heading.append(node);
    return node;
  });
  const ink = names.map(node => [...node.querySelectorAll('path')].map(path => {
    const length = path.getTotalLength();
    path.style.stroke = 'currentColor';
    path.style.strokeWidth = '16';
    path.style.strokeLinecap = 'round';
    path.style.strokeLinejoin = 'round';
    path.style.strokeDasharray = String(length);
    return { path, length };
  }));
  function write(index, amount) {
    const progress = clamp(amount) * (1 + (ink[index].length - 1) * .015);
    ink[index].forEach(({ path, length }, order) => {
      const value = clamp(progress - order * .015);
      path.style.strokeDashoffset = String(length * (1 - clamp(value / .7)));
      path.style.strokeOpacity = value > 0 && value < 1 ? '1' : '0';
      path.style.fillOpacity = String(clamp((value - .7) / .3));
    });
  }
  function rename(from, to, alpha) {
    names[from].style.visibility = alpha < 1 ? 'visible' : 'hidden';
    names[to].style.visibility = alpha > 0 ? 'visible' : 'hidden';
    write(from, 1 - alpha * 2.4);
    write(to, (alpha - .3) / .7);
  }
  const diagram = createConjectureDiagram();
  diagram.element.style.cssText = 'position:absolute;left:0;top:44px;width:864px;height:218px;overflow:visible;pointer-events:none';
  results.append(diagram.element);
  const timeline = motion();
  let step = -1, revision = 0, disposed = false;

  function state(next) {
    for (const node of [intro, conjecture, results, batyrev, yasuda, cohomology, warning]) {
      node.style.opacity = '1';
      node.style.transform = '';
    }
    intro.style.display = next < 3 ? '' : 'none';
    intro.children[1].style.visibility = next > 0 ? 'visible' : 'hidden';
    conjecture.style.visibility = next >= 2 ? 'visible' : 'hidden';
    conjecture.style.marginTop = next < 3 ? '25px' : '0';
    results.style.display = next >= 3 ? '' : 'none';
    batyrev.style.visibility = next === 4 ? 'visible' : 'hidden';
    yasuda.style.visibility = next === 7 ? 'visible' : 'hidden';
    cohomology.style.visibility = next >= 9 ? 'visible' : 'hidden';
    warning.style.visibility = next >= 10 ? 'visible' : 'hidden';
    const name = next < 5 ? 0 : next < 8 ? 1 : 2;
    names.forEach((node, index) => {
      node.style.visibility = index === name ? 'visible' : 'hidden';
      write(index, 1);
    });
    diagram.state(next < 5 ? 'batyrev' : next < 6 ? 'yasuda' : next < 8 ? 'dm' : 'artin');
  }

  return {
    animated: true,
    async play(next = 0) {
      if (disposed) return;
      const previous = step, token = ++revision;
      timeline.cancel();
      step = next;
      slide.dataset.step = String(next);
      const run = async (seconds, update) => await timeline.run(seconds, update) && !disposed && token === revision;
      if (next === 3 && (previous === 2 || previous === 3)) {
        state(2);
        const offset = conjecture.offsetTop;
        if (!await run(.25, alpha => { intro.style.opacity = String(1 - ease(alpha)); })) return;
        state(3);
        results.style.opacity = '0';
        if (!await run(.8, alpha => { conjecture.style.transform = 'translateY(' + offset * (1 - ease(alpha)) + 'px)'; })) return;
        conjecture.style.transform = '';
        if (!await run(.25, alpha => { results.style.opacity = String(ease(alpha)); })) return;
      } else if (next === 5 && (previous === 4 || previous === 5)) {
        state(4);
        if (!await run(.25, alpha => {
          const opacity = String(1 - ease(alpha));
          batyrev.style.opacity = opacity;
          diagram.source.style.opacity = opacity;
          diagram.arrow.style.opacity = opacity;
        })) return;
        batyrev.style.visibility = 'hidden';
        if (!await run(1.1, alpha => {
          diagram.center(ease(alpha));
          rename(0, 1, alpha);
        })) return;
      } else if (next === 6 && (previous === 5 || previous === 6)) {
        state(5);
        if (!await run(1.25, alpha => { diagram.resolve(ease(alpha)); })) return;
      } else if (next === 8 && (previous === 7 || previous === 8)) {
        state(7);
        if (!await run(.25, alpha => { yasuda.style.opacity = String(1 - ease(alpha)); })) return;
        yasuda.style.visibility = 'hidden';
        if (!await run(1.2, alpha => {
          diagram.artin(ease(alpha));
          rename(1, 2, alpha);
        })) return;
      }
      if (!disposed && token === revision) state(next);
    },
    dispose() {
      disposed = true;
      revision++;
      timeline.dispose();
      body.remove();
    }
  };
}
