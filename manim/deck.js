import Reveal from './vendor/reveal.js';

export async function mountTalk(createAnimation, animationSteps = []) {
  const root = document.querySelector('.reveal');
  const width = Number(root.dataset.width) || 960;
  const height = Number(root.dataset.height) || 540;
  const steps = index => Math.max(1, animationSteps[index] || 1);
  const deck = new Reveal(root, {
    width,
    height,
    margin: 0,
    minScale: 0.05,
    maxScale: 4,
    embedded: true,
    center: false,
    controls: false,
    progress: false,
    keyboard: false,
    overview: false,
    touch: false,
    hash: false,
    history: false,
    transition: 'none',
    backgroundTransition: 'none',
    view: 'slide',
    scrollActivationWidth: null,
    autoAnimate: false
  });
  let active;
  let generation = 0;
  let index = 0;
  let step = 0;
  const total = () => deck.getTotalSlides();
  const fail = error => {
    console.error(error);
    window.parent.postMessage({ type: 'talk-error' }, location.origin);
  };
  const resize = () => {
    if (!active?.scene) return;
    const renderer = active.scene.renderer.getThreeRenderer();
    const canvas = active.scene.renderer.getCanvas();
    const bounds = canvas.getBoundingClientRect();
    if (!bounds.width || !bounds.height) return;
    const size = renderer.getSize({ set: (x, y) => ({ x, y }) });
    const ratio = Math.max(Math.ceil(bounds.width * devicePixelRatio) / size.x, Math.ceil(bounds.height * devicePixelRatio) / size.y);
    if (canvas.width === Math.floor(size.x * ratio) && canvas.height === Math.floor(size.y * ratio)) return;
    renderer.setPixelRatio(ratio);
    active.scene.render();
  };
  const observer = new ResizeObserver(resize);
  let resolution;
  const watchResolution = () => {
    resolution?.removeEventListener('change', watchResolution);
    resolution = matchMedia('(resolution: ' + devicePixelRatio + 'dppx)');
    resolution.addEventListener('change', watchResolution);
    resize();
  };
  const clear = () => {
    generation++;
    observer.disconnect();
    active?.dispose();
    active = null;
  };
  const show = (nextIndex = index, nextStep = step) => {
    nextIndex = Math.max(0, Math.min(nextIndex, total() - 1));
    nextStep = Math.max(0, Math.min(nextStep, steps(nextIndex) - 1));
    const slide = deck.getSlides()[nextIndex];
    try {
      if (nextIndex !== index || !active) {
        clear();
        if (typeof createAnimation === 'function' && !document.hidden) {
          active = createAnimation(document.createElement('div'), nextIndex, slide);
          if (active?.scene) {
            const stage = slide.querySelector('.animation-stage');
            stage.replaceChildren(active.scene.renderer.getCanvas());
            observer.observe(stage);
          }
        }
      }
      index = nextIndex;
      step = nextStep;
      deck.slide(index);
      const token = ++generation;
      Promise.resolve(active?.play(step)).catch(error => {
        if (token === generation) fail(error);
      });
      resize();
      const numbers = deck.getSlides().filter(item => item.hasAttribute('data-number')).map(item => Number(item.dataset.number));
      const number = slide.hasAttribute('data-number') ? Number(slide.dataset.number) : index + 1;
      window.parent.postMessage({
        type: 'talk-state', index, step, steps: steps(index), total: total(), width, height,
        animated: active?.animated ?? !!active, interactive: typeof active?.handleKey === 'function',
        number, contentTotal: numbers.length ? Math.max(...numbers) : total()
      }, location.origin);
    } catch (error) {
      clear();
      fail(error);
    }
  };
  const command = (name, value) => {
    if (name === 'jump') {
      const match = typeof value === 'string' && value.trim().match(/^(\d+)(?:\.(\d+))?$/);
      const number = match ? Number(match[1]) : NaN;
      const nextStep = match ? Number(match[2] ?? 1) : NaN;
      const nextIndex = deck.getSlides().findIndex((slide, position) =>
        (slide.hasAttribute('data-number') ? Number(slide.dataset.number) : position + 1) === number);
      if (nextIndex < 0 || !Number.isSafeInteger(nextStep) || nextStep < 1 || nextStep > steps(nextIndex)) {
        window.parent.postMessage({ type: 'talk-jump-error', value }, location.origin);
        return;
      }
      clear();
      show(nextIndex, nextStep - 1);
      return;
    }
    if (name === 'previous') {
      if (step > 0) show(index, step - 1);
      else if (index > 0) show(index - 1, steps(index - 1) - 1);
    }
    if (name === 'next') {
      if (active?.beforeNext?.()) return;
      if (step + 1 < steps(index)) show(index, step + 1);
      else if (index + 1 < total()) show(index + 1, 0);
    }
    if (name === 'restart') show(0, 0);
  };
  const key = value => {
    const name = value.length === 1 ? value.toLowerCase() : value;
    const handled = active?.handleKey?.(name);
    if (Number.isInteger(handled)) {
      show(index, handled);
      return true;
    }
    if (handled) return true;
    const action = { ArrowLeft: 'previous', PageUp: 'previous', ArrowRight: 'next', PageDown: 'next', ' ': 'next', r: 'restart' }[name];
    if (action) {
      command(action);
      return true;
    }
    if (name === 'Escape') {
      window.parent.postMessage({ type: 'talk-restore' }, location.origin);
      return true;
    }
    if (name === 'f') {
      window.parent.postMessage({ type: 'talk-fullscreen' }, location.origin);
      return true;
    }
    return false;
  };
  window.addEventListener('message', event => {
    if (event.source !== window.parent || event.origin !== location.origin) return;
    if (event.data?.type === 'talk-command') command(event.data.command, event.data.value);
    if (event.data?.type === 'talk-key' && typeof event.data.key === 'string') key(event.data.key);
    if (event.data?.type === 'talk-dispose') clear();
  });
  document.addEventListener('keydown', event => {
    if (event.ctrlKey || event.metaKey || event.altKey) return;
    if (key(event.key)) {
      event.preventDefault();
      event.stopPropagation();
    }
  });
  deck.on('resize', resize);
  window.addEventListener('resize', resize);
  watchResolution();
  document.addEventListener('visibilitychange', () => document.hidden ? clear() : show());
  window.addEventListener('pagehide', clear);
  await deck.initialize();
  const parameters = new URL(location.href).searchParams;
  const requestedIndex = Number(parameters.get('slide'));
  const requestedStep = Number(parameters.get('step'));
  show(Number.isInteger(requestedIndex) ? requestedIndex : 0, Number.isInteger(requestedStep) ? requestedStep : 0);
  return deck;
}
