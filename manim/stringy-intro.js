import { Scene, UpdateFromAlphaFunc } from './vendor/manim-web.js';
import { createGeometry } from './intro-geometry.js';
import { createAnswers } from './intro-answers.js';
import { createDomain } from './intro-domain.js';

export function createIntro(container, slide) {
  const scene = new Scene(container, { width: 800, height: 400, frameWidth: 16, frameHeight: 8, backgroundColor: '#ffffff', backgroundOpacity: 0, autoRender: false });
  const geometry = createGeometry(scene);
  const answerBox = slide.querySelector('.intro-answer');
  const answers = createAnswers(answerBox);
  const domain = createDomain(slide.querySelector('.intro-domain'));
  const jobs = new Set();
  let frame, last = 0, phase = 0, speed = .6, velocity = 0, fast = false;
  let step = -1, revision = 0, pending = '', answerKey = '', morph = 0, disposed = false;
  geometry.setStretch(1);
  geometry.setBallVisible(true);

  function cancel() {
    revision++;
    for (const job of jobs) job.resolve(false);
    jobs.clear();
    fast = false;
    return revision;
  }

  function animate(update, duration, token) {
    if (disposed || token !== revision) return Promise.resolve(false);
    const animation = new UpdateFromAlphaFunc(geometry.anchor, (_, alpha) => update(alpha), { duration });
    animation.begin();
    return new Promise(resolve => jobs.add({ animation, start: performance.now(), token, resolve }));
  }

  function clearAnswer() {
    answers.clear();
    answerBox.style.transform = '';
    answerBox.style.clipPath = '';
    answerKey = '';
    slide.dataset.answer = '';
  }

  async function hideAnswer(token) {
    if (answerKey) {
      answers.erase(0);
      if (!await animate(alpha => answers.erase(alpha), .28, token)) return false;
    }
    if (token !== revision || disposed) return false;
    clearAnswer();
    return true;
  }

  async function showAnswer(key, token) {
    fast = true;
    slide.dataset.busy = 'true';
    if (!await hideAnswer(token)) return;
    fast = true;
    slide.dataset.answer = key;
    await answers.prepare(key);
    if (token !== revision || disposed) return;
    answerKey = key;
    answers.write(1);
    const offset = 255;
    const move = alpha => {
      const eased = alpha * alpha * alpha * (alpha * (alpha * 6 - 15) + 10);
      answerBox.style.transform = 'translateX(' + offset * (1 - eased) + 'px)';
      answerBox.style.clipPath = 'inset(0 ' + 100 * (1 - eased) + '% 0 0)';
    };
    move(0);
    if (!await animate(move, 1.55, token)) return;
    answerBox.style.clipPath = '';
    fast = false;
    slide.dataset.busy = 'false';
  }

  function choose(key) {
    const token = cancel();
    Promise.all([showAnswer(key, token), shape(step < 3 ? 0 : 1, token)]).catch(fail);
  }

  function fail(error) {
    if (disposed) return;
    fast = false;
    console.error(error);
    window.parent.postMessage({ type: 'talk-error' }, location.origin);
  }

  async function shape(target, token, duration = 1.5) {
    const from = morph;
    if (from === target) {
      domain.set(!!target);
      return;
    }
    await animate(alpha => {
      const eased = alpha * alpha * (3 - 2 * alpha);
      morph = from + (target - from) * eased;
      geometry.setMorph(morph);
      domain.transition(morph, false, true);
    }, duration, token);
  }

  function tick(now) {
    if (disposed) return;
    const dt = Math.min(.1, (now - (last || now)) / 1000);
    last = now;
    for (const job of [...jobs]) {
      if (job.token !== revision) { jobs.delete(job); job.resolve(false); continue; }
      const progress = Math.min(1, (now - job.start) / (job.animation.duration * 1000));
      job.animation.interpolate(progress);
      if (progress === 1) {
        job.animation.finish();
        jobs.delete(job);
        job.resolve(true);
      }
    }
    const target = fast ? 3.5 : .6;
    const difference = speed - target;
    const decay = Math.exp(-3.2 * dt);
    const change = velocity + 3.2 * difference;
    speed = target + (difference + change * dt) * decay;
    velocity = (velocity - 3.2 * change * dt) * decay;
    phase += dt * speed;
    geometry.setSpin(phase);
    scene.render();
    frame = requestAnimationFrame(tick);
  }
  frame = requestAnimationFrame(tick);

  return {
    scene,
    async play(nextStep = 0) {
      if (disposed) return;
      const previous = step;
      const key = pending;
      pending = '';
      const token = cancel();
      step = nextStep;
      slide.dataset.step = String(step);
      slide.dataset.busy = 'false';
      if (step === 0) {
        clearAnswer();
        morph = 0;
        geometry.setMorph(0);
        domain.set(false);
      } else if (step === 1) {
        clearAnswer();
        await shape(0, token, .7);
      } else if (step === 2) {
        await Promise.all([shape(0, token, .7), showAnswer(key || (previous === step && answerKey) || 'h', token)]);
      } else if (step === 3) {
        if (previous === step) {
          morph = 0;
          geometry.setMorph(0);
          domain.set(false);
        }
        await Promise.all([hideAnswer(token), shape(1, token)]);
      } else {
        await Promise.all([shape(1, token), showAnswer(key || (previous === step && answerKey) || 'i', token)]);
      }
      if (token === revision && !disposed) scene.render();
    },
    handleKey(key) {
      key = key.toLowerCase();
      const allowed = step === 1 || step === 2 ? 'hekfcb' : step === 3 || step === 4 ? 'is' : '';
      if (disposed || key.length !== 1 || !allowed.includes(key)) return false;
      if (step === 1 || step === 3) {
        pending = key;
        return step + 1;
      }
      choose(key);
      return true;
    },
    dispose() {
      if (disposed) return;
      disposed = true;
      cancel();
      cancelAnimationFrame(frame);
      answers.dispose();
      domain.dispose();
      geometry.dispose();
      scene.dispose();
    }
  };
}
