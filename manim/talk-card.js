const icons = {
  previous: '<path d="m14 6-6 6 6 6"/>',
  next: '<path d="m10 6 6 6-6 6"/>',
  restart: '<path d="M4 10a8 8 0 1 1 1 7M4 4v6h6"/>',
  maximize: '<rect x="3" y="3" width="18" height="18" rx="1"/><path d="M3 8h18"/>',
  restore: '<rect x="3" y="7" width="14" height="14" rx="1"/><path d="M7 7V3h14v14h-4"/>',
  fullscreen: '<path d="M8 3H3v5m13-5h5v5M3 16v5h5m13-5v5h-5"/>'
};
const button = (command, label) => '<button type="button" data-talk-command="' + command + '" aria-label="' + label + '"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">' + icons[command] + '</svg></button>';

class TalkPlayer extends HTMLElement {
  connectedCallback() {
    this.innerHTML = '<div class="talk-viewport"><div class="talk-frame"></div><p class="talk-status" role="status"></p></div><nav class="talk-controls" aria-label="Presentation controls">' + button('previous', 'Previous step') + '<span class="talk-page"><button type="button" class="talk-page-button" aria-label="Go to slide and step"><output aria-live="polite"></output></button><input class="talk-jump" type="text" inputmode="decimal" aria-label="Slide and step" autocomplete="off" spellcheck="false" hidden></span>' + button('next', 'Next step') + '<span class="talk-spacer"></span>' + button('restart', 'Return to title') + button('maximize', 'Maximize in tab') + button('fullscreen', 'Enter fullscreen') + '</nav>';
    this.card = this.closest('.card');
    this.viewport = this.querySelector('.talk-frame');
    this.status = this.querySelector('.talk-status');
    this.pageButton = this.querySelector('.talk-page-button');
    this.jumpInput = this.querySelector('.talk-jump');
    this.controller = new AbortController();
    const options = { signal: this.controller.signal };
    this.querySelector('[data-talk-command="maximize"]').setAttribute('aria-pressed', 'false');
    this.pageButton.addEventListener('click', event => {
      event.stopPropagation();
      this.jumpInput.value = this.number === 0 ? '0' : this.number + '.' + (this.step + 1);
      this.pageButton.hidden = true;
      this.jumpInput.hidden = false;
      this.jumpInput.removeAttribute('aria-invalid');
      this.jumpInput.focus({ preventScroll: true });
      this.jumpInput.select();
    }, options);
    this.jumpInput.addEventListener('keydown', event => {
      event.stopPropagation();
      if (event.key === 'Escape') {
        event.preventDefault();
        this.closeJump(true);
      }
      if (event.key === 'Enter') {
        event.preventDefault();
        const value = this.jumpInput.value.trim();
        if (!/^\d+(?:\.\d+)?$/.test(value)) {
          this.jumpInput.setAttribute('aria-invalid', 'true');
          return;
        }
        if (this.ready) {
          this.jumpValue = value;
          this.frame.contentWindow.postMessage({ type: 'talk-command', command: 'jump', value }, location.origin);
        }
      }
    }, options);
    this.jumpInput.addEventListener('input', () => this.jumpInput.removeAttribute('aria-invalid'), options);
    this.jumpInput.addEventListener('blur', () => this.closeJump(), options);
    this.querySelector('nav').addEventListener('click', event => {
      const control = event.target.closest('[data-talk-command]');
      if (control && !control.disabled) {
        event.stopPropagation();
        this.command(control.dataset.talkCommand);
      }
    }, options);
    this.addEventListener('keydown', event => {
      if (event.ctrlKey || event.metaKey || event.altKey) return;
      const key = event.key.length === 1 ? event.key.toLowerCase() : event.key;
      const command = { ArrowLeft: 'previous', PageUp: 'previous', ArrowRight: 'next', PageDown: 'next', ' ': 'next', r: 'restart', f: 'fullscreen' }[key];
      if (command || this.interactive && /^[a-z]$/.test(key)) {
        event.preventDefault();
        event.stopPropagation();
        if (this.ready) this.frame.contentWindow.postMessage({ type: 'talk-key', key }, location.origin);
      }
    }, options);
    window.addEventListener('keydown', event => {
      if (event.key === 'Escape' && this.maximized && event.target !== this.jumpInput) {
        event.preventDefault();
        event.stopImmediatePropagation();
        this.setMaximized(false);
      }
    }, { ...options, capture: true });
    for (const type of ['pointerdown', 'wheel']) this.addEventListener(type, event => {
      if (this.maximized) event.stopPropagation();
    }, { ...options, passive: true });
    window.addEventListener('message', event => {
      if (event.origin !== location.origin || event.source !== this.frame?.contentWindow) return;
      const data = event.data;
      if (data?.type === 'talk-state') {
        this.ready = true;
        this.status.textContent = '';
        this.index = data.index;
        this.step = data.step;
        this.steps = data.steps;
        this.total = data.total;
        this.animated = data.animated;
        this.interactive = data.interactive;
        this.number = data.number ?? data.index + 1;
        this.contentTotal = data.contentTotal ?? data.total;
        if (data.width > 0 && data.height > 0) this.style.setProperty("--talk-ratio", data.width / data.height);
        this.updateControls();
        if (this.jumpValue !== undefined) this.closeJump(true);
        this.dispatchEvent(new Event("talk-layout", { bubbles: true }));
      }
      if (data?.type === 'talk-jump-error' && data.value === this.jumpValue) {
        this.jumpValue = undefined;
        this.jumpInput.setAttribute('aria-invalid', 'true');
      }
      if (data?.type === 'talk-fullscreen') this.command('fullscreen');
      if (data?.type === 'talk-restore' && this.maximized) this.setMaximized(false);
      if (data?.type === 'talk-error') this.status.textContent = 'The presentation could not be displayed.';
    }, options);
    document.addEventListener('fullscreenchange', () => {
      const control = this.querySelector('[data-talk-command="fullscreen"]');
      const fullscreen = document.fullscreenElement === this;
      control.setAttribute('aria-label', fullscreen ? 'Exit fullscreen' : 'Enter fullscreen');
      if (!fullscreen && this.returnMaximized) {
        this.returnMaximized = false;
        this.setMaximized(true);
      }
    }, options);
    this.observer = new MutationObserver(() => this.sync());
    if (this.card) this.observer.observe(this.card, { attributes: true, attributeFilter: ['class', 'inert'] });
    this.sync();
    queueMicrotask(() => this.dispatchEvent(new Event('talk-layout', { bubbles: true })));
  }

  closeJump(focus = false) {
    this.jumpValue = undefined;
    if (this.jumpInput.hidden) return;
    this.jumpInput.hidden = true;
    this.pageButton.hidden = false;
    this.jumpInput.removeAttribute('aria-invalid');
    if (focus) this.pageButton.focus({ preventScroll: true });
  }

  disconnectedCallback() {
    this.returnMaximized = false;
    this.setMaximized(false);
    this.controller?.abort();
    this.observer?.disconnect();
    this.unload();
  }

  setMaximized(active) {
    if (!!this.maximized === active) return;
    if (active) {
      this.placeholder = document.createElement('div');
      this.placeholder.style.cssText = 'height:' + this.offsetHeight + 'px;margin-top:' + getComputedStyle(this).marginTop;
      this.before(this.placeholder);
      this.setAttribute('popover', 'manual');
      this.showPopover();
    } else {
      if (this.matches(':popover-open')) this.hidePopover();
      this.removeAttribute('popover');
      this.placeholder?.remove();
      this.placeholder = null;
    }
    this.maximized = active;
    const control = this.querySelector('[data-talk-command="maximize"]');
    control.setAttribute('aria-label', active ? 'Restore to card' : 'Maximize in tab');
    control.setAttribute('aria-pressed', String(active));
    control.querySelector('svg').innerHTML = icons[active ? 'restore' : 'maximize'];
    if (!active && this.isConnected) control.focus({ preventScroll: true });
  }

  unload() {
    this.closeJump();
    this.returnMaximized = false;
    this.setMaximized(false);
    this.frame?.contentWindow?.postMessage({ type: 'talk-dispose' }, location.origin);
    this.frame?.remove();
    this.frame = null;
    this.ready = false;
  }

  sync() {
    if (this.card?.matches('.compact,.leaving,[inert]')) {
      this.unload();
      return;
    }
    if (this.frame) return;
    this.index ??= 0;
    this.step ??= 0;
    this.total ??= 0;
    this.steps ??= 1;
    this.updateControls();
    this.status.textContent = 'Loading presentation…';
    const url = new URL(this.getAttribute('src'), document.baseURI);
    if (url.origin !== location.origin) {
      this.status.textContent = 'Choose a presentation on this website.';
      return;
    }
    url.searchParams.set('slide', this.index);
    url.searchParams.set('step', this.step);
    this.frame = document.createElement('iframe');
    this.frame.src = url.href;
    this.frame.title = (this.getAttribute('aria-label') || 'Presentation') + ' slides';
    this.frame.allowFullscreen = true;
    this.viewport.replaceChildren(this.frame);
  }

  updateControls() {
    const number = this.number ?? this.index + 1;
    this.pageButton.disabled = !this.ready;
    this.querySelector('output').textContent = this.total ? (number === 0 ? 'Title / ' : number + (this.steps > 1 ? '.' + (this.step + 1) : '') + '/') + (this.contentTotal ?? this.total) : '';
    this.querySelector('[data-talk-command="previous"]').setAttribute('aria-label', this.animated ? 'Previous step' : 'Previous slide');
    this.querySelector('[data-talk-command="next"]').setAttribute('aria-label', this.animated ? 'Next step' : 'Next slide');
    this.querySelector('[data-talk-command="previous"]').disabled = !this.ready || this.index === 0 && this.step === 0;
    this.querySelector('[data-talk-command="next"]').disabled = !this.ready || this.index === this.total - 1 && this.step === this.steps - 1;
    this.querySelector('[data-talk-command="restart"]').disabled = !this.ready || this.index === 0 && this.step === 0;
  }

  async command(command) {
    if (command === 'maximize') {
      this.returnMaximized = false;
      if (document.fullscreenElement === this) await document.exitFullscreen();
      this.setMaximized(!this.maximized);
      return;
    }
    if (command === 'fullscreen') {
      try {
        if (document.fullscreenElement === this) await document.exitFullscreen();
        else {
          this.returnMaximized = !!this.maximized;
          this.setMaximized(false);
          await this.requestFullscreen();
        }
      } catch {
        if (this.returnMaximized) this.setMaximized(true);
        this.returnMaximized = false;
        this.status.textContent = 'Fullscreen is unavailable in this browser.';
      }
      return;
    }
    if (this.ready) this.frame.contentWindow.postMessage({ type: 'talk-command', command }, location.origin);
  }
}

customElements.define('talk-player', TalkPlayer);
