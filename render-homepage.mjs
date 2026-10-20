import { readFile, writeFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const home = 'https://j346huan.github.io/';
const escape = value => String(value ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
const url = value => {
  if (!value) return '';
  try {
    const result = new URL(value, home);
    return ['https:', 'http:'].includes(result.protocol) ? result.href : '';
  } catch { return ''; }
};
const section = id => `section-${encodeURIComponent(id)}`;
const label = value => {
  let input = String(value ?? '').replace(/\{\{[^|{}]+\|([^{}]+)\}\}/g, '$1');
  const pattern = /\\(?:term|card)\{[^{}]*\}\{/;
  for (let match; (match = pattern.exec(input));) {
    const start = match.index + match[0].length;
    let end = start, depth = 1;
    while (end < input.length && depth) {
      if (input[end] === '{' && input[end - 1] !== '\\') depth++;
      if (input[end] === '}' && input[end - 1] !== '\\') depth--;
      end++;
    }
    if (depth) break;
    input = input.slice(0, match.index) + input.slice(start, end - 1) + input.slice(end);
  }
  return input;
};
const text = value => {
  const input = label(value), pattern = /\$\$([\s\S]*?)\$\$|\$([^$\n]+)\$/g;
  let result = '', start = 0;
  for (const match of input.matchAll(pattern)) {
    result += escape(input.slice(start, match.index));
    result += `<code class="math-text">${escape(match[1] ?? match[2])}</code>`;
    start = match.index + match[0].length;
  }
  return result + escape(input.slice(start));
};

export function renderHomepage(graph) {
  const cards = new Map((graph.cards || []).map(card => [card.id, card]));
  const roots = [...new Set((graph.roots || []).filter(id => cards.has(id)))];
  const order = [...roots], seen = new Set(roots);
  const pattern = /\[\[([^|\]]+)(?:\|([^\]]+))?\]\]|\[([^\]\n]+)\]\(([^\s)]+)\)/g;
  const linked = card => {
    const values = [card.content, ...Object.values(card.fields || {})];
    const media = Array.isArray(card.media) ? card.media : [card.media];
    values.push(...media.map(item => item?.caption));
    const ids = values.flatMap(value => [...String(value ?? '').matchAll(pattern)].map(match => match[1]).filter(Boolean));
    ids.push(...(graph.connections || []).filter(edge => edge.source === card.id).map(edge => edge.target));
    return ids;
  };
  for (let i = 0; i < order.length; i++) {
    for (const id of linked(cards.get(order[i]))) {
      if (cards.has(id) && !seen.has(id)) { seen.add(id); order.push(id); }
    }
  }
  const target = id => {
    if (seen.has(id)) return `#${encodeURIComponent(section(id))}`;
    if (!['graph:math-127', 'graph:pmath-965'].includes(id)) return '';
    const source = url(graph.graphs?.[id.slice(6)]);
    if (!source) return '';
    const result = new URL('math/', home);
    result.searchParams.set('graph', source);
    return result.href;
  };
  const anchor = (href, value, local = false) => {
    const destination = local ? href : url(href);
    return destination ? `<a href="${escape(destination)}">${text(value)}</a>` : text(value);
  };
  const inline = value => {
    const input = label(value);
    let result = '', start = 0;
    for (const match of input.matchAll(pattern)) {
      result += text(input.slice(start, match.index));
      result += match[1]
        ? anchor(target(match[1]), match[2] || cards.get(match[1])?.title || match[1], true)
        : anchor(match[4], match[3]);
      start = match.index + match[0].length;
    }
    return result + text(input.slice(start));
  };
  const blocks = value => String(value ?? '').trim().split(/\n\s*\n/).filter(Boolean).map(part => {
    const lines = part.split('\n');
    if (lines.length > 1 && lines.every(line => /^\s*(?:\[\[|\[[^\]]+\]\(|[-*] )/.test(line))) {
      return `<ul>${lines.map(line => `<li>${inline(line.replace(/^\s*[-*] /, ''))}</li>`).join('')}</ul>`;
    }
    return `<p>${inline(part).replace(/\n/g, '<br>')}</p>`;
  }).join('\n');
  const renderCard = card => {
    const heading = card.id === 'profile' ? 'h1' : 'h2';
    let result = `<section id="${escape(section(card.id))}"><${heading}>${text(card.title)}</${heading}>`;
    if (card.content) result += blocks(card.content);
    for (const [key, value] of Object.entries(card.fields || {})) {
      if (!value) continue;
      const title = key === 'cv' ? 'CV' : key.charAt(0).toUpperCase() + key.slice(1);
      if (!['text', 'introduction'].includes(key)) result += `<h3>${text(title)}</h3>`;
      if (key === 'email' && /^[^\s@<>]+@[^\s@<>]+$/.test(value)) {
        result += `<p><a href="mailto:${escape(value)}">${escape(value)}</a></p>`;
      } else if (['cv', 'url'].includes(key)) {
        result += `<p>${anchor(value, key === 'cv' ? 'Curriculum Vitae' : value)}</p>`;
      } else result += blocks(value);
    }
    const media = Array.isArray(card.media) ? card.media : [card.media];
    for (const item of media) {
      if (url(item?.href)) result += `<p>${anchor(item.href, item.caption || card.title)}</p>`;
      else if (item?.caption) result += blocks(item.caption);
    }
    return `${result}</section>`;
  };
  return `<!doctype html>
<html lang="en" data-initial-graph="./jiahui-huang.json">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="theme-color" content="#000000">
<meta name="description" content="Jiahui Huang is a PhD student at the University of Waterloo, studying algebraic geometry, motivic integration, and singularity theory.">
<link rel="canonical" href="https://j346huan.github.io/">
<title>Jiahui Huang</title>
<script>
(() => {
  const root = document.documentElement;
  let timer;
  const fail = () => {
    root.dataset.homeView = 'failed';
    clearTimeout(timer);
  };
  const ready = () => {
    if (root.dataset.homeView === 'failed') return;
    root.dataset.homeView = 'ready';
    clearTimeout(timer);
  };
  window.addEventListener('error', fail, true);
  window.addEventListener('unhandledrejection', fail);
  window.addEventListener('personal-graph-error', fail);
  document.fonts.addEventListener('loadingerror', fail);
  window.addEventListener('personal-graph-ready', ready);
  root.dataset.homeView = 'loading';
  timer = setTimeout(fail, 15000);
})();
</script>
<style>
html,body{margin:0;background:#000;color:#eee}
html[data-home-view="loading"],html[data-home-view="loading"] body{height:100%!important;overflow:hidden!important;background:#000!important}
html[data-home-view="loading"] #app{visibility:hidden!important}
html:not([data-home-view]) #app,html[data-home-view="failed"] body>:not(#static-home){display:none!important}
html[data-home-view="loading"] #static-home,html[data-home-view="ready"] #static-home{display:none!important}
html:not([data-home-view]),html:not([data-home-view]) body,html[data-home-view="failed"],html[data-home-view="failed"] body{height:auto!important;min-height:100%!important;overflow:auto!important;position:static!important;background:#000!important}
#static-home{max-width:72rem;margin:0 auto;padding:2rem 1.25rem;font:16px/1.6 system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;overflow-wrap:anywhere;color:#eee}
#static-home h1,#static-home h2,#static-home h3{color:inherit;line-height:1.3}
#static-home h2{margin-top:2.5rem}
#static-home a{color:#9ecbff;text-decoration:underline}
#static-home .math-text{white-space:pre-wrap;overflow-wrap:anywhere;font-size:.95em}
</style>
</head>
<body>
<main id="static-home">${order.map(id => renderCard(cards.get(id))).join('\n')}</main>
<div id="app"></div>
<script type="module">
const root = document.documentElement;
try {
  if (root.dataset.homeView !== 'failed') {
    await new Promise((resolve, reject) => {
      const link = document.createElement('link');
      link.rel = 'stylesheet';
      link.href = './assets/homepage-db0e5a56.css';
      link.onload = resolve;
      link.onerror = reject;
      document.head.append(link);
    });
    if (root.dataset.homeView !== 'failed') await import('./assets/homepage-85f06acf.js');
  }
} catch {
  window.dispatchEvent(new Event('personal-graph-error'));
}
</script>
</body>
</html>
`;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const graph = JSON.parse(await readFile(new URL('jiahui-huang.json', import.meta.url), 'utf8'));
  await writeFile(new URL('index.html', import.meta.url), renderHomepage(graph));
}
