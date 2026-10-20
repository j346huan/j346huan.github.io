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
const text = value => escape(value).replace(/\$([^$]+)\$/g, (_, math) => `<i>${math.replace(/_([A-Za-z0-9]+)/g, '<sub>$1</sub>')}</i>`);
const anchor = (href, label) => url(href) ? `<a href="${escape(url(href))}">${text(label)}</a>` : text(label);

export function renderHomepage(graph) {
  const cards = new Map((graph.cards || []).map(card => [card.id, card]));
  const graphLink = (source, card) => {
    const result = new URL('math/', home);
    result.searchParams.set('graph', source);
    if (card) result.searchParams.set('card', card);
    return result.href;
  };
  const target = id => {
    if (id.startsWith('graph:')) return url(graph.graphs?.[id.slice(6)]) ? graphLink(url(graph.graphs[id.slice(6)])) : '';
    const card = cards.get(id);
    if (!card) return '';
    const linkedGraph = Object.values(card.fields || {}).join('\n').match(/\[\[(graph:[^|\]]+)/)?.[1];
    if (linkedGraph) return target(linkedGraph);
    const media = Array.isArray(card.media) ? card.media : [card.media];
    return media.map(item => url(item?.href)).find(Boolean) || graphLink(`${home}jiahui-huang.json`, id);
  };
  const inline = value => {
    const input = String(value ?? '');
    const pattern = /\[\[([^|\]]+)(?:\|([^\]]+))?\]\]|\[([^\]\n]+)\]\(([^\s)]+)\)/g;
    let result = '', start = 0;
    for (const match of input.matchAll(pattern)) {
      result += text(input.slice(start, match.index));
      result += match[1] ? anchor(target(match[1]), match[2] || cards.get(match[1])?.title || match[1]) : anchor(match[4], match[3]);
      start = match.index + match[0].length;
    }
    return result + text(input.slice(start));
  };
  const paragraphs = value => String(value ?? '').trim().split(/\n\s*\n/).filter(Boolean).map(part => `<p>${inline(part).replace(/\n/g, '<br>')}</p>`).join('\n');
  const list = (value, papers = false) => `<ul>${String(value).split('\n').map(line => line.trim()).filter(Boolean).map(line => {
    const paper = papers && cards.get(line.match(/\[\[([^|\]]+)/)?.[1]);
    return `<li>${inline(line)}${paper?.fields?.authors ? `<p class="static-authors">${inline(paper.fields.authors)}</p>` : ''}${paper?.fields?.results ? `<p class="static-result">${inline(paper.fields.results.split(/\n\s*\n/)[0])}</p>` : ''}</li>`;
  }).join('\n')}</ul>`;
  const renderCard = card => {
    const fields = card.fields || {};
    const color = /^#[\da-f]{6}$/i.test(card.color) ? card.color : '#777d85';
    let content = '';
    if (card.id === 'profile') {
      content = Object.entries(fields).filter(([key, value]) => value && !['email', 'office', 'cv'].includes(key)).map(([key, value]) => `${key === 'introduction' ? '' : `<h3>${text(key)}</h3>`}${paragraphs(value)}`).join('\n');
      const email = String(fields.email || '');
      const contact = [email ? `<dt>Email</dt><dd>${/^[^\s@<>]+@[^\s@<>]+$/.test(email) ? `<a href="mailto:${escape(email)}">${text(email)}</a>` : text(email)}</dd>` : '', fields.office ? `<dt>Office</dt><dd>${text(fields.office)}</dd>` : ''].join('');
      content += `${contact ? `<dl>${contact}</dl>` : ''}${fields.cv ? `<p>${anchor(fields.cv, 'CV')}</p>` : ''}`;
    } else {
      content = Object.entries(fields).filter(([, value]) => value).map(([key, value]) => `${['text', 'mentees'].includes(key) ? '' : `<h3>${text(key.charAt(0).toUpperCase() + key.slice(1))}</h3>`}${list(value, card.id === 'publications')}`).join('\n');
    }
    const title = `<${card.id === 'profile' ? 'h1' : 'h2'}>${text(card.title)}</${card.id === 'profile' ? 'h1' : 'h2'}>`;
    return `<section class="static-card" id="home-${escape(card.id)}" style="--static-color:${color}">${['profile', 'publications'].includes(card.id) ? `<header>${title}</header><div class="static-content">${content}</div>` : `<details><summary>${title}</summary><div class="static-content">${content}</div></details>`}</section>`;
  };
  const roots = (graph.roots || []).filter(id => cards.has(id));
  const seen = new Set();
  const columns = (graph.rootColumns || [roots]).map(group => group.filter(id => roots.includes(id) && !seen.has(id) && seen.add(id))).filter(group => group.length);
  const remaining = roots.filter(id => !seen.has(id));
  if (remaining.length) columns.push(remaining);
  return `<!doctype html>
<html lang="en" data-initial-graph="https://j346huan.github.io/jiahui-huang.json" data-workspace="/math/">
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
  root.classList.add('graph-loading');
  const done = () => {
    root.classList.remove('graph-loading');
    clearTimeout(timer);
    window.removeEventListener('personal-graph-ready', done);
    window.removeEventListener('personal-graph-error', done);
  };
  const timer = setTimeout(done, 15000);
  window.addEventListener('personal-graph-ready', done);
  window.addEventListener('personal-graph-error', done);
})();
</script>
<style>
html,body{margin:0;background:#000}
html.graph-loading,html.graph-loading body{background:#000}
.graph-loading #app{visibility:hidden}
.graph-loading #static-home{display:none}
html:has(#static-home),html:has(#static-home) body{margin:0;min-height:100%;height:auto;overflow:auto;background:#000;color:#fff}
html:has(#static-home) #app{height:auto;min-height:100vh}
#static-home{box-sizing:border-box;display:grid;grid-template-columns:repeat(${Math.max(1, columns.length)},minmax(0,1fr));gap:24px;max-width:1600px;margin:auto;padding:24px;font:15px/1.55 system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}
#static-home *{box-sizing:border-box}
#static-home .static-column{min-width:0}
#static-home .static-card{margin-bottom:24px;border:1px solid #343740;border-radius:12px;overflow:hidden;background:#101216}
#static-home header,#static-home summary{padding:13px 18px;background:color-mix(in srgb,var(--static-color) 52%,#303540)}
#static-home summary{cursor:pointer}
#static-home summary h2{display:inline}
#static-home h1,#static-home h2{margin:0;font-size:18px;font-weight:600;line-height:1.35;color:#fff}
#static-home h3{margin:20px 0 10px;font-size:14px;font-weight:650;color:#e8e9ec}
#static-home .static-content{padding:2px 18px 16px;overflow-wrap:anywhere}
#static-home p{margin:14px 0 0}
#static-home ul{list-style:none;margin:14px 0 0;padding:0}
#static-home li{margin:0 0 17px}
#static-home li:last-child{margin-bottom:0}
#static-home a{color:#fff;text-decoration:underline;text-decoration-color:#8994a8;text-underline-offset:3px}
#static-home a:hover{color:#c7dbf4}
#static-home a:focus-visible,#static-home summary:focus-visible{outline:2px solid #a6c9f4;outline-offset:3px}
#static-home .static-authors{margin:5px 0 0;color:#c4c8d0;font-size:13px}
#static-home .static-result{margin:7px 0 0;color:#d7dae0;font-size:14px}
#static-home dl{display:grid;grid-template-columns:auto 1fr;gap:5px 12px;margin:18px 0 0}
#static-home dt{color:#c4c8d0}
#static-home dd{margin:0}
@media(max-width:760px){#static-home{display:block;padding:12px}#static-home .static-card{margin-bottom:16px}}
</style>
</head>
<body>
<div id="app"><main id="static-home">${columns.map(group => `<div class="static-column">${group.map(id => renderCard(cards.get(id))).join('\n')}</div>`).join('\n')}</main></div>
<script type="module">
const fallback = document.getElementById('static-home');
window.addEventListener('personal-graph-error', () => document.getElementById('app').replaceChildren(fallback), { once: true });
try {
  const base = new URL('/math/', location.href), response = await fetch(base);
  if (!response.ok) throw new Error('Unable to load website');
  const page = new DOMParser().parseFromString(await response.text(), 'text/html');
  await Promise.all([...page.querySelectorAll('link[rel="stylesheet"]')].map(source => new Promise((resolve, reject) => {
    const link = document.createElement('link');
    link.rel = 'stylesheet';
    link.href = new URL(source.getAttribute('href'), base).href;
    link.onload = resolve;
    link.onerror = reject;
    document.head.append(link);
  })));
  const source = page.querySelector('script[type="module"][src]');
  if (!source) throw new Error('Unable to load website');
  await import(new URL(source.getAttribute('src'), base).href);
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
