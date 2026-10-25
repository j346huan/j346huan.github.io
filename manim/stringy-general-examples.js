import { svg, math, typeset, motion } from './slide-utils.js';
import { createPolynomialDiagram } from './polynomial-diagram.js';

const red = '#b8202f', black = '#202020';
const clamp = x => Math.max(0, Math.min(1, x));
const ease = x => { const t = clamp(x); return t * t * (3 - 2 * t); };
const mix = (a, b, t) => a + (b - a) * t;
const m = latex => '<span data-math="' + latex + '"></span>';
const key = (p, q) => p + ',' + q;
const seed = new Map([['0,0',1],['1,1',2],['2,2',14],['3,3',14],['4,4',2],['5,5',1],['2,3',-1],['3,2',-1]]);
const factors = [[[0,0],[1,0],[0,1],[1,1]], [[0,0],[1,1]]];
function multiply(values, shifts) {
  const result = new Map();
  for (const [entry, value] of values) {
    const [p,q] = entry.split(',').map(Number);
    for (const [a,b] of shifts) result.set(key(p+a,q+b), (result.get(key(p+a,q+b)) || 0) + value);
  }
  return result;
}
const products = [seed, multiply(seed, factors[0])];
products.push(multiply(products[1], factors[1]));
const tint = (a,b,t) => '#' + [1,3,5].map(i => Math.round(mix(parseInt(a.slice(i,i+2),16),parseInt(b.slice(i,i+2),16),t)).toString(16).padStart(2,'0')).join('');

function createProducts(parent) {
  const node = svg('svg', { width:866, height:440, viewBox:'0 0 866 440' });
  node.style.cssText = 'position:absolute;left:0;top:100px;overflow:visible'; parent.append(node);
  const shade = svg('path', { fill:'#f1f1f1' }), grid = svg('g', { stroke:'#d0d0d0', 'stroke-width':.7 });
  const points = svg('g'), moving = svg('g'); node.append(shade,grid,points,moving);
  const entries = [], lines = [];
  for (let p=0;p<=7;p++) for(let q=0;q<=7;q++) {
    const dot = svg('circle', { r:2.3, fill:black }); points.append(dot); entries.push({p,q,dot});
    for(const [a,b] of [[p+1,q],[p,q+1]]) if(a<=7&&b<=7) {
      const line = svg('line'); grid.append(line); lines.push({p,q,a,b,line});
    }
  }
  let travelers = [], active = -1;
  const position = (p,q,n) => [433+(p-q)*29, 220+(n-p-q)*29];
  function set(stage, progress=1) {
    const next = Math.max(0, Math.min(2, stage));
    const previous = Math.max(0,next-1), from = 5+previous, to = 5+next;
    const growth = next ? ease(progress/.72) : 1;
    const n = next ? mix(from,to,growth) : 5;
    const settle = next ? ease((progress-.72)/.28) : 1;
    const pos = (p,q) => position(p,q,n);
    shade.setAttribute('d','M'+[[0,0],[n,0],[n,n],[0,n]].map(([p,q])=>pos(p,q).join(',')).join('L')+'Z');
    for (const {p,q,dot} of entries) {
      const [x,y] = pos(p,q); dot.setAttribute('cx',x); dot.setAttribute('cy',y);
      const old = p<=from&&q<=from, visible = p<=to&&q<=to;
      dot.style.opacity = String(visible ? old ? 1 : growth : 0);
      const start = (products[previous].get(key(p,q))||0)<0 ? red : black;
      const end = (products[next].get(key(p,q))||0)<0 ? red : black;
      dot.setAttribute('fill', next ? tint(start,end,settle) : end);
      if(next && progress<1 && start===red) dot.setAttribute('fill',tint(start,end,ease(progress/.2)));
    }
    for (const {p,q,a,b,line} of lines) {
      const start = pos(p,q), end = pos(a,b);
      for(const [name,value] of Object.entries({x1:start[0],y1:start[1],x2:end[0],y2:end[1]})) line.setAttribute(name,value);
      line.style.opacity = String(a<=to&&b<=to ? a<=from&&b<=from ? 1 : growth : 0);
    }
    if(active!==next) {
      moving.replaceChildren(); travelers=[]; active=next;
      if(next) for(const [entry,value] of products[previous]) if(value<0) {
        const [p,q]=entry.split(',').map(Number);
        for(const [a,b] of factors[next-1]) {
          const dot=svg('circle',{r:2.8,fill:red}); moving.append(dot); travelers.push({p,q,a,b,dot});
        }
      }
    }
    for(const {p,q,a,b,dot} of travelers) {
      const shift=ease((progress-.08)/.57), [x,y]=pos(p+a*shift,q+b*shift);
      dot.setAttribute('cx',x); dot.setAttribute('cy',y); dot.style.opacity=String(1-settle);
    }
  }
  set(0);return {node,set,dispose(){node.remove();}};
}

export function createGeneralExamples(slide) {
  const body=document.createElement('div');
  body.style.cssText='position:absolute;left:47px;top:145px;width:866px;height:550px;color:#000;font:23px/1.3 Beamer,serif';slide.append(body);
  const formula=document.createElement('div');formula.style.cssText='position:absolute;left:0;top:0;width:866px;text-align:center';
  formula.append(math('E_{\\mathrm{st}}(X\\times C^r)=E_{\\mathrm{st}}(X)\\cdot(1-g(u+v)+uv)^r.'));body.append(formula);
  const theorem=document.createElement('div');
  theorem.style.cssText='position:absolute;left:0;top:60px;width:866px;box-sizing:border-box;border:1px solid #000;padding:12px 16px;font-style:italic';
  theorem.innerHTML='<strong style="font-style:normal">Theorem B (H.-Satriano).</strong> Let '+m('(n,p,q)\\in\\mathbb Z_{\\geq0}^3')+'. Then '+m('h_{\\mathrm{st}}^{p,q}(Y)\\geq0')+' for all projective Gorenstein canonical '+m('n')+'-folds '+m('Y')+' with polynomial '+m('E_{\\mathrm{st}}(Y)')+' if and only if at least one of the following holds:';
  const conditions=document.createElement('div');conditions.style.cssText='display:grid;grid-template-columns:1fr 1fr;gap:3px 20px;margin-top:8px';
  for(const latex of ['\\min(p,q)\\leq1','\\max(p,q)\\geq n-1','(p,q)=(2,2)','(p,q)=(n-2,n-2)']) {
    const item=document.createElement('div');item.innerHTML='<span style="display:inline-block;width:22px;font-style:normal">•</span>'+m(latex);conditions.append(item);
  }
  theorem.append(conditions);typeset(theorem);body.append(theorem);
  const classification=createPolynomialDiagram(body);
  classification.set({x:433,y:150,n:8,unit:17,band:2,bandAlpha:1,special:1,neutral:1,counterexamples:1});
  const productsDiagram=createProducts(body);
  const operation=document.createElement('div');operation.style.cssText='position:absolute;left:0;top:65px;width:866px;text-align:center';body.append(operation);
  const operations=[null, math('\\times\\; C\\qquad (g=1)'), math('\\times\\;\\mathbb P^1')];
  let displayed=-1;
  function layout(theoremTop=60) {
    theorem.style.top=theoremTop+'px';
    const top=theoremTop+theorem.offsetHeight+13, scale=Math.min(1.3,(550-top)/300);
    classification.node.style.top=top+'px';classification.node.style.left=(866*(1-scale)/2)+'px';
    classification.node.style.transformOrigin='0 0';classification.node.style.transform='scale('+scale+')';
  }
  function show(node, alpha) {node.style.opacity=String(alpha);node.style.visibility=alpha>0?'visible':'hidden';}
  function setOperation(next) {
    if(displayed===next)return;
    operation.replaceChildren(...(operations[next]?[operations[next]]:[]));displayed=next;
  }
  function paint(next) {
    layout(next>=2?0:60);show(formula,next<2?1:0);
    show(theorem,next>=1&&next<=3?1:0);show(classification.node,next===3?1:0);
    show(productsDiagram.node,next>=4?1:0);setOperation(Math.max(0,next-4));show(operation,next>=5?1:0);
    productsDiagram.set(Math.max(0,next-4));
  }
  const timeline=motion();let step=-1,revision=0,disposed=false;
  return {
    animated:true,
    async play(next=0) {
      if(disposed)return;
      next=Math.max(0,Math.min(6,Number(next)||0));const previous=step,token=++revision;
      timeline.cancel();step=next;slide.dataset.step=String(next);
      const run=async(seconds,update)=>await timeline.run(seconds,update)&&!disposed&&token===revision;
      if(next===previous+1&&next===2) {
        if(!await run(.25,t=>show(formula,1-ease(t))))return;
        if(!await run(.65,t=>layout(60*(1-ease(t)))))return;
      } else if(next===previous+1&&next===4) {
        if(!await run(.3,t=>{show(theorem,1-ease(t));show(classification.node,1-ease(t));}))return;
        productsDiagram.set(0);if(!await run(.3,t=>show(productsDiagram.node,ease(t))))return;
      } else if(next===previous+1&&next>=5) {
        if(previous>=5&&!await run(.2,t=>show(operation,1-ease(t))))return;
        setOperation(next-4);show(operation,1);
        if(!await run(2,t=>productsDiagram.set(next-4,t)))return;
      }
      if(!disposed&&token===revision)paint(next);
    },
    dispose(){disposed=true;revision++;timeline.dispose();classification.dispose();productsDiagram.dispose();body.remove();}
  };
}
