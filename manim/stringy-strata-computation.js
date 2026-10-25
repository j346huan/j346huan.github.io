import { svg, math, mathAt, typeset, motion } from './slide-utils.js';
import { createDiamond, createBrace } from './hodge-stratum.js';

const red = '#b8202f', grey = '#777777', black = '#202020';
const unit = 26, base = 408, left = 214;
const clamp = x => Math.max(0, Math.min(1, x));
const ease = x => x * x * (3 - 2 * x);
const mix = (a, b, t) => '#' + [1, 3, 5].map(i => Math.round(parseInt(a.slice(i, i + 2), 16) * (1 - t) + parseInt(b.slice(i, i + 2), 16) * t).toString(16).padStart(2, '0')).join('');
const m = text => '<span data-math="' + text + '"></span>';
const show = (node, visible) => { node.style.display = visible ? '' : 'none'; node.style.opacity = '1'; };
const place = (node, x, y) => { node.setAttribute('x', x - Number(node.getAttribute('width')) / 2); node.setAttribute('y', y - Number(node.getAttribute('height')) / 2); };

function ink(node) {
  const paths = [...node.querySelectorAll('path')].map(path => {
    const length = path.getTotalLength(), glyph = !!path.closest('.math-svg');
    path.style.stroke = 'currentColor'; path.style.strokeWidth = glyph ? '16' : '1.2';
    path.style.strokeLinecap = 'round'; path.style.strokeLinejoin = 'round'; path.style.strokeDasharray = String(length);
    return { path, length, glyph };
  });
  return amount => {
    paths.forEach(({ path, length, glyph }, i) => {
      const t = clamp(amount * (1 + paths.length * .002) - i * .002);
      path.style.strokeDashoffset = String(length * (1 - clamp(t / .75)));
      if (glyph) { path.style.strokeOpacity = t > 0 && t < 1 ? '1' : '0'; path.style.fillOpacity = String(clamp((t - .7) / .3)); }
    });
    node.querySelectorAll('circle,polygon').forEach(item => { item.style.opacity = String(clamp(amount * 1.4)); });
  };
}

export function createStrataComputation(slide) {
  const body = document.createElement('div');
  body.style.cssText = 'position:absolute;left:47px;top:139px;width:866px;color:#000'; slide.append(body);
  const equation = math('E_{\\mathrm{st}}(Y)=\\sum_{J\\subseteq I}E(D_J^\\circ)\\prod_{j\\in J}\\left((uv)^{-(a_j+1)}(uv-1)+(uv)^{-2(a_j+1)}(uv-1)+\\cdots\\right)', 22);
  const ew = Number(equation.getAttribute('width'));
  if (ew > 866) { equation.setAttribute('width', 866); equation.setAttribute('height', Number(equation.getAttribute('height')) * 866 / ew); }
  equation.style.cssText += ';position:absolute;left:' + Math.max(0, (866 - Math.min(866, ew)) / 2) + 'px;top:7px'; body.append(equation);
  const panel = svg('svg', { width: 866, height: 470, viewBox: '0 0 866 470' });
  panel.style.cssText = 'position:absolute;left:0;top:85px;overflow:visible'; body.append(panel);
  panel.append(svg('rect', { x: .7, y: .7, width: 864.6, height: 468.6, fill: 'none', stroke: '#000', 'stroke-width': 1.2 }));
  const headings = ['\\textbf{0-stratum}', '\\textbf{1-strata}', '\\textbf{2-strata}', '\\textbf{Final result}'].map(value => {
    const node = math(value, 23); node.setAttribute('x', 18); node.setAttribute('y', 14); panel.append(node); return node;
  });
  const defs = svg('defs'), gradient = svg('linearGradient', { id: 'strata-computation-fade', gradientUnits: 'userSpaceOnUse', x1: 0, y1: 48, x2: 0, y2: 466 });
  [[0,0],[.09,1],[.88,1],[1,0]].forEach(([offset, opacity]) => gradient.append(svg('stop', { offset, 'stop-color': '#fff', 'stop-opacity': opacity })));
  const mask = svg('mask', { id: 'strata-computation-mask', maskUnits: 'userSpaceOnUse', x: 0, y: 48, width: 866, height: 418 });
  mask.append(svg('rect', { x: 0, y: 48, width: 866, height: 418, fill: 'url(#strata-computation-fade)' })); defs.append(gradient, mask); panel.append(defs);
  const masked = svg('g', { mask: 'url(#strata-computation-mask)' }); panel.append(masked);
  const diagrams = svg('g'); masked.append(diagrams);
  const common = { x: left, y: base, unit, size: 21, opacity: .08 };
  const zero = createDiamond(diagrams, { ...common, n: 6, dimension: 'n', color: red, label: 'h_c^{p,q}(D_{\\varnothing}^{\\circ})' });
  const one = createDiamond(diagrams, { ...common, n: 5, dimension: 'n-1', color: red, label: 'h_c^{p,q}(D_i^{\\circ})' });
  const duplicate = createDiamond(diagrams, { ...common, n: 5, dimension: 'n-1', vertices: false, detail: 'short', color: red });
  const two = createDiamond(diagrams, { ...common, n: 4, dimension: 'n-2', vertices: false, color: red, label: 'h_c^{p,q}(D_{ij}^{\\circ})' });
  function paragraph(html, y) {
    const div = document.createElement('div'); div.style.cssText = 'position:absolute;left:442px;top:' + (85 + y) + 'px;width:398px;font-size:22px;line-height:1.4';
    div.innerHTML = html; typeset(div); body.append(div); return div;
  }
  const rightZero = paragraph(m('D_{\\varnothing}^{\\circ}=X\\setminus D\\cong Y_{\\mathrm{reg}}') + '<br>is the only ' + m('0') + '-stratum.', 181);
  const rightOne = paragraph(m('D_i^\\circ') + ' has codimension 1,<br>adjusted by', 143);
  const rightTwo = paragraph(m('D_{ij}^\\circ') + ' has codimension 2,<br>adjusted by', 158);
  const f1 = svg('g'); panel.append(f1);
  function aligned(latex, x, y, size = 22) {
    const node = math(latex, size); node.setAttribute('x', x); node.setAttribute('y', y - Number(node.getAttribute('height')) / 2); f1.append(node); return node;
  }
  const positive = aligned('(uv)^{-a_i}', 448, 245);
  const negative = aligned('-(uv)^{-(a_i+1)}', 595, 245);
  const lowerPositive = aligned('+(uv)^{-2(a_i+1)+1}', 448 - Number(math('+',22).getAttribute('width')), 299);
  const lowerNegative = aligned('-(uv)^{-2(a_i+1)}', 595, 299);
  const tailDots = aligned('+\\cdots', 595 + Number(lowerNegative.getAttribute('width')) + 7, 299, 22);
  const f2 = mathAt(panel, '(uv)^{-a_i-a_j}+\\cdots', 642, 260, 25);
  function outline(nodes, color) {
    const x = Math.min(...nodes.map(n => Number(n.getAttribute('x')))) - 5;
    const y = Math.min(...nodes.map(n => Number(n.getAttribute('y')))) - 5;
    const right = Math.max(...nodes.map(n => Number(n.getAttribute('x')) + Number(n.getAttribute('width')))) + 5;
    const bottom = Math.max(...nodes.map(n => Number(n.getAttribute('y')) + Number(n.getAttribute('height')))) + 5;
    const rect = svg('rect', { x, y, width: right - x, height: bottom - y, fill: 'none', stroke: color, 'stroke-width': 1.5 }); panel.append(rect); return rect;
  }
  const positiveBox = outline([positive], red), minusBox = outline([negative], red), tailBox = outline([lowerPositive, lowerNegative, tailDots], red), productBox = outline([f2], red);
  productBox.setAttribute('width', Number(productBox.getAttribute('width')) - Number(math('+\\cdots', 25).getAttribute('width')) - 4);
  function brace(x, from, to, label) {
    const group = svg('g', { color: red }); diagrams.append(group);
    const glyph = createBrace(group,{color:red,size:24}), text = math(label,21);group.append(text);
    const set = (start,end) => {glyph.set(x,start,end);text.setAttribute('x',x+glyph.width+7);text.setAttribute('y',(start+end)/2-Number(text.getAttribute('height'))/2);};
    set(from,to);return {group,set,write:ink(group)};
  }
  const shift = brace(378, 148, 252, 'a_i'), shiftI = brace(378, 200, 252, 'a_i'), shiftJ = brace(378, 252, 304, 'a_j');
  const omitted = svg('g', { color: red }); diagrams.append(omitted);
  [-9,0,9].forEach(dy => omitted.append(svg('circle', { cx: left, cy: 560 + dy, r: 1.7, fill: 'currentColor' })));
  const blade = svg('g'); masked.append(blade);
  const bladeFill = svg('polygon', { fill: '#888', 'fill-opacity': .08 });
  const bladeBorder = svg('path', { fill: 'none', stroke: '#777', 'stroke-width': 1.2 });
  const bladeMarks = svg('g', { fill: black }); blade.append(bladeFill, bladeBorder, bladeMarks);
  const center = { x: 433, y: 244 };
  const point = (p, q) => ({ x: 433 + (q - p) * unit, y: 400 - (p + q) * unit });
  const vertices = [{ p:6,q:6,latex:'n,n',mono:'u^nv^n',sign:'',tx:224,ty:250 },{p:0,q:6,latex:'0,n',mono:'v^n',sign:'+(-1)^n',tx:449,ty:110},{p:6,q:0,latex:'n,0',mono:'u^n',sign:'+(-1)^n',tx:449,ty:390}];
  const terms = [...vertices,{p:-1,q:5,latex:'-1,n-1',mono:'u^{-1}v^{n-1}',sign:'+(-1)^n',tx:711,ty:110},{p:5,q:-1,latex:'n-1,-1',mono:'u^{n-1}v^{-1}',sign:'+(-1)^n',tx:711,ty:390}].map(spec => {
    const node = mathAt(blade, 'h_{\\mathrm{st}}^{'+spec.latex+'}', 0, 0, 21);
    const sign = mathAt(blade, spec.sign, 0, 0, 19), mono = mathAt(blade, spec.mono, 0, 0, 19);
    const nw = Number(node.getAttribute('width')), sw = Number(sign.getAttribute('width')), mw = Number(mono.getAttribute('width')), width = nw + sw + mw + 10;
    const start = spec.tx - width / 2;
    return { ...spec,node,sign,mono, origin:point(spec.p,spec.q), target:{x:start+sw+5+nw/2,y:spec.ty}, signX:start+sw/2, monoX:start+sw+nw+10+mw/2, write:ink(node), signWrite:ink(sign), monoWrite:ink(mono) };
  });
  const adjacent = [[5,6],[6,5],[5,5],[0,5],[1,6],[5,0],[6,1],[-1,5],[5,-1]];
  const dots = adjacent.map(([p,q]) => { const node = svg('circle',{r:2.2}); bladeMarks.append(node); return {node,origin:point(p,q)}; });
  function ellipsis(origin, direction) {
    const group = svg('g'); bladeMarks.append(group);
    const nodes = [-1,0,1].map(i => {const node = svg('circle',{r:1.3});group.append(node);return {node,origin:{x:origin.x+direction.x*i*5,y:origin.y+direction.y*i*5}};});
    return nodes;
  }
  const ellipsisDots = [...ellipsis({x:407,y:157},{x:-.707,y:.707}),...ellipsis({x:459,y:157},{x:.707,y:.707}),...ellipsis({x:433,y:187},{x:0,y:1})];
  const equationEllipses = [
    {origin:point(5,6),x:363,y:180}, {origin:point(6,5),x:363,y:320}, {origin:point(5,5),x:457,y:250},
    {origin:point(1,6),x:537,y:156}, {origin:point(6,1),x:537,y:344}
  ].map(spec => ({...spec,node:mathAt(blade,'+\\cdots',0,0,21)}));
  const prefix = mathAt(panel,'E_{\\mathrm{st}}(Y)=',72,250,22);
  const negativeTermsBox = svg('rect',{x:584,y:76,width:265,height:348,fill:'none',stroke:'#000','stroke-width':1.2}); panel.append(negativeTermsBox);
  const negativeLabel = mathAt(panel,'\\text{negative degree terms}',716.5,250,20);
  const tailTop = mathAt(panel,'+\\cdots',818,155,19), tailBottom = mathAt(panel,'+\\cdots',818,345,19);
  const extras = [prefix,negativeTermsBox,negativeLabel,tailTop,tailBottom];
  const headingPens = headings.map(ink), timeline = motion();
  let current=-1,revision=0,disposed=false;
  const focus = step => step <=3 ? 0 : step <=6 ? -70 : step===7 ? -30 : -100;
  const moveFocus = y => {diagrams.setAttribute('transform','translate(0,'+y+')');[...omitted.children].forEach((dot,i)=>dot.setAttribute('cy',430-y+(i-1)*9));};
  function rotate(p, angle) { const c=Math.cos(angle),s=Math.sin(angle),x=p.x-center.x,y=p.y-center.y; return {x:center.x+x*c-y*s,y:center.y+x*s+y*c}; }
  const blend = (a,b,t) => ({x:a.x+(b.x-a.x)*t,y:a.y+(b.y-a.y)*t});
  function gap(a,b,first=0,last=0) { const d=Math.hypot(b.x-a.x,b.y-a.y),dx=(b.x-a.x)/d,dy=(b.y-a.y)/d;return 'M'+(a.x+dx*first)+','+(a.y+dy*first)+'L'+(b.x-dx*last)+','+(b.y-dy*last); }
  function renderBlade(angle=0, spread=0) {
    bladeBorder.style.opacity=String(1-clamp(Math.abs(angle)/(Math.PI/2)));
    const tip = blend(rotate(point(6,6),angle),terms[0].target,spread);
    const upper = blend(rotate(point(0,6),angle),terms[1].target,spread);
    const lower = blend(rotate(point(6,0),angle),terms[2].target,spread);
    const endA = blend(rotate({x:589,y:520},angle),{x:864,y:110},spread);
    const endB = blend(rotate({x:277,y:520},angle),{x:864,y:390},spread);
    bladeFill.setAttribute('points',[tip,upper,endA,endB,lower].map(p=>p.x+','+p.y).join(' '));
    const edgeA=blend(rotate({x:589,y:520},angle),{x:584,y:110},spread),edgeB=blend(rotate({x:277,y:520},angle),{x:584,y:390},spread);
    bladeBorder.setAttribute('d',gap(tip,upper,24+30*spread,24+35*spread)+gap(tip,lower,24+30*spread,24+35*spread)+gap(upper,edgeA,24+65*spread,0)+gap(lower,edgeB,24+65*spread,0));
    dots.forEach(({node,origin})=>{const p=rotate(origin,angle);node.setAttribute('cx',p.x);node.setAttribute('cy',p.y);node.style.opacity=String(1-spread);});
    ellipsisDots.forEach(({node,origin})=>{const p=rotate(origin,angle);node.setAttribute('cx',p.x);node.setAttribute('cy',p.y);node.style.opacity=String(1-spread);});
    const reveal=clamp((spread-.3)/.7);
    terms.forEach((term,i)=>{
      const position=blend(rotate(term.origin,angle),term.target,spread);place(term.node,position.x,position.y);
      term.node.style.opacity='1';term.write(i<3?1:reveal);
      place(term.sign,position.x+term.signX-term.target.x,position.y);place(term.mono,position.x+term.monoX-term.target.x,position.y);
      term.signWrite(reveal);term.monoWrite(reveal);
    });
    equationEllipses.forEach(item=>{const p=blend(rotate(item.origin,angle),{x:item.x,y:item.y},spread);place(item.node,p.x,p.y);item.node.style.opacity=String(reveal);});
  }
  function state(step) {
    show(panel,step>=1);headings.forEach((node,i)=>show(node,i===(step<=2?0:step<=6?1:step<=8?2:3)));
    show(diagrams,step>=1&&step<=8); moveFocus(focus(step));
    zero.set({...common,n:6,color:step===1?red:black,vertices:step===1,detail:'full',label:step===1?'h_c^{p,q}(D_{\\varnothing}^{\\circ})':''});
    show(one.group,step>=3&&step<=8);one.set({...common,y:step===3?base:base+4*unit,color:step<=5?red:grey,vertices:step===3,detail:'short',label:step===3?'h_c^{p,q}(D_i^{\\circ})':''});
    show(duplicate.group,step>=5&&step<=8);duplicate.set({y:base+6*unit,color:step===5?red:grey});
    show(two.group,step>=7&&step<=8);two.set({...common,y:step===8?base+4*unit:base,label:'h_c^{p,q}(D_{ij}^{\\circ})'});
    show(rightZero,step===1);show(rightOne,step>=3&&step<=6);show(rightTwo,step===7||step===8);
    show(f1,step>=3&&step<=6);show(f2,step===7||step===8);
    show(positiveBox,step===4||step===5);show(minusBox,step===5);show(tailBox,step===6);show(productBox,step===8);
    extras.forEach(node=>show(node,step===10));
    show(shift.group,step>=4&&step<=6);shift.set(148,252);show(shiftI.group,step===8);show(shiftJ.group,step===8);shiftI.set(200,252);shiftJ.set(252,304);
    show(omitted,step>=6&&step<=8);omitted.style.color=step===6?red:black;
    show(blade,step>=9);renderBlade(step===10?-Math.PI/2:0,step===10?1:0);
    [zero,one,duplicate,two].forEach(item=>{ink(item.group)(1);item.group.children[2].style.opacity='1';});
    headings.forEach(node=>ink(node)(1));[shift,shiftI,shiftJ].forEach(item=>item.write(1));terms.forEach((item,i)=>{item.write(step===10||i<3?1:0);item.signWrite(step===10?1:0);item.monoWrite(step===10?1:0);});
  }
  const fade = async(run,nodes,incoming=false)=>run(.28,a=>nodes.forEach(node=>{node.style.opacity=String(incoming?ease(a):1-ease(a));}));
  async function rename(run,from,to){show(headings[to],true);if(!await run(.65,a=>{headingPens[from](1-a*2);headingPens[to](clamp((a-.3)/.7));}))return false;show(headings[from],false);return true;}
  async function unlabel(diamond,n,from,to,run){
    const labels=ink(diamond.group.children[4]),centerInk=ink(diamond.group.children[5]);
    const corners=[[0,-2*n*unit],[n*unit,-n*unit],[0,0],[-n*unit,-n*unit]];
    return run(.85,a=>{
      const t=ease(a);diamond.set({color:mix(from,to,t),vertices:a<.45,label:a<.45?(n===6?'h_c^{p,q}(D_{\\varnothing}^{\\circ})':'h_c^{p,q}(D_i^{\\circ})'):''});labels(clamp(1-a*2.2));centerInk(clamp(1-a*2.2));diamond.group.children[2].style.opacity=String(clamp((a-.4)/.6));
      const inset=23*(1-t);diamond.group.children[1].setAttribute('d',corners.map((p,i)=>gap({x:p[0],y:p[1]},{x:corners[(i+1)%4][0],y:corners[(i+1)%4][1]},inset,inset)).join(''));
    });
  }
  async function animate(previous,next,run){
    state(previous);
    if(next===1){state(next);rightZero.style.opacity='0';if(!await run(.9,ink(zero.group)))return;await fade(run,[rightZero],true);}
    else if(next===2){if(!await fade(run,[rightZero]))return;show(rightZero,false);if(!await unlabel(zero,6,red,black,run))return;state(next);}
    else if(next===3){if(!await rename(run,0,1))return;state(next);rightOne.style.opacity='0';f1.style.opacity='0';if(!await run(1,ink(one.group)))return;await fade(run,[rightOne,f1],true);}
    else if(next===4){
      if(!await unlabel(one,5,red,red,run))return;show(shift.group,true);show(positiveBox,true);
      if(!await run(1.1,a=>{const t=ease(a);one.set({y:base+4*unit*t});shift.set(148,148+4*unit*t);shift.write(a);positiveBox.style.opacity=String(t);moveFocus(-70*t);} ))return;state(next);
    }else if(next===5){
      show(positiveBox,true);show(duplicate.group,true);show(minusBox,true);duplicate.set({y:base+4*unit,color:red});
      if(!await run(.9,a=>duplicate.set({y:base+4*unit+2*unit*ease(a)})))return;
      state(next);
    }else if(next===6){
      if(!await run(.65,a=>{one.set({color:mix(red,grey,ease(a))});duplicate.set({color:mix(red,grey,ease(a))});minusBox.style.opacity=String(1-ease(a));positiveBox.style.opacity=String(1-ease(a));}))return;state(next);omitted.style.opacity='0';tailBox.style.opacity='0';await fade(run,[omitted,tailBox],true);
    }else if(next===7){
      if(!await fade(run,[rightOne,f1,tailBox,shift.group]))return;if(!await rename(run,1,2))return;
      if(!await run(.65,a=>moveFocus(-70+40*ease(a))))return;state(next);rightTwo.style.opacity='0';f2.style.opacity='0';if(!await run(.9,ink(two.group)))return;await fade(run,[rightTwo,f2],true);
    }else if(next===8){
      show(shiftI.group,true);if(!await run(.8,a=>{const t=ease(a);two.set({y:base+2*unit*t});shiftI.set(200,200+2*unit*t);shiftI.write(a);moveFocus(-30-35*t);} ))return;
      show(shiftJ.group,true);show(productBox,true);if(!await run(.8,a=>{const t=ease(a);two.set({y:base+2*unit+2*unit*t});shiftJ.set(252,252+2*unit*t);shiftJ.write(a);productBox.style.opacity=String(t);moveFocus(-65-35*t);} ))return;state(next);
    }else if(next===9){
      if(!await fade(run,[rightTwo,f2,productBox,shiftI.group,shiftJ.group]))return;if(!await rename(run,2,3))return;
      if(!await run(1,a=>{const t=ease(a);two.set({color:mix(red,grey,t),label:''});diagrams.setAttribute('transform','translate('+(433-left)*t+','+(-100*(1-t))+')');}))return;
      show(blade,true);renderBlade();blade.style.opacity='0';if(!await run(.5,a=>{diagrams.style.opacity=String(1-a);blade.style.opacity=String(a);}))return;state(next);
    }else if(next===10){
      extras.forEach(node=>show(node,false));show(prefix,true);
      if(!await run(1.2,a=>renderBlade(-Math.PI/2*ease(a),0)))return;
      if(!await run(1.35,a=>renderBlade(-Math.PI/2,ease(a))))return;
      [negativeTermsBox,negativeLabel,tailTop,tailBottom].forEach(node=>{show(node,true);node.style.opacity='0';});
      if(!await fade(run,[negativeTermsBox,negativeLabel,tailTop,tailBottom],true))return;state(next);
    }else state(next);
  }
  return {animated:true,async play(next=0){if(disposed)return;const previous=current,token=++revision;timeline.cancel();current=next;slide.dataset.step=String(next);const run=async(seconds,update)=>await timeline.run(seconds,update)&&!disposed&&token===revision;if(next===previous+1&&previous>=0)await animate(previous,next,run);else state(next);},dispose(){disposed=true;revision++;timeline.dispose();body.remove();}};
}
