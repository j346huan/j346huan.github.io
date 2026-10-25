import { svg, math } from './slide-utils.js';

const black = '#202020', blue = '#3333b3', red = '#b8202f';
const clamp = value => Math.max(0, Math.min(1, value));
const ease = value => { const t = clamp(value); return t * t * (3 - 2 * t); };
const mix = (from, to, t) => '#' + [1,3,5].map(i => Math.round(parseInt(from.slice(i,i+2),16)*(1-t)+parseInt(to.slice(i,i+2),16)*t).toString(16).padStart(2,'0')).join('');

function diamond(x, y, radius) {
  const corners = [[x,y-radius],[x+radius,y],[x,y+radius],[x-radius,y]], inset = Math.min(10,radius*.2);
  return corners.map((point,i) => {
    const previous = corners[(i+3)%4], next = corners[(i+1)%4], length = Math.hypot(point[0]-previous[0],point[1]-previous[1]);
    const before = [point[0]+(previous[0]-point[0])*inset/length,point[1]+(previous[1]-point[1])*inset/length];
    const after = [point[0]+(next[0]-point[0])*inset/length,point[1]+(next[1]-point[1])*inset/length];
    return (i?'L':'M')+before.join(',')+'Q'+point.join(',')+' '+after.join(',');
  }).join('')+'Z';
}

export function createPolynomialDiagram(parent) {
  const node = svg('svg',{width:866,height:300,viewBox:'0 0 866 300'});
  node.style.cssText='position:absolute;left:0;top:0;overflow:visible;pointer-events:none';parent.append(node);
  const shade = svg('path',{'fill-rule':'evenodd',stroke:'none'});
  const counter = svg('path',{fill:'#f5d0d4',opacity:0});
  const outlines = svg('path',{fill:'none',stroke:'#000','stroke-width':1.4});
  const defs = svg('defs'), grid = svg('g',{'stroke-width':.7}), localGrid = svg('g'), fullGrid = svg('g',{stroke:'#d0d0d0'});
  const dots = svg('g'), omissions = svg('g'), highlights = svg('g');
  grid.append(localGrid,fullGrid);node.append(defs,shade,counter,grid,outlines,dots,omissions,highlights);
  const gridLines = [];
  function addGrid(coordinates) {
    const id='polynomial-grid-'+gridLines.length;
    const gradient=svg('linearGradient',{id,gradientUnits:'userSpaceOnUse'});
    const stops=Array.from({length:4},()=>svg('stop',{'stop-color':'#d0d0d0'}));gradient.append(...stops);defs.append(gradient);
    const line=svg('line',{stroke:'url(#'+id+')'});localGrid.append(line);gridLines.push({line,gradient,stops,coordinates});
  }
  for(let k=0;k<3;k++)for(const upper of [false,true])for(const swap of [false,true]) {
    addGrid(n=>{
      const extension=Math.min(.85,Math.max(0,n-2)),fixed=upper?n-k:k;
      const a=upper?n-2-extension:0,b=upper?n:2+extension;
      return {a:swap?[a,fixed]:[fixed,a],b:swap?[b,fixed]:[fixed,b],start:upper?extension:0,end:upper?0:extension};
    });
  }
  for(const side of [false,true])for(const swap of [false,true])addGrid(n=>{
    const a=side?[n,0]:[0,n],b=side?(swap?[n,.85]:[n-.85,0]):(swap?[.85,n]:[0,n-.85]);
    return {a,b,start:0,end:.85};
  });
  const fullLines=[];
  for(let k=0;k<5;k++)for(const swap of [false,true]) {
    const line=svg('line');fullGrid.append(line);fullLines.push({line,k,swap});
  }
  const label = math('h_{\\mathrm{st}}^{p,q}(Y)',24);node.append(label);
  const points = [];
  const add = (coordinates,extra=false,merge=false) => {
    const circle=svg('circle',{r:2.1});dots.append(circle);points.push({circle,coordinates,extra,merge});
  };
  for(let p=0;p<3;p++)for(let q=0;q<3;q++)add(()=>[p,q]);
  for(let p=0;p<3;p++)for(let q=0;q<3;q++)add(n=>[n-p,n-q],false,p===2&&q===2);
  add(n=>[0,n]);add(n=>[n,0]);
  [n=>[0,n-1],n=>[1,n-1],n=>[1,n],n=>[n-1,0],n=>[n-1,1],n=>[n,1]].forEach(coordinates=>add(coordinates,true));
  const omissionDots = [];
  for(let k=0;k<3;k++)for(const [coordinates,angle] of [[n=>[k,n/2],-45],[n=>[n/2,k],45],[n=>[n-k,n/2],-45],[n=>[n/2,n-k],45]]) {
    const group=svg('g'),glyph=math('\\dots',18);
    glyph.setAttribute('x',-Number(glyph.getAttribute('width'))/2);glyph.setAttribute('y',-Number(glyph.getAttribute('height'))/2);
    group.append(glyph);omissions.append(group);omissionDots.push({group,coordinates,angle});
  }
  const rings = [svg('circle',{r:8,fill:'none',stroke:red,'stroke-width':1.4}),svg('circle',{r:8,fill:'none',stroke:red,'stroke-width':1.4})];
  highlights.append(...rings);
  const counterCenters=Array.from({length:2},()=>svg('circle',{r:2.1,fill:black,opacity:0}));highlights.append(...counterCenters);
  const counterPoints=Array.from({length:6},()=>svg('circle',{r:2.1,fill:red,opacity:0}));
  dots.append(...counterPoints);
  const config={x:433,y:122,n:8,unit:18,band:1,bandAlpha:1,special:0,complete:0,neutral:0,counterexamples:0};
  function set(values={}) {
    Object.assign(config,values);
    const {x,y,n,unit,band,bandAlpha,special,complete,neutral,counterexamples}=config;
    const point=(p,q)=>({x:x+(q-p)*unit,y:y+(n-p-q)*unit});
    const placeLine=(line,a,b)=>{
      const first=point(...a),last=point(...b);
      line.setAttribute('x1',first.x);line.setAttribute('y1',first.y);line.setAttribute('x2',last.x);line.setAttribute('y2',last.y);
      return {first,last};
    };
    gridLines.forEach(({line,gradient,stops,coordinates})=>{
      const {a,b,start,end}=coordinates(n),{first,last}=placeLine(line,a,b),length=Math.hypot(b[0]-a[0],b[1]-a[1]);
      gradient.setAttribute('x1',first.x);gradient.setAttribute('y1',first.y);gradient.setAttribute('x2',last.x);gradient.setAttribute('y2',last.y);
      const offsets=[0,clamp(start/length),clamp(1-end/length),1],alphas=[start?0:1,1,1,end?0:1];
      stops.forEach((stop,i)=>{stop.setAttribute('offset',offsets[i]);stop.setAttribute('stop-opacity',alphas[i]);});
    });
    fullLines.forEach(({line,k,swap})=>placeLine(line,swap?[0,k*n/4]:[k*n/4,0],swap?[n,k*n/4]:[k*n/4,n]));
    const full=ease((complete-.6)/.4);localGrid.style.opacity=String(1-full);fullGrid.style.opacity=String(full);
    const outer=diamond(x,y,n*unit+8),inner=diamond(x,y,Math.max(4,(n-2*band+1)*unit));
    counter.setAttribute('d',inner);counter.style.opacity=String(counterexamples);
    shade.setAttribute('d',outer+inner);shade.setAttribute('fill',mix(mix('#eeeeee','#dce9f8',ease(band-1)),'#e5e5e5',neutral));
    outlines.setAttribute('d',outer+inner);
    shade.style.opacity=outlines.style.opacity=String(ease(bandAlpha));
    const separation=2*Math.abs(n-4)*unit,merge=ease((5-separation)/5),ringMerge=ease((16-separation)/16);
    const specialAmount=ease(special),expanded=ease(band-1);
    points.forEach(({circle,coordinates,extra,merge:merging})=>{
      const [p,q]=coordinates(n),location=point(p,q),depth=Math.min(p,q,n-p,n-q);
      const selected=1-ease(depth-(band-1));
      let color=mix(black,blue,selected*expanded*(1-neutral));
      const isSpecial=(Math.abs(p-2)<.0001&&Math.abs(q-2)<.0001)||(Math.abs(p-(n-2))<.0001&&Math.abs(q-(n-2))<.0001);
      if(isSpecial)color=mix(color,red,specialAmount*(1-neutral));
      circle.setAttribute('cx',location.x);circle.setAttribute('cy',location.y);circle.setAttribute('fill',color);
      circle.style.opacity=String((extra?ease(complete):1)*(merging?1-merge:1));
    });
    omissionDots.forEach(({group,coordinates,angle})=>{
      const [p,q]=coordinates(n),location=point(p,q),depth=Math.min(p,q,n-p,n-q);
      const selected=1-ease(depth-(band-1));
      group.setAttribute('transform','translate('+location.x+','+location.y+') rotate('+angle+')');
      group.style.color=mix(mix('#777777',blue,selected*expanded*(1-neutral)),red,depth>=2?counterexamples:0);
    });
    omissions.style.opacity=String(1-ease(complete));
    [[2,2],[n-2,n-2]].forEach(([p,q],i)=>{const location=point(p,q);rings[i].setAttribute('cx',location.x);rings[i].setAttribute('cy',location.y);rings[i].setAttribute('stroke',mix(red,black,neutral));rings[i].setAttribute('fill',counterexamples?'#e5e5e5':'none');counterCenters[i].setAttribute('cx',location.x);counterCenters[i].setAttribute('cy',location.y);counterCenters[i].style.opacity=String(counterexamples);rings[i].style.opacity=String(specialAmount*(i?1-ringMerge:1));});
    label.setAttribute('x',x-Number(label.getAttribute('width'))/2);label.setAttribute('y',y-Number(label.getAttribute('height'))/2);
    label.style.opacity=String((1-ease(complete*2.5))*(1-counterexamples));
    [[2,3],[3,2],[n-2,n-3],[n-3,n-2],[2,n-2],[n-2,2]].forEach(([p,q],i)=>{const location=point(p,q);counterPoints[i].setAttribute('cx',location.x);counterPoints[i].setAttribute('cy',location.y);counterPoints[i].style.opacity=String(counterexamples);});
  }
  set();return {node,set,dispose(){node.remove();}};
}
