import { svg, math } from './slide-utils.js';

const clamp=value=>Math.max(0,Math.min(1,value));
const ease=value=>{const t=clamp(value);return t*t*(3-2*t);};
const mix=(a,b,t)=>a+(b-a)*t;
const red='#b8202f';
let serial=0;

function clip(polygon,a,b,c) {
  const result=[];
  polygon.forEach((point,i)=>{
    const previous=polygon[(i+polygon.length-1)%polygon.length],v=a*point[0]+b*point[1]-c,u=a*previous[0]+b*previous[1]-c;
    if((v<=0)!==(u<=0)){const t=u/(u-v);result.push([previous[0]+(point[0]-previous[0])*t,previous[1]+(point[1]-previous[1])*t]);}
    if(v<=0)result.push(point);
  });
  return result;
}

function rounded(points,radius=4) {
  return points.map((point,i)=>{
    const previous=points[(i+points.length-1)%points.length],next=points[(i+1)%points.length];
    const a=Math.hypot(point[0]-previous[0],point[1]-previous[1]),b=Math.hypot(point[0]-next[0],point[1]-next[1]),r=Math.min(radius,a/3,b/3);
    const before=point.map((v,j)=>v+(previous[j]-v)*r/a),after=point.map((v,j)=>v+(next[j]-v)*r/b);
    return(i?'L':'M')+before.join(',')+'Q'+point.join(',')+' '+after.join(',');
  }).join('')+'Z';
}

export function createNonpolynomialDiagram(parent) {
  const id='nonpoly-'+(++serial)+'-';
  const node=svg('svg',{width:866,height:417,viewBox:'0 0 866 417'});
  node.style.cssText='position:absolute;left:0;top:-60px;overflow:hidden;pointer-events:none';parent.append(node);
  const defs=svg('defs');
  const makeMask=(name,coordinates)=>{
    const gradient=svg('linearGradient',{id:name+'-fade',gradientUnits:'userSpaceOnUse',...coordinates});
    gradient.append(svg('stop',{offset:0,'stop-color':'#fff','stop-opacity':0}),svg('stop',{offset:1,'stop-color':'#fff','stop-opacity':1}));
    const mask=svg('mask',{id:name,maskUnits:'userSpaceOnUse',x:0,y:0,width:866,height:417});mask.append(svg('rect',{x:0,y:0,width:866,height:417,fill:'url(#'+name+'-fade)'}));defs.append(gradient,mask);return name;
  };
  const topMask=makeMask(id+'top',{x1:0,y1:0,x2:0,y2:18});
  const geometry=svg('g',{mask:'url(#'+topMask+')'});node.append(defs,geometry);
  const regionGradients=[];let regionParent=geometry;
  for(const axis of ['p','q']){
    const name=id+'region-'+axis,gradient=svg('linearGradient',{id:name+'-fade',gradientUnits:'userSpaceOnUse'});
    gradient.append(svg('stop',{offset:0,'stop-color':'#fff','stop-opacity':1}),svg('stop',{offset:1,'stop-color':'#fff','stop-opacity':0}));
    const mask=svg('mask',{id:name,maskUnits:'userSpaceOnUse',x:0,y:0,width:866,height:417});mask.append(svg('rect',{x:0,y:0,width:866,height:417,fill:'url(#'+name+'-fade)'}));defs.append(gradient,mask);regionGradients.push(gradient);
    const group=svg('g',{mask:'url(#'+name+')'});regionParent.append(group);regionParent=group;
  }
  const counterMask=svg('mask',{id:id+'counter-mask',maskUnits:'userSpaceOnUse',x:0,y:0,width:866,height:417});
  const counterBase=svg('path',{fill:'#fff'}),counterCuts=Array.from({length:3},()=>svg('path',{fill:'#000'})),counterDisks=Array.from({length:3},()=>svg('circle',{r:8.8,fill:'#000'}));
  counterMask.append(counterBase,...counterCuts,...counterDisks);defs.append(counterMask);
  const counterArea=svg('path',{fill:red,opacity:0,mask:'url(#'+id+'counter-mask)'});regionParent.append(counterArea);
  const regions=Array.from({length:3},()=>svg('path',{fill:'#d8d8d8',stroke:'#202020','stroke-width':1.4,'stroke-linejoin':'round'}));regionParent.append(...regions);
  const finiteBand=svg('path',{fill:'#d8d8d8',stroke:'#202020','stroke-width':1.4,'fill-rule':'evenodd',opacity:0});regionParent.append(finiteBand);
  const grid=svg('g',{stroke:'#d0d0d0','stroke-width':.7}),dots=svg('g',{fill:'#202020'}),omissions=svg('g',{color:'#888'}),specials=svg('g');geometry.append(grid,dots,omissions,specials);
  const gridLines=[];
  for(const [pCorner,qCorner] of [[0,0],[0,1],[1,0],[1,1]])for(let k=0;k<3;k++){
    for(const direction of [0,1]){
      const name=id+'grid-'+gridLines.length,lead=(direction?pCorner:qCorner)*.85,length=2.85+lead;
      const gradient=svg('linearGradient',{id:name,gradientUnits:'userSpaceOnUse'});
      const stops=lead?[[0,0],[lead/length,1],[(lead+2)/length,1],[1,0]]:[[0,1],[2/length,1],[1,0]];
      gradient.append(...stops.map(([offset,opacity])=>svg('stop',{offset,'stop-color':'#d0d0d0','stop-opacity':opacity})));defs.append(gradient);
      const line=svg('line',{stroke:'url(#'+name+')'});grid.append(line);gridLines.push({line,gradient,stops,pCorner,qCorner,k,direction,coordinates:n=>{
        const p=pCorner*n,q=qCorner*n;
        return direction?[pCorner?p-.85:0,q+k,p+2.85,q+k]:[p+k,qCorner?q-.85:0,p+k,q+2.85];
      }});
    }
  }
  const lattice=[];
  const addPoint=coordinates=>{const circle=svg('circle',{r:2.1});dots.append(circle);lattice.push({coordinates,circle});};
  for(let p=0;p<3;p++)for(let q=0;q<3;q++)addPoint(()=>[p,q]);
  for(let p=0;p<3;p++)for(let q=0;q<3;q++){
    addPoint(n=>[p,n+q]);addPoint(n=>[n+p,q]);addPoint(n=>[n+p,n+q]);
  }
  const omitted=[];
  const addOmission=(coordinates,angle)=>{
    const group=svg('g'),label=math('\\dots',18);label.setAttribute('x',-Number(label.getAttribute('width'))/2);label.setAttribute('y',-Number(label.getAttribute('height'))/2);group.append(label);omissions.append(group);omitted.push({coordinates,angle,group});
  };
  for(let k=0;k<3;k++){
    addOmission(n=>[k,n*.56],45);addOmission(n=>[n*.56,k],-45);
    addOmission(n=>[k,n+3.6],45);addOmission(n=>[n+3.6,k],-45);
    addOmission(n=>[n*.6,n+k],-45);addOmission(n=>[n+k,n*.6],45);
    addOmission(n=>[n+k,n+3.6],45);addOmission(n=>[n+3.6,n+k],-45);
  }
  const marks=Array.from({length:3},()=>{
    const group=svg('g'),ring=svg('circle',{r:8,fill:'#d8d8d8',stroke:'#202020','stroke-width':1.4}),dot=svg('circle',{r:2.1,fill:'#202020'});group.append(ring,dot);specials.append(group);return {group,ring,dot};
  });
  const extra=svg('g'),extraRing=svg('circle',{r:8,fill:'#d8d8d8',stroke:'#202020','stroke-width':1.4}),extraDot=svg('circle',{r:2.1,fill:'#202020'});extra.append(extraRing,extraDot);specials.append(extra);
  const counterLabel=math('\\text{counterexamples}',23.8);counterLabel.style.color=red;geometry.append(counterLabel);
  const config={x:433,bottom:404,n:8,unit:17,edge:0,point:0,side:0,pair:0,pointRed:0,counterexamples:0,finite:0};
  function set(values={}) {
    Object.assign(config,values);
    const {x,n,edge,point:pointAmount,side,pair,pointRed,counterexamples}=config,f=clamp(config.finite),bottom=mix(config.bottom,384,f),unit=mix(config.unit,32,f),coordinate=(a,b)=>mix(a*config.unit,b*32,f)/unit,corner=coordinate(n,3);
    const position=(p,q)=>[x+(p-q)*unit,bottom-(p+q)*unit];
    for(const ring of [...marks.map(mark=>mark.ring),extraRing])ring.setAttribute('r',mix(8,10,f));
    regionGradients.forEach((gradient,i)=>{const start=i?position(0,coordinate(n+3.1,7)):position(coordinate(n+3.1,7),0),end=i?position(0,coordinate(n+5.4,9)):position(coordinate(n+5.4,9),0);gradient.setAttribute('x1',start[0]);gradient.setAttribute('y1',start[1]);gradient.setAttribute('x2',end[0]);gradient.setAttribute('y2',end[1]);});
    const path=polygon=>rounded(polygon.map(([p,q])=>position(p,q)));
    const low=-.24,upper=coordinate(n+5.8,5.24),depth=1.38;
    const lowerBand=[[low,low],[upper,low],[upper,depth],[depth,depth],[depth,upper],[low,upper]];
    const domain=[[low,low],[upper,low],[upper,upper],[low,upper]];
    const shapes=[path(lowerBand),path(clip(domain,1-f,-1,coordinate(-n+1.38,-3.62))),path(clip(domain,-1,1-f,coordinate(-n+1.38,-3.62)))];
    const bandFade=ease(clamp((f-.65)/.35));
    [edge,side,side].forEach((amount,i)=>{const alpha=ease(amount),region=regions[i];region.setAttribute('d',shapes[i]);region.style.opacity=String(alpha*(1-bandFade));counterCuts[i].setAttribute('d',shapes[i]);counterCuts[i].style.opacity=String(alpha);});
    finiteBand.setAttribute('d',path(domain)+path([[depth,depth],[depth,3.62],[3.62,3.62],[3.62,depth]]));finiteBand.style.opacity=String(bandFade);
    counterBase.setAttribute('d',path(domain));counterArea.setAttribute('d',path(domain));counterArea.style.opacity=String(.18*counterexamples*(1-f));
    gridLines.forEach(({coordinates,line,gradient,stops,pCorner,qCorner,k,direction})=>{
      const original=coordinates(n),target=direction?[pCorner?2.5:0,qCorner*3+k,pCorner?5:2.5,qCorner*3+k]:[pCorner*3+k,qCorner?2.5:0,pCorner*3+k,qCorner?5:2.5];
      const [p0,q0,p1,q1]=original.map((v,i)=>coordinate(v,target[i])),start=position(p0,q0),end=position(p1,q1);
      for(const item of [line,gradient]){item.setAttribute('x1',start[0]);item.setAttribute('y1',start[1]);item.setAttribute('x2',end[0]);item.setAttribute('y2',end[1]);}
      [...gradient.children].forEach((stop,i)=>stop.setAttribute('stop-opacity',mix(stops[i][1],1,f)));
    });
    lattice.forEach(({coordinates,circle})=>{const location=position(...coordinates(corner));circle.setAttribute('cx',location[0]);circle.setAttribute('cy',location[1]);});
    omitted.forEach(({coordinates,angle,group})=>{const location=position(...coordinates(corner));group.setAttribute('transform','translate('+location.join(',')+') rotate('+angle+')');group.style.opacity=String(1-ease(f));});
    [[2,2,pointAmount],[2,corner,pair],[corner,2,pair]].forEach(([p,q,amount],i)=>{
      const location=position(p,q),t=i?f:pointRed;
      marks[i].group.style.opacity=String(ease(amount));
      for(const item of [marks[i].ring,marks[i].dot,counterDisks[i]]){item.setAttribute('cx',location[0]);item.setAttribute('cy',location[1]);}
      const ink='rgb('+[32,32,32].map((v,j)=>Math.round(mix(v,[184,32,47][j],t))).join(',')+')',shade='rgb('+[216,216,216].map((v,j)=>Math.round(mix(v,[245,208,212][j],t))).join(',')+')';
      marks[i].ring.setAttribute('stroke',ink);marks[i].ring.setAttribute('fill',shade);marks[i].dot.setAttribute('fill',ink);counterDisks[i].style.opacity=String(ease(amount));
    });
    const topPoint=position(corner,corner);extra.style.opacity=String(ease(f));for(const item of [extraRing,extraDot]){item.setAttribute('cx',topPoint[0]);item.setAttribute('cy',topPoint[1]);}
    counterLabel.setAttribute('x',x-Number(counterLabel.getAttribute('width'))/2);counterLabel.setAttribute('y',215-Number(counterLabel.getAttribute('height'))/2);counterLabel.style.opacity=String(counterexamples*(1-ease(f)));

  }
  set();return {node,set,dispose(){node.remove();}};
}
