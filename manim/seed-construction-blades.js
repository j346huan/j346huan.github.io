import { svg, math } from './slide-utils.js';

let serial=0;
const red='#b8202f', clamp=x=>Math.max(0,Math.min(1,x)), mix=(a,b,t)=>a+(b-a)*t;
const ease=x=>{const t=clamp(x);return t*t*(3-2*t);};
const key=(p,q)=>p+','+q;
const u=new Map([['2,2',12],['3,3',1],['4,4',1],['2,1',-1],['1,2',-1]]);
const d=new Map([['0,0',1],['1,1',2],['2,2',2],['3,3',1],['2,1',1],['1,2',1]]);
const final=new Map([['0,0',1],['1,1',2],['2,2',14],['3,3',14],['4,4',2],['5,5',1],['2,3',-1],['3,2',-1]]);
const coefficient=(p,q)=>p===q?({0:1,1:1,2:13,3:1,4:1}[p]||0):Math.abs(p-q)===1&&Math.max(p,q)<=2?(-1)**(3-Math.max(p,q)):0;
const inBlade=(p,q)=>p<=4&&q<=4&&Math.abs(p-q)<=4&&p+q>=-4;
const path=points=>'M'+points.map(point=>point.join(',')).join('L')+'Z';

function label(parent,value,size=22) {
  const group=svg('g'),node=math(String(value),size);
  node.setAttribute('x',-Number(node.getAttribute('width'))/2);
  node.setAttribute('y',-Number(node.getAttribute('height'))/2);
  group.style.color=value<0?red:'#171717';group.append(node);parent.append(group);
  return group;
}

function segment(line,a,b,gap,endGap=gap) {
  const length=Math.hypot(b[0]-a[0],b[1]-a[1]),t=Math.min(.45,gap/length),u=Math.min(.45,endGap/length);
  line.setAttribute('x1',mix(a[0],b[0],t));line.setAttribute('y1',mix(a[1],b[1],t));
  line.setAttribute('x2',mix(b[0],a[0],u));line.setAttribute('y2',mix(b[1],a[1],u));
}

function diamond(parent,n,values,sign=1) {
  const group=svg('g'),shade=svg('path',{fill:'#000',opacity:.075}),grid=svg('g',{stroke:'#c6c6c6','stroke-width':.75}),points=svg('g');
  group.append(shade,grid,points);parent.append(group);
  const entries=[],lines=[];
  for(let p=0;p<=n;p++)for(let q=0;q<=n;q++){
    const value=sign*(values.get(key(p,q))||0),item=svg('g'),number=label(item,value),dot=svg('circle',{r:2.2,fill:value<0?red:'#202020'});item.append(dot);points.append(item);entries.push({p,q,item,number,dot});
    for(const [a,b] of [[p+1,q],[p,q+1]])if(a<=n&&b<=n){const line=svg('line');grid.append(line);lines.push({p,q,a,b,line});}
  }
  function set(cx,top,unit,dots=0,alpha=1){
    group.style.opacity=String(alpha);
    const pos=(p,q)=>[cx+(p-q)*unit,top+(2*n-p-q)*unit];
    shade.setAttribute('d',path([[n,n],[n,0],[0,0],[0,n]].map(pair=>pos(...pair))));
    for(const entry of entries){entry.item.setAttribute('transform','translate('+pos(entry.p,entry.q).join(',')+')');entry.number.style.opacity=String(1-dots);entry.dot.style.opacity=String(dots);}
    for(const entry of lines)segment(entry.line,pos(entry.p,entry.q),pos(entry.a,entry.b),mix(12,2.4,dots));
  }
  return {group,set};
}

function blade(parent,dotted=false) {
  const group=svg('g'),shade=svg('g',{fill:'#000',opacity:.075}),grid=svg('g',{stroke:'#c6c6c6','stroke-width':.75}),points=svg('g'),omissions=svg('g',{color:'#888'});
  group.append(shade,grid,points,omissions);parent.append(group);
  const entries=[],lines=[],cells=[],holes=[];
  const oldValue=(p,q)=>inBlade(p,q)?coefficient(p,q):0,newValue=(p,q)=>final.get(key(p,q))||0;
  if(dotted){
    const id='seed-blade-'+(++serial),defs=svg('defs'),mask=svg('mask',{id,maskUnits:'userSpaceOnUse',x:0,y:0,width:866,height:600});
    mask.append(svg('rect',{x:0,y:0,width:866,height:600,fill:'#fff'}));defs.append(mask);group.prepend(defs);
    grid.setAttribute('mask','url(#'+id+')');points.setAttribute('mask','url(#'+id+')');
    for(let p=-4;p<=4;p++)for(let q=-4;q<=4;q++)if(oldValue(p,q)){const hole=svg('rect',{width:26,height:26,fill:'#000'});mask.append(hole);holes.push({p,q,hole});}
  }
  for(let p=-4;p<=5;p++)for(let q=-4;q<=5;q++){
    const old=oldValue(p,q),last=newValue(p,q);
    if(old||last){
      const item=svg('g'),number=old?(dotted?svg('circle',{r:2.2,fill:old<0?red:'#202020'}):label(item,old)):null,sum=!dotted&&last?label(item,last):null;
      if(dotted&&number)item.append(number);points.append(item);entries.push({p,q,item,number,sum});
      for(const [a,b] of [[p+1,q],[p,q+1]]){
        const was=Boolean(old&&oldValue(a,b)),next=Boolean(last&&newValue(a,b));
        if(was||next){const line=svg('line');grid.append(line);lines.push({p,q,a,b,line,was,next});}
      }
    }
    const corners=[[p,q],[p+1,q],[p+1,q+1],[p,q+1]],was=corners.every(pair=>oldValue(...pair)!==0),next=corners.every(pair=>newValue(...pair)!==0);
    if(was||next){const cell=svg('path');shade.append(cell);cells.push({corners,cell,was,next});}
  }
  const omitted=label(omissions,'\\vdots',22);
  function set(cx,top,unit,finite=0,alpha=1,obstacleTop=top,options={}){
    group.style.opacity=String(alpha);
    const sum=options.sum??finite,truncate=options.truncate??finite,anchor=mix(4,5,sum),pos=(p,q)=>[cx+(p-q)*unit,top+(2*anchor-p-q)*unit];
    for(const entry of cells){entry.cell.setAttribute('d',path(entry.corners.map(pair=>pos(...pair))));entry.cell.style.opacity=String(dotted?Number(entry.was):mix(Number(entry.was),Number(entry.next),sum));}
    for(const entry of entries){
      entry.item.setAttribute('transform','translate('+pos(entry.p,entry.q).join(',')+')');
      if(entry.number)entry.number.style.opacity=String(dotted?1:1-sum);
      if(entry.sum)entry.sum.style.opacity=String(sum);
    }
    for(const entry of lines){segment(entry.line,pos(entry.p,entry.q),pos(entry.a,entry.b),dotted?2.4:12);entry.line.style.opacity=String(dotted?Number(entry.was):mix(Number(entry.was),Number(entry.next),sum));}
    omissions.style.opacity=String(dotted?0:1-truncate);
    for(const {p,q,hole} of holes){hole.setAttribute('x',cx+(p-q)*unit-13);hole.setAttribute('y',obstacleTop+(8-p-q)*unit-13);}
    omitted.setAttribute('transform','translate('+cx+','+(top+(2*anchor+3)*unit+34)+')');
  }
  return {group,set};
}

export function createSeedConstructionBlades(parent) {
  const node=svg('svg',{width:866,height:520,viewBox:'0 0 866 520'});
  node.style.cssText='position:absolute;left:0;top:0;overflow:visible;pointer-events:none';parent.append(node);
  const sources=svg('g');node.append(sources);
  const open=diamond(sources,4,u),divisors=[diamond(sources,3,d),diamond(sources,3,d,-1),diamond(sources,3,d)];
  const negatives=svg('g',{fill:red});sources.append(negatives);
  const negativeDots=[...d.entries()].filter(([,value])=>value>0).map(([key])=>{const [p,q]=key.split(',').map(Number),dot=svg('circle',{r:2.2});negatives.append(dot);return {p,q,dot};});
  const omitted=label(sources,'\\vdots',22),formula=label(sources,'\\frac{uv-1}{(uv)^2-1}=(uv)^{-1}-(uv)^{-2}+(uv)^{-3}-\\cdots',21.5);
  const copy=blade(node,true),result=blade(node);
  function set(value=0){
    const step=Math.max(0,Math.min(5,value)),expand=ease(step),merge=ease((step-1)/.62),left=ease(step-2),multiply=ease(step-3);
    const replace=ease((step-1.76)/.24),unit=mix(mix(42,28,expand),33,merge),cx=mix(205,433,merge),top=mix(50,45,merge);
    sources.style.opacity=String(1-replace);
    open.set(mix(220,cx,expand),top,unit);
    for(let i=0;i<3;i++){
      const shift=mix(2*unit,2*(i+2)*unit,expand);
      divisors[i].set(mix(646,mix(655,433,merge),expand),top+shift,unit,expand,i?expand:1);
    }
    negatives.style.opacity=String(expand);
    for(const {p,q,dot} of negativeDots){dot.setAttribute('cx',mix(646,mix(655,433,merge),expand)+(p-q)*unit);dot.setAttribute('cy',top+mix(2*unit,6*unit,expand)+(6-p-q)*unit);}
    omitted.setAttribute('transform','translate('+mix(655,433,merge)+',465)');omitted.style.opacity=String(expand*(1-merge));
    formula.setAttribute('transform','translate(433,503)');formula.style.opacity=String(expand*(1-merge));
    const progress=clamp(step-4),sum=ease(progress/.35),truncate=ease((progress-.35)/.3),zoom=ease((progress-.65)/.35);
    const resultX=mix(433,205,left),baseTop=mix(45,105,multiply),baseUnit=mix(33,30,multiply),resultTop=mix(baseTop-2*baseUnit*sum,60,zoom),resultUnit=mix(baseUnit,35,zoom);
    result.set(resultX,resultTop,resultUnit,0,replace,resultTop,{sum,truncate});
    copy.set(resultX,baseTop-2*baseUnit*multiply,baseUnit,0,multiply*(1-sum),baseTop);
  }
  set();return {node,set,dispose(){node.remove();}};
}
