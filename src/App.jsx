import { useState, useEffect, useRef, useCallback } from "react";

const T = {
  bg: "#080b11", panel: "#0e1219", border: "#1a2030", grid: "#131a25",
  text: "#5d6878", bright: "#c8d2e0", green: "#00c853", red: "#ef3340",
  rsi: "#f7b731", autoTL: "#ff6d00", trendBreak: "#ff1744", manualTL: "#00e5ff",
  sma200: "#d500f9", bb: "#5c6bc0", bbFill: "rgba(92,107,192,0.05)",
  sar: "#fdd835", forming: "#448aff", vLine: "#fdd835",
  envM5: "#cc2200", envM15: "#00bfa5", envM30: "#76ff03", envH1: "#e040fb",
  tPO: "#689413", tWkUp: "#a0c864", tRng: "#888", tWkDn: "#e6788a", tRevPO: "#db0968",
  menu: "#1c2233", menuBorder: "#2a3550",
};
const TR_COL = { 1: T.tPO, 2: T.tWkUp, 0: T.tRng, "-1": T.tRevPO, "-2": T.tWkDn };
const TR_LBL = { 1: "▲", 2: "△", 0: "─", "-1": "▼", "-2": "▽" };
const TF_NAMES = ["M5", "M15", "M30", "H1"];
const IS_TOUCH = typeof window !== "undefined" && navigator.maxTouchPoints > 0;
const HIT_R = IS_TOUCH ? 22 : 10;

function calcSma(a,p){const o=[];for(let i=0;i<a.length;i++){if(i<p-1){o.push(null);continue;}let s=0;for(let j=i-p+1;j<=i;j++)s+=a[j];o.push(s/p);}return o;}
function calcEma(a,p){const o=[],k=2/(p+1);let e=null;for(let i=0;i<a.length;i++){if(i<p-1){o.push(null);continue;}if(e===null){let s=0;for(let j=i-p+1;j<=i;j++)s+=a[j];e=s/p;}else e=a[i]*k+e*(1-k);o.push(e);}return o;}
function rsiSeries(c,p){if(c.length<p+1)return{v:[],ag:0,al:0};const v=new Array(p).fill(null);let ag=0,al=0;for(let i=1;i<=p;i++){const d=c[i]-c[i-1];ag+=d>0?d:0;al+=d<0?-d:0;}ag/=p;al/=p;v.push(al===0?100:100-100/(1+ag/al));for(let i=p+1;i<c.length;i++){const d=c[i]-c[i-1];ag=(ag*(p-1)+(d>0?d:0))/p;al=(al*(p-1)+(d<0?-d:0))/p;v.push(al===0?100:100-100/(1+ag/al));}return{v,ag,al};}
function liveRsiCalc(ag,al,prev,cur,p){const d=cur-prev;const a2=(ag*(p-1)+(d>0?d:0))/p;const l2=(al*(p-1)+(d<0?-d:0))/p;return l2===0?100:100-100/(1+a2/l2);}
function trendClass(f,m,s){if(f==null||m==null||s==null)return 0;if(f>m&&m>s)return 1;if(f>s&&s>m)return 2;if(s>m&&m>f)return-1;if(s>f&&f>m)return-2;return 0;}
function findBottoms(v){const b=[];for(let i=2;i<v.length-1;i++){if(v[i]==null||v[i-1]==null||v[i+1]==null)continue;if(v[i]<v[i-1]&&v[i]<v[i+1])b.push({i,v:v[i]});}return b;}
function ptLineDist(px,py,x1,y1,x2,y2){const dx=x2-x1,dy=y2-y1,len2=dx*dx+dy*dy;if(len2===0)return Math.hypot(px-x1,py-y1);let t=((px-x1)*dx+(py-y1)*dy)/len2;t=Math.max(0,Math.min(1,t));return Math.hypot(px-(x1+t*dx),py-(y1+t*dy));}

function parseCSV(text){
  const lines=text.trim().split("\n");const bars=[];
  for(let i=1;i<lines.length;i++){const c=lines[i].split(",");if(c.length<5)continue;
    const ts=Number(c[0]);const o=+c[1],h=+c[2],l=+c[3],cl=+c[4];
    if(isNaN(ts)||isNaN(o))continue;
    const pf=j=>{const v=parseFloat(c[j]);return isNaN(v)||c[j]===""?null:v;};
    bars.push({time:ts*(String(ts).length<=10?1000:1),o,h,l,c:cl,
      ind:{envM5U:pf(16),envM5L:pf(17),envM15U:pf(18),envM15L:pf(19),envM30U:pf(20),envM30L:pf(21),envH1U:pf(22),envH1L:pf(23),sma200H1:pf(32),bbU3:pf(37),bbU2:pf(38),bbL2:pf(39),bbL3:pf(40),sar:pf(41)}});}
  return bars;
}
function parsePreset(arr){return arr.map(r=>({time:r[0]*1000,o:r[1],h:r[2],l:r[3],c:r[4],ind:{envM5U:r[5],envM5L:r[6],envM15U:r[7],envM15L:r[8],envM30U:r[9],envM30L:r[10],envH1U:r[11],envH1L:r[12],sma200H1:r[13],bbU3:r[14],bbU2:r[15],bbL2:r[16],bbL3:r[17],sar:r[18]}}));}
async function decompressB64(b64){const bin=atob(b64);const bytes=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)bytes[i]=bin.charCodeAt(i);const ds=new DecompressionStream("gzip");const w=ds.writable.getWriter();w.write(bytes);w.close();const rd=ds.readable.getReader();const chunks=[];while(true){const{done,value}=await rd.read();if(done)break;chunks.push(value);}const total=new Uint8Array(chunks.reduce((a,c)=>a+c.length,0));let off=0;for(const ch of chunks){total.set(ch,off);off+=ch.length;}return new TextDecoder().decode(total);}

function aggFn(data,upTo,ms=900000){const done=[];let f=null;for(let i=0;i<=upTo&&i<data.length;i++){const b=data[i],bk=Math.floor(b.time/ms)*ms;if(!f||f.bk!==bk){if(f)done.push({...f});f={bk,time:b.time,o:b.o,h:b.h,l:b.l,c:b.c,ind:{...b.ind}};}else{f.h=Math.max(f.h,b.h);f.l=Math.min(f.l,b.l);f.c=b.c;f.ind={...b.ind};}}return{done,forming:f};}
function buildTrendMap(data,upTo,ms){const{done,forming}=aggFn(data,upTo,ms);const all=forming?[...done,forming]:[...done];const cl=all.map(b=>b.c);const e=calcEma(cl,13),s21=calcSma(cl,21),s75=calcSma(cl,75);const m=new Map();for(let i=0;i<all.length;i++)m.set(all[i].bk,trendClass(e[i],s21[i],s75[i]));return m;}

export default function App(){
  const[d1m,setD1m]=useState(null);
  const[loading,setLoading]=useState(true);
  const[idx,setIdx]=useState(0);
  const[play,setPlay]=useState(false);
  const[spd,setSpd]=useState(80);
  const[vis,setVis]=useState(30);
  const[yZoom,setYZoom]=useState(1.0);
  const[showBB,setShowBB]=useState(true);
  const[showSAR,setShowSAR]=useState(false);
  const[showAutoTL,setShowAutoTL]=useState(true);
  const[pendingPt,setPendingPt]=useState(null);
  const[mLines,setMLines]=useState([]);
  const[vLines,setVLines]=useState([]);
  const[dragSt,setDragSt]=useState(null);
  const[ctxMenu,setCtxMenu]=useState(null);
  const[panSt,setPanSt]=useState(null);
  const[panOff,setPanOff]=useState({x:0,y:0});
  const cvRef=useRef(null);
  const magRef=useRef(null);
  const boxRef=useRef(null);
  const[magPos,setMagPos]=useState(null);
  const tmr=useRef(null);
  const dp=useRef({});
  const longPressRef=useRef(null);
  const touchStartRef=useRef(null);
  const pinchRef=useRef(null);
  const[dim,setDim]=useState(()=>{const w=Math.min(typeof window!=="undefined"?window.innerWidth:375,920);return{w,h:Math.floor(Math.min(760,Math.max(400,w*0.75)))};});
  const[rsiPos,setRsiPos]=useState({top:0,height:60});

  useEffect(()=>{(async()=>{try{const json=await decompressB64(PRESET_B64);const arr=JSON.parse(json);const bars=parsePreset(arr);if(bars.length){setD1m(bars);setIdx(Math.min(90,bars.length-1));}}catch(e){console.error("Preset fail",e);}setLoading(false);})();},[]);
  useEffect(()=>{const ro=new ResizeObserver(e=>{const w=Math.floor(e[0].contentRect.width);const vh=window.innerHeight;const h=Math.floor(Math.min(vh*0.72,Math.max(300,w*0.75)));setDim({w,h});});if(boxRef.current)ro.observe(boxRef.current);return()=>ro.disconnect();},[]);
  useEffect(()=>{if(tmr.current)clearInterval(tmr.current);if(play&&d1m){tmr.current=setInterval(()=>{setIdx(p=>{if(p>=d1m.length-1){setPlay(false);return p;}return p+1;});},spd);}return()=>{if(tmr.current)clearInterval(tmr.current);};},[play,spd,d1m]);

  const onFile=useCallback(e=>{const f=e.target.files[0];if(!f)return;const r=new FileReader();r.onload=ev=>{const p=parseCSV(ev.target.result);if(p.length){setD1m(p);setIdx(Math.min(90,p.length-1));setPlay(false);setMLines([]);setVLines([]);setPendingPt(null);setPanOff({x:0,y:0});}};r.readAsText(f);},[]);

  const px2bar=px=>(px-dp.current.padL)/dp.current.bW+dp.current.st;
  const px2rsi=py=>Math.max(0,Math.min(100,((dp.current.rT+dp.current.rH-py)/dp.current.rH)*100));
  const bar2px=bar=>dp.current.padL+(bar-dp.current.st+0.5)*dp.current.bW;
  const rsi2py=rsi=>dp.current.rT+dp.current.rH-(rsi/100)*dp.current.rH;

  // Shared logic: place point or line
  const placeAction=useCallback((mx,my)=>{
    const d=dp.current;if(!d.rT)return;
    const inRsi=my>=d.rT&&my<=d.rT+d.rH&&mx>=d.padL&&mx<=d.padL+d.drawW;
    const inPrice=my>=d.pT&&my<d.rT&&mx>=d.padL&&mx<=d.padL+d.drawW;
    if(inRsi){
      const bar=px2bar(mx),rsi=px2rsi(my);
      if(pendingPt){setMLines(prev=>[...prev,{id:Date.now(),p1:pendingPt,p2:{bar,rsi}}]);setPendingPt(null);}
      else{setPendingPt({bar,rsi});}
      if(IS_TOUCH)try{navigator.vibrate(30);}catch(e){}
    }else if(inPrice){
      setVLines(prev=>[...prev,{id:Date.now(),bar:Math.round(px2bar(mx))}]);
      if(IS_TOUCH)try{navigator.vibrate(30);}catch(e){}
    }
  },[pendingPt]);

  // Check handle hit (TL handles + vLine handle)
  const findHandle=useCallback((mx,my)=>{
    const d=dp.current;if(!d.rT)return null;
    // Vertical line handles
    for(const vl of vLines){
      const vi=vl.bar-d.st;if(vi<0||vi>=d.vis)continue;
      const hx=bar2px(vl.bar),hy=d.pT+12;
      if(Math.hypot(mx-hx,my-hy)<HIT_R)return{type:"vline",id:vl.id,ob:vl.bar-px2bar(mx)};
    }
    // TL handles
    const inRsi=my>=d.rT&&my<=d.rT+d.rH;
    if(inRsi){
      for(const ml of mLines){
        const pts=[{key:"p1",bar:ml.p1.bar,rsi:ml.p1.rsi},{key:"p2",bar:ml.p2.bar,rsi:ml.p2.rsi},{key:"mid",bar:(ml.p1.bar+ml.p2.bar)/2,rsi:(ml.p1.rsi+ml.p2.rsi)/2}];
        for(const pt of pts){
          if(Math.hypot(mx-bar2px(pt.bar),my-rsi2py(pt.rsi))<HIT_R)
            return{type:"mline",id:ml.id,handle:pt.key,ob:pt.bar-px2bar(mx),or:pt.rsi-px2rsi(my)};
        }
      }
    }
    return null;
  },[mLines,vLines]);

  // Check line hit for deletion
  const findLineHit=useCallback((mx,my)=>{
    const d=dp.current;if(!d.rT)return null;
    for(const vl of vLines){const vx=bar2px(vl.bar);if(Math.abs(mx-vx)<8&&my>=d.pT&&my<=d.rT+d.rH)return{type:"vline",id:vl.id};}
    if(my>=d.rT&&my<=d.rT+d.rH){
      for(const ml of mLines){
        const slope=(ml.p2.rsi-ml.p1.rsi)/(ml.p2.bar-ml.p1.bar||0.001);
        const extBar=d.st+d.vis+d.vis*0.2;
        const x1=bar2px(ml.p1.bar),y1=rsi2py(ml.p1.rsi);
        const x2=bar2px(extBar),y2=rsi2py(ml.p1.rsi+slope*(extBar-ml.p1.bar));
        if(ptLineDist(mx,my,x1,y1,x2,y2)<8)return{type:"mline",id:ml.id};
      }
    }
    return null;
  },[mLines,vLines]);

  const applyDrag=useCallback((mx,my,ds)=>{
    if(ds.type==="vline"){
      const newBar=Math.round(px2bar(mx)+ds.ob);
      setVLines(prev=>prev.map(v=>v.id===ds.id?{...v,bar:newBar}:v));
    }else if(ds.type==="mline"){
      const bar=px2bar(mx)+ds.ob,rsi=px2rsi(my)+ds.or;
      setMLines(prev=>prev.map(ml=>{
        if(ml.id!==ds.id)return ml;
        if(ds.handle==="p1")return{...ml,p1:{bar,rsi}};
        if(ds.handle==="p2")return{...ml,p2:{bar,rsi}};
        const db=bar-(ml.p1.bar+ml.p2.bar)/2,dr=rsi-(ml.p1.rsi+ml.p2.rsi)/2;
        return{...ml,p1:{bar:ml.p1.bar+db,rsi:ml.p1.rsi+dr},p2:{bar:ml.p2.bar+db,rsi:ml.p2.rsi+dr}};
      }));
    }
  },[]);

  // ─── MOUSE HANDLERS ───
  const onCtxMenu=useCallback(e=>{e.preventDefault();setCtxMenu(null);const rect=cvRef.current.getBoundingClientRect();placeAction(e.clientX-rect.left,e.clientY-rect.top);},[placeAction]);
  const onMouseDown=useCallback(e=>{
    setCtxMenu(null);const rect=cvRef.current.getBoundingClientRect();const mx=e.clientX-rect.left,my=e.clientY-rect.top;
    if(e.button===1){e.preventDefault();setPanSt({startX:e.clientX,startY:e.clientY,startPan:{...panOff}});return;}
    if(e.button!==0)return;
    const h=findHandle(mx,my);if(h){setDragSt(h);return;}
  },[panOff,findHandle]);
  const onMouseMove=useCallback(e=>{
    if(panSt){const dx=e.clientX-panSt.startX,dy=e.clientY-panSt.startY;setPanOff({x:panSt.startPan.x-dx/(dp.current.bW||10),y:panSt.startPan.y+dy});return;}
    if(dragSt){const rect=cvRef.current.getBoundingClientRect();applyDrag(e.clientX-rect.left,e.clientY-rect.top,dragSt);}
  },[dragSt,panSt,applyDrag]);
  const onMouseUp=useCallback(()=>{setPanSt(null);setDragSt(null);},[]);
  const onClick=useCallback(e=>{
    if(dragSt||panSt)return;const rect=cvRef.current.getBoundingClientRect();const mx=e.clientX-rect.left,my=e.clientY-rect.top;
    const hit=findLineHit(mx,my);if(hit){setCtxMenu({x:mx,y:my,...hit});return;}
    setCtxMenu(null);
  },[findLineHit,dragSt,panSt]);

  // ─── TOUCH HANDLERS ───
  const onTouchStart=useCallback(e=>{
    setCtxMenu(null);
    const rect=cvRef.current.getBoundingClientRect();
    if(e.touches.length===1){
      const t=e.touches[0];const mx=t.clientX-rect.left,my=t.clientY-rect.top;
      // Check handle first
      const h=findHandle(mx,my);
      if(h){e.preventDefault();setDragSt(h);if(h.type==="mline"&&(h.handle==="p1"||h.handle==="p2"))setMagPos({x:mx,y:my});touchStartRef.current=null;return;}
      // Start long press timer
      touchStartRef.current={x:t.clientX,y:t.clientY,mx,my,moved:false,startPan:{...panOff}};
      longPressRef.current=setTimeout(()=>{
        if(touchStartRef.current&&!touchStartRef.current.moved){
          placeAction(touchStartRef.current.mx,touchStartRef.current.my);
          touchStartRef.current=null;
        }
      },500);
    }else if(e.touches.length===2){
      e.preventDefault();
      // Cancel long press
      if(longPressRef.current){clearTimeout(longPressRef.current);longPressRef.current=null;}
      touchStartRef.current=null;
      const t1=e.touches[0],t2=e.touches[1];
      const cx=(t1.clientX+t2.clientX)/2,cy=(t1.clientY+t2.clientY)/2;
      const dist=Math.hypot(t1.clientX-t2.clientX,t1.clientY-t2.clientY);
      pinchRef.current={cx,cy,dist,startZoom:yZoom,startPan:{...panOff}};
    }
  },[findHandle,placeAction,yZoom,panOff]);

  const onTouchMove=useCallback(e=>{
    if(dragSt&&e.touches.length===1){
      e.preventDefault();
      const t=e.touches[0];const rect=cvRef.current.getBoundingClientRect();
      const mx=t.clientX-rect.left,my=t.clientY-rect.top;
      if(dragSt.type==="mline"&&(dragSt.handle==="p1"||dragSt.handle==="p2"))setMagPos({x:mx,y:my});
      applyDrag(mx,my,dragSt);return;
    }
    if(e.touches.length===1&&touchStartRef.current){
      const t=e.touches[0];
      const dx=t.clientX-touchStartRef.current.x,dy=t.clientY-touchStartRef.current.y;
      if(Math.hypot(dx,dy)>10){
        touchStartRef.current.moved=true;
        if(longPressRef.current){clearTimeout(longPressRef.current);longPressRef.current=null;}
        // 1-finger pan: hide magnifier
        setMagPos(null);
        e.preventDefault();
        const sp=touchStartRef.current.startPan;
        setPanOff({x:sp.x-dx/(dp.current.bW||10),y:sp.y+dy});
      }
    }
    if(e.touches.length===2&&pinchRef.current){
      e.preventDefault();
      const t1=e.touches[0],t2=e.touches[1];
      const dist=Math.hypot(t1.clientX-t2.clientX,t1.clientY-t2.clientY);
      const scale=dist/pinchRef.current.dist;
      setYZoom(Math.max(0.5,Math.min(5,pinchRef.current.startZoom*scale)));
    }
  },[dragSt,applyDrag]);

  const onTouchEnd=useCallback(e=>{
    setMagPos(null);
    if(dragSt){setDragSt(null);return;}
    if(longPressRef.current){clearTimeout(longPressRef.current);longPressRef.current=null;}
    // Tap detection (for line deletion)
    if(touchStartRef.current&&!touchStartRef.current.moved&&e.changedTouches.length>0){
      const hit=findLineHit(touchStartRef.current.mx,touchStartRef.current.my);
      if(hit)setCtxMenu({x:touchStartRef.current.mx,y:touchStartRef.current.my,...hit});
    }
    touchStartRef.current=null;pinchRef.current=null;
  },[dragSt,findLineHit]);

  const onMenuDel=useCallback(()=>{
    if(!ctxMenu)return;
    if(ctxMenu.type==="mline")setMLines(prev=>prev.filter(l=>l.id!==ctxMenu.id));
    if(ctxMenu.type==="vline")setVLines(prev=>prev.filter(l=>l.id!==ctxMenu.id));
    setCtxMenu(null);
  },[ctxMenu]);

  // Mouse wheel Y-axis zoom
  const onWheel=useCallback(e=>{
    e.preventDefault();
    const delta=e.deltaY>0?-0.1:0.1;
    setYZoom(z=>Math.max(0.5,Math.min(5,z+delta*z)));
  },[]);

  // ═══════════ DRAW ═══════════
  useEffect(()=>{
    if(!d1m||!cvRef.current)return;
    const cv=cvRef.current,dprV=window.devicePixelRatio||1;
    cv.width=dim.w*dprV;cv.height=dim.h*dprV;
    const ctx=cv.getContext("2d");ctx.scale(dprV,dprV);
    const W=dim.w,H=dim.h;
    const pad={l:56,r:10,t:8,b:18};
    const trendH=52,gap=4;
    const inner=H-pad.t-pad.b-trendH-gap*2;
    const pH=inner*0.56,rH=inner*0.44;
    const pT=pad.t,rT=pT+pH+gap,tT=rT+rH+gap;
    const fullW=W-pad.l-pad.r,drawW=fullW*0.80,marginX=pad.l+drawW;
    ctx.fillStyle=T.bg;ctx.fillRect(0,0,W,H);

    const intMs=900000;
    const{done,forming}=aggFn(d1m,idx,intMs);
    const all=forming?[...done,forming]:[...done];
    if(!all.length)return;
    const panBars=Math.round(panOff.x);
    const st=Math.max(0,Math.min(all.length-1,Math.max(0,all.length-vis)+panBars));
    const vBars=all.slice(st,st+vis);
    const isF=forming&&(st+vBars.length-1>=all.length-1);
    const closes=done.map(b=>b.c);
    const{v:rsiDone,ag,al}=rsiSeries(closes,5);
    let lRsi=null;
    if(forming&&closes.length>=6)lRsi=liveRsiCalc(ag,al,closes[closes.length-1],forming.c,5);
    const allRsi=[...rsiDone,...(lRsi!=null?[lRsi]:[])];
    const visRsi=allRsi.slice(st,st+vBars.length);
    const tMaps=[300000,900000,1800000,3600000].map(ms=>buildTrendMap(d1m,idx,ms));
    const tfMs=[300000,900000,1800000,3600000];

    const bW=drawW/vis,cndW=Math.max(1,bW*0.56);
    const bX=i=>pad.l+(i+0.5)*bW;
    let pMin=Infinity,pMax=-Infinity;
    for(const b of vBars){
      pMin=Math.min(pMin,b.l);pMax=Math.max(pMax,b.h);
      for(const k of["envM5U","envM15U","envM30U","envH1U"])if(b.ind[k]!=null)pMax=Math.max(pMax,b.ind[k]);
      for(const k of["envM5L","envM15L","envM30L","envH1L"])if(b.ind[k]!=null)pMin=Math.min(pMin,b.ind[k]);
      if(b.ind.sma200H1!=null){pMin=Math.min(pMin,b.ind.sma200H1);pMax=Math.max(pMax,b.ind.sma200H1);}
      if(showBB&&b.ind.bbU2!=null){pMax=Math.max(pMax,b.ind.bbU2);pMin=Math.min(pMin,b.ind.bbL2);}
    }
    const basePad=(pMax-pMin)*0.04||1;const mid=(pMax+pMin)/2;const halfR=((pMax-pMin)/2+basePad)/yZoom;
    const ppp=(halfR*2)/pH;const yMid=mid+(panOff.y||0)*ppp;
    pMin=yMid-halfR;pMax=yMid+halfR;
    const pY=v=>pT+pH-((v-pMin)/(pMax-pMin))*pH;
    const rY=v=>rT+rH-(v/100)*rH;
    dp.current={rT,rH,pT,padL:pad.l,drawW,bW,st,vis};
    setRsiPos({top:rT,height:rH});

    // Grid
    ctx.strokeStyle=T.grid;ctx.lineWidth=0.5;ctx.font="10px monospace";ctx.fillStyle=T.text;ctx.textAlign="right";
    for(let i=0;i<=5;i++){const v=pMin+(pMax-pMin)*i/5,y=pY(v);ctx.beginPath();ctx.moveTo(pad.l,y);ctx.lineTo(pad.l+drawW,y);ctx.stroke();ctx.fillText(v.toFixed(1),pad.l-4,y+3);}

    const drawInd=(getter,color,width,dash,alpha=1)=>{ctx.strokeStyle=color;ctx.lineWidth=width;ctx.globalAlpha=alpha;if(dash)ctx.setLineDash(dash);ctx.beginPath();let s=false;for(let i=0;i<vBars.length;i++){const v=getter(vBars[i]);if(v==null)continue;const x=bX(i),y=pY(v);if(!s){ctx.moveTo(x,y);s=true;}else ctx.lineTo(x,y);}ctx.stroke();if(dash)ctx.setLineDash([]);ctx.globalAlpha=1;};
    const labels=[];const addLbl=(val,text,color)=>{if(val!=null)labels.push({y:pY(val),text,color});};

    // BB
    if(showBB){ctx.beginPath();let s=false;for(let i=0;i<vBars.length;i++){const v=vBars[i].ind.bbU2;if(v==null)continue;if(!s){ctx.moveTo(bX(i),pY(v));s=true;}else ctx.lineTo(bX(i),pY(v));}for(let i=vBars.length-1;i>=0;i--){const v=vBars[i].ind.bbL2;if(v==null)continue;ctx.lineTo(bX(i),pY(v));}ctx.closePath();ctx.fillStyle=T.bbFill;ctx.fill();drawInd(b=>b.ind.bbU2,T.bb,1,null);drawInd(b=>b.ind.bbL2,T.bb,1,null);drawInd(b=>b.ind.bbU3,T.bb,0.7,[3,3],0.4);drawInd(b=>b.ind.bbL3,T.bb,0.7,[3,3],0.4);}

    // Envelopes
    for(const ev of[{u:"envM5U",l:"envM5L",col:T.envM5,name:"M5"},{u:"envM15U",l:"envM15L",col:T.envM15,name:"M15"},{u:"envM30U",l:"envM30L",col:T.envM30,name:"M30"},{u:"envH1U",l:"envH1L",col:T.envH1,name:"H1"}]){
      ctx.beginPath();let s=false;for(let i=0;i<vBars.length;i++){const v=vBars[i].ind[ev.u];if(v==null)continue;if(!s){ctx.moveTo(bX(i),pY(v));s=true;}else ctx.lineTo(bX(i),pY(v));}for(let i=vBars.length-1;i>=0;i--){const v=vBars[i].ind[ev.l];if(v==null)continue;ctx.lineTo(bX(i),pY(v));}ctx.closePath();ctx.fillStyle=ev.col+"08";ctx.fill();
      drawInd(b=>b.ind[ev.u],ev.col,1,null,0.7);drawInd(b=>b.ind[ev.l],ev.col,1,null,0.7);
      const lb=vBars[vBars.length-1];addLbl(lb.ind[ev.u],`${ev.name} hi`,ev.col);addLbl(lb.ind[ev.l],`${ev.name} lo`,ev.col);
    }
    drawInd(b=>b.ind.sma200H1,T.sma200,2,null);addLbl(vBars[vBars.length-1].ind.sma200H1,"H1 SMA200",T.sma200);
    if(showSAR){for(let i=0;i<vBars.length;i++){const v=vBars[i].ind.sar;if(v==null)continue;ctx.beginPath();ctx.arc(bX(i),pY(v),2,0,Math.PI*2);ctx.fillStyle=v<vBars[i].c?T.green:T.red;ctx.fill();}}
    labels.sort((a,b)=>a.y-b.y);for(let i=1;i<labels.length;i++){if(labels[i].y-labels[i-1].y<10)labels[i].y=labels[i-1].y+10;}
    ctx.font="9px monospace";ctx.textAlign="left";for(const lb of labels){ctx.fillStyle=lb.color;ctx.fillText(lb.text,marginX+4,lb.y+3);}

    // Candles
    for(let i=0;i<vBars.length;i++){
      const b=vBars[i],x=bX(i),isFm=i===vBars.length-1&&isF;const bull=b.c>=b.o,col=bull?T.green:T.red;
      ctx.globalAlpha=isFm?0.6:1;ctx.strokeStyle=col;ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(x,pY(b.h));ctx.lineTo(x,pY(b.l));ctx.stroke();
      const yt=pY(Math.max(b.o,b.c)),yb=pY(Math.min(b.o,b.c));ctx.fillStyle=col;ctx.fillRect(x-cndW/2,yt,cndW,Math.max(1,yb-yt));
      if(isFm){ctx.strokeStyle=T.forming;ctx.lineWidth=1.5;ctx.setLineDash([3,3]);ctx.strokeRect(x-cndW/2-2,yt-2,cndW+4,Math.max(1,yb-yt)+4);ctx.setLineDash([]);}ctx.globalAlpha=1;
    }
    if(forming){const y=pY(forming.c);ctx.strokeStyle=forming.c>=forming.o?T.green:T.red;ctx.lineWidth=0.7;ctx.setLineDash([4,4]);ctx.beginPath();ctx.moveTo(pad.l,y);ctx.lineTo(pad.l+drawW,y);ctx.stroke();ctx.setLineDash([]);ctx.fillStyle=forming.c>=forming.o?T.green:T.red;ctx.font="bold 10px monospace";ctx.textAlign="left";ctx.fillText(forming.c.toFixed(2),marginX+4,y+3);}

    // RSI panel
    ctx.fillStyle=T.panel;ctx.fillRect(pad.l,rT,fullW,rH);
    ctx.fillStyle="rgba(0,200,83,0.02)";ctx.fillRect(pad.l,rY(100),fullW,rY(50)-rY(100));
    ctx.fillStyle="rgba(239,51,64,0.02)";ctx.fillRect(pad.l,rY(50),fullW,rY(0)-rY(50));
    ctx.strokeStyle=T.grid;ctx.lineWidth=0.5;ctx.font="10px monospace";ctx.fillStyle=T.text;ctx.textAlign="right";
    for(const v of[30,50,70]){const y=rY(v);ctx.beginPath();ctx.moveTo(pad.l,y);ctx.lineTo(pad.l+fullW,y);ctx.stroke();ctx.fillText(String(v),pad.l-4,y+3);}
    ctx.setLineDash([5,5]);ctx.lineWidth=1;
    ctx.strokeStyle="rgba(255,255,255,0.3)";
    for(const v of[5,10,15,20,30,70,80,85,90,95]){ctx.beginPath();ctx.moveTo(pad.l,rY(v));ctx.lineTo(pad.l+fullW,rY(v));ctx.stroke();}
    ctx.strokeStyle="rgba(255,255,255,0.5)";
    ctx.beginPath();ctx.moveTo(pad.l,rY(50));ctx.lineTo(pad.l+fullW,rY(50));ctx.stroke();
    ctx.setLineDash([]);

    ctx.strokeStyle=T.rsi;ctx.lineWidth=2;ctx.beginPath();let rs=false;
    for(let i=0;i<visRsi.length;i++){if(visRsi[i]==null)continue;const x=bX(i),y=rY(visRsi[i]);if(!rs){ctx.moveTo(x,y);rs=true;}else ctx.lineTo(x,y);}ctx.stroke();
    if(rs){ctx.globalAlpha=0.05;ctx.fillStyle=T.rsi;ctx.lineTo(bX(visRsi.length-1),rY(0));ctx.lineTo(bX(0),rY(0));ctx.closePath();ctx.fill();ctx.globalAlpha=1;}
    if(lRsi!=null&&visRsi.length>0){const li=visRsi.length-1,x=bX(li),y=rY(lRsi);ctx.beginPath();ctx.arc(x,y,5,0,Math.PI*2);ctx.fillStyle=T.rsi;ctx.fill();ctx.beginPath();ctx.arc(x,y,9,0,Math.PI*2);ctx.strokeStyle=T.rsi;ctx.globalAlpha=0.25;ctx.lineWidth=2;ctx.stroke();ctx.globalAlpha=1;ctx.fillStyle=T.rsi;ctx.font="bold 11px monospace";ctx.textAlign="left";ctx.fillText(lRsi.toFixed(1),marginX+4,y+4);}

    // Clip for TL
    ctx.save();ctx.beginPath();ctx.rect(pad.l,rT,fullW,rH);ctx.clip();
    if(showAutoTL){const bots=findBottoms(allRsi);if(bots.length>=2){const recent=bots.slice(-8);const asc=[];for(let i=recent.length-1;i>=0;i--){if(asc.length===0||recent[i].v<asc[asc.length-1].v)asc.push(recent[i]);if(asc.length>=3)break;}asc.reverse();if(asc.length>=2){for(let b=0;b<asc.length-1;b++){const b1=asc[b],b2=asc[b+1];const slope=(b2.v-b1.v)/(b2.i-b1.i);const ext=vis+vis*0.2;const extV=b2.v+slope*(st+ext-b2.i);const i1=b1.i-st;if(i1<-vis)continue;ctx.strokeStyle=T.autoTL;ctx.lineWidth=1.5;ctx.setLineDash([6,4]);ctx.beginPath();ctx.moveTo(bX(Math.max(0,i1)),rY(i1>=0?b1.v:b1.v+slope*(st-b1.i)));ctx.lineTo(bX(ext),rY(extV));ctx.stroke();ctx.setLineDash([]);if(lRsi!=null){const tlAt=b2.v+slope*(allRsi.length-1-b2.i);if(lRsi<tlAt){ctx.fillStyle=T.trendBreak;ctx.globalAlpha=0.1;ctx.fillRect(pad.l,rT,fullW,rH);ctx.globalAlpha=1;ctx.font="bold 12px monospace";ctx.fillStyle=T.trendBreak;ctx.textAlign="center";ctx.fillText("⚠ TRENDLINE BREAK",pad.l+drawW/2,rT+15);}}for(const bt of asc){const bi=bt.i-st;if(bi>=0&&bi<visRsi.length){ctx.beginPath();ctx.arc(bX(bi),rY(bt.v),4,0,Math.PI*2);ctx.fillStyle=T.autoTL;ctx.fill();}}}}}}

    for(const ml of mLines){const slope=(ml.p2.rsi-ml.p1.rsi)/(ml.p2.bar-ml.p1.bar||0.001);const leftB=st-10,rightB=st+vis+vis*0.2;const x1=bar2px(leftB),y1=rsi2py(ml.p1.rsi+slope*(leftB-ml.p1.bar));const x2=bar2px(rightB),y2=rsi2py(ml.p1.rsi+slope*(rightB-ml.p1.bar));ctx.strokeStyle=T.manualTL;ctx.lineWidth=1.5;ctx.setLineDash([4,3]);ctx.beginPath();ctx.moveTo(x1,y1);ctx.lineTo(x2,y2);ctx.stroke();ctx.setLineDash([]);const midB=(ml.p1.bar+ml.p2.bar)/2,midR=(ml.p1.rsi+ml.p2.rsi)/2;for(const h of[{b:ml.p1.bar,r:ml.p1.rsi,s:5},{b:ml.p2.bar,r:ml.p2.rsi,s:5},{b:midB,r:midR,s:4}]){const hx=bar2px(h.b),hy=rsi2py(h.r);ctx.beginPath();ctx.arc(hx,hy,h.s,0,Math.PI*2);ctx.fillStyle=T.manualTL;ctx.fill();ctx.beginPath();ctx.arc(hx,hy,h.s+2,0,Math.PI*2);ctx.strokeStyle=T.manualTL;ctx.globalAlpha=0.3;ctx.lineWidth=1.5;ctx.stroke();ctx.globalAlpha=1;}}
    if(pendingPt){const px=bar2px(pendingPt.bar),py=rsi2py(pendingPt.rsi);ctx.beginPath();ctx.arc(px,py,6,0,Math.PI*2);ctx.strokeStyle=T.manualTL;ctx.lineWidth=2;ctx.stroke();ctx.setLineDash([2,2]);ctx.beginPath();ctx.moveTo(px-12,py);ctx.lineTo(px+12,py);ctx.moveTo(px,py-12);ctx.lineTo(px,py+12);ctx.stroke();ctx.setLineDash([]);}
    ctx.restore();

    // MA Trend
    ctx.fillStyle=T.panel;ctx.fillRect(pad.l,tT,fullW,trendH);ctx.strokeStyle=T.border;ctx.lineWidth=0.5;ctx.strokeRect(pad.l,tT,fullW,trendH);
    const rowH=(trendH-4)/4;
    for(let i=0;i<vBars.length;i++){const bar=vBars[i];for(let r=0;r<4;r++){const bk=Math.floor(bar.bk/tfMs[r])*tfMs[r];ctx.fillStyle=TR_COL[String(tMaps[r].get(bk)??0)]||T.tRng;ctx.fillRect(bX(i)-bW/2+0.5,tT+2+r*rowH,bW-1,rowH-1);}}
    ctx.font="9px monospace";ctx.textAlign="left";
    for(let r=0;r<4;r++){const ry=tT+2+r*rowH+rowH/2+3;ctx.fillStyle=T.bright;ctx.fillText(TF_NAMES[r],marginX+4,ry);const lb=vBars[vBars.length-1];const bk=Math.floor(lb.bk/tfMs[r])*tfMs[r];const tr=tMaps[r].get(bk)??0;ctx.fillStyle=TR_COL[String(tr)]||T.tRng;ctx.fillText(TR_LBL[String(tr)]||"─",marginX+26,ry);}

    // Vertical lines - drawn last so they appear on top of all panels
    for(const vl of vLines){
      const vi=vl.bar-st;if(vi<0||vi>=vis)continue;const x=bX(vi);
      ctx.strokeStyle=T.vLine;ctx.lineWidth=1;ctx.setLineDash([4,3]);ctx.globalAlpha=0.7;
      ctx.beginPath();ctx.moveTo(x,pT);ctx.lineTo(x,tT+trendH);ctx.stroke();
      ctx.setLineDash([]);ctx.globalAlpha=1;
      // Drag handle at top
      ctx.beginPath();ctx.arc(x,pT+12,6,0,Math.PI*2);ctx.fillStyle=T.vLine;ctx.globalAlpha=0.8;ctx.fill();ctx.globalAlpha=1;
      ctx.beginPath();ctx.arc(x,pT+12,8,0,Math.PI*2);ctx.strokeStyle=T.vLine;ctx.globalAlpha=0.3;ctx.lineWidth=1.5;ctx.stroke();ctx.globalAlpha=1;
    }

    ctx.font="bold 10px monospace";ctx.textAlign="left";ctx.fillStyle=T.bright;ctx.fillText("15min",pad.l+3,pT+11);ctx.fillStyle=T.rsi;ctx.fillText("RSI(5)",pad.l+3,rT+12);ctx.fillStyle=T.bright;ctx.fillText("MA Trend",pad.l+3,tT+12);
    const pct=((idx/(d1m.length-1))*100).toFixed(1);const bIn=forming?Math.floor((d1m[idx].time%intMs)/60000)+1:0;
    ctx.fillStyle=T.text;ctx.font="10px monospace";ctx.textAlign="right";ctx.fillText(`${idx+1}/${d1m.length} (${pct}%)  Bar ${bIn}/15`,W-pad.r,H-3);ctx.textAlign="left";ctx.fillText(new Date(d1m[idx].time).toLocaleString("ja-JP"),pad.l,H-3);
  },[d1m,idx,dim,vis,yZoom,showBB,showSAR,showAutoTL,mLines,vLines,pendingPt,panOff]);

  // ─── MAGNIFIER DRAW ───
  useEffect(()=>{
    const mag=magRef.current;const src=cvRef.current;
    if(!mag||!src)return;
    if(!magPos){const c=mag.getContext("2d");c.clearRect(0,0,mag.width,mag.height);return;}
    const dpr=window.devicePixelRatio||1;
    const MAG=3,SIZE=110;
    mag.width=SIZE*dpr;mag.height=SIZE*dpr;
    const c=mag.getContext("2d");c.scale(dpr,dpr);
    // clip to circle
    c.save();c.beginPath();c.arc(SIZE/2,SIZE/2,SIZE/2-1,0,Math.PI*2);c.clip();
    // source region in CSS pixels on main canvas, zoom MAG×
    const srcW=SIZE/MAG,srcH=SIZE/MAG;
    const sx=(magPos.x-srcW/2)*dpr,sy=(magPos.y-srcH/2)*dpr;
    c.drawImage(src,sx,sy,srcW*dpr,srcH*dpr,0,0,SIZE,SIZE);
    // crosshair
    c.strokeStyle="rgba(255,255,255,0.9)";c.lineWidth=1;
    c.beginPath();c.moveTo(SIZE/2,SIZE/2-10);c.lineTo(SIZE/2,SIZE/2+10);
    c.moveTo(SIZE/2-10,SIZE/2);c.lineTo(SIZE/2+10,SIZE/2);c.stroke();
    // dot at center
    c.beginPath();c.arc(SIZE/2,SIZE/2,2,0,Math.PI*2);
    c.fillStyle="rgba(255,255,255,0.9)";c.fill();
    c.restore();
    // border ring
    c.beginPath();c.arc(SIZE/2,SIZE/2,SIZE/2-1,0,Math.PI*2);
    c.strokeStyle="rgba(255,255,255,0.3)";c.lineWidth=1.5;c.stroke();
  },[magPos,d1m,idx,dim,vis,yZoom,showBB,showSAR,showAutoTL,mLines,vLines,pendingPt,panOff]);

  useEffect(()=>{if(dragSt||panSt){const mm=e=>onMouseMove(e),mu=()=>onMouseUp();window.addEventListener("mousemove",mm);window.addEventListener("mouseup",mu);return()=>{window.removeEventListener("mousemove",mm);window.removeEventListener("mouseup",mu);};};},[dragSt,panSt,onMouseMove,onMouseUp]);
  useEffect(()=>{const h=e=>{if(e.code==="Space"){e.preventDefault();setPlay(p=>!p);}if(e.code==="ArrowRight"){e.preventDefault();setIdx(i=>Math.min(i+1,(d1m?.length||1)-1));}if(e.code==="ArrowLeft"){e.preventDefault();setIdx(i=>Math.max(i-1,0));}if(e.code==="ArrowUp"){e.preventDefault();setSpd(s=>Math.max(5,s-10));}if(e.code==="ArrowDown"){e.preventDefault();setSpd(s=>Math.min(500,s+10));}if(e.code==="Escape"){setPendingPt(null);setCtxMenu(null);}};window.addEventListener("keydown",h);return()=>window.removeEventListener("keydown",h);},[d1m]);

  const maxIdx=d1m?d1m.length-1:0;
  if(loading)return <div style={{color:T.text,padding:40,fontFamily:"monospace",background:T.bg,minHeight:"100vh"}}>プリセットデータ読込中...</div>;

  const hints=IS_TOUCH
    ?["長押し(RSI)=TL描画","長押し(チャート)=垂直ライン","タップ=削除","2本指=パン/ピンチ"]
    :["右クリック(RSI)=TL","右クリック(チャート)=垂直ライン","左クリック=削除","中ボタン=パン","ホイール=Y軸ズーム"];

  return(
    <div style={{background:T.bg,minHeight:"100vh",maxWidth:"100vw",overflowX:"hidden",fontFamily:"'JetBrains Mono','Fira Code',monospace",color:T.bright,position:"relative",touchAction:"none"}}>
      <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"6px 12px",borderBottom:`1px solid ${T.border}`,flexWrap:"wrap",gap:4}}>
        <div style={{display:"flex",alignItems:"center",gap:6}}><span style={{fontSize:13,fontWeight:700,color:T.rsi}}>⟐</span><span style={{fontSize:12,fontWeight:700,letterSpacing:1}}>INTRA-BAR REPLAY</span></div>
        <label style={{fontSize:11,color:T.forming,cursor:"pointer"}}><span style={{background:"rgba(68,138,255,0.1)",padding:"3px 10px",borderRadius:4,border:`1px solid ${T.forming}33`}}>1分足 CSV</span><input type="file" accept=".csv,.txt" onChange={onFile} style={{display:"none"}}/></label>
      </div>
      <div style={{display:"flex",alignItems:"center",gap:4,padding:"4px 12px",borderBottom:`1px solid ${T.border}`,flexWrap:"wrap",fontSize:11}}>
        <Btn c={T.text} onClick={()=>setIdx(i=>Math.max(i-15,0))}>←15</Btn>
        <Btn c={T.text} onClick={()=>setIdx(i=>Math.min(i+1,maxIdx))}>→1</Btn>
        <Btn c={T.text} onClick={()=>{if(!d1m)return;const cur=Math.floor(d1m[idx].time/900000);let n=idx+1;while(n<d1m.length&&Math.floor(d1m[n].time/900000)===cur)n++;setIdx(Math.min(n,d1m.length-1));}}>→15m</Btn>
        <Btn c={T.text} onClick={()=>{setIdx(0);setPlay(false);}}>⏮</Btn>
        <Sep/><Lb>速度</Lb><input type="range" min={5} max={500} value={spd} onChange={e=>setSpd(+e.target.value)} style={{width:60,accentColor:T.forming}}/><Lb>{spd}ms</Lb>
        <Sep/><Lb>表示</Lb><input type="range" min={20} max={120} value={vis} onChange={e=>setVis(+e.target.value)} style={{width:50,accentColor:T.forming}}/><Lb>{vis}</Lb>
        <Sep/><Lb>Y軸</Lb><input type="range" min={50} max={500} value={yZoom*100} onChange={e=>setYZoom(+e.target.value/100)} style={{width:55,accentColor:T.forming}}/><Lb>{yZoom.toFixed(1)}x</Lb>
        <Btn c={T.text} onClick={()=>{setYZoom(1.0);setPanOff({x:0,y:0});}}>reset</Btn>
      </div>
      <div style={{display:"flex",alignItems:"center",gap:4,padding:"4px 12px",borderBottom:`1px solid ${T.border}`,flexWrap:"wrap",fontSize:10}}>
        <Lb>位置</Lb><input type="range" min={0} max={maxIdx} value={idx} onChange={e=>{setIdx(+e.target.value);setPlay(false);}} style={{flex:"1 1 100px",minWidth:60,accentColor:T.forming}}/>
        <Sep/><Chk c={T.bb} v={showBB} set={setShowBB}>BB</Chk><Chk c={T.sar} v={showSAR} set={setShowSAR}>SAR</Chk><Chk c={T.autoTL} v={showAutoTL} set={setShowAutoTL}>自動TL</Chk>
        <Sep/>{(mLines.length>0||vLines.length>0)&&<Btn c={T.red} onClick={()=>{setMLines([]);setVLines([]);setPendingPt(null);}}>全消し</Btn>}
        {pendingPt&&<span style={{color:T.manualTL,fontSize:10}}>✏ 2点目を{IS_TOUCH?"長押し":"右クリック"}</span>}
      </div>
      <div ref={boxRef} style={{padding:0,position:"relative"}}>
        <canvas ref={cvRef} onMouseDown={onMouseDown} onClick={onClick} onContextMenu={onCtxMenu}
          onWheel={onWheel}
          onAuxClick={e=>{if(e.button===1)e.preventDefault();}}
          onTouchStart={onTouchStart} onTouchMove={onTouchMove} onTouchEnd={onTouchEnd}
          style={{width:dim.w,height:dim.h,display:"block",touchAction:"none",cursor:dragSt?"grabbing":panSt?"move":"default"}}/>
        <div
          onTouchStart={e=>{e.stopPropagation();}}
          onTouchEnd={e=>{e.preventDefault();e.stopPropagation();setPlay(p=>!p);}}
          onClick={()=>setPlay(p=>!p)}
          style={{position:"absolute",left:0,top:rsiPos.top,width:56,height:rsiPos.height,display:"flex",alignItems:"center",justifyContent:"center",cursor:"pointer",zIndex:5}}>
          <div style={{width:36,height:36,borderRadius:8,background:play?"rgba(239,51,64,0.15)":"rgba(0,200,83,0.15)",border:`1.5px solid ${play?T.red:T.green}`,display:"flex",alignItems:"center",justifyContent:"center",fontSize:16,color:play?T.red:T.green}}>
            {play?"⏸":"▶"}
          </div>
        </div>
        {magPos&&(
          <canvas ref={magRef} style={{position:"absolute",top:8,left:8,width:110,height:110,borderRadius:"50%",pointerEvents:"none",boxShadow:"0 2px 12px rgba(0,0,0,0.7)"}}/>
        )}
        {ctxMenu&&(<div style={{position:"absolute",left:Math.min(ctxMenu.x,dim.w-140),top:ctxMenu.y-4,background:T.menu,border:`1px solid ${T.menuBorder}`,borderRadius:6,padding:2,zIndex:10,boxShadow:"0 4px 16px rgba(0,0,0,0.5)"}}>
          <div onClick={onMenuDel} style={{padding:"8px 18px",cursor:"pointer",fontSize:12,color:T.red,fontFamily:"inherit",borderRadius:4,fontWeight:600}}
            onMouseEnter={e=>e.target.style.background="rgba(239,51,64,0.12)"} onMouseLeave={e=>e.target.style.background="transparent"}>
            🗑 {ctxMenu.type==="vline"?"垂直ライン削除":"ライン削除"}
          </div>
        </div>)}
      </div>
      <div style={{padding:"3px 12px",display:"flex",gap:8,flexWrap:"wrap",fontSize:9,color:T.text,opacity:0.5}}>
        {hints.map((h,i)=><span key={i}>{h}</span>)}
      </div>
      <div style={{padding:"0 12px 8px",display:"flex",gap:7,flexWrap:"wrap",fontSize:9}}>
        {[[T.tPO,"▲ PO"],[T.tWkUp,"△ 弱↑"],[T.tRng,"─ Range"],[T.tWkDn,"▽ 弱↓"],[T.tRevPO,"▼ RevPO"]].map(([c,l],i)=>(<div key={i} style={{display:"flex",alignItems:"center",gap:3}}><div style={{width:8,height:8,borderRadius:2,background:c}}/><span style={{color:c}}>{l}</span></div>))}
      </div>
    </div>
  );
}

function Btn({c,onClick,children}){return <button onClick={onClick} style={{background:"transparent",border:`1px solid ${c}44`,color:c,padding:IS_TOUCH?"4px 12px":"2px 8px",borderRadius:4,cursor:"pointer",fontSize:IS_TOUCH?13:11,fontFamily:"inherit",fontWeight:600}}>{children}</button>;}
function Sep(){return <div style={{width:1,height:16,background:T.border,margin:"0 1px"}}/>;}
function Lb({children}){return <span style={{color:T.text,fontSize:10}}>{children}</span>;}
function Chk({c,v,set,children}){return <label style={{color:c,display:"flex",alignItems:"center",gap:2,cursor:"pointer",fontSize:10}}><input type="checkbox" checked={v} onChange={e=>set(e.target.checked)} style={{accentColor:c,width:IS_TOUCH?16:12,height:IS_TOUCH?16:12}}/>{children}</label>;}

const PRESET_B64 = "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";
