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
// ═══════════ MT4 CSV SUPPORT ═══════════
function parseMT4CSV(text) {
  const lines = text.trim().split("\n");
  const bars = [];
  for (let i = 0; i < lines.length; i++) {
    const parts = lines[i].replace(/\r/g, "").split(",");
    if (parts.length < 6) continue;
    const dateStr = parts[0].trim(), timeStr = parts[1].trim();
    if (!/^\d{4}\./.test(dateStr)) continue;
    const [y, m, d] = dateStr.split(".").map(Number);
    const [hh, mm] = timeStr.split(":").map(Number);
    const time = Date.UTC(y, m - 1, d, hh, mm, 0);
    const o = +parts[2], h = +parts[3], l = +parts[4], c = +parts[5];
    if (isNaN(time) || isNaN(o)) continue;
    bars.push({ time, o, h, l, c, ind: {} });
  }
  return bars;
}

function detectCSVFormat(text) {
  const firstLine = text.trim().split("\n")[0];
  if (firstLine.toLowerCase().includes("time") && firstLine.toLowerCase().includes("open")) return "tv";
  if (/^\d{4}\./.test(firstLine.trim())) return "mt4";
  return "unknown";
}

// Aggregate 1m bars into higher TF bars
function aggTF(bars, ms) {
  const out = [];
  let cur = null;
  for (const b of bars) {
    const bk = Math.floor(b.time / ms) * ms;
    if (!cur || cur.bk !== bk) {
      if (cur) out.push(cur);
      cur = { bk, o: b.o, h: b.h, l: b.l, c: b.c };
    } else {
      cur.h = Math.max(cur.h, b.h);
      cur.l = Math.min(cur.l, b.l);
      cur.c = b.c;
    }
  }
  if (cur) out.push(cur);
  return out;
}

// SMA with running sum (O(n))
function smaArr(vals, p) {
  const out = [];
  let sum = 0;
  for (let i = 0; i < vals.length; i++) {
    sum += vals[i];
    if (i >= p) sum -= vals[i - p];
    out.push(i >= p - 1 ? sum / p : null);
  }
  return out;
}

// EMA
function emaArr(vals, p) {
  const out = [];
  const k = 2 / (p + 1);
  let e = null;
  for (let i = 0; i < vals.length; i++) {
    if (i < p - 1) { out.push(null); continue; }
    if (e === null) { let s = 0; for (let j = i - p + 1; j <= i; j++) s += vals[j]; e = s / p; }
    else e = vals[i] * k + e * (1 - k);
    out.push(e);
  }
  return out;
}

// Bollinger Bands (period=20, 2σ/3σ)
function bbArr(closes, p = 20) {
  const ma = smaArr(closes, p);
  const u2 = [], l2 = [], u3 = [], l3 = [];
  for (let i = 0; i < closes.length; i++) {
    if (ma[i] === null) { u2.push(null); l2.push(null); u3.push(null); l3.push(null); continue; }
    let vr = 0;
    for (let j = i - p + 1; j <= i; j++) vr += (closes[j] - ma[i]) ** 2;
    const sd = Math.sqrt(vr / p);
    u2.push(ma[i] + 2 * sd); l2.push(ma[i] - 2 * sd);
    u3.push(ma[i] + 3 * sd); l3.push(ma[i] - 3 * sd);
  }
  return { u2, l2, u3, l3 };
}

// Compute all indicators from 1m OHLC data (MT4 path)
function computeIndicators(bars) {
  console.time("computeIndicators");

  // XAU envelope deviations (from MT4 source)
  const ENV_DEV = { M5: 0.45, M15: 0.70, M30: 1.30, H1: 1.80 };
  const TF_MS = { M5: 300000, M15: 900000, M30: 1800000, H1: 3600000, H4: 14400000, D1: 86400000 };
  const ENV_TFS = ["M5", "M15", "M30", "H1"];
  const SMA200_TFS = ["H1"];

  // 1. Aggregate into each TF
  const tfData = {};
  for (const [name, ms] of Object.entries(TF_MS)) {
    const tfBars = aggTF(bars, ms);
    const closes = tfBars.map(b => b.c);
    const buckets = tfBars.map(b => b.bk);
    const data = { bars: tfBars, closes, buckets };

    // Envelope center: SMA(21)
    if (ENV_TFS.includes(name)) data.sma21 = smaArr(closes, 21);
    // SMA200
    if (SMA200_TFS.includes(name)) data.sma200 = smaArr(closes, 200);

    tfData[name] = data;
  }

  // 2. BB on M15
  const m15bb = bbArr(tfData.M15.closes, 20);

  // 3. Build bucket→index maps
  const tfMaps = {};
  for (const [name, data] of Object.entries(tfData)) {
    const map = new Map();
    data.bars.forEach((b, i) => map.set(b.bk, i));
    tfMaps[name] = map;
  }

  // 4. Assign indicator values to each 1m bar
  for (let bi = 0; bi < bars.length; bi++) {
    const bar = bars[bi];
    const ind = {};

    // Envelopes
    for (const tf of ENV_TFS) {
      const bk = Math.floor(bar.time / TF_MS[tf]) * TF_MS[tf];
      const idx = tfMaps[tf].get(bk);
      const sma = idx != null ? tfData[tf].sma21[idx] : null;
      const dev = ENV_DEV[tf];
      ind[`env${tf}U`] = sma != null ? sma * (1 + dev / 100) : null;
      ind[`env${tf}L`] = sma != null ? sma * (1 - dev / 100) : null;
    }

    // SMA200 H1
    const h1bk = Math.floor(bar.time / TF_MS.H1) * TF_MS.H1;
    const h1idx = tfMaps.H1.get(h1bk);
    ind.sma200H1 = h1idx != null && tfData.H1.sma200 ? tfData.H1.sma200[h1idx] : null;

    // BB from M15
    const m15bk = Math.floor(bar.time / TF_MS.M15) * TF_MS.M15;
    const m15idx = tfMaps.M15.get(m15bk);
    ind.bbU2 = m15idx != null ? m15bb.u2[m15idx] : null;
    ind.bbL2 = m15idx != null ? m15bb.l2[m15idx] : null;
    ind.bbU3 = m15idx != null ? m15bb.u3[m15idx] : null;
    ind.bbL3 = m15idx != null ? m15bb.l3[m15idx] : null;

    // SAR: not computed (complex, default OFF)
    ind.sar = null;

    bar.ind = ind;
  }

  console.timeEnd("computeIndicators");
  return bars;
}
function aggFn(data,upTo,ms=900000){const done=[];let f=null;for(let i=0;i<=upTo&&i<data.length;i++){const b=data[i],bk=Math.floor(b.time/ms)*ms;if(!f||f.bk!==bk){if(f)done.push({...f});f={bk,time:b.time,o:b.o,h:b.h,l:b.l,c:b.c,ind:{...b.ind}};}else{f.h=Math.max(f.h,b.h);f.l=Math.min(f.l,b.l);f.c=b.c;f.ind={...b.ind};}}return{done,forming:f};}
function buildTrendMap(data,upTo,ms){const{done,forming}=aggFn(data,upTo,ms);const all=forming?[...done,forming]:[...done];const cl=all.map(b=>b.c);const e=calcEma(cl,13),s21=calcSma(cl,21),s75=calcSma(cl,75);const m=new Map();for(let i=0;i<all.length;i++)m.set(all[i].bk,trendClass(e[i],s21[i],s75[i]));return m;}

const SPD_LEVELS=[500,350,250,180,120,80,50,30,15,5];
function spdToLevel(ms){let best=0;let bd=Infinity;SPD_LEVELS.forEach((v,i)=>{const d=Math.abs(v-ms);if(d<bd){bd=d;best=i;}});return best+1;}
function levelToSpd(lv){return SPD_LEVELS[Math.max(0,Math.min(9,lv-1))];}

function Spinner({value,setValue,min,max,step=1,fmt,color}){
  const ref=useRef(null);
  const dragRef=useRef(null);
  const vals=[];for(let v=min;v<=max+step*0.01;v=Math.round((v+step)*1000)/1000)vals.push(Math.round(v*1000)/1000);
  const idx=vals.findIndex(v=>Math.abs(v-value)<step*0.01);
  const prev=vals[idx-1]??null;const next=vals[idx+1]??null;
  const onTS=e=>{e.stopPropagation();dragRef.current={y:e.touches[0].clientY,idx};};
  const onTM=e=>{e.stopPropagation();if(!dragRef.current)return;const dy=dragRef.current.y-e.touches[0].clientY;const steps=Math.round(dy/18);const ni=Math.max(0,Math.min(vals.length-1,dragRef.current.idx+steps));setValue(vals[ni]);};
  const onTE=e=>{e.stopPropagation();dragRef.current=null;};
  const sz=11;
  return(
    <div ref={ref} style={{display:"flex",flexDirection:"column",alignItems:"center",userSelect:"none",touchAction:"none",minWidth:36}}
      onTouchStart={onTS} onTouchMove={onTM} onTouchEnd={onTE}>
      <div style={{fontSize:sz,color:color||"#5d6878",opacity:0.4,height:14,lineHeight:"14px"}}>{prev!=null?fmt(prev):""}</div>
      <div style={{fontSize:sz+1,color:color||"#c8d2e0",fontWeight:700,height:16,lineHeight:"16px",borderTop:"1px solid rgba(255,255,255,0.1)",borderBottom:"1px solid rgba(255,255,255,0.1)",padding:"0 4px"}}>{fmt(value)}</div>
      <div style={{fontSize:sz,color:color||"#5d6878",opacity:0.4,height:14,lineHeight:"14px"}}>{next!=null?fmt(next):""}</div>
    </div>
  );
}

export default function App(){
  const[d1m,setD1m]=useState(null);
  const[loading,setLoading]=useState(true);
  const[idx,setIdx]=useState(0);
  const[play,setPlay]=useState(false);
  const[spd,setSpd]=useState(80);
  const[vis,setVis]=useState(30);
  const[yZoom,setYZoom]=useState(1.0);
  const[boostMult,setBoostMult]=useState(4);
  const[boosting,setBoosting]=useState(false);
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

  useEffect(()=>{(async()=>{try{
    const base=import.meta.env.BASE_URL||"/";
    const res=await fetch(base+"XAUUSD1.csv");
    const text=await res.text();
    const bars=parseMT4CSV(text);
    if(bars.length){computeIndicators(bars);setD1m(bars);setIdx(Math.min(90,bars.length-1));}
  }catch(e){console.error("CSV load fail",e);}setLoading(false);})();},[]);
  useEffect(()=>{const ro=new ResizeObserver(e=>{const w=Math.floor(e[0].contentRect.width);const vh=window.innerHeight;const h=Math.floor(Math.min(vh*0.72,Math.max(300,w*0.75)));setDim({w,h});});if(boxRef.current)ro.observe(boxRef.current);return()=>ro.disconnect();},[]);
  useEffect(()=>{if(tmr.current)clearInterval(tmr.current);if(play&&d1m){const interval=boosting?Math.max(5,Math.round(spd/boostMult)):spd;tmr.current=setInterval(()=>{setIdx(p=>{if(p>=d1m.length-1){setPlay(false);return p;}return p+1;});},interval);}return()=>{if(tmr.current)clearInterval(tmr.current);};},[play,spd,d1m,boosting,boostMult]);

  const onFile=useCallback(e=>{const f=e.target.files[0];if(!f)return;const r=new FileReader();r.onload=ev=>{
    const text=ev.target.result;
    const fmt=detectCSVFormat(text);
    let p;
    if(fmt==="mt4"){
      p=parseMT4CSV(text);
      if(p.length){
        setLoading(true);
        // Use setTimeout to let loading UI render before heavy computation
        setTimeout(()=>{
          computeIndicators(p);
          setD1m(p);setIdx(Math.min(90,p.length-1));setPlay(false);setMLines([]);setVLines([]);setPendingPt(null);setPanOff({x:0,y:0});
          setLoading(false);
        },50);
        return;
      }
    }else{
      p=parseCSV(text);
    }
    if(p&&p.length){setD1m(p);setIdx(Math.min(90,p.length-1));setPlay(false);setMLines([]);setVLines([]);setPendingPt(null);setPanOff({x:0,y:0});}
  };r.readAsText(f);},[]);

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
  if(loading)return <div style={{color:T.text,padding:40,fontFamily:"monospace",background:T.bg,minHeight:"100vh"}}>データ読込中・インジケーター計算中...</div>;

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
        {IS_TOUCH?(
          <>
            <Sep/>
            <Lb>速度</Lb><Spinner value={spdToLevel(spd)} setValue={lv=>setSpd(levelToSpd(lv))} min={1} max={10} step={1} fmt={v=>`速${v}`} color={T.forming}/>
            <Sep/>
            <Lb>表示</Lb><Spinner value={vis} setValue={setVis} min={20} max={60} step={5} fmt={v=>`${v}本`} color={T.forming}/>
            <Sep/>
            <Lb>Y軸</Lb><Spinner value={yZoom} setValue={setYZoom} min={0.5} max={5.0} step={0.5} fmt={v=>`${v.toFixed(1)}x`} color={T.forming}/>
            <Btn c={T.text} onClick={()=>{setYZoom(1.0);setPanOff({x:0,y:0});}}>reset</Btn>
          </>
        ):(
          <>
            <Sep/><Lb>速度</Lb><input type="range" min={5} max={500} value={spd} onChange={e=>setSpd(+e.target.value)} style={{width:60,accentColor:T.forming}}/><Lb>{spd}ms</Lb>
            <Sep/><Lb>表示</Lb><input type="range" min={20} max={60} value={vis} onChange={e=>setVis(+e.target.value)} style={{width:50,accentColor:T.forming}}/><Lb>{vis}</Lb>
            <Sep/><Lb>Y軸</Lb><input type="range" min={50} max={500} value={yZoom*100} onChange={e=>setYZoom(+e.target.value/100)} style={{width:55,accentColor:T.forming}}/><Lb>{yZoom.toFixed(1)}x</Lb>
            <Sep/><Lb style={{color:"#fdd835"}}>倍速</Lb><input type="range" min={2} max={16} value={boostMult} onChange={e=>setBoostMult(+e.target.value)} style={{width:50,accentColor:"#fdd835"}}/><Lb style={{color:"#fdd835"}}>×{boostMult}</Lb>
            <Btn c={T.text} onClick={()=>{setYZoom(1.0);setPanOff({x:0,y:0});}}>reset</Btn>
          </>
        )}
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
        {/* Play button - top half of RSI panel */}
        <div
          onTouchStart={e=>{e.stopPropagation();}}
          onTouchEnd={e=>{e.preventDefault();e.stopPropagation();setPlay(p=>!p);}}
          onClick={()=>setPlay(p=>!p)}
          style={{position:"absolute",left:0,top:rsiPos.top,width:56,height:rsiPos.height*0.45,display:"flex",alignItems:"center",justifyContent:"center",cursor:"pointer",zIndex:5}}>
          <div style={{width:34,height:34,borderRadius:8,background:play?"rgba(239,51,64,0.15)":"rgba(0,200,83,0.15)",border:`1.5px solid ${play?T.red:T.green}`,display:"flex",alignItems:"center",justifyContent:"center",fontSize:16,color:play?T.red:T.green}}>
            {play?"⏸":"▶"}
          </div>
        </div>
        {/* Boost button - bottom half of RSI panel */}
        <div style={{position:"absolute",left:0,top:rsiPos.top+rsiPos.height*0.45,width:56,height:rsiPos.height*0.55,display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",gap:2,zIndex:5}}>
          <div
            onTouchStart={e=>{e.stopPropagation();e.preventDefault();setBoosting(true);}}
            onTouchEnd={e=>{e.stopPropagation();e.preventDefault();setBoosting(false);}}
            onMouseDown={()=>setBoosting(true)}
            onMouseUp={()=>setBoosting(false)}
            onMouseLeave={()=>setBoosting(false)}
            style={{width:34,height:26,borderRadius:6,background:boosting?"rgba(253,216,53,0.25)":"rgba(253,216,53,0.08)",border:`1.5px solid ${boosting?"#fdd835":"rgba(253,216,53,0.4)"}`,display:"flex",alignItems:"center",justifyContent:"center",fontSize:11,color:"#fdd835",cursor:"pointer",fontWeight:700}}>
            ⚡
          </div>
          {IS_TOUCH?(
            <Spinner value={boostMult} setValue={v=>setBoostMult(Math.round(v))} min={2} max={16} step={1} fmt={v=>`×${v}`} color="#fdd835"/>
          ):(
            <span style={{fontSize:9,color:"#fdd835"}}>×{boostMult}</span>
          )}
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

