// Fardriver Dash — READ-ONLY. Protocol per github.com/jackhumbert/fardriver-controllers
// HARD WRITE LOCK: any write method on a BLE characteristic throws; this app never transmits.
const WRITE_LOCK=Object.freeze(true);
// READ_ALLOW: exact byte sequences permitted to be sent. EMPTY on purpose: no documented, side-effect-free
// read-request exists (only the 0x13 login/status command, which also touches password/binding) — see README.
const READ_ALLOW=Object.freeze([]);
const allowed=b=>READ_ALLOW.some(a=>a.length===b.length&&a.every((x,i)=>x===b[i]));
function lockChar(ch){for(const m of['writeValue','writeValueWithResponse','writeValueWithoutResponse'])try{const orig=ch[m]&&ch[m].bind(ch);Object.defineProperty(ch,m,{value:v=>{const b=Array.from(new Uint8Array(v.buffer||v));return allowed(b)&&orig?orig(v):Promise.reject(new Error('Blocked by write lock: '+b.length+' bytes'))},writable:false,configurable:false})}catch(e){}return ch}
const ADDR=[0xE2,0xE8,0xEE,0xE4,0x06,0x0C,0x12,0xE2,0xE8,0xEE,0x18,0x1E,0x24,0x2A,0xE2,0xE8,0xEE,0x30,0x5D,0x63,0x69,0xE2,0xE8,0xEE,0x7C,0x82,0x88,0x8E,0xE2,0xE8,0xEE,0x94,0x9A,0xA0,0xA6,0xE2,0xE8,0xEE,0xAC,0xB2,0xB8,0xBE,0xE2,0xE8,0xEE,0xC4,0xCA,0xD0,0xE2,0xE8,0xEE,0xD6,0xDC,0xF4,0xFA];
const FAULTS=[ // addr E2 byte 4 then byte 5, LSB first
 'Motor hall sensor fault (check hall plug/wiring)','Throttle fault (check throttle wiring / stuck throttle)','Over-current protection restart','Phase current surge protection','Voltage protection (battery too high/low)','Alarm/anti-theft protection','Motor over-temperature','Controller over-temperature',
 'Phase current overflow protection','Phase zero-point error (needs re-learn?)','Phase short protection','Line current zero-point error','MOSFET high-side fault','MOSFET low-side fault','MOE current protection',null /*brake*/];
const MODELS={ND72450:{vmax:90,vmin:30,ph:450},ND961000:{vmax:120,vmin:40,ph:1000}};
const PACK={48:{vmin:39,vmax:58.8},72:{vmin:60,vmax:84}};
// 48V class: 13S/14S Li-ion 39–58.8V (accept 36–58.8). 72V class: 20S 60–84V (accept 62–88). Between/outside = ambiguous → ask.
function detectPack(v){if(!Number.isFinite(v))return null;if(v>=36&&v<=58.8)return'48';if(v>=62&&v<=88)return'72';return null}
let detected=null,asked=false;
// All modes: full launch phase current + 200A battery + SMOOTH progressive throttle (ThrottleResponse=Line, gentle Max_Acc).
// Modes differ only mid/top end. Names from fardriver.hpp; scaling of %/accel fields UNCONFIRMED.
const PROFILES={Eco:{batA:200,launch:1,mid:0.6,top:0.5,speed:0.6,fw:'off'},Normal:{batA:200,launch:1,mid:0.8,top:0.75,speed:0.85,fw:'off'},Sport:{batA:200,launch:1,mid:1,top:1,speed:1,fw:'on (unconfirmed param)'}};
const $=id=>document.getElementById(id);
const S={v:null,a:null,raw:0,gear:null,fwd:0,rev:0,brake:0,ct:null,mt:null,soc:null,faults:[],pk:0};
const cfg=()=>{const D={bms:200,bmschg:30,phmax:400,pp:16,gr:6.5,diff:3.909,wheel:2.55,rf:4};const g=k=>{const x=parseFloat($(k).value);return Number.isFinite(x)&&x>0&&x<1e5?x:(k in D&&['pp','gr','diff','wheel','rf'].includes(k)?D[k]:0)};const sel=$('pack').value;return{chg:g('bmschg'),model:$('model').value,packSel:sel,pack:sel==='auto'?(detected||'48'):sel,bms:g('bms'),ph:g('phmax'),pp:g('pp'),wheel:g('wheel'),gr:g('gr'),diff:g('diff'),rf:g('rf')}};
['model','pack','bms','bmschg','phmax','pp','gr','diff','wheel','rf','svc','chr'].forEach(k=>{const s=localStorage['fd_'+k];if(s!=null)$(k).value=s;$(k).onchange=()=>{localStorage['fd_'+k]=$(k).value;renderProf();}});

function crcOK(p){if(p.length!==16)return false;let c=0x7F3C;for(let i=0;i<14;i++){c^=p[i];for(let j=0;j<8;j++)c=c&1?(c>>1)^0xA001:c>>1;}return c===(p[14]|p[15]<<8);}
function crcSet(p){let c=0x7F3C;for(let i=0;i<14;i++){c^=p[i];for(let j=0;j<8;j++)c=c&1?(c>>1)^0xA001:c>>1;}p[14]=c&255;p[15]=c>>8;return p;}
const i16=(lo,hi)=>{const x=lo|hi<<8;return x&0x8000?x-0x10000:x};
const rawLog=[];
function makeFeeder(onP){let buf=[];return bytes=>{for(const b of bytes)buf.push(b);if(buf.length>4096)buf=buf.slice(-64);while(buf.length>=16){const k=buf.indexOf(0xAA);if(k<0){buf=[];return}if(k>0)buf.splice(0,k);if(buf.length<16)return;const p=buf.slice(0,16);if(crcOK(p)){buf.splice(0,16);onP(p)}else buf.shift();}}}
const feed=makeFeeder(p=>parse(p));
const UNIQUE=[...new Set(ADDR)];const CAP={};
function parse(p){const id=p[1]&0x3F;if(id>=ADDR.length)return;const d=p.slice(2);S.pk++;
 const a=ADDR[id];CAP[a]={id,hex:p.map(x=>x.toString(16).padStart(2,'0')).join(' '),data:d.slice(0,12),seen:(CAP[a]?.seen||0)+1,t:Date.now()};
 switch(ADDR[id]){
 case 0xE2:S.fwd=d[0]&1;S.rev=d[0]>>1&1;S.gear=((d[0]>>2)&3)+1;S.raw=i16(d[6],d[7]);
  const bits=d[2]|d[3]<<8;S.brake=bits>>15&1;S.faults=FAULTS.filter((f,i)=>f&&(bits>>i&1));break;
 case 0xE8:S.v=(d[0]|d[1]<<8)/10;autoPack(S.v);S.a=i16(d[4],d[5])/4;break;
 case 0xD6:S.ct=i16(d[10],d[11]);break;
 case 0xF4:S.mt=i16(d[0],d[1]);S.soc=d[3];break;}
}
function autoPack(v){if($('pack').value!=='auto'||detected)return;const r=detectPack(v);if(r){detected=r;return}
 if(!asked&&v>5){asked=true;setTimeout(()=>{const a=prompt(`Pack voltage ${v.toFixed(1)}V is ambiguous. Enter 48 or 72 (Cancel = keep asking via Setup):`);if(a==='48'||a==='72'){detected=a}},0)}}
function render(){const pc=cfg();$('packlbl').textContent=pc.packSel==='auto'?(detected?`Pack: ${detected}V (auto)`:'Pack: detecting…'):`Pack: ${pc.packSel}V (manual)`;const c=cfg();const rpm=Math.max(0,S.raw)*c.rf/c.pp;const kmh=rpm/(c.gr*c.diff)*c.wheel*60/1000;
 $('speed').textContent=kmh.toFixed(0);$('rpm').textContent=rpm.toFixed(0);$('gear').textContent=S.gear??'-';$('dir').textContent=S.rev?'· REV':'';
 const f=(x,n,u)=>x==null?'--<small> '+u+'</small>':x.toFixed(n)+'<small> '+u+'</small>';
 $('volt').innerHTML=f(S.v,1,'V');$('amp').innerHTML=f(S.a,1,'A');$('kw').innerHTML=f(S.v!=null&&S.a!=null?S.v*S.a/1000:null,2,'kW');
 $('ctemp').innerHTML=f(S.ct,0,'°C');$('mtemp').innerHTML=f(S.mt,0,'°C');$('soc').textContent=S.soc!=null?'SOC '+S.soc+'%':'';
 $('regen').textContent=(S.a<0?'♻ Regen ':'')+(S.brake?'🛑 Brake':'')||'—';
 const pv=PACK[c.pack];const warn=[...S.faults];if(S.v!=null&&(S.v<pv.vmin||S.v>pv.vmax))warn.push(`Voltage ${S.v.toFixed(1)}V outside ${c.pack}V pack range ${pv.vmin}–${pv.vmax}V`);
 if(S.a!=null&&S.a>c.bms)warn.push(`Battery current above your BMS limit (${c.bms}A)`);
 $('errbox').className='err'+(warn.length?' on':'');$('errtitle').textContent=warn.length?'⚠ '+warn.length+' warning(s)':'✅ No faults';$('errlist').innerHTML=warn.map(w=>'• '+w).join('<br>');
 $('pkt').textContent='Valid packets: '+S.pk;}
setInterval(render,200);

// Simulator: builds genuine CRC'd 16-byte frames and feeds them through the real parser
let demo=null,t=0;
function frame(addr,d){const id=ADDR.indexOf(addr);const p=new Array(16).fill(0);p[0]=0xAA;p[1]=id;d.forEach((x,i)=>p[2+i]=x&255);return crcSet(p);}
function demoTick(){t+=0.1;const c=cfg();const pv=PACK[c.pack];const thr=(Math.sin(t/3)+1)/2;const amps=Math.round((thr*c.bms*0.9-(thr<0.15?15:0))*4);
 const v=Math.round(((pv.vmax+pv.vmin)/2+0.5-thr*2)*10);const raw=Math.round(thr*20000);
 const fault=(Math.floor(t)%30>26)?0x40:0;// motor-temp warning every 30s
 feed(frame(0xE2,[0x01|(2<<2),0,fault,0,0,0,raw,raw>>8]));
 feed(frame(0xE8,[v,v>>8,0,0,amps,amps>>8]));
 feed(frame(0xD6,[0,0,0,0,0,0,0,0,0,0,38+Math.round(thr*10),0]));
 feed(frame(0xF4,[55+Math.round(thr*20),0,0,72]));}
$('btDemo').onclick=()=>{if(demo){clearInterval(demo);demo=null;$('status').textContent='Disconnected';$('status').className='badge';$('btDemo').textContent='Demo mode';return}
 demo=setInterval(demoTick,100);$('status').textContent='DEMO';$('status').className='badge demo';$('btDemo').textContent='Stop demo';};

// BLE (read-only: subscribe to notifications, never write)
let bleBusy=false;
$('btConnect').onclick=async()=>{if(bleBusy)return;bleBusy=true;
 if(!navigator.bluetooth){alert('Web Bluetooth not available.\niPhone: open this page in the Bluefy app.\nAndroid: use Chrome.');return}
 try{const svc=$('svc').value.trim(),chr=$('chr').value.trim().toLowerCase();
  const FFF0='0000fff0-0000-1000-8000-00805f9b34fb',FD00='0000fd00-0000-1000-8000-00805f9b34fb',FFE0='0000ffe0-0000-1000-8000-00805f9b34fb';
  const FFF1='0000fff1-0000-1000-8000-00805f9b34fb'; // controller WRITE channel — never used, also blocked by lock
  const okU=u=>/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/.test(u);
  const svcs=[...new Set([svc.toLowerCase(),FFF0,FD00,FFE0].filter(okU))];
  const dev=await navigator.bluetooth.requestDevice({filters:[{namePrefix:'Controller'},{services:[FD00]},{services:[FFE0]}],optionalServices:svcs});
  $('status').textContent='Connecting…';const g=await dev.gatt.connect();
  // Subscribe to EVERY notify/indicate char (startNotifications only). Count valid 0xAA packets per char; auto-select the first with ≥3 valid.
  const subs=[];window.__subs=subs;let sel=null;
  for(const su of svcs){let s;try{s=await g.getPrimaryService(su)}catch(e){continue}
   let list=[];try{list=await s.getCharacteristics()}catch(e){}
   for(const c of list){if(!(c.properties&&(c.properties.notify||c.properties.indicate)))continue;lockChar(c);
    const rec={svc:su,uuid:c.uuid,valid:0,bytes:0};rec.feed=makeFeeder(p=>{rec.valid++;
     if(!sel&&(rec.valid>=3||(chr&&c.uuid===chr&&rec.valid>=1))){sel=rec;window.__found=su+' / '+c.uuid;localStorage.fd_found=window.__found}
     if(sel===rec)parse(p)});
    c.addEventListener('characteristicvaluechanged',e=>{const b=new Uint8Array(e.target.value.buffer);rec.bytes+=b.length;
     rawLog.push(c.uuid.slice(4,8).toUpperCase()+': '+Array.from(b,x=>x.toString(16).padStart(2,'0')).join(' '));if(rawLog.length>40)rawLog.shift();rec.feed(b)});
    try{await c.startNotifications();subs.push(rec)}catch(e){rawLog.push(c.uuid.slice(4,8)+': subscribe failed '+e.message)}}}
  if(!subs.length)throw new Error('No notify characteristic found under '+svcs.join(', '));
  const showBle=()=>{$('bleinfo').innerHTML=(dev.name||'?')+'<br>'+subs.map(r=>`${r.uuid.slice(4,8).toUpperCase()} (${r.svc.slice(4,8).toUpperCase()}): ${r.valid} valid / ${r.bytes} B${sel===r?' ← selected':''}`).join('<br>');$('rawlog').textContent=rawLog.join('\n')};window.__bleIv=setInterval(showBle,500);
  $('status').textContent=dev.name||'Connected';$('status').className='badge ok';
  detected=null;asked=false;dev.addEventListener('gattserverdisconnected',()=>{bleBusy=false;clearInterval(window.__bleIv);$('status').textContent='Disconnected';$('status').className='badge'});
 }catch(e){bleBusy=false;$('status').textContent='Error';alert('BLE: '+e.message)}};

// Profiles (preview only, clamped)
function limits(){const c=cfg(),m=MODELS[c.model];return{bat:c.bms,ph:Math.min(c.ph,m.ph)}}
function featureMap(){const c=cfg(),pv=PACK[c.pack];const s=Math.min(1,Math.max(0,(+$('op_str').value||0)/100));
 // regen battery-side current capped by BMS charge limit; disabled at top of charge
 const want=Math.min(60,Math.max(0,+$('op_amp').value||0));const backA=Math.floor(Math.min(want,c.chg)*s);const full=S.v!=null&&S.v>pv.vmax-1;
 const hold=Math.min(8,Math.max(0,Math.round(+$('hold_str').value||0)));
 return{want,one:$('op_on').checked,backA,full,hold:$('hold_on').checked,park:hold,
  writes:[...($('op_on').checked?[['0x1A FollowConfig',3],['0x30 StopBackCurr (×4)',backA*4],['0x31 MaxBackCurr (×4)',backA*4],['0x2A+ Max_Dec (smooth onset ramp, units UNCONFIRMED)','gentle'],['0x8E nratio_0..3 (low→high rpm regen %, near-flat strong to stop, lowest step 90% to avoid end lurch, UNCONFIRMED)','90, 100, 100, 100']]:[['0x1A FollowConfig',0]]),
   ...($('hold_on').checked?[['0x60 ParkConfig',2],['0xCF ParkCoeff',hold],['0xC6 SlowDownRpm (anti-rollback engage threshold, rpm, UNCONFIRMED)',50],['ParkTime (s×500, UNCONFIRMED)',5*500]]:[['0x60 ParkConfig',3]])]};}
function renderFeat(){const f=featureMap();$('op_val').textContent=$('op_str').value;
 $('op_map').textContent=`→ regen battery current ${f.backA} A (selected ${f.want} A, cap = BMS charge ${cfg().chg} A)`+(f.want>cfg().chg?` — ⚠ ${f.want} A exceeds your BMS charge limit (${cfg().chg} A), capped. If your pack/BMS allows ${f.want} A charge, set the BMS charge field to ${f.want} in Setup.`:'')+(f.full?' — ⚠ pack near full: regen would be blocked':'');
 $('hold_map').textContent=`→ ParkCoeff ${f.park}/15 (app caps at 8 to limit heating); hold timeout fixed at 5 s → ParkTime = 2500 (header says ÷500 = seconds; unconfirmed)`;}
['op_on','op_str','op_amp','hold_on','hold_str'].forEach(k=>{$(k).oninput=renderFeat;$(k).onchange=renderFeat});
function renderProf(){setTimeout(renderFeat);const L=limits();let h='<tr><th>Mode</th><th>Batt A</th><th>Launch ph A</th><th>Mid %</th><th>Top %</th><th>Speed %</th><th></th></tr>';
 for(const[n,p]of Object.entries(PROFILES))h+=`<tr><td>${n}</td><td>${Math.floor(Math.min(p.batA,L.bat))}</td><td>${Math.floor(L.ph*p.launch)}</td><td>${p.mid*100}</td><td>${p.top*100}</td><td>${p.speed*100}</td><td><input type=radio name=pf value=${n} style="width:auto"></td></tr>`;
 $('proftbl').innerHTML=h;const c=cfg(),m=MODELS[c.model];if(+c.pack===72&&c.model==='ND72450')h;$('dry').textContent=`Hard caps: battery ≤ ${L.bat}A (BMS), phase ≤ ${L.ph}A (min of motor ${c.ph}A, ${c.model} ${m.ph}A), pack ${c.pack}V within controller ${m.vmin}–${m.vmax}V.`;}
renderProf();
$('devsw').onchange=e=>{if(e.target.checked&&!confirm('Developer mode only enables a DRY-RUN. No data is written to the controller. Continue?')){e.target.checked=false}$('btApply').disabled=!e.target.checked};
$('btApply').onclick=()=>{const sel=document.querySelector('input[name=pf]:checked');if(!sel)return alert('Pick a profile');const F=featureMap();if(F.full&&F.one)return alert('Pack near full — regen change blocked.');if(!confirm('DRY-RUN: show what would be written? Nothing is sent.'))return;
 const L=limits(),p=PROFILES[sel.value];const backup={time:new Date().toISOString(),live:{...S},note:'Full param backup requires reading config addresses (unverified mapping)'};
 localStorage.fd_backup=JSON.stringify(backup);
 $('dry').textContent=`DRY-RUN ${sel.value}: would set battery ${Math.floor(Math.min(p.batA,L.bat))}A, launch phase ${Math.floor(L.ph*p.launch)}A, speed ${p.speed*100}%.\n  0x19 MaxLineCurr (/4) = ${Math.min(p.batA,L.bat)*4}\n  0x2A+ MaxPhaseCurr (/4) = ${Math.floor(L.ph)*4}\n  0x30+ LowSpeedPhaseCurr (%×128/100, UNCONFIRMED) = 128\n  0x30+ LowSpeedLineCurr = 128\n  0x30+ MidSppedPhaseCurr = ${Math.round(p.mid*128)}\n  0x30+ MidSpeedLineCurr = ${Math.round(p.mid*128)}\n  0x8E RatioMax (high-rpm %, UNCONFIRMED) = ${p.top*100}\n  0x1A ThrottleResponse = 0 (Line: smooth/progressive)\n  0x2A+ Max_Acc = gentle (units UNCONFIRMED; tune in official app)\n  Field weakening: ${p.fw}\n${F.writes.map(w=>'  '+w[0]+' = '+w[1]).join('\n')}\nBackup saved to this browser.\nNOTHING SENT — write protocol for these parameters is unverified.`;};
document.querySelectorAll('nav button').forEach(b=>b.onclick=()=>{document.querySelectorAll('.tab').forEach(x=>x.classList.remove('on'));$('t-'+b.dataset.t).classList.add('on')});
if('serviceWorker'in navigator)navigator.serviceWorker.register('sw.js').catch(()=>{});
if(location.hash.includes('demo'))$('btDemo').click();
if(location.hash.includes('prof'))document.querySelector('nav button[data-t=prof]').click();

// ---- Tune backup: PASSIVE capture of streamed blocks (no requests sent) ----
function backupObj(){const blocks={};for(const a of UNIQUE)if(CAP[a])blocks['0x'+a.toString(16).toUpperCase().padStart(2,'0')]={tableId:CAP[a].id,words16:Array.from({length:6},(_,i)=>CAP[a].data[2*i]|CAP[a].data[2*i+1]<<8),rawPacketHex:CAP[a].hex,timesSeen:CAP[a].seen};
 return{app:'Fardriver Dash',status:'UNVERIFIED — passive capture, not yet checked on real hardware',created:new Date().toISOString(),device:$('status').textContent,model:$('model').value,
  coverage:`${Object.keys(blocks).length}/${UNIQUE.length} address blocks`,note:'Each block = 6×16-bit words starting at the address. All packets CRC-verified (0xAA frame, CRC16 0xA001 init 0x7F3C). Live-telemetry blocks (E2/E8/EE/D6/F4…) change constantly.',blocks}}
function renderBk(){const n=UNIQUE.filter(a=>CAP[a]).length;$('bkprog').textContent=`Captured ${n}/${UNIQUE.length} blocks`+(n===UNIQUE.length?' ✅ complete':' — keep connected ~30 s');}
setInterval(()=>$('bkprog')&&renderBk(),500);
$('btBkSave').onclick=()=>{const b=backupObj();localStorage.fd_tune=JSON.stringify(b);$('bkmsg').textContent='Saved in this browser: '+b.coverage+(b.coverage.startsWith(UNIQUE.length+'/')?'':' (INCOMPLETE)');};
$('btBkExport').onclick=async()=>{const b=localStorage.fd_tune?JSON.parse(localStorage.fd_tune):backupObj();
 const hex=Object.entries(b.blocks).map(([a,x])=>a+': '+x.rawPacketHex).join('\n');const name='fardriver-tune-'+b.created.slice(0,19).replace(/:/g,'-');
 const files=[new File([JSON.stringify(b,null,1)],name+'.json',{type:'application/json'}),new File([hex],name+'.hex.txt',{type:'text/plain'})];
 if(navigator.canShare&&navigator.canShare({files}))try{await navigator.share({files,title:name});return}catch(e){}
 for(const f of files){const u=URL.createObjectURL(f);const a=document.createElement('a');a.href=u;a.download=f.name;a.click();setTimeout(()=>URL.revokeObjectURL(u),2000)}};
