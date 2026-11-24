// §17: TYPE-RELATIVE re-expression of the §14 tree. request s_J = phi_J * m_J (phi=1: whole type) from logs/phi_rule.json;
// node label = her classification of each observed reply (nearest of the 0.5-tilt U / O replies, L1, ties -> U).
// Over budget: partial types scaled pro rata, then completes dropped smallest-mass first.  Under budget: no fill.
const fs=require('fs');const T=0.76,N=1.8;
const phi=JSON.parse(fs.readFileSync('logs/phi_rule.json'));
const popc=x=>{let c=0;while(x){c+=x&1;x>>=1}return c};
const TYPES=[...Array(128).keys()];
const ORD={U:[...TYPES].sort((a,b)=>popc(a)-popc(b)||a-b),O:[...TYPES].sort((a,b)=>popc(b)-popc(a)||a-b),
 G:[...TYPES].sort((a,b)=>((a==0)-(b==0))||popc(a)-popc(b)||a-b)};
const fracs=(process.argv[2]||"0.25,0.5,0.75,1").split(',').map(Number);
const orders=(process.argv[3]||"UOG").split('');
const ASC=process.env.ASC==='1';const FILL=+(process.env.FILL||0);const only05=process.argv[4]==="only05";
const modes=[{f:0,o:'U',name:'P'}];
for(const o of orders)for(const f of fracs)modes.push({f,o,name:o+f});
const ms=only05?modes.filter(x=>x.f==0.5&&x.o!='G'):modes;
let top=[],cnt=0,wins=0,over=0;const TOPN=25;const hist={};
function leaf(m,real,seq,bits){ if(process.env.DBG){const tb=seq.map(x=>x[0]).join("");if(tb!==bits)console.error("LABELMISMATCH",tb,bits)}
  const sup=new Uint8Array(128);for(let K=0;K<128;K++)sup[K]=real[K];
  for(let b=1;b<128;b<<=1)for(let c=0;c<128;c++)if(!(c&b))sup[c]|=sup[c|b];
  let best=1e9,bd=0;
  for(let d=0;d<7;d++){const I=127&~(1<<d);let D=0;for(let J=0;J<128;J++){if(m[J]>0&&sup[I&~J])D+=m[J]}if(D<best){best=D;bd=d+1}}
  const v=best-T;cnt++;if(v>0)wins++;
  {const dv=seq.filter(x=>x!=='U0.5'&&x!=='O0.5').length;const h=hist[dv]||(hist[dv]={n:0,w:0,worst:-9});h.n++;if(v>0)h.w++;if(v>h.worst)h.worst=v;}
  if(top.length<TOPN||v>top[top.length-1].v){top.push({v,bd,seq:seq.join(','),bits});top.sort((a,b)=>b.v-a.v);if(top.length>TOPN)top.pop()}
}
function reply(m,s,a,tot,md){
  const slack=N-tot-1,lam=1/(N-tot);const ov=new Float64Array(128);let left=slack;
  if(md.f>0)for(const J of ORD[md.o]){if(a[J]<=0)continue;const x=Math.min(left,a[J]);ov[J]=x;left-=x;if(left<=1e-15)break}
  const r=new Float64Array(128);
  for(let J=0;J<128;J++){const o=(1-md.f)*(1-lam)*a[J]+md.f*ov[J];r[J]=a[J]-o}
  return r;
}
function rec(e,m,real,seq,lab){
  if(e==7){leaf(m,real,seq,lab);return}
  const ph=phi[lab],b=1<<e;
  // request
  const s=new Float64Array(128);let C=0,P=0;
  for(let J=0;J<128;J++){if(m[J]<=0)continue;const p=ph[J];if(!p)continue;if(p>=1){s[J]=m[J];C+=m[J]}else{s[J]=p*m[J];P+=s[J]}}
  if(C+P>T){over++;
    if(C<T){const f=(T-C)/P;for(let J=0;J<128;J++)if(s[J]>0&&ph[J]<1)s[J]*=f}
    else{for(let J=0;J<128;J++)if(ph[J]<1)s[J]=0;
      const cs=TYPES.filter(J=>s[J]>0).sort((x,y)=>m[x]-m[y]);let t=C;for(const J of cs){if(t<=T)break;t-=s[J];s[J]=0}}}
  if(process.env.DBG2&&lab=="OO"&&!global.pp){global.pp=1;console.error(JSON.stringify([...s].map((x,i)=>x>0?[i,x,m[i]]:null).filter(x=>x)))}
  if(process.env.DBG3&&seq.join("")=="O0.5O0.5U0.5O0.5U0.5"&&e==6){console.error("rel e",e,lab,JSON.stringify([...s].map((x,i)=>x>0?[i,+x.toFixed(5)]:null).filter(x=>x)))}
  if(FILL){let t=0;for(let J=0;J<128;J++)t+=s[J];let left=FILL-t;
    if(left>1e-9){const un=TYPES.filter(J=>m[J]-s[J]>1e-9).sort((x,y)=>ASC?(m[x]-s[x])-(m[y]-s[y]):(m[y]-s[y])-(m[x]-s[x]));
      for(const J of un){if(left<=1e-12)break;const x=Math.min(left,m[J]-s[J]);s[J]+=x;left-=x}}}
  let tot=0;const a=new Float64Array(128);
  for(let J=0;J<128;J++){a[J]=m[J]-s[J];tot+=s[J]}
  const rU=reply(m,s,a,tot,{f:.5,o:'U'}),rO=reply(m,s,a,tot,{f:.5,o:'O'});
  for(const md of ms){
    const r=reply(m,s,a,tot,md);let dU=0,dO=0;
    for(let J=0;J<128;J++){dU+=Math.abs(r[J]-rU[J]);dO+=Math.abs(r[J]-rO[J])}
    const l=dU<=dO?'U':'O';
    const m2=new Float64Array(128),r2=real.slice();
    for(let J=0;J<128;J++){if(m[J]<=0&&!real[J])continue;
      m2[J]+=m[J]-r[J];if(a[J]>1e-12){r2[J|b]=1;if(r[J]>1e-12)m2[J|b]=r[J]}}
    rec(e+1,m2,r2,seq.concat(md.name),lab+l);
  }
}
const m0=new Float64Array(128);m0[0]=N-1;m0[1]=1;const r0=new Uint8Array(128);r0[1]=1;
rec(1,m0,r0,[],"");
console.log(JSON.stringify({leaves:cnt,wins,overbudget_nodes:over,hist,top:top.slice(0,12)}));
