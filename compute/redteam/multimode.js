// §16(a): multi-mode tilt vs the FIXED §14 tree. modes = (frac f of dump concentrated, ordering). float DFS, top leaves printed.
const fs=require('fs');
const T=0.76,N=1.8;
const tree=JSON.parse(fs.readFileSync('logs/adaptive_tree_full_T0.76_N1.8.json'));
const popc=x=>{let c=0;while(x){c+=x&1;x>>=1}return c};
const TYPES=[...Array(128).keys()];
const ORD={U:[...TYPES].sort((a,b)=>popc(a)-popc(b)||a-b),O:[...TYPES].sort((a,b)=>popc(b)-popc(a)||a-b),
 G:[...TYPES].sort((a,b)=>((a==0)-(b==0))||popc(a)-popc(b)||a-b)};
const fracs=(process.argv[3]||"0.25,0.5,0.75,1").split(',').map(Number);
const orders=(process.argv[4]||"UOG").split('');
const modes=[];
if(process.argv[5]!=="nozero") modes.push({f:0,o:'U',name:'P'});
for(const o of orders)for(const f of fracs)modes.push({f,o,name:o+f});
const mapv=process.argv[2]||"UU"; // GIFT->mapv[0], f=0 -> mapv[1]
const bitOf=md=>md.name==='P'?mapv[1]:(md.o==='G'?mapv[0]:md.o);
const Tn=T;const TAU=+(process.env.TAU||0);let pruned=0;const BYD={};
const req=[]; // req[prefixString]
function getreq(key){const r=new Float64Array(128);const d=tree[key];for(const k in d)r[+k]=d[k];return r}
const rc={};function R(key){return rc[key]||(rc[key]=getreq(key))}
let top=[];const TOPN=40;let cnt=0,wins=0;
function leaf(m,real,modesSeq,bits){ if(process.env.DBG&&bits=="UUUUUU"){let t=0;for(let J=0;J<128;J++)t+=m[J];console.log("sum",t,[...m].map((x,i)=>x>0?i+":"+x.toFixed(4):"").filter(x=>x).join(" "))}
  const sup=new Uint8Array(128);for(let K=0;K<128;K++)sup[K]=real[K];
  for(let b=1;b<128;b<<=1)for(let c=0;c<128;c++)if(!(c&b))sup[c]|=sup[c|b];
  let best=1e9,bd=0;
  for(let d=0;d<7;d++){const I=127&~(1<<d);let D=0;for(let J=0;J<128;J++){if(m[J]>0&&sup[I&~J])D+=m[J]}
    if(D<best){best=D;bd=d+1}}
  const v=best-Tn;cnt++;if(v>0)wins++;{const dv=modesSeq.filter(x=>x!=='U0.5'&&x!=='O0.5').length;if(!(dv in BYD)||v>BYD[dv].v)BYD[dv]={v,seq:modesSeq.join(',')}}
  if(top.length<TOPN||v>top[top.length-1].v){top.push({v,bd,seq:modesSeq.join(','),bits});top.sort((a,b)=>b.v-a.v);if(top.length>TOPN)top.pop()}
}
function rec(e,m,real,seq,bits){
  if(e==7){leaf(m,real,seq,bits);return}
  const rq=R(bits.slice(0,e-1)),b=1<<e;
  const s=new Float64Array(128);let tot=0;
  for(let J=0;J<128;J++){const mj=m[J];if(mj<=0&&!real[J]){continue}
    const x=rq[J];s[J]=(x>=mj-3e-5||(TAU>0&&x>=3e-5&&mj<=x+TAU))?mj:(x<3e-5?0:x);tot+=s[J]}
  if(TAU>0&&tot>T+1e-12){pruned++;return}
  const a=new Float64Array(128);for(let J=0;J<128;J++)a[J]=m[J]-s[J];
  const slack=N-tot-1,lam=1/(N-tot);
  for(const md of modes){
    const ov=new Float64Array(128);let left=slack;
    if(md.f>0)for(const J of ORD[md.o]){if(a[J]<=0)continue;const x=Math.min(left,a[J]);ov[J]=x;left-=x;if(left<=1e-15)break}
    const m2=new Float64Array(128),r2=real.slice();
    for(let J=0;J<128;J++){if(m[J]<=0&&!real[J]&&s[J]==0&&a[J]==0)continue;
      const o=(1-md.f)*(1-lam)*a[J]+md.f*ov[J];
      m2[J]+=s[J]+o;
      if(a[J]>1e-12){r2[J|b]=1;const r=a[J]-o;if(r>1e-12)m2[J|b]=r}}
    rec(e+1,m2,r2,seq.concat(md.name),bits+bitOf(md));
  }
}
const m0=new Float64Array(128);m0[0]=N-1;m0[1]=1;const r0=new Uint8Array(128);r0[1]=1;
rec(1,m0,r0,[],"");
console.log(JSON.stringify({mapv,modes:modes.map(x=>x.name),bydev:BYD,leaves:cnt,wins,pruned,TAU,top:top.slice(0,15)}));
