// Exhaustive small tables of achievable (r, rho) for parity-check matrices with M rows.
// Enumerates column-type multisets (types in F_2^M, incl. the zero type), s = 1 (WLOG: GL(M,2) is transitive
// on nonzero s), n <= NMAX, every k. Uses engine_b (brute force over position subsets).
// Usage: node tables.js M NMAX [rho3only]
'use strict';
const {analyse}=require('./engine_b.js');
const M=+process.argv[2], NMAX=+process.argv[3], RHO3=process.argv[4]==='rho3';
const s=1, Q=1<<M;
const pairs={}; // (r,rho) -> {count, maxTau, maxTau_example, lemma8regime_example, Tge3k4_example}
let configs=0;
function record(h,R){
  const T=R.n-R.k-R.r;const key=`${R.r},${R.rho}`;
  let P=pairs[key];if(!P)P=pairs[key]={count:0,maxTau:-1,ex:null,lemma8:null,t34:null};
  P.count++;
  if(R.tau>P.maxTau){P.maxTau=R.tau;P.ex={h:h.slice(),k:R.k,n:R.n,tau:R.tau,e:R.e};}
  if(!P.lemma8 && 2*R.n>=3*R.k+2*R.r+2)P.lemma8={h:h.slice(),k:R.k,n:R.n,tau:R.tau};
  if(!P.t34 && 4*T>=3*R.k && R.tau>=2)P.t34={h:h.slice(),k:R.k,n:R.n,tau:R.tau};
}
const h=[];
function rec(t,used){
  if(h.length>=1){
    // evaluate this multiset
    if(!RHO3 || ok3()){
      configs++;
      for(let k=1;k<=h.length;k++){const R=analyse(h,s,k);if(R&&R.r>=0)record(h,R);}
    }
  }
  if(h.length===NMAX)return;
  for(let v=t;v<Q;v++){
    if(RHO3 && (v===s || used.has(v^s)))continue;
    h.push(v);const had=used.has(v);used.add(v);
    rec(v,used);
    h.pop();if(!had)used.delete(v);
  }
}
function ok3(){const st=new Set(h);if(st.has(s))return false;for(const v of st)if(st.has(v^s))return false;return true;}
rec(0,new Set());
console.log(`M=${M} NMAX=${NMAX} rho3only=${RHO3} multisets=${configs}`);
const keys=Object.keys(pairs).sort((a,b)=>{const[x,y]=a.split(',').map(Number),[u,w]=b.split(',').map(Number);return x-u||y-w;});
for(const key of keys){const P=pairs[key];const [r,rho]=key.split(',').map(Number);
  console.log(`(r,rho)=(${key}) ${rho>=r+2?'VIOLATES rho<=r+1':''} count=${P.count} maxTau=${P.maxTau} ex=${JSON.stringify(P.ex)} lemma8regime=${P.lemma8?JSON.stringify(P.lemma8):'none'} T>=3k/4&tau>=2=${P.t34?JSON.stringify(P.t34):'none'}`);}
