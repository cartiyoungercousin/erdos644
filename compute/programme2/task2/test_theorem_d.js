// Random tests of (i) Lemma C: w-subset sums fill the coset w*h_1+E when n>=2e+1, e<=w<=n-e;
// (ii) Theorem D: rho <= r+1 when e <= min(k+r, T) and n >= 2e+1;  (iii) records every rho >= r+2 seen.
'use strict';
const {analyse,rank}=require('./engine_b.js');
let seed=12345;function rnd(){seed=(seed*1103515245+12345)&0x7fffffff;return seed/0x7fffffff;}
function ri(a,b){return a+Math.floor(rnd()*(b-a+1));}
let lemmaC=0,lemmaCfail=0,thmD=0,thmDfail=0,viol=[];
const trials=+process.argv[2]||3000;
for(let t=0;t<trials;t++){
  const M=ri(2,7), n=ri(4,16);
  // random column distribution: biased toward few types sometimes
  const ntypes=ri(1,Math.min(1<<M,n));const types=[];for(let i=0;i<ntypes;i++)types.push(ri(0,(1<<M)-1));
  const h=[];for(let i=0;i<n;i++)h.push(types[ri(0,ntypes-1)]);
  // Lemma C directly
  const e=rank(h.map(v=>v^h[0]));
  if(n>=2*e+1){
    for(let w=e;w<=n-e;w++){
      // compute set of w-subset sums
      const seen=new Set();const N=1<<n;
      for(let S=0;S<N;S++){let c=0,x=0,T=S;while(T){const low=T&-T;x^=h[31-Math.clz32(low)];c++;T^=low;}if(c===w)seen.add(x);}
      lemmaC++; if(seen.size!==(1<<e)){lemmaCfail++;console.log('LEMMA C FAIL',JSON.stringify(h),w);}
    }
  }
  // Theorem D on random s,k
  const s=ri(1,(1<<M)-1);
  for(let k=1;k<n;k++){
    const R=analyse(h,s,k); if(!R)continue;
    const T=R.n-R.k-R.r;
    if(R.r<0)continue;
    if(R.rho>=R.r+2)viol.push({h,s,...R,T});
    if(R.e<=Math.min(R.k+R.r,T)&&R.n>=2*R.e+1){thmD++; if(R.rho>R.r+1){thmDfail++;console.log('THEOREM D FAIL',JSON.stringify(h),s,JSON.stringify(R));}}
  }
}
console.log(JSON.stringify({trials,lemmaC,lemmaCfail,thmD,thmDfail,violations_seen:viol.length}));
// summarise violations: are they all outside the hypotheses?
const summ={};for(const v of viol){const key=`r=${v.r},rho=${v.rho}`;summ[key]=(summ[key]||0)+1;}
console.log('rho>=r+2 instances by (r,rho):',JSON.stringify(summ));
const ex=viol.slice(0,8).map(v=>({n:v.n,k:v.k,tau:v.tau,T:v.T,r:v.r,rho:v.rho,e:v.e,dimC:v.dimC,why:[v.e>v.T?'e>T':'',v.e>v.k+v.r?'e>w':'',v.n<2*v.e+1?'n<2e+1':''].join('')}));
console.log(JSON.stringify(ex,null,0));
