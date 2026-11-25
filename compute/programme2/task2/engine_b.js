// Engine B: brute force over position subsets (independent of the type-based engine).
// Columns h[0..n-1] (ints, bit-vectors in F_2^M), syndrome s != 0, uniformity k.
// D = {x subset V : sum_{i in x} h_i = s}; H = D ∩ (V choose k).
// Returns tau(H), r = n-k-tau+1 (least r with every (k+r)-set containing a member), rho = min wt over D,
// and e = dim span{h_i + h_j}, dimC = n - rank(h).
'use strict';
function popcount(x){x=x-((x>>>1)&0x55555555);x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0F0F0F0F)*0x01010101)>>>24;}
function rank(vs){const b=[];for(let v of vs){for(const w of b){if((v^w)<v)v^=w;}if(v){b.push(v);b.sort((a,c)=>c-a);}}return b.length;}
function analyse(h,s,k){
  const n=h.length, N=1<<n;
  const sum=new Int32Array(N), pc=new Uint8Array(N);
  for(let S=1;S<N;S++){const low=S&-S;const i=31-Math.clz32(low);sum[S]=sum[S^low]^h[i];pc[S]=pc[S^low]+1;}
  let rho=Infinity;for(let S=1;S<N;S++)if(sum[S]===s&&pc[S]<rho)rho=pc[S];
  // A[S]=1 iff S contains a member
  const A=new Uint8Array(N);let nmem=0;
  // process by increasing popcount: iterate S ascending works since S\i < S
  for(let S=1;S<N;S++){
    if(pc[S]===k&&sum[S]===s){A[S]=1;nmem++;continue;}
    if(pc[S]>k){let T=S;while(T){const low=T&-T;if(A[S^low]){A[S]=1;break;}T^=low;}}
  }
  if(nmem===0)return null;
  let tau=Infinity;const full=N-1;
  for(let U=0;U<N;U++){if(!A[full^U]&&pc[U]<tau)tau=pc[U];}
  const r=n-k-tau+1;
  const diffs=h.map(v=>v^h[0]);
  return {n,k,tau,r,rho,nmem,e:rank(diffs),dimC:n-rank(h)};
}
module.exports={analyse,rank,popcount};
