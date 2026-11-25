"""Independent check of the counting claim: dim C >= k+r for coset families (n=k+r+T, tau=T+1).
Exact: |H| >= C(n,w)/C(n-k,r), |C|>=|H|. If C(n,w) > 2^(w-1)*C(n-k,r) then |C|>2^(w-1) so dim C>=w."""
from math import comb, log2
def h(x): return 0 if x<=0 or x>=1 else -x*log2(x)-(1-x)*log2(1-x)
def g(om,t):
    N=1+om+t
    return N*h((1+om)/N)-(t+om)*h(om/(t+om))-(1+om)
# asymptotic thresholds
import numpy as np
for t in (0.75,0.8,0.875,1.0):
    lo,hi=0,1.0
    for _ in range(60):
        mid=(lo+hi)/2
        if all(g(o,t)>=0 for o in np.linspace(1e-6,mid,400)): lo=mid
        else: hi=mid
    print("t=%.3f omega*=%.4f N*=%.4f"%(t,lo,1+lo+t))
# region N<11/6, t>=3/4, omega>0
mn=9
for t in np.linspace(0.75,1.0,251):
    for om in np.linspace(1e-6,11/6-1-t-1e-9,300):
        if om<=0: continue
        mn=min(mn,g(om,t))
print("min g on region N<11/6,t>=3/4:",mn)
# exact finite check
def ok(k,r,T):
    n=k+r+T; w=k+r
    return comb(n,w) > (1<<(w-1))*comb(n-k,r)
bad=[]; tot=0; bad_small=[]
for k in range(8,260):
    T0=-(-3*k//4)
    for T in range(T0,T0+3):  # T = ceil(3k/4) .. +2 ; larger T only helps? check separately below
        for r in range(0,k):
            n=k+r+T
            if 6*n>=11*k: break
            tot+=1
            if not ok(k,r,T): bad.append((k,r,T))
print("finite checks",tot,"fail",len(bad))
import collections
byk=collections.defaultdict(list)
for k,r,T in bad: byk[k].append((r,T))
print("largest k failing:",max(byk) if byk else None)
print({k:v[:4] for k,v in list(byk.items())[-6:]})
# is r small always failing?  record the smallest-r failure pattern
print("fails with r<=1 or so:", [(k,r,T) for k,r,T in bad if r<=2][:15])
