"""Threshold-focused: only instances with e==min(w,T) or n==2e+1 (tight side conditions), and the nearest outside (e=min+1)."""
import random
from thmD import run
random.seed(77); tight=viol=0; outside_bad=0; outside=0
for _ in range(900):
    n=random.randint(7,14); M=random.randint(2,7)
    cols=[random.randrange(1<<M) for _ in range(n)]
    s=random.randrange(1,1<<M)
    for k in range(2,n):
        r=run(cols,s,k)
        if not r: continue
        e,w,T=r['e'],r['w'],r['T']
        bound=r['r'] if w%2==0 else r['r']+1
        if e<=min(w,T) and n>=2*e+1 and (e==min(w,T) or n==2*e+1):
            tight+=1
            if r['rho']>bound: viol+=1; print("VIOL",cols,s,r)
        elif e==min(w,T)+1 or n==2*e:
            outside+=1; outside_bad+= r['rho']>bound
print("tight-inside",tight,"violations",viol,"| just-outside",outside,"of which rho>bound",outside_bad)
