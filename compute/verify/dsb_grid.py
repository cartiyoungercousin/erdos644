import sys
from common import *
from ds import *
k,T=80,60
rows=[]
for d in [4,6,8,9,10]:
    for n in [k-d, k-d+2, k-d+10, k-1, k, k+3, k+10]:
        if n< k-d: continue
        bound = n-k+7*d
        a0=2*(k-d)-n
        if not (a0-1>2*d): continue
        if bound> T: continue
        fam=Family(k,n,n,[d,d])
        st=run_search(fam,dsb_strategy,T,200,seed=n*31+d)
        print("d",d,"n",n,"bound(n-k+7d)",bound,"c_thr",a0-1,"maxreq",st['maxreq'],"viol",st['budget_viol'],"loses",st['loses'],"flags",sorted(set(st['flags']))[:3]);sys.stdout.flush()
