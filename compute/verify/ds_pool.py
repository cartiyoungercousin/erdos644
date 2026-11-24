import sys
from common import *
from ds import *
from ap import ap_strategy
k,T=80,60
for pool in (0,40):
  for d in (4,8,10):
    n=k+T//2-d
    fam=Family(k,n,n,[d,d],pool)
    s1=run_search(fam,ds_strategy,T,400,seed=d+pool)
    s2=run_search(fam,ap_strategy,T,200,seed=d+pool)
    print("pool",pool,"d",d,"DS: loses",s1['loses'],"viol",s1['budget_viol'],"flags",sorted(set(s1['flags']))[:2],"| AP-strategy: loses",s2['loses'],"viol",s2['budget_viol'],"maxreq",s2['maxreq'])
