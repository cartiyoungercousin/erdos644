import sys
from search import *
k=12;c=7;mu=6;T=9
for n in range(30,49):
    cnt=0;tot=0
    for p in partitions(n,4,24):
        tot+=1
        r=solve_size(list(p),k,c,mu,T,ap_cegar=False)
        if r['status']!='INFEAS': cnt+=1
    print(n,tot,cnt,flush=True)
