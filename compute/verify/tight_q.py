import itertools, random
from qprime_sigma_density import *
def run(n,k,T,extra_types,maxp):
    c=n-k; pairs=[(0,1),(2,3),(0,2),(1,3),(0,3),(1,2)]
    cnt=tight=bad=0
    for xs in itertools.product(range(maxp+1),repeat=6):
        p=sum(xs)
        if p>n: continue
        for ex in extra_types:  # ex: list of types for remaining points
            if len(ex)!=n-p: continue
            typ=[]
            for t,x in zip(pairs,xs): typ+= [t]*x
            typ+=ex
            if any(sum(1 for t in typ if i in t)!=c for i in range(4)): continue
            V=list(range(n)); K=[{x for x in V if i in typ[x]} for i in range(4)]
            cm=[sum(1 for t in typ if t in (a,b)) for a,b in MATCH]
            sig=sum(1 for t in typ if len(t)<=1)
            if not(2*sig<=3*T-n and all(cm[r]+sig<=T for r in range(3))): continue
            cnt+=1
            if 2*sig==3*T-n or 2*sig==3*T-n-1: tight+=1
            S=[set() for _ in range(3)]
            for x in V:
                t=typ[x]
                if len(t)<=1:
                    for r in range(3): S[r].add(x)
                elif len(t)==2:
                    for r,(a,b) in enumerate(MATCH):
                        if t in (a,b): S[r].add(x)
            r=0
            for x in V:
                if len(typ[x])>=3:
                    while len(S[r])>=T: r+=1
                    S[r].add(x)
            if not(all(len(s)<=T for s in S) and covers_all_pairs(K+S,V)): bad+=1
    print((n,k,T),"hyp instances",cnt,"near-tight",tight,"fail",bad)
# n=15,k=8,T=6 : remaining points among {(),(0,),(1,),(2,),(3,),triples,(0,1,2,3)}
ex=[]
base=[(),(0,),(1,),(2,),(3,),(0,1,2),(0,1,3),(0,2,3),(1,2,3),(0,1,2,3)]
for m in range(0,4):
    for e in itertools.combinations_with_replacement(base,m): ex.append(list(e))
run(15,8,6,ex,5)
run(14,8,6,ex,5)
run(16,8,7,ex,6)
