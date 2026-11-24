import itertools, random
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
def feasible(n,T,K,nreq=4):
    V=range(n); pool=IDPool(); cl=[]
    y=lambda x,r: pool.id(('y',x,r))
    for x in V:
        for z in V:
            if x>z: continue
            if any(x in s and z in s for s in K): continue
            zs=[]
            for r in range(nreq):
                v=pool.id(('z',x,z,r)); zs.append(v)
                cl.append([-v,y(x,r)]); cl.append([-v,y(z,r)])
            cl.append(zs)
    for r in range(nreq):
        enc=CardEnc.atmost([y(x,r) for x in V],bound=T,vpool=pool,encoding=EncType.seqcounter); cl+=enc.clauses
    s=Cadical153(bootstrap_with=cl); return s.solve()
rng=random.Random(5)
def inst(q,kap,n,c):
    V=list(range(n)); kern=V[:kap]; Q=[];off=kap
    for s in q: Q.append(V[off:off+s]); off+=s
    K=[]
    for i in range(3):
        base=set(kern)|set(Q[i]); others=[x for x in V if x not in base]
        K.append(base|set(rng.sample(others,c-len(base))))
    return K
for (n,k,T,q,kap) in [(15,8,7,(5,3,6),1),(15,8,7,(5,3,6),1),(11,6,5,(3,3,4),1),(17,8,7,(4,5,5),3),(23,12,10,(7,5,8),3)]:
    c=n-k; ok=all(feasible(n,T,inst(q,kap,n,c)) for _ in range(5)); print((n,k,T),q,kap,"4 requests of size<=T always suffice (5 paddings):",ok)
