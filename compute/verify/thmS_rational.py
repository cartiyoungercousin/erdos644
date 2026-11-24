# Theorem S, first order, exact rationals. Given V=(v_j), t, N, member profile pi (v/3<=pi<=v, |pi|=N-1),
# build class masses of the Fano certificate from the proof and check: co-type structure, member profiles, transversal masses <= t.
from fractions import Fraction as F
import random, itertools
def check(v,pi,t):
    N=sum(v); c=N-1; m=len(v)
    assert sum(pi)==c and all(3*p>=vj and p<=vj for p,vj in zip(pi,v))
    kap=[(3*p-vj)/2 for p,vj in zip(pi,v)]
    pet=[(vj-p)/2 for p,vj in zip(pi,v)]   # each of three petals
    assert all(x>=0 for x in kap+pet)
    assert all(kap[j]+3*pet[j]==v[j] for j in range(m))
    mk=sum(kap); mp=sum(pet)
    assert mk==N-F(3,2) and mp==F(1,2)
    # cell-wise: petal i has profile pet; member profile kap+pet = pi
    assert all(kap[j]+pet[j]==pi[j] for j in range(m))
    # halves of petals: each half mass 1/4 ; transversals 3 halves = 3/4
    return F(3,4)<=t
rnd=random.Random(3); n=0
for _ in range(100000):
    m=rnd.randint(1,8)
    t=F(3,4)+F(rnd.randint(0,40),100)
    N=rnd.choice([F(3,2),F(9,4),F(rnd.randint(150,225),100)])
    if N<1+t: continue   # non-vacuous
    w=[F(rnd.randint(1,20)) for _ in range(m)]; s=sum(w); v=[x*N/s for x in w]
    # pi in [v/3, v], sum c; random
    lo=[x/3 for x in v]; slack=(N-1)-sum(lo)
    if slack<0: continue
    room=[vj-l for vj,l in zip(v,lo)]
    if sum(room)<slack: continue
    f=slack/sum(room); pi=[l+f*r for l,r in zip(lo,room)]   # proportional
    # also a random extreme: fill cells greedily in random order
    order=list(range(m)); rnd.shuffle(order); pi2=lo[:]; rem=slack
    for j in order:
        d=min(rem,room[j]); pi2[j]+=d; rem-=d
    for p in (pi,pi2):
        assert check(v,p,t); n+=1
    # requested profile s with v/3<=s<=v,|s|=t exists iff N/3<=t<=N
    assert N/3<=t<=N
print("S: checks",n,"ok")
