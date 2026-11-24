import random, sys, math
sys.path.insert(0,'compute/verify')
from splus_construct import build, pairs_ok
rnd=random.Random(9); worst={False:-99,True:-99}; N=0; bad=0
for _ in range(150000):
    m=rnd.randint(1,40); k=rnd.randint(1,80)
    v=[rnd.choice([1,2,3,4,5,6,7,8,9,10,11,13]) for _ in range(m)]
    n=sum(v); c=n-k
    if c<=0: continue
    lo=[(vj+2)//3 for vj in v]
    if sum(lo)>c: continue
    pi=lo[:]; rem=c-sum(lo)
    while rem>0:
        cand=[j for j in range(m) if pi[j]<v[j]]
        if not cand: break
        pi[rnd.choice(cand)]+=1; rem-=1
    if rem>0: continue
    u=sum((3*pi[j]-v[j])%2 for j in range(m))
    for rot in (False,True):
        K,tr,mx,_,_=build(v,pi,k,0,rot)
        N+=1
        if not pairs_ok(K,n): bad+=1; print("pairs fail",v,pi,k,rot)
        claim = 3*math.ceil((k+u)/4) if not rot else 3*k/4+u/4+3
        if rot is False and (k+u)%2: print("parity!",k,u)
        worst[rot]=max(worst[rot],mx-claim)
        if mx>claim+1e-9: bad+=1; print("ineq fail",rot,v,pi,k,u,mx,claim)
print(N,"checks; bad",bad,"worst mx-claim",worst)
