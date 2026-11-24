import random, sys
sys.path.insert(0,'compute/verify')
from splus_construct import build, pairs_ok
# adversarial: all cells odd (3*pi_j - v_j odd), T at minimal allowed (or below, to see the bound is binding)
def trial(rnd, rot, shift):
    m=rnd.randint(2,40); k=rnd.randint(8,80)
    v=[rnd.choice([2,4,6,8,10]) for _ in range(m)]   # even v, pi odd => 3pi-v odd
    n=sum(v); c=n-k
    pi=[]
    for vj in v:
        opts=[p for p in range(((vj+2)//3),vj+1) if (3*p-vj)%2==1]
        if not opts: return None
        pi.append(rnd.choice(opts))
    if sum(pi)!=c: return None
    u=m
    # smallest T allowed by hypotheses
    for T in range(1,n+1):
        eps=T-3*k/4
        mm = 4*eps-12 if rot else 4*eps/3-4
        if m<=mm+1e-9+shift and n/3+m<=T+1e-9: break
    else: return None
    if c<T: return None
    K,tr,mx,_,_=build(v,pi,k,T,rot)
    return pairs_ok(K,n) and mx<=T, T, mx, u
for rot in (False,True):
  for shift in (0,1,3,6):
    cnt=bad=0; rnd=random.Random(5)
    for _ in range(400000):
        r=trial(rnd,rot,shift)
        if r is None: continue
        cnt+=1
        if not r[0]: bad+=1
    print("rot" if rot else "plain","shift(cells beyond bound)",shift,"instances",cnt,"fails",bad)
