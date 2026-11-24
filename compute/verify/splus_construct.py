# Independent verifier: explicit construction from the S+ proofs (39.4 plain, 45.1 rotating), random instances,
# brute-force all-pairs check. Members K4..K7 = the requested transversal ONLY (worst case: adversary adds nothing useful).
import random, itertools, math, sys
def build(v, pi, k, T, rot):
    m=len(v); n=sum(v); c=n-k
    pts=[];  # points numbered consecutively per cell
    off=0; cells=[]
    for vj in v: cells.append(list(range(off,off+vj))); off+=vj
    kappa=set(); P=[set(),set(),set()]; ycls={}  # y -> class index owning it
    r=0
    for j in range(m):
        d=3*pi[j]-v[j]; assert d>=0 and pi[j]<=v[j]
        kj=d//2; pj=pi[j]-kj
        cell=cells[j][:]
        kappa|=set(cell[:kj]); rest=cell[kj:]
        assert len(rest)==v[j]-kj
        if d%2==0:
            assert 3*pj==len(rest)
            for i in range(3): P[i]|=set(rest[i*pj:(i+1)*pj])
        else:
            assert 3*pj==len(rest)+1 and pj>=1
            # two sets share rest[0]; layout: P_a = rest[0:pj], P_b = {rest[0]} + rest[pj:2pj-1], P_c = rest[2pj-1:]
            a,b = (0,1) if not rot else (r%3,(r+1)%3)
            cc = 3-a-b
            y=rest[0]
            Pa=set(rest[0:pj]); Pb={y}|set(rest[pj:2*pj-1]); Pc=set(rest[2*pj-1:])
            assert len(Pa)==pj and len(Pb)==pj and len(Pc)==pj and Pa|Pb|Pc==set(rest)
            P[a]|=Pa; P[b]|=Pb; P[cc]|=Pc
            ycls[y]= a  # y assigned to the class of petal a (rot: line r; plain: petal 1 => P1)
            r+=1
    K=[kappa|P[i] for i in range(3)]
    assert all(len(x)==c for x in K), (len(K[0]),c)
    # classes Q_i: P_i minus y's assigned elsewhere
    Q=[set(P[i]) for i in range(3)]
    for y,a in ycls.items():
        for i in range(3):
            if i!=a and y in Q[i]: Q[i].remove(y)
    assert set().union(*Q)|kappa==set(range(n))
    assert len(kappa)+sum(len(q) for q in Q)==n, "classes overlap"
    # halves (a large, b small)
    H=[]
    for i in range(3):
        q=sorted(Q[i]); h=(len(q)+1)//2; H.append((set(q[:h]),set(q[h:])))
    trans=[ H[0][0]|H[1][0]|H[2][0], H[0][0]|H[1][1]|H[2][1], H[0][1]|H[1][0]|H[2][1], H[0][1]|H[1][1]|H[2][0] ]
    mx=max(len(t) for t in trans)
    K+= [set(t) for t in trans]
    return K, trans, mx, n, c
def pairs_ok(K,n):
    cov=[[False]*n for _ in range(n)]
    typ=[0]*n
    for i,Ki in enumerate(K):
        for x in Ki: typ[x]|=1<<i
    for x in range(n):
        for y in range(x,n):
            if typ[x]&typ[y]==0: return False
    return True
def run(trials, seed, rot, tight):
    rnd=random.Random(seed); done=0; fails=0; maxslack=10**9
    while done<trials:
        m=rnd.randint(1,12); k=rnd.randint(4,60)
        v=[rnd.choice([1,1,2,3,4,5,7,10,15,30]) for _ in range(m)]
        n=sum(v)
        bound=(4*(0) )  # placeholder
        # choose T minimal satisfying hypotheses (tight) or random above
        def okT(T):
            eps=T-3*k/4
            mm = 4*eps-12 if rot else 4*eps/3-4
            return m<=mm+1e-9 and n/3+m<=T+1e-9
        Ts=[T for T in range(1,n+1) if okT(T) and n-k>=T]
        if not Ts: continue
        T=Ts[0] if tight else rnd.choice(Ts)
        c=n-k
        lo=[(vj+2)//3 for vj in v]
        if sum(lo)>c or c>n: continue
        # random profile pi >= lo, <= v, sum c
        pi=lo[:]; rem=c-sum(lo)
        idx=list(range(m))
        while rem>0:
            j=rnd.choice(idx)
            if pi[j]<v[j]: pi[j]+=1; rem-=1
            elif all(pi[i]==v[i] for i in idx): break
        if rem>0: continue
        K,trans,mx,n_,c_=build(v,pi,k,T,rot)
        done+=1
        ok = pairs_ok(K,n) and mx<=T and all(len(t)<=T for t in trans)
        if not ok:
            fails+=1; print("FAIL",rot,v,pi,k,T,mx,pairs_ok(K,n))
    return fails
if __name__=="__main__":
    for rot in (False,True):
        for tight in (True,False):
            f=run(20000,1+rot*10+tight,rot,tight)
            print("rot" if rot else "plain","tight" if tight else "random","fails",f)
