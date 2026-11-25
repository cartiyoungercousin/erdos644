"""Independent implementation of Theorem 9' (from the statement) + independent exact verifier + stress test."""
import random, sys, itertools
from collections import defaultdict
LINES=[(1,2,4),(2,3,5),(3,4,6),(4,5,7),(1,5,6),(2,6,7),(1,3,7)]
L={ ''.join(map(str,l)):set(l) for l in LINES}
LID={l:i for i,l in enumerate(LINES)}
def lid(s): return LID[tuple(int(c) for c in s)]
PEN={p:[i for i,l in enumerate(LINES) if p in l] for p in range(1,8)}
# fix: '346' key
TST=[lid('124'),lid('235'),lid('346')]
def hypcheck(cols,alpha,k,Om):
    """returns dict of hypotheses booleans"""
    n=len(cols); w=[len(o) for o in Om]; W=sum(w); D=max(w)-min(w)
    used=set().union(*map(set,Om))
    Vp=[i for i in range(n) if i not in used]
    cnt=defaultdict(int)
    for i in Vp: cnt[cols[i]]+=1
    s=4*n-7*k-W
    H0=s>=0; H1=all(x%2==k%2 for x in w)
    if not (H0 and H1): return dict(H0=H0,H1=H1,ok=False)
    f=1 if s%4==2 else 0; u=(s-2*f)//4; c=len(cnt)
    H2=k>=W+2*D+4*c+6
    gstar=max(cnt,key=lambda g:cnt[g]) if cnt else None
    H3=bool(cnt) and cnt[gstar]>=u+2*f+7
    H4=sum(1 for g in cnt if cnt[g]==1)<=u
    return dict(H0=H0,H1=H1,H2=H2,H3=H3,H4=H4,ok=H2 and H3 and H4,s=s,f=f,u=u,c=c,W=W,gstar=gstar)
def construct(cols,alpha,k,Om):
    n=len(cols); w=[len(o) for o in Om]; W=sum(w)
    hy=hypcheck(cols,alpha,k,Om); assert hy['ok']
    f,u,gstar=hy['f'],hy['u'],hy['gstar']
    used=set().union(*map(set,Om))
    cells=defaultdict(list)
    for i in range(n):
        if i not in used: cells[cols[i]].append(i)
    Z=[]
    for g in list(cells):
        if len(cells[g])==1: Z.append(cells[g].pop()); del cells[g]
    while len(Z)<u: Z.append(cells[gstar].pop())
    F=[]
    if f: F=[cells[gstar].pop(),cells[gstar].pop()]
    # colours: T_i colour q_i
    Tri=[ [lid('124'),lid('156'),lid('267')], [lid('124'),lid('137'),lid('346')], [lid('124'),lid('235'),lid('457')] ]
    e=[0]*7
    for i in range(3):
        for l in Tri[i]: e[l]+=w[i]
    if f:
        for l in TST: e[l]+=2
    t=[k-x for x in e]; St=sum(t)
    assert St%4==0
    m={}
    for p in range(1,8):
        v=St//4-sum(t[l] for l in PEN[p])/2
        assert v==int(v); m[p]=int(v)
    for l in range(7): assert sum(m[p] for p in range(1,8) if p not in LINES[l])==t[l]
    Hamgen=[set(l) for l in LINES]
    pi={}; cyc=0
    for g in cells:
        if len(cells[g])%2==0: pi[g]=set()
        elif g!=gstar: pi[g]=set(LINES[cyc%7]); cyc+=1
    acc=set(p for p in range(1,8) if m[p]%2)
    for g in pi: acc^=pi[g]
    pi[gstar]=acc
    Y={p:[] for p in range(1,8)}
    for g in cells:
        pts=cells[g]
        assert len(pts)>=len(pi[g]) and (len(pts)-len(pi[g]))%2==0
        for p in sorted(pi[g]): Y[p].append(pts.pop())
    rem=[]
    for g in cells:
        while cells[g]: rem.append((cells[g].pop(),cells[g].pop()))
    for p in range(1,8):
        need=m[p]-len(Y[p]); assert need>=0 and need%2==0,(p,need)
        for _ in range(need//2): Y[p]+=list(rem.pop())
    assert not rem
    B=[]
    for l in range(7):
        S=set()
        for p in range(1,8):
            if p not in LINES[l]: S|=set(Y[p])
        for i in range(3):
            if l in Tri[i]: S|=set(Om[i])
        if l in TST: S|=set(F)
        B.append(S)
    return B
def verify(cols,alpha,k,B):
    n=len(cols)
    for S in B:
        if len(S)!=k: return False,'size'
        x=0
        for i in S:x^=cols[i]
        if x!=alpha: return False,'class'
    if len({frozenset(S) for S in B})<7: return False,'distinct'
    for x in range(n):
        for y in range(x,n):
            if all((x in S or y in S) for S in B): return False,'transversal'
    for p in range(1,8):
        a,b,c=PEN[p]
        if B[a]&B[b]&B[c]: return False,'pencil'
    return True,'ok'
def find_omegas(cols,alpha,k,tries=4000):
    n=len(cols); rnd=random
    best=None
    for _ in range(tries):
        size=rnd.choice([1,2,3,4,5,6]); 
        if size%2!=k%2: size+=1
        S=rnd.sample(range(n),size); x=0
        for i in S:x^=cols[i]
        if x==alpha: return S
    return None
def gen(rng):
    M=rng.randint(1,4); ncl=rng.randint(1,min(2**M,8))
    classes=rng.sample(range(1<<M),ncl) if rng.random()<0.8 else [0]+rng.sample(range(1,1<<M),min(ncl-1,2**M-1))
    cells=[]
    for g in classes:
        sz=rng.choice([1,1,2,3,rng.randint(4,40),rng.randint(20,80)])
        cells+= [g]*sz
    rng.shuffle(cells)
    return cells
def main(seed,trials):
    rng=random.Random(seed); random.seed(seed)
    tot=okc=fail=0; hist=defaultdict(int)
    for _ in range(trials):
        cols=gen(rng); n=len(cols)
        if n<40: continue
        span=set([0])
        for c in cols: span|={x^c for x in span}
        nz=[x for x in span if x]
        if not nz: continue
        alpha=rng.choice(nz)
        kpar=rng.randint(0,1)
        # try to find three disjoint Omega via random search on remaining points
        Om=[];remaining=list(range(n));ok=True
        for i in range(3):
            sub=[cols[j] for j in remaining]
            best=None
            for _t in range(3000):
                size=rng.choice([1,2,3,4,5]); 
                if size%2!=kpar: size+=1
                if size>len(remaining): continue
                idx=rng.sample(range(len(remaining)),size); x=0
                for j in idx:x^=sub[j]
                if x==alpha: best=[remaining[j] for j in idx]; break
            if best is None: ok=False;break
            Om.append(best); remaining=[j for j in remaining if j not in best]
        if not ok: hist['noOmega']+=1; continue
        W=sum(map(len,Om))
        kmax=(4*n-W)//7
        for dj in range(0,4):
            k=kmax-dj
            if k<1 or k%2!=kpar: continue
            tot+=1
            hy=hypcheck(cols,alpha,k,Om)
            if not hy.get('ok'): hist['hyp_fail:'+''.join(x for x in ('H2','H3','H4') if not hy.get(x,True))]+=1; continue
            B=construct(cols,alpha,k,Om)
            v,msg=verify(cols,alpha,k,B)
            if v: okc+=1
            else: fail+=1; print("FAIL",msg,len(cols),k)
    print("seed",seed,"candidates",tot,"hypotheses+construct OK",okc,"FAIL",fail,dict(hist))
if __name__=="__main__":
    main(int(sys.argv[1]),int(sys.argv[2]))
