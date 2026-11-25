"""Independent check of FABLE_C 5.4 (collinear repair). Written from the statement only."""
import itertools, sys
from fractions import Fraction as Fr
LINES=[(1,2,3),(1,4,5),(1,6,7),(2,4,6),(2,5,7),(3,4,7),(3,5,6)]
# (a) every blocking set of the Fano plane contains a line
for m in range(128):
    Z={i+1 for i in range(7) if m>>i&1}
    blocking=all(set(l)&Z for l in LINES)
    hasline=any(set(l)<=Z for l in LINES)
    if blocking: assert hasline
    if not hasline: assert not blocking
print("blocking-set lemma ok")
# (b) r_i and class formulas with exact fractions
r=[sum(1 for l in LINES if max(l)==i) for i in range(1,8)]
print("r=",r)
def plan(Nmy,eta,t):
    S=3*Nmy+7*eta
    if S>7*t: return None
    theta=t-eta-Fr(3*Nmy,7)
    ell=[t-theta-r[i]*eta for i in range(7)]
    assert sum(ell)==3*Nmy
    V={l:Fr(1,2)*sum(ell[i-1] for i in l)-Fr(1,6)*sum(ell) for l in LINES}
    for i in range(1,8):
        assert sum(V[l] for l in LINES if i in l)==ell[i-1]
    assert sum(V.values())==Nmy
    return ell,V,theta
for (Nmy,eta,t) in [(Fr(7,4),Fr(1,100),Fr(3,4)+Fr(1,10)),(Fr(7,4),Fr(4,7)*Fr(1,10),Fr(3,4)+Fr(1,10)),(Fr(185,100),Fr(1,200),Fr(8,10))]:
    p=plan(Nmy,eta,t)
    ell,V,theta=p
    print(Nmy,eta,t,"theta",float(theta),"min class",float(min(V.values())), "min=(N-y)/7-eta:",V[(1,6,7)]==Nmy/7-eta)
    assert min(V.values())>=0 and theta>=0
# (c) exhaustive adaptive game on a discrete instance: Y of size ny, each reply misses any <=eta subset of Y (adversary free choice,
# also adds arbitrary dump). Plan from the proof, integer sizes via chosen classes.
def run(ny,eta,vsizes,exhaustive=True):
    # points: classes V_lambda (sizes vsizes), Y = ny points.
    pts={}
    cur=0
    cls={}
    for l,s in zip(LINES,vsizes):
        cls[l]=list(range(cur,cur+s)); cur+=s
    Y=list(range(cur,cur+ny))
    L={i:[x for l in LINES if i in l for x in cls[l]] for i in range(1,8)}
    subsets=[frozenset(c) for e in range(eta+1) for c in itertools.combinations(Y,e)]
    bad=0;cnt=0
    maxreq=0
    def rec(i,M):
        nonlocal bad,cnt,maxreq
        if i==8:
            cnt+=1
            # K_i contains V-class parts L_i, and Y minus M_i (+ the repair)
            return
    # iterative: DFS with explicit requests
    def dfs(i,Ms,Ks):
        nonlocal bad,cnt,maxreq
        if i==8:
            cnt+=1
            # co-types
            I={x:frozenset(j for j in range(1,8) if x in Ks[j]) for x in range(cur+ny)}
            vals=list(I.values())
            ok=all(v for v in vals) and all(a&b for a in set(vals) for b in set(vals))
            if not ok: bad+=1
            return
        R=set()
        for l in LINES:
            if i in l:
                a,b=[j for j in l if j!=i]
                if a<i and b<i: R|=Ms[a]&Ms[b]
        S=set(L[i])|R
        maxreq=max(maxreq,len(S))
        for M in subsets:
            K=set(S)|(set(Y)-M)   # adversary's reply: contains S and Y minus M (M disjoint from S needed)
            if M&S: continue      # a reply containing S cannot miss points of S
            Ms[i]=M;Ks[i]=K
            dfs(i+1,Ms,Ks)
    dfs(1,{},{})
    return cnt,bad,maxreq

def best_v(T,eta):
    best=None
    top=T//3+1
    for v in itertools.product(range(top+1),repeat=7):
        if all(sum(v[j] for j,l in enumerate(LINES) if i in l)+r[i-1]*eta<=T for i in range(1,8)):
            if best is None or sum(v)>sum(best): best=v
    return list(best)
if __name__=="__main__":
    for (T,eta,ny) in [(12,1,3),(12,1,4),(14,2,3),(10,1,5),(9,2,4)]:
        v=best_v(T,eta)
        n=sum(v)
        print("T",T,"eta",eta,"ny",ny,"v",v,"n'",n,"condition 3n'+7eta<=7T:",3*n+7*eta<=7*T,
              "exhaustive (count,bad,maxreq):",run(ny,eta,v))
