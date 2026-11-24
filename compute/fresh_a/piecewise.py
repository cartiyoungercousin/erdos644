# Piecewise-complete families: classes c with sizes s*sig[c] (unit k=1), pieces = subsets of classes,
# H = union over pieces X of all k-subsets of X.
# tau(H)/k (measure limit) = min sum d_c  s.t. for every piece X: sum_{c in X}(size_c - d_c) <= 1   (LP)
# obstruction threshold s* = min s such that some 7 edges (each inside a piece) are non-2-coverable (MILP).
# For s < s*, H is (7,2) (any real obstruction gives a feasible MILP point).
import itertools, pulp, sys
N=7; FULL=(1<<N)-1
TYPES=list(range(1,FULL))
COVER=[(a,b) for i,a in enumerate(TYPES) for b in TYPES[i:] if a|b==FULL]
def tau(sizes,pieces):
    m=pulp.LpProblem("t",pulp.LpMinimize)
    d=[m.add_variable(f"d{c}",0,sizes[c]) for c in range(len(sizes))]
    m+=pulp.lpSum(d)
    for X in pieces: m+= pulp.lpSum(sizes[c]-d[c] for c in X)<=1
    m.solve(pulp.HiGHS(msg=False)); return pulp.value(m.objective)
def sstar(sig,pieces,nsets=N,fixed_s=None):
    C=len(sig); P=len(pieces)
    m=pulp.LpProblem("o",pulp.LpMinimize)
    s=m.add_variable("s",0,10)
    w={(J,c):m.add_variable(f"w{J}_{c}",0,1) for J in TYPES for c in range(C)}
    z={J:m.add_variable(f"z{J}",cat="Binary") for J in TYPES}
    a={(i,p):m.add_variable(f"a{i}_{p}",cat="Binary") for i in range(N) for p in range(P)}
    m+= s
    if fixed_s is not None: m+= s==fixed_s
    for i in range(N):
        m+= pulp.lpSum(a[i,p] for p in range(P))==1
        m+= pulp.lpSum(w[J,c] for J in TYPES if J>>i&1 for c in range(C))==1
    for i in range(N-1):  # symmetry: piece index nondecreasing
        m+= pulp.lpSum(p*a[i,p] for p in range(P))<=pulp.lpSum(p*a[i+1,p] for p in range(P))
    for c in range(C):
        m+= pulp.lpSum(w[J,c] for J in TYPES)<=sig[c]*s
        for J in TYPES:
            m+= w[J,c]<=z[J]
            for i in range(N):
                if J>>i&1:
                    m+= w[J,c]<=pulp.lpSum(a[i,p] for p in range(P) if c in pieces[p])
    for (x,y) in COVER: m+= z[x]+z[y]<=1
    st=m.solve(pulp.HiGHS(msg=False,timeLimit=1500))
    val=pulp.value(m.objective)
    asg=[max(range(P),key=lambda p:a[i,p].value()) for i in range(N)]
    sup={(bin(J)[2:].zfill(7)[::-1],c):round(w[J,c].value(),4) for J in TYPES for c in range(C) if w[J,c].value()>1e-7}
    return st,val,asg,sup
if __name__=="__main__":
    name=sys.argv[1]
    if name=="triangle":
        sig=[1,1,1]; pieces=[(0,1),(1,2),(0,2)]
    elif name=="single":
        sig=[1]; pieces=[(0,)]
    elif name=="k4pairs":
        sig=[1]*4; pieces=list(itertools.combinations(range(4),2))
    elif name=="k4triples":
        sig=[1]*4; pieces=list(itertools.combinations(range(4),3))
    elif name=="k5triples":
        sig=[1]*5; pieces=list(itertools.combinations(range(5),3))
    elif name=="k5quads":
        sig=[1]*5; pieces=list(itertools.combinations(range(5),4))
    elif name=="pentagon2":
        sig=[1]*5; pieces=[(i,(i+1)%5) for i in range(5)]
    elif name=="pentagon3":
        sig=[1]*5; pieces=[(i,(i+1)%5,(i+2)%5) for i in range(5)]
    st,val,asg,sup=sstar(sig,pieces)
    print(name,"status",st,"s* =",val,"assignment",asg)
    for k_,v in sorted(sup.items(),key=lambda t:(t[0][1],t[0][0])): print("   ",k_,v)
    sizes=[val*x for x in sig]
    print("  ground/k =",sum(sizes),"  tau/k at s* =",tau(sizes,pieces))
