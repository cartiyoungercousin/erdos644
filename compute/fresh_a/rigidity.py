# Rigidity of the Fano obstruction among non-2-coverable 7-tuples of unit-measure sets.
# Types J subset [7] (which of the 7 sets contain a point).  Non-2-coverable <=> no two present types cover [7].
# theta1 = min union; theta2(delta) = min union subject to: for every Fano plane Phi on [7],
#   mass of types containing a Phi-line >= delta   (delta=0: such a type merely "allowed", i.e. infimum).
import itertools, pulp, sys
N=7; FULL=(1<<N)-1
base=[(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
planes=set()
for p in itertools.permutations(range(N)):
    planes.add(frozenset(frozenset(p[i] for i in L) for L in base))
planes=[[sum(1<<i for i in L) for L in P] for P in planes]
assert len(planes)==30
types=list(range(1,FULL))  # exclude empty and full
def solve(delta, nonfano=True):
    m=pulp.LpProblem("r",pulp.LpMinimize)
    w={J:m.add_variable(f"w{J}",0,1) for J in types}
    z={J:m.add_variable(f"z{J}",cat="Binary") for J in types}
    m+=pulp.lpSum(w.values())
    for J in types: m+= w[J]<=z[J]
    for i in range(N): m+= pulp.lpSum(w[J] for J in types if J>>i&1)==1
    for a in range(len(types)):
        for b in range(a,len(types)):
            if types[a]|types[b]==FULL:
                m+= z[types[a]]+z[types[b]]<=1
    if nonfano:
        for P in planes:
            viol=[J for J in types if any(J&L==L for L in P)]
            m+= pulp.lpSum(z[J] for J in viol)>=1
            if delta>0: m+= pulp.lpSum(w[J] for J in viol)>=delta
    m.solve(pulp.HiGHS(msg=False))
    val=pulp.value(m.objective)
    sup={bin(J)[2:].zfill(7):round(w[J].value(),4) for J in types if w[J].value()>1e-7}
    return val,sup
v,s=solve(0,False); print("theta1 (any obstruction) =",v, s)
for d in [0,0.01,0.05,0.1,0.25]:
    v,s=solve(d,True); print("delta",d,"theta2 =",v); print("   support",s); sys.stdout.flush()
