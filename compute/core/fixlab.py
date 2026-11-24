"""Fixed-labelling potential game (CORE Part V).  Lines = replies 0..6 in time order; a 'plane' = 7 triples of
concurrent lines (pencils).  History h = set of earlier lines containing x.
pencil P completable for (h, tau) iff P & [0..tau-1] subset of h.   e(h,tau) = |h| - max_{P completable} |h & P| (inf if none).
W_j = histories h subset [0..j-1] with e(h+{j}, j+1) > e(h, j)   (including x in reply j adds one unit of final excess)."""
import itertools, sys, pulp
def planes():
    base=[(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
    seen=set(); out=[]
    for p in itertools.permutations(range(7)):
        pl=frozenset(frozenset(p[i] for i in tr) for tr in base)
        if pl not in seen: seen.add(pl); out.append(pl)
    return out
INF=99
def e(h,tau,pl):
    best=None
    for P in pl:
        if all((i in h) for i in P if i<tau):
            v=len(h&P); best=v if best is None or v>best else best
    return INF if best is None else len(h)-best
def Wtypes(j,pl):
    W=[]
    for r in range(j+1):
        for h in itertools.combinations(range(j),r):
            h=frozenset(h); e0=e(h,j,pl)
            if e0>=INF: continue
            if e(h|{j},j+1,pl)>e0: W.append(h)
    return set(W)
def solve(pl,N,t,need=None,obj=False):
    c=N-1; om=N-1-t
    Hs=[frozenset(H) for r in range(3,8) for H in itertools.combinations(range(7),r) if any(P<=frozenset(H) for P in pl)]
    prob=pulp.LpProblem("f",pulp.LpMaximize)
    m={H:prob.add_variable("m_"+"".join(map(str,sorted(H))),0,None) for H in Hs}
    s=prob.add_variable("s",-1,1); prob+=s
    prob+=pulp.lpSum(m.values())==N
    for i in range(7): prob+=pulp.lpSum(m[H] for H in Hs if i in H)==c
    bs={}
    for j in range(2,7):
        W=Wtypes(j,pl)
        w=pulp.lpSum(m[H] for H in Hs if frozenset(x for x in H if x<j) in W)
        kw=pulp.lpSum(m[H] for H in Hs if j in H and frozenset(x for x in H if x<j) in W)
        b=prob.add_variable(f"b{j}",0,1,"Binary"); bs[j]=b
        prob+=kw>=om+s-3*b            # adversary dumps omega (+s) onto W_j
        prob+=kw>=w-3*(1-b)           # or all of W_j ends inside K_j
    prob.solve(pulp.HiGHS(msg=False,timeLimit=60))
    return "x", pulp.value(s), {j:int(round(pulp.value(b))) for j,b in bs.items()}, {"".join(str(x+1) for x in sorted(H)):round(pulp.value(v),4) for H,v in m.items() if pulp.value(v)>1e-6}
if __name__=="__main__":
    t=float(sys.argv[1]); Ns=[float(x) for x in sys.argv[2:]]
    pls=planes(); print(len(pls),"planes")
    for N in Ns:
        res=[]
        for k,pl in enumerate(pls):
            st,s,b,sol=solve(pl,N,t); res.append((s,k,b,sol,sorted("".join(str(x+1) for x in sorted(P)) for P in pl)))
        res.sort(key=lambda r:-r[0])
        print("N",N,"omega",round(N-1-t,4),"4eps",round(4*(t-.75),4),"best s over planes",round(res[0][0],5),"worst",round(res[-1][0],5))
        for r in res[:3]: print("   s=%.5f plane %s b=%s"%(r[0],r[4],r[2])); print("      ",r[3])
