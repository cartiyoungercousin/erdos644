# Exhaustive adversary check: symmetric family given by profile set Pi (all sets with a profile in Pi). Existence is monotone
# in Pi, so only MINIMAL T-covering Pi matter. SAT decides whether seven members cover all pairs. Independent of proofs.
import itertools, random, sys, time
from pysat.solvers import Cadical153
def profiles(v,total):
    res=[]
    def rec(j,rem,cur):
        if j==len(v):
            if rem==0: res.append(tuple(cur))
            return
        for x in range(0,min(v[j],rem)+1): rec(j+1,rem-x,cur+[x])
    rec(0,total,[]); return res
def minimal_covers(v,T,c,limit,rnd):
    P=profiles(v,c); R=profiles(v,T)
    cov={s:[i for i,p in enumerate(P) if all(a<=b for a,b in zip(s,p))] for s in R}
    if any(not x for x in cov.values()): return None,None
    seen=set()
    for _ in range(limit):
        S=set(range(len(P))); order=list(S); rnd.shuffle(order)
        cnt={s:len(cov[s]) for s in R}
        users={i:[s for s in R if i in cov[s]] for i in S}
        for i in order:
            if all(cnt[s]>1 for s in users[i]):
                S.remove(i)
                for s in users[i]: cnt[s]-=1
        seen.add(frozenset(S))
    return P,seen
class CNF:
    def __init__(s): s.n=0; s.cl=[]
    def new(s): s.n+=1; return s.n
def good_seven(v,Pi):
    n=sum(v); m=len(v); cnf=CNF()
    x=[[cnf.new() for _ in range(n)] for _ in range(7)]
    cells=[]; off=0
    for vj in v: cells.append(list(range(off,off+vj))); off+=vj
    # unary counters: ge[i][j][r] <-> at least r chosen in cell j of member i (r=1..v_j)
    ge={}
    for i in range(7):
        for j in range(m):
            lits=[x[i][p] for p in cells[j]]
            prev=[None]*(len(lits)+2)  # prev[r] var for first a lits >=r ; None means False; r=0 True
            T_=cnf.new(); cnf.cl.append([T_])
            cur={0:T_}
            for a,l in enumerate(lits,1):
                new={0:T_}
                for r in range(1,a+1):
                    s=cnf.new(); new[r]=s
                    A=cur.get(r)  # first a-1 >= r (may not exist if r>a-1)
                    B=cur.get(r-1)
                    # s <-> A or (l and B)
                    if A is None:
                        cnf.cl+= [[-s,l],[-s,B],[s,-l,-B]]
                    else:
                        cnf.cl+= [[-s,A,l],[-s,A,B],[s,-A],[s,-l,-B]]
                cur=new
            ge[i,j]=cur
    zs=[]
    for i in range(7):
        zi=[]
        for p in Pi:
            z=cnf.new(); zi.append(z)
            for j in range(m):
                r=p[j]; g=ge[i,j]
                cnf.cl.append([-z,g[r]])
                if r+1 in g: cnf.cl.append([-z,-g[r+1]])
        cnf.cl.append(zi); zs.append(zi)
    for a in range(n):
        for b in range(a,n):
            ys=[]
            for i in range(7):
                if a==b: ys.append(x[i][a]); continue
                y=cnf.new(); cnf.cl+=[[-y,x[i][a]],[-y,x[i][b]]]; ys.append(y)
            cnf.cl.append(ys)
    # symmetry breaking: order members by first-point... skip
    s=Cadical153(bootstrap_with=cnf.cl)
    r=s.solve(); s.delete(); return r
if __name__=="__main__":
    # sanity: seven 3-subsets of 16 points cannot work
    print("sanity (expect False):", good_seven([16],[(3,)]), " (expect True):", good_seven([16],[(8,)]))
    rnd=random.Random(1)
    cases=[]
    # (k,T,v) satisfying 39.4 hypotheses with n-k>=T
    for k in (8,12):
        for T in range(k*3//4+4,k+8):
            for m in (1,2,3):
                if m>4*(T-3*k/4)/3-4+1e-9: continue
                for n in range(k+T,3*(T-m)+1):
                    for _ in range(3):
                        cut=sorted(rnd.sample(range(1,n),m-1)) if m>1 else []
                        v=[b-a for a,b in zip([0]+cut,cut+[n])]
                        cases.append((k,T,v))
    random.Random(2).shuffle(cases)
    t0=time.time(); bad=0; tot=0
    for (k,T,v) in cases[:int(sys.argv[1]) if len(sys.argv)>1 else 60]:
        n=sum(v); c=n-k
        P,covs=minimal_covers(v,T,c,40,rnd)
        if P is None: continue
        for S in covs:
            Pi=[P[i] for i in S]; tot+=1
            if not good_seven(v,Pi):
                bad+=1; print("NO GOOD SEVEN",k,T,v,Pi)
        print(k,T,v,"minimal covers",len(covs),"ok so far, bad",bad,round(time.time()-t0),flush=True)
    print("total families",tot,"bad",bad)
