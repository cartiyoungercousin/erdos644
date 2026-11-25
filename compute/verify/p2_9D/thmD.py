"""Independent brute-force test of Theorem D and Lemmas A,B,C (own code, bitmask)."""
import random, itertools, sys
from math import comb
def rank_span(vs):
    basis=[]
    for v in vs:
        for b in basis: v=min(v,v^b)
        if v: basis.append(v)
    return len(basis)
def analyse(cols,s):
    n=len(cols)
    # syndromes of all subsets via gray-ish DP
    syn=[0]*(1<<n); pc=[0]*(1<<n)
    for m in range(1,1<<n):
        lb=m&-m; i=lb.bit_length()-1
        syn[m]=syn[m^lb]^cols[i]; pc[m]=pc[m^lb]+1
    return syn,pc
def run(cols,s,k):
    n=len(cols); syn,pc=analyse(cols,s)
    mem=[m for m in range(1<<n) if pc[m]==k and syn[m]==s]
    if not mem: return None
    # max independent set size (no member inside)
    # contains member: dp "has[m]" = exists member subset of m
    has=bytearray(1<<n)
    for m in mem: has[m]=1
    for i in range(n):
        for m in range(1<<n):
            if m>>i&1 and has[m^(1<<i)]: has[m]=1
    mis=max(pc[m] for m in range(1<<n) if not has[m]) if any(not has[m] for m in range(1<<n)) else -1
    # covering threshold: every (mis+1)-set contains member -> k+r = mis+1
    w=mis+1
    if w<k: w=k
    r=w-k
    T=n-w
    rho=min(pc[m] for m in range(1,1<<n) if syn[m]==s and (pc[m]-k)%2==0)
    E=rank_span([cols[i]^cols[0] for i in range(1,n)])
    return dict(n=n,k=k,r=r,T=T,w=w,e=E,rho=rho,H=len(mem))
def main(seed,trials):
    random.seed(seed); inside=0; viol=0; stats={}
    for _ in range(trials):
        n=random.randint(5,15); M=random.randint(1,7)
        mode=random.random()
        if mode<0.3: cols=[random.randrange(1<<M) for _ in range(n)]
        elif mode<0.5: # low weight structure: many zero/dup columns
            pool=[0]+[random.randrange(1,1<<M) for _ in range(2)]; cols=[random.choice(pool) for _ in range(n)]
        elif mode<0.7: # all distinct nonzero (Hamming-like / simplex-like)
            M=max(M,4); vs=list(range(1,1<<M)); random.shuffle(vs); cols=(vs*2)[:n]
        elif mode<0.85: # even-weight columns (extended): top bit 1 on all
            cols=[(1<<M)|random.randrange(1<<M) for _ in range(n)]
        else: # columns concentrated in a subspace of dim d near threshold
            d=random.randint(1,5); cols=[random.randrange(1<<d)<<random.randint(0,1) for _ in range(n)]
        s=random.randrange(1,1<<(M+1))
        for k in range(2,n):
            res=run(cols,s,k)
            if res is None: continue
            # note: s may lie outside span -> no members
            e=res['e']
            if e<=min(res['w'],res['T']) and n>=2*e+1:
                inside+=1
                bound=res['r'] if res['w']%2==0 else res['r']+1
                if res['rho']>bound:
                    viol+=1; print("VIOLATION",cols,s,res)
            stats[(res['rho']-res['r'])]=stats.get(res['rho']-res['r'],0)+1
    print("seed",seed,"inside",inside,"violations",viol,"rho-r hist",dict(sorted(stats.items())))
if __name__=="__main__":
    main(int(sys.argv[1]),int(sys.argv[2]))
