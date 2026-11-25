"""Exhaustive-ish test of Lemma B (rainbow matching) and Lemma C (fixed-size subset sums) and Lemma A."""
import random, itertools
from math import comb
def span(vs):
    S={0}
    for v in vs: S|={x^v for x in S}
    return S
def rank(vs):
    b=[]
    for v in vs:
        for x in b: v=min(v,v^x)
        if v:b.append(v)
    return len(b)
random.seed(5); fB=fC=nB=nC=0
for _ in range(1500):
    n=random.randint(3,13); M=random.randint(1,6)
    cols=[random.randrange(1<<M) for _ in range(n)]
    if random.random()<0.4:
        pool=[random.randrange(1<<M) for _ in range(random.randint(2,5))]; cols=[random.choice(pool) for _ in range(n)]
    e=rank([c^cols[0] for c in cols[1:]])
    E=span([c^cols[0] for c in cols[1:]])
    if n>=2*e+1:
        nB+=1
        # find e disjoint pairs w/ independent differences by brute-force search
        found=False
        def rec(avail,chosen):
            global found
            if found: return
            if len(chosen)==e:
                if rank([cols[i]^cols[j] for i,j in chosen])==e: found=True
                return
            if len(avail)<2*(e-len(chosen)): return
            i=avail[0]
            for j in avail[1:]:
                rec([x for x in avail if x not in(i,j)],chosen+[(i,j)])
            rec(avail[1:],chosen)
        rec(list(range(n)),[])
        if not found: fB+=1; print("LemmaB FAIL",cols)
        for w in range(e,n-e+1):
            nC+=1
            sums=set()
            for Q in itertools.combinations(range(n),w):
                x=0
                for i in Q:x^=cols[i]
                sums.add(x)
            target={ (cols[0] if w%2 else 0)^y for y in E}
            if sums!=target: fC+=1; print("LemmaC FAIL",cols,w)
print("LemmaB tests",nB,"fail",fB,"| LemmaC tests",nC,"fail",fC)
