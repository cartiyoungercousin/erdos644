"""Edge/boundary stress of Theorem 9': hit equality in H2/H3/H4' and parity-tight sizes."""
import random, sys
from collections import defaultdict
from t9 import hypcheck, construct, verify
def trial(rng):
    M=6; alpha=rng.randrange(1,1<<M)
    kpar=rng.randint(0,1)
    # Omegas: w_i small, built explicitly from points of chosen classes
    def omega(wlen):
        # wlen points with xor alpha, wlen parity = kpar guaranteed by caller
        cs=[rng.randrange(1<<M) for _ in range(wlen-1)]
        x=alpha
        for c in cs:x^=c
        return cs+[x]
    ws=[]
    for _ in range(3):
        w=rng.choice([1,2,3,4,5,6,7,8]);
        if w%2!=kpar: w+=1
        ws.append(w)
    cols=[];Om=[]
    for w in ws:
        o=omega(w); Om.append(list(range(len(cols),len(cols)+w))); cols+=o
    # remaining points: some singleton classes, big class(es), few mid cells
    nsing=rng.randint(0,12)
    sing=rng.sample(range(1,1<<M),min(nsing,60))
    big=rng.randrange(1<<M); mids=[rng.randrange(1<<M) for _ in range(rng.randint(0,5))]
    rest=[]
    rest+=sing
    G=rng.randint(7,160); rest+=[big]*G
    for g in mids: rest+=[g]*rng.randint(2,25)
    cols+=rest
    n=len(cols); W=sum(ws)
    out=[]
    kmax=(4*n-W)//7
    for dj in range(0,6):
        k=kmax-dj
        if k>=1 and k%2==kpar: out.append((cols,alpha,k,Om))
    return out
def main(seed,trials):
    rng=random.Random(seed); n_ok=fail=tight=0; hist=defaultdict(int)
    for _ in range(trials):
        for cols,alpha,k,Om in trial(rng):
            # require V' classes: check alpha not in C trivial
            hy=hypcheck(cols,alpha,k,Om)
            if not hy.get('ok'): hist['hypfail']+=1; continue
            # margin
            n=len(cols);cnt=defaultdict(int)
            used=set(sum(Om,[]))
            for i in range(n):
                if i not in used: cnt[cols[i]]+=1
            sing=sum(1 for g in cnt if cnt[g]==1)
            w=[len(o) for o in Om]
            m2=k-(sum(w)+2*(max(w)-min(w))+4*hy['c']+6)
            m3=cnt[hy['gstar']]-(hy['u']+2*hy['f']+7)
            m4=hy['u']-sing
            if min(m2,m3,m4)<=1: tight+=1
            B=construct(cols,alpha,k,Om)
            v,msg=verify(cols,alpha,k,B)
            if v:n_ok+=1
            else: fail+=1; print("FAIL",msg,n,k)
    print("seed",seed,"OK",n_ok,"tight(margin<=1)",tight,"FAIL",fail,dict(hist))
main(int(sys.argv[1]),int(sys.argv[2]))
