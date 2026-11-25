"""Independent simulation of PETAL 40.2 Theorem CR on an explicit fixed two-class arena-with-pool family.
Written from the statement only.  Family: R_X, R_Y disjoint arenas, big pool.  Class c = all k-sets with >= k-rho points in R_c.
She knows H.  Adversary answers each request by ANY member avoiding it (several greedy/random policies)."""
import random, sys, itertools
def twocover(sets, N):
    m=len(sets); mask=[0]*N
    for j,s in enumerate(sets):
        for x in s: mask[x]|=1<<j
    ms=sorted(set(mask)); full=(1<<m)-1
    for a in range(len(ms)):
        for b in range(a,len(ms)):
            if ms[a]|ms[b]==full: return True
    return False
def play(k,T,rho,h,seed,policy):
    rnd=random.Random(seed)
    nx=h+k-rho-1; npool=300
    N=2*nx+npool
    R=[list(range(0,nx)),list(range(nx,2*nx))]
    pool=list(range(2*nx,N))
    reg=[0]*nx+[1]*nx+[2]*npool
    replies=[];cls=[];maxreq=0
    def reply(S,forced_class=None):
        S=set(S); assert len(S)<=T
        free=lambda pts:[x for x in pts if x not in S]
        opts=[]
        for c in (0,1):
            if len(free(R[c]))>=k-rho: opts.append(c)
        assert opts, "no member avoids S: tau(H)<=|S|"
        c=rnd.choice(opts) if policy!='greedy' else opts[0 if rnd.random()<.5 else -1]
        # weights: points in many previous replies preferred (dense adversary)
        w={}
        for r_ in replies:
            for x in r_: w[x]=w.get(x,0)+1
        key=lambda x:(-w.get(x,0) if policy!='random' else 0, rnd.random())
        inreg=sorted(free(R[c]),key=key)[:k-rho]
        rest=sorted([x for x in range(N) if x not in S and x not in set(inreg)],key=key)[:rho]
        rep=set(inreg)|set(rest)
        assert len(rep)==k and not (rep&S)
        return rep,c
    # petal phase: unforced running intersections, b each
    b=T//2
    I=[None,None]
    cntc=[0,0]; pet=[[],[]]
    for step in range(7):
        S=set()
        for c in (0,1):
            if cntc[c]<4:
                cur=I[c] if I[c] is not None else set(range(N))
                S|=set(sorted(cur)[:b]) if I[c] is not None else set()
        if len(S)>T: S=set(sorted(S)[:T])
        rep,c=reply(S); maxreq=max(maxreq,len(S))
        replies.append(rep);cls.append(c)
        if cntc[c]<4:
            pet[c].append(rep); cntc[c]+=1
            I[c]=set(rep) if I[c] is None else I[c]&rep
        if max(cntc)==4: break
    P=0 if cntc[0]==4 else 1
    petals=pet[P]
    assert not (set.intersection(*petals)), "petal intersection nonempty"
    U=set().union(*petals)
    A=set(R[P]); B=sorted(U-A)
    third=-(-len(B)//3)
    Bs=[set(B[i*third:(i+1)*third]) for i in range(3)]
    Z=set(); 
    centres=[]
    for j in range(3):
        Zi=Z&A
        G=set(Zi)
        for x in R[P]:
            if len(G)>=h: break
            G.add(x)
        S=G|(set(B)-Bs[j])
        maxreq=max(maxreq,len(S))
        assert len(S)<=T, ("request too big",len(S),T)
        rep,c=reply(S); assert c!=P
        centres.append(rep); Z|=rep&U
    seven=petals+centres
    return not twocover(seven,N), maxreq, cntc
if __name__=="__main__":
    k,T,rho,h=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])
    res=[play(k,T,rho,h,s,pol) for pol in ('random','dense','greedy') for s in range(int(sys.argv[5]))]
    print("params k,T,rho,h",k,T,rho,h,"wins",sum(r[0] for r in res),"/",len(res),"max request",max(r[1] for r in res))
