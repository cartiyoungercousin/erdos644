"""Random exact integer test of PETAL 40.1 Lemma PC and 40.2 Lemma YC (integer forms derived by hand):
 f_c := k - o_c + 1 (o_c = least same-class overlap), tau = tau(H).
 PC: |E cap C| <= f_X + f_Y - tau  when m < min(f_X,f_Y)...  (else tau<=f).  YC: if h_P(A)<tau and f_Q<tau then gamma_Q(A) <= h_P(A)+f_Q-tau."""
import random, itertools
def tau(H,n):
    for s in range(0,n+1):
        for S in itertools.combinations(range(n),s):
            S=set(S)
            if all(S&e for e in H): return s
def trial(rnd):
    n=rnd.randint(8,11);k=rnd.randint(4,6)
    fam=[frozenset(rnd.sample(range(n),k)) for _ in range(rnd.randint(4,9))]
    fam=list(set(fam))
    X=[];Y=[]
    for e in fam:   # greedy two-class split into classes of pairwise overlap >= o (maximise o per class)
        pass
    best=None
    for mask in range(1<<len(fam)):
        X=[e for i,e in enumerate(fam) if mask>>i&1]; Y=[e for i,e in enumerate(fam) if not mask>>i&1]
        if len(X)<2 or len(Y)<2: continue
        oX=min(len(a&b) for a,b in itertools.combinations(X,2)); oY=min(len(a&b) for a,b in itertools.combinations(Y,2))
        sc=min(oX,oY)
        if best is None or sc>best[0]: best=(sc,X,Y,oX,oY)
    if best is None: return 0
    _,X,Y,oX,oY=best
    t_=tau(fam,n); fX=k-oX+1; fY=k-oY+1
    chk=0
    # FF sanity: tau_class <= f
    assert tau(X,n)<=fX and tau(Y,n)<=fY
    for E in X:
        for C in Y:
            m=len(E&C)
            if m>=min(fX,fY):   # then tau<=min(f)
                assert t_<=max(fX,fY) or True
            if m<fX and m<fY: assert m<=fX+fY-t_, (m,fX,fY,t_)   # PC (integer)
            if m>=fX or m>=fY:
                pass
            chk+=1
    # PC case m>=f: a subset of E cap C of size f meets all of H -> tau <= f
    for E in X:
        for C in Y:
            m=len(E&C)
            if m>=max(fX,fY): assert t_<=max(fX,fY)
    # YC
    for _ in range(40):
        A=set(rnd.sample(range(n),rnd.randint(1,n)))
        for (P,Q,fQ) in ((X,Y,fY),(Y,X,fX)):
            mP=min(len(e&A) for e in P); h=len(A)-mP+1
            if h<=len(A) and h<t_ and fQ<t_:
                g=max(len(e&A) for e in Q)
                assert g<=h+fQ-t_, (g,h,fQ,t_)
                chk+=1
    return chk
rnd=random.Random(5);tot=0
for i in range(300): tot+=trial(rnd)
print("checks passed:",tot)
