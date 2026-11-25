"""Independent verifier for notes/PROGRAMME2_NC.md (Lemma NC1, Theorem NC, NC0, E_k).

Fresh code: does not import compute/programme2/NC.  Sets are int bitmasks.
(7,2)-test: SAT over member-selection variables (<= 7 chosen, every pair/singleton
of V avoided by some chosen member); every SAT witness is re-checked by brute force.
"""
import itertools, random, sys, json, math
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

FANO = [(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
PAIRS = [(1,3),(4,5),(6,2)]          # pair s with line {0} u PAIRS[s]

def pc(x): return bin(x).count("1")
def bits(x):
    i=0
    while x:
        if x&1: yield i
        x>>=1; i+=1

def fano_sanity():
    pts=set(range(7))
    for a,b in itertools.combinations(range(7),2):
        assert sum(1 for L in FANO if a in L and b in L)==1
    for s,(p,q) in enumerate(PAIRS): assert any(set(L)=={0,p,q} for L in FANO)
    avoid=[L for L in FANO if 0 not in L]; assert len(avoid)==4
    for L in avoid:
        for p,q in PAIRS: assert (p in L)!=(q in L)
    return True

def no2transversal(seven, V):
    """brute force: True iff no set of <=2 points of V meets every member of seven"""
    vs=list(bits(V))
    for i,u in enumerate(vs):
        for v in vs[i:]:
            m=(1<<u)|(1<<v)
            if all(B&m for B in seven): return False
    return True

def good_seven(H, V):
    """return a list of <=7 members with no <=2-point transversal, or None"""
    H=list(dict.fromkeys(H)); m=len(H)
    if m==0: return None
    var=lambda i:i+1
    s=Cadical153()
    vs=list(bits(V))
    for i,u in enumerate(vs):
        for v in vs[i:]:
            msk=(1<<u)|(1<<v)
            cl=[var(j) for j,B in enumerate(H) if not B&msk]
            if not cl: s.delete(); return None
            s.add_clause(cl)
    enc=CardEnc.atmost([var(j) for j in range(m)],bound=7,top_id=m,encoding=EncType.seqcounter)
    for c in enc.clauses: s.add_clause(c)
    ok=s.solve(); res=None
    if ok:
        mod=set(x for x in s.get_model() if x>0)
        res=[H[j] for j in range(m) if var(j) in mod]
        assert len(res)<=7 and no2transversal(res,V), "SAT witness failed brute check"
    s.delete(); return res

def tau(H, V, lo=0):
    vs=list(bits(V)); idx={v:i+1 for i,v in enumerate(vs)}; n=len(vs)
    for t in range(lo, n+1):
        s=Cadical153()
        for B in H: s.add_clause([idx[v] for v in bits(B)])
        enc=CardEnc.atmost(list(range(1,n+1)),bound=t,top_id=n,encoding=EncType.seqcounter)
        for c in enc.clauses: s.add_clause(c)
        r=s.solve(); s.delete()
        if r: return t
    return n

def is_complete(H, Wl, k, d):
    """every (k+d)-subset of W contains a member"""
    Wm=sum(1<<v for v in Wl); HW=[B for B in H if B&~Wm==0]
    if len(Wl)<k+d: return True
    for S in itertools.combinations(Wl,k+d):
        sm=sum(1<<v for v in S)
        if not any(B&~sm==0 for B in HW): return False
    return True

def find_triple(H, Wm, bound):
    """G1,G2,G3 (repeats allowed) with empty common intersection and |W n union| <= bound"""
    H=list(dict.fromkeys(H)); m=len(H)
    for i in range(m):
        for j in range(i,m):
            I=H[i]&H[j]; U=(H[i]|H[j])&Wm
            if pc(U)>bound: continue
            if I==0: return (H[i],H[j],H[j])
            for l in range(j,m):
                if I&H[l]==0 and pc(U|(H[l]&Wm))<=bound: return (H[i],H[j],H[l])
    return None

def nc1_colouring(H, V, Wm, G, k, d):
    """construction of the NC1 proof; returns colour dict and checks every line closed"""
    U=G[0]|G[1]|G[2]; col={}
    for v in bits(V & ~U): col[v]=0
    X=[[],[],[]]
    for v in bits(U):
        s=next(s for s in range(3) if not (G[s]>>v)&1); X[s].append(v)
    for s,(p,q) in enumerate(PAIRS):
        inW=[v for v in X[s] if (Wm>>v)&1]; out=[v for v in X[s] if not (Wm>>v)&1]
        random.shuffle(inW); h=(len(inW)+random.randint(0,1))//2
        for v in inW[:h]: col[v]=p
        for v in inW[h:]: col[v]=q
        for v in out: col[v]=random.choice((p,q))
    seven=[]
    for L in FANO:
        Lm=sum(1<<v for v,c in col.items() if c in L)
        if 0 not in L: assert pc(Lm&Wm)<=pc(Wm)-k-d, "line too big on W"
        cand=[B for B in H if B&Lm==0]
        assert cand, "line %s is a transversal"%(L,)
        seven.append(cand[0])
    assert no2transversal(seven,V)
    return seven

# ---------------- generators ----------------
def gen_W_part(w,k,d,kind,rng):
    Wl=list(range(w)); H=set()
    if kind=="complete":
        for S in itertools.combinations(Wl,k): H.add(sum(1<<v for v in S))
    elif kind=="parity":
        w1=rng.randint(1,w-1); W1=sum(1<<v for v in range(w1))
        for S in itertools.combinations(Wl,k):
            m=sum(1<<v for v in S)
            if pc(m&W1)%2==1: H.add(m)
    elif kind=="cells":
        r=rng.randint(2,3); cell=[rng.randrange(r) for _ in Wl]; tgt=[rng.randint(0,1) for _ in range(r)]
        for S in itertools.combinations(Wl,k):
            if all(sum(1 for v in S if cell[v]==c)%2==tgt[c] for c in range(r)):
                H.add(sum(1<<v for v in S))
    # greedy fix-up to (W,d)-completeness with members of varied size <= k
    subs=list(itertools.combinations(Wl,k+d)); rng.shuffle(subs)
    for S in subs:
        sm=sum(1<<v for v in S)
        if any(B&~sm==0 for B in H): continue
        sz=rng.choice([k,k,k,max(1,k-1),max(1,k-2)])
        H.add(sum(1<<v for v in rng.sample(S,sz)))
    # prune: remove random members while completeness holds (makes H[W] thin)
    if kind!="complete" and rng.random()<0.7:
        Hl=list(H); rng.shuffle(Hl)
        for B in Hl[:min(len(Hl),40)]:
            H.discard(B)
            if not is_complete(list(H),Wl,k,d): H.add(B)
    return list(H)

def gen_outside(w,z,k,rng,style,cnt):
    W=list(range(w)); Z=list(range(w,w+z)); out=[]
    for _ in range(cnt):
        if style=="random":
            sz=rng.randint(1,k); pool=W+Z; S=rng.sample(pool,min(sz,len(pool)))
            if not any(v>=w for v in S): S[0]=rng.choice(Z)
        elif style=="bigW":   # large W-trace plus a few outside points
            zo=rng.randint(1,min(2,z)); S=rng.sample(Z,zo)+rng.sample(W,min(k-zo,w))
        elif style=="star":   # all through a fixed outside point
            S=[w]+rng.sample(W+Z[1:],rng.randint(0,k-1))
        elif style=="pure":   # entirely outside W
            S=rng.sample(Z,rng.randint(1,min(k,z)))
        out.append(sum(1<<v for v in set(S)))
    return out

def run(seed, N):
    rng=random.Random(seed); random.seed(seed)
    st=dict(inst=0,nc1_hyp=0,nc1_ok=0,thm_hyp=0,thm_ok=0,small_H=0,bnd=0,bnd72=0,fail=[])
    for it in range(N):
        k=rng.randint(3,8); d=rng.choice([0,0,1,1,2])
        w=rng.randint(k+d+2, min(k+d+7, 13)); z=rng.randint(1,5)
        kind=rng.choice(["complete","parity","cells","random"])
        if kind=="complete" and rng.random()<0.5: kind="random"
        HW=gen_W_part(w,k,d,kind,rng)
        style=rng.choice(["random","bigW","star","pure","none"])
        out=[] if style=="none" else gen_outside(w,z,k,rng,style,rng.randint(1,25))
        H=list(dict.fromkeys(HW+out)); V=0
        for B in H: V|=B
        Wm=(1<<w)-1; Wl=list(range(w))
        assert is_complete(H,Wl,k,d)
        st["inst"]+=1
        if len(H)<7: st["small_H"]+=1
        bound=2*(w-k-d)-3
        G=find_triple(H,Wm,bound)
        gs=None
        if G is not None:
            st["nc1_hyp"]+=1
            nc1_colouring(H,V,Wm,G,k,d)
            gs=good_seven(H,V)
            if gs is None: st["fail"].append(("NC1",seed,it)); print("NC1 FAIL",k,d,w,kind,style,flush=True)
            else: st["nc1_ok"]+=1
        a=max(0,2*k+2*d+3-w); t=tau(H,V)
        thr=(k+1)/2+a
        if t>thr:
            st["thm_hyp"]+=1
            A=sum(1<<v for v in rng.sample(Wl,a)); HA=[B for B in H if B&A==0]
            assert tau(HA,V)>(k+1)/2
            G2=find_triple(HA,Wm,10**9); assert G2 is not None, "A0 failed"
            assert pc((G2[0]|G2[1]|G2[2])&Wm)<=bound
            nc1_colouring(H,V,Wm,G2,k,d)
            if gs is None: gs=good_seven(H,V)
            if gs is None: st["fail"].append(("THM",seed,it)); print("THM FAIL",flush=True)
            else: st["thm_ok"]+=1
        elif t>=thr-1 and G is None:
            st["bnd"]+=1
            if good_seven(H,V) is None: st["bnd72"]+=1
    return st

# ---------------- adversarial mode: raise tau with members spread over W ----------------
def min_transversal(H, V):
    vs=list(bits(V)); idx={v:i+1 for i,v in enumerate(vs)}; n=len(vs)
    for t in range(0,n+1):
        s=Cadical153()
        for B in H: s.add_clause([idx[v] for v in bits(B)])
        enc=CardEnc.atmost(list(range(1,n+1)),bound=t,top_id=n,encoding=EncType.seqcounter)
        for c in enc.clauses: s.add_clause(c)
        if s.solve():
            M=sum(1<<vs[i-1] for i in s.get_model()[:n] if i>0); s.delete(); return t,M
        s.delete()

def run_kill(seed, N):
    rng=random.Random(seed); random.seed(seed)
    st=dict(inst=0,thm_hyp=0,thm_ok=0,nc1_hyp=0,nc1_ok=0,just_below=0,just_below_72=0,fail=[])
    for it in range(N):
        k=rng.randint(3,8); d=rng.choice([0,1,1,2,2])
        w=rng.randint(k+d+2, min(k+d+6, 13))
        HW=gen_W_part(w,k,d,rng.choice(["parity","cells","random"]),rng)
        Wm=(1<<w)-1; Wl=list(range(w)); H=list(HW); nxt=w
        a=max(0,2*k+2*d+3-w); thr=(k+1)/2+a
        V=0
        for B in H: V|=B
        snap=None
        for _ in range(40):
            t,M=min_transversal(H,V)
            if t>thr: break
            if t==math.floor(thr) or (t<thr and t+1>thr): snap=list(H)
            freeW=[v for v in Wl if not (M>>v)&1]
            j=rng.randint(1,max(1,k//3))          # outside points, mostly fresh
            outs=[]
            for _ in range(j):
                if nxt>w and rng.random()<0.4:
                    cand=[v for v in range(w,nxt) if not (M>>v)&1]
                    if cand: outs.append(rng.choice(cand)); continue
                outs.append(nxt); nxt+=1
            Wpart=rng.sample(freeW,min(len(freeW),k-len(set(outs))))
            B=sum(1<<v for v in set(outs)|set(Wpart)); H.append(B); V|=B
        H=list(dict.fromkeys(H)); st["inst"]+=1
        assert is_complete(H,Wl,k,d)
        bound=2*(w-k-d)-3
        if snap is not None:
            snap=list(dict.fromkeys(snap)); Vs=0
            for B in snap: Vs|=B
            st["just_below"]+=1
            if good_seven(snap,Vs) is None: st["just_below_72"]+=1
        t=tau(H,V)
        G=find_triple(H,Wm,bound)
        if G is not None:
            st["nc1_hyp"]+=1; nc1_colouring(H,V,Wm,G,k,d)
            if good_seven(H,V) is None: st["fail"].append(("NC1",seed,it))
            else: st["nc1_ok"]+=1
        if t>thr:
            st["thm_hyp"]+=1
            A=sum(1<<v for v in rng.sample(Wl,a)); HA=[B for B in H if B&A==0]
            assert tau(HA,V)>(k+1)/2
            G2=find_triple(HA,Wm,10**9); assert G2 is not None
            assert pc((G2[0]|G2[1]|G2[2])&Wm)<=bound
            nc1_colouring(H,V,Wm,G2,k,d)
            if good_seven(H,V) is None: st["fail"].append(("THM",seed,it))
            else: st["thm_ok"]+=1
    return st

# ---------------- Lemma A0 and SAT-vs-exhaustive cross-check ----------------
def run_a0(seed, N):
    rng=random.Random(seed); bad=0; tight=0; cnt=0
    for _ in range(N):
        k=rng.randint(2,7); n=rng.randint(k,12)
        H=[]
        for _ in range(rng.randint(1,30)):
            B=sum(1<<v for v in rng.sample(range(n),rng.randint(1,k)))
            if all(B&C&D for C in H for D in H+[B]) and all(B&C for C in H) and B: H.append(B)
        V=0
        for B in H: V|=B
        assert find_triple(H,V,10**9) is None
        t=tau(H,V); cnt+=1
        if t>(k+1)/2: bad+=1
        if t==(k+1)//2 and k%2==1: tight+=1
    return dict(a0_inst=cnt,a0_viol=bad,a0_tight_odd_k=tight)

def exhaustive_good7(H,V):
    H=list(dict.fromkeys(H))
    for r in range(1,8):
        for S in itertools.combinations(H,r):
            if no2transversal(S,V): return list(S)
    return None

def run_cross(seed,N):
    rng=random.Random(seed); agree=0
    for _ in range(N):
        n=rng.randint(4,9); k=rng.randint(2,4)
        H=list({sum(1<<v for v in rng.sample(range(n),rng.randint(1,k))) for _ in range(rng.randint(3,16))})
        V=0
        for B in H: V|=B
        a=good_seven(H,V) is None; b=exhaustive_good7(H,V) is None
        assert a==b, "SAT/exhaustive disagree"; agree+=1
    return dict(cross_agree=agree)

if __name__=="__main__":
    assert fano_sanity()
    seed=int(sys.argv[1]); N=int(sys.argv[2])
    mode=sys.argv[3] if len(sys.argv)>3 else "rand"
    st={"rand":run,"kill":run_kill,"a0":run_a0,"cross":run_cross}[mode](seed,N); print(json.dumps(st))
