# Independent check of CORE 90.1/90.2 (no import from compute/strip).
import itertools, random, sys
from math import comb, lgamma, log
LINES=[(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
def build(k,T,n,o,rule):
    """explicit seven sets on points 0..n-1 following the 90.2 recipe; returns (sets,c) or None"""
    c=n-k
    A=c-o; G=n-(2*c-o)
    if min(A,G,o)<0 or o>c: return None
    pts=list(range(n)); 
    O=pts[:o]; Ap=pts[o:o+A]; Bp=pts[o+A:o+2*A]; Gp=pts[o+2*A:]
    assert len(Gp)==G
    cls={l:[] for l in LINES}
    cls[(0,1,2)]=O
    h=A//2; assert A%2==0
    cls[(0,3,4)]=Ap[:h]; cls[(0,5,6)]=Ap[h:]
    cls[(1,3,5)]=Bp[:h]; cls[(1,4,6)]=Bp[h:]
    g=G//2
    if G%2==0: cls[(2,3,6)]=Gp[:g]; cls[(2,4,5)]=Gp[g:]
    else: cls[(2,3,6)]=Gp[:g+1]; cls[(2,4,5)]=Gp[g+1:]
    K=[None]*7
    L=[[x for l in LINES if j in l for x in cls[l]] for j in range(7)]
    return L,O,Ap,Bp,Gp,c
def check(k,T,n,rng,pads=3):
    c=n-k
    o=n-2*T if k%2==0 else n-2*T+1
    r=build(k,T,n,o,None)
    if r is None: return 'cells'
    L,O,Ap,Bp,Gp,c=r
    # K0=O+A, K1=O+B must be members of size c with intersection o
    K0=set(O)|set(Ap); K1=set(O)|set(Bp)
    if len(K0)!=c or len(K1)!=c or len(K0&K1)!=o: return 'KK'
    if any(len(L[j])>T for j in range(2,7)): return 'load %s'%[len(L[j]) for j in range(2,7)]
    for _ in range(pads):
        S=[K0,K1]
        for j in range(2,7):
            s=set(L[j]); rest=[x for x in range(n) if x not in s]; rng.shuffle(rest)
            S.append(s|set(rest[:c-len(s)]))
        assert all(len(s)==c for s in S)
        for x in range(n):
            for y in range(x,n):
                if not any(x in s and y in s for s in S): return 'pair %d %d'%(x,y)
    return 'ok'
if __name__=='__main__':
    rng=random.Random(1); bad=0; tot=0
    for k in range(8,41):
        for T in range(-(-3*k//4)+0,k):
            if 4*T<=3*k: continue
            lo=-(-(6*T-k)//2)+1   # n > 3T-k/2
            hi=5*T-2*k-(2 if k%2 else 0)
            for n in range(max(lo,k+T),hi+1):
                tot+=1; res=check(k,T,n,rng)
                if res!='ok': bad+=1; print('FAIL',k,T,n,res)
    print('strip triples',tot,'failures',bad)
    # just above the strip, parity-rule recipe should break (load) -- expected
    for k,T in [(24,19),(32,25),(33,26)]:
        n=5*T-2*k+(1 if k%2==0 else -1)+ (0 if k%2==0 else 3)
        print('above',k,T,n,check(k,T,n,rng,1))
    # exhaustive integer Fano-shape search for odd k, strip top and just above
    def feas(k,T,n):
        c=n-k
        for o in range(max(0,n-2*k),c):
            A=c-o;G=n-2*c+o
            if G<0: continue
            for a1 in range(A+1):
              a2=A-a1
              for b1 in range(A+1):
                b2=A-b1
                for g1 in range(G+1):
                  g2=G-g1
                  for y in range(o+1):
                    for p in range(y+1):
                      for q in range(y-p+1):
                        for r_ in range(y-p-q+1):
                          s=y-p-q-r_
                          z=o-y
                          # lines: 012:z, 034:p+a1, 056:q+a2, 135:r+b1, 146:s+b2, 236:g1, 245:g2
                          L2=z+g1+g2
                          L3=(p+a1)+(r_+b1)+g1; L4=(p+a1)+(s+b2)+g2
                          L5=(q+a2)+(r_+b1)+g2; L6=(q+a2)+(s+b2)+g1
                          if max(L2,L3,L4,L5,L6)<=T: return True
        return False
    for k,T in [(9,8),(11,10),(13,11)]:
        for n in range(5*T-2*k-3, 5*T-2*k+2):
            print('exh odd',k,T,n,'parity-bound',5*T-2*k-2,'shape feasible',feas(k,T,n))
