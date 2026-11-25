from math import comb, log, ceil, floor
from fractions import Fraction as F
def lc(a,b): return log(comb(a,b))
worst={}
for eps in [0.04,0.02,0.01,0.005,0.002]:
    k=int(40/eps/ 4) ; k+= k%2   # large even k, then odd
    for kk in (k,k+1):
        T=int((0.75+eps)*kk+1e-9)
        rm=0; bad=0
        lo=-(-(6*T-kk)//2)+1; hi=5*T-2*kk-(2 if kk%2 else 0)
        for n in range(max(lo,kk+T),hi+1,max(1,(hi-lo)//12)):
            c=n-kk
            if c<T: continue
            m=-(-7*c//3)-n
            assert m>=0 and c==(3*(n+m))//7, (kk,T,n)
            npr=n+m
            o=n-2*T if kk%2==0 else n-2*T+1
            eta=F(1,14)
            ok = eta*npr<=o<=c-eta*npr and 2*c-npr<0
            if not ok: bad+=1
            # density lower bound exponent
            ld=-(lc(n-T,c-T)+lc(npr,c)-lc(n,c))
            r=-ld/npr; rm=max(rm,r)
        print('eps',eps,'k',kk,'T',T,'maxr',round(rm,4),'FR-range violations',bad)
