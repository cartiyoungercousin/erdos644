"""Pure integer arithmetic check of the cost inequality in 23.2 (ignoring the game): over all (tauX,tauY) with rho maximal."""
import math, sys
from fractions import Fraction as Fr
def worst(k,T):
    t=Fr(T,k); th=(6*t-2)/5
    best=None
    for tx in range(0,k+1):
        for ty in range(0,k+1):
            if tx+ty<=T: continue
            rho=[]
            ok=True
            for tc in (tx,ty):
                # c = k - tau - rho > th*k, rho>=0 integer, max rho
                r=math.ceil(k-tc-th*k)-1   # strict: k-tc-r > th k  => r < k-tc-thk
                if r<0: ok=False;break
                rho.append(r)
            if not ok: continue
            for X in (0,1):
                tX,tY=(tx,ty)[::-1] if X==1 else (tx,ty)
                rX,rY=(rho[1],rho[0]) if X==1 else (rho[0],rho[1])
                valid = (tx>=Fr(T,2) and ty>=Fr(T,2)) or (tX>=Fr(T,2) and tY<Fr(T,2))
                if not valid: continue
                b=4*rX
                # B split in 3 near-equal parts; biggest request = b - floor(b/3)
                cost=max(tX+1,2*rY)+ (b-b//3)
                slack=T-cost
                if best is None or slack<best[0]: best=(slack,tx,ty,rho,X,cost)
    return best
for (k,T) in [(60,45),(100,75),(151,112),(150,112),(200,150),(302,224),(300,230),(300,260),(200,190)]:
    print(k,T,float(Fr(T,k)),worst(k,T)); sys.stdout.flush()
