"""Which Corollary-7 targets does Theorem D (counting form) exclude?
Theorem D: if dim C_ev >= max(k+r, T, ceil((n+1)/2)) then rho_par <= r+1.  dim C_ev >= ceil(log2 LB),
LB = C(n,k+r)/C(n-k,r) <= |H|.  A Corollary-7 target is (r, rho) with 7 rho > 3(4n-7k), rho = k mod 2,
rho <= min(2r+1, k) (Lemma 8) and rho >= r+2 (otherwise it is not a target once rho_par <= r+1... we list all).
Prints, for T = tau-1 one above the known benchmark, the r for which a target exists and counting does NOT apply.
"""
from math import comb, log2, ceil
def covered(k, T, r):
    n = k + r + T
    L0 = ceil(log2(comb(n, k+r)) - log2(comb(n-k, r)) - 1e-12)
    return L0 >= max(k + r, T, ceil((n+1)/2))
def targets(k, T):
    out = []
    for r in range(0, k):
        n = k + r + T
        for rho in range(r+2, min(2*r+1, k)+1):
            if rho % 2 != k % 2: continue
            if 7*rho > 3*(4*n - 7*k):
                out.append(r); break
    return out
print('k, T, uncovered r (targets that Theorem D-by-counting does not exclude)')
for k in range(4, 81):
    for T in sorted({(3*k)//4 + 1, -(-3*k//4)}):   # T = floor(3k/4)+1 and ceil(3k/4)
        unc = [r for r in targets(k, T) if not covered(k, T, r)]
        if unc:
            n_lo = k + min(unc) + T
            print(k, T, f'uncovered r in [{min(unc)},{max(unc)}] ({len(unc)} values); min N there = {n_lo/k:.3f}')
