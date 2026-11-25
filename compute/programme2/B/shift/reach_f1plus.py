"""[heuristic] reach of the F1+ / F1 criterion for random-like D' (dimension d' = rho N):
number of lam in D'(x)F2^3 at distance fN from the constants ~ 8 C(N, fN) 7^{fN} 8^{d' - N} (random-like),
bound per word: min(F1, F1+) with equal regions:
  F1+ : f <= 1/50: 7^{-fN};  f >= 1/50: exp((N/2)(ln(50/49) - h(f)))
  F1  : off-dominant mass spread uniformly over 7 values (typical): exp((N/2)(ln(8/7) - H(1-f, f/7 x 7)))
         [F1's water-filling bound evaluated at the typical type; for f <= 1/8 it is <= 7^{-fN/2}]
Exponent per N: E(f) = H2(f) + f ln 7 + (rho - 1) ln 8 + min(...).  Reach = largest rho with max_f E(f) < 0.
Also F1 alone (as in F''') for comparison."""
from math import log
def h(f): return 0 if f <= 0 or f >= 1 else -f*log(f)-(1-f)*log(1-f)
def F1p(f): return -f*log(7) if f <= 1/50 else 0.5*(log(50/49) - h(f))
def F1(f):
    H = h(f) + f*log(7)        # entropy of (1-f, f/7, ..., f/7)
    if 1 - f >= 7/8:           # near-constant regime: t_dom = 1, others share 1/7 uniformly -> (1/49)^{f/2}
        return -f*log(7)/1.0 * 0.5 - 0.5*f*log(7)  # t_u = (1/7)/7 = 1/49 each -> 49^{-f/2} = 7^{-f}
    return 0.5*(log(8/7) - H)
def reach(bound):
    lo, hi = 0.0, 1.0
    for _ in range(60):
        rho = (lo+hi)/2
        E = max(h(f) + f*log(7) + (rho-1)*log(8) + bound(f) for f in [i/4000 for i in range(1, 3500)])
        lo, hi = (rho, hi) if E < 0 else (lo, rho)
    return lo
print("reach with min(F1, F1+):", round(reach(lambda f: min(F1(f), F1p(f))), 4))
print("reach with F1+ alone:", round(reach(F1p), 4))
print("reach with F1 alone (typical types):", round(reach(F1), 4))
# two-valued words lam = u(x)1 + u'(x)mu, mu in D' of weight fN: count ~ 56 C(N,fN) 2^{d'-N}
def reach2(bound):
    lo, hi = 0.0, 1.0
    for _ in range(60):
        rho = (lo+hi)/2
        E = max(h(f) + (rho-1)*log(2) + bound(f) for f in [i/4000 for i in range(1, 2000)])
        lo, hi = (rho, hi) if E < 0 else (lo, rho)
    return lo
def F1_two(f):   # F1 water-filling for a two-valued word: t_dom = 1, t_u' = 1/7 if f <= 1/8
    return -0.5*f*log(7) if f <= 1/8 else 0.5*(log(8/7) - h(f))
print("two-valued words: reach with F1+:", round(reach2(F1p), 4), "; with F1 only:", round(reach2(F1_two), 4))
