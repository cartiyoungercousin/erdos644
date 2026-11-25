r"""CORE 70-72: first-order exponents (nats per k) for the entropy formulation.  [computed float; closed forms proved by hand]
Phi    = N h(t/N) - c h(t/c)          : log of the counting lower bound C(N,t)/C(c,t) on |C| for a T-covering family
Lam0   = (7/4) h(3/7) = log C(7/4,3/4): log-size of the 7-free family P' = {Y' u A : A in C(W,3/4)}, |W| = 7/4, |Y'| = delta
E0     = Lam0 - Phi                   : > 0  <=>  the size/entropy (Gilmer-shape) route is dead at (t,N)
r      = log C(N,t) - log C(delta,eps) - Lam0 : rate of Pr_unif[|S n Y'| <= eps] (requests P' fails to cover)
iid    = (1 - (c/N)^2)^7              : Jensen lower bound on E[uncovered pair mass]/N^2 for 7 iid members of ANY law
TCmin  = 7 h(c/N) - Hfano             : least total correlation (per point) of a Fano-type co-type law with marginals c/N
pdump  = F + 3 p                      : log E[#pencils] in the uniform-random-dump family (CORE 57 / exponents.py)
"""
import math
def h(x): return 0.0 if x <= 0 or x >= 1 else -x * math.log(x) - (1 - x) * math.log(1 - x)
def lC(a, b): return 0.0 if b <= 0 or b >= a else a * h(b / a)
CNT = [7, 28, 21, 7, 1]
def maxent(mean):
    lo, hi = 1e-9, 1e9
    for _ in range(200):
        x = math.sqrt(lo * hi); den = sum(cc * x ** j for j, cc in enumerate(CNT))
        mm = 3 + sum(j * cc * x ** j for j, cc in enumerate(CNT)) / den
        lo, hi = (x, hi) if mm < mean else (lo, x)
    return math.log(den) - (mean - 3) * math.log(x)
Lam0 = lC(1.75, 0.75)
print(f"Lam0 = log C(7/4,3/4) = {Lam0:.4f}")
for t in (0.7501, 0.76, 0.78, 0.80):
    eps = t - 0.75; lo, hi = 3 * t - 0.5, 3 - t
    print(f"t={t}:   N     Phi     E0=Lam0-Phi   r      iid-unc   TCmin   pdump")
    for i in range(11):
        N = lo + (hi - lo) * i / 10; c = N - 1; d = N - 1.75
        Phi = lC(N, t) - lC(c, t)
        typ = t * d / N
        r = (lC(N, t) - lC(d, eps) - Lam0) if eps < typ else 0.0
        iid = (1 - (c / N) ** 2) ** 7
        TC = 7 * h(c / N) - N * maxent(7 * c / N) / N
        F = N * h(1.5 / N) + 1.5 * math.log(3); p = N * h(t / N) - N * h(c / N)
        print(f"     {N:.4f}  {Phi:.4f}  {Lam0-Phi:+.4f}     {r:.4f}  {iid:.4f}   {TC:.4f}  {F+3*min(p,0):+.4f}")
