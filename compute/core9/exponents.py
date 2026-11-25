r"""CORE 57: first-order exponents (nats per k) for random T-covering families.  [computed float]
gamma  = (N-t) h(omega/(N-t))      : -log density of the sparsest possible T-covering family (and of the threshold random family)
F      = N h(3/(2N)) + (3/2) ln 3  : log number of perfect pencil frames
D1     = c h(1/(2c)) + ln 2        : log number of pencils through one co-edge
pen_sparse = F - 3 gamma           : log E[#pencils], binomial family at the covering threshold
pen_dump   = F + 3 p, p = N h(t/N) - N h(c/N) (<0): the same for the random-dump model (one uniform dump per request)
G7     = N * maxent(co-types containing a Fano line, mean size 7c/N) : log number of Fano-type good sevens;  sev = G7 - 7 gamma
sh     = shadow density exponent at level 3N/7 for the threshold family: (4N/7) h(7/(4N)) - gamma  (if < 0: shadow is sparse)
"""
import math, sys
def h(x): return 0.0 if x <= 0 or x >= 1 else -x * math.log(x) - (1 - x) * math.log(1 - x)
CNT = [7, 28, 21, 7, 1]                     # co-types of size 3..7 containing a Fano line
def maxent(mean):
    lo, hi = 1e-9, 1e9
    for _ in range(200):
        x = math.sqrt(lo * hi)
        den = sum(c * x ** j for j, c in enumerate(CNT)); m = 3 + sum(j * c * x ** j for j, c in enumerate(CNT)) / den
        if m < mean: lo = x
        else: hi = x
    return math.log(den) - (mean - 3) * math.log(x)
for t in (0.7501, 0.76, 0.78):
    print(f"t={t}:  N   omega  gamma   F     pen_sparse pen_dump  G7-7gamma  shadow(3N/7)")
    lo, hi = 3 * t - 0.5, 3 - t
    for i in range(11):
        N = lo + (hi - lo) * i / 10; c = N - 1; om = c - t
        g = (N - t) * h(om / (N - t)); F = N * h(1.5 / N) + 1.5 * math.log(3)
        p = N * h(t / N) - N * h(c / N)
        G7 = N * maxent(7 * c / N)
        sh = (4 * N / 7) * h(7 / (4 * N)) - g if 4 * N / 7 > 1 else float('-inf')
        print(f"   {N:.4f} {om:.4f} {g:.4f} {F:.4f}  {F-3*g:+.4f}   {F+3*min(p,0):+.4f}   {G7-7*g:+.4f}    {sh:+.4f}")
