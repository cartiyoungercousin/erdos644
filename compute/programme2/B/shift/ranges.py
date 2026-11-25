"""Asymptotic ranges (normalised by k) for PROGRAMME2_B section 8/9.
L = log2( C(n,k+r)/C(n-k,r) ) / k  is the counting lower bound on log2|H|/k, hence on dim C/k.
(a) Theorem S0 (shift 0): needs e <= min((k-1)/2, n - 3k/2) with e <= n - L - 1; and |H| > 2^(n/2) (k = 2 mod 4).
(b) Theorem D with ground set shrunk by x (no recount: e' <= e <= n - L): needs n - L <= min(k + r, T - x).
    recount version (task2/asymptotic.py): g(omega, t - x) >= 0."""
from math import log2
def h(p): return 0.0 if p <= 0 or p >= 1 else -p*log2(p)-(1-p)*log2(1-p)
def L(w, e):           # omega = r/k, eps: T = (3/4+eps)k, N = 7/4 + omega + eps
    t = 0.75+e; N = 1+w+t
    return N*h((1+w)/N) - (t+w)*h(w/(t+w))
def g_recount(w, t): N = 1+w+t; return N*h((1+w)/N) - (t+w)*h(w/(t+w)) - (1+w)
grid = [(w/2000, e/2000) for w in range(0, 501) for e in range(0, 501)]
def region(pred, Nmax=2.3):
    """largest N0 such that pred holds for all grid points with N < N0"""
    bad = [1.75+w+e for (w, e) in grid if not pred(w, e)]
    return min(bad) if bad else None
# (a) S0
s0 = lambda w, e: (1.75+w+e) - L(w, e) <= min(0.5, 0.25+w+e) and L(w, e) > (1.75+w+e)/2
print('S0 (codim <= min(k/2, n-3k/2) and |H| > 2^(n/2)) holds for all N <', round(region(s0), 4))
s0_mod4 = lambda w, e: (1.75+w+e) - L(w, e) <= min(0.5, 0.25+w+e)
print('S0 dimension condition alone: N <', round(region(s0_mod4), 4))
# worst slack inside N < 11/6
sl = min(min(0.5, 0.25+w+e) - ((1.75+w+e) - L(w, e)) for (w, e) in grid if w+e < 1/12)
print('  min slack (per k) of S0 condition over N < 11/6:', round(sl, 4))
print('  codim bound n - L at N=7/4 (w=e=0):', round(1.75-L(0, 0), 4), '; at w=1/12,e=0:', round(1.75+1/12-L(1/12, 0), 4))
# (b) shrink thresholds
for name, frac in (('2(r+1) [disjoint]', 2.0), ('(r+1)/2 [empty common intersection, halving]', 0.5), ('0', 0.0)):
    nr = lambda w, e, f=frac: (1.75+w+e) - L(w, e) <= min(1+w, 0.75+e - f*w)
    rc = lambda w, e, f=frac: g_recount(w, 0.75+e - f*w) >= 0
    print(f'shrink {name}: no-recount N < {region(nr):.4f}; recount N < {region(rc):.4f}')
# (c) S0, k = 0 mod 4 form: only codim-1 <= (k-1)/2 needed (member with e_x >= e - r exists inside a (k+r)-set holding an affine basis)
s0b = lambda w, e: (1.75+w+e) - L(w, e) <= 0.5
print('S0 (4|k form, e <= k/2 only): N <', region(s0b))
print('  max over N<1.9385 region of (n-L)/k:', round(max((1.75+w+e)-L(w,e) for (w,e) in grid if 1.75+w+e < 1.9385), 4))
