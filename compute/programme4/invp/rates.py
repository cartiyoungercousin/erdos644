"""INV-P go/no-go: exact-binomial feasibility of the random coset-union construction.

Construction U (heuristic existence, see notes/PROGRAMME4_INVP.md section 3):
  G <= F_2^V a random linear code of codimension m, R = F_2^V / G (|R| = 2^m),
  Gamma a random set of classes of density p, minus every class in a light triple,
  H = union over gamma in Gamma of the k-layer of gamma + G.
Window parameters: n = floor((7/4+d)k), T = ceil((3/4+e)k), r = n-k-T,
  P = 4T-3k-5 (every seven-free T-covering family has all pencils of weight >= P, Lemma P1).
Light classes Lambda: classes containing a vector of weight <= P-1 with parity k;
  |Lambda| <= L := sum_{w<=P-1, w=k mod 2} C(n,w).
Ball of one (k+r)-set: its k-subsets, N_b = C(k+r, r) classes (2^m >= N_b, collisions ~ N_b^2/2^m).
Conditions used (all with explicit polynomial safety factors):
  (C) covering by union bound over all C(n,k+r) sets:      p N_b (1 - N_b/2^m) >= 2 ln C(n,k+r)
  (N) no covering coset layer of ANY code inside H:        2^m / N_b >= 2 (n^2+n+1)
      (a covering layer meets >= 2^m/N_b classes; union bound over <= 2^(n^2+n) layers)
  (H) light triples are rare (alteration):                 3 p^2 2^m L <= 0.1
Linear comparison (L): one random coset covers and is heavy:  L * 2 ln C(n,k+r) < N_b.
Usage: py -3.14 rates.py [k ...]
"""
import sys
from math import lgamma, log, log2, ceil, floor

def lc(a, b):
    if b < 0 or b > a:
        return float('-inf')
    return (lgamma(a + 1) - lgamma(b + 1) - lgamma(a - b + 1)) / log(2)

def lsum(xs):
    xs = [x for x in xs if x != float('-inf')]
    if not xs:
        return float('-inf')
    M = max(xs)
    return M + log2(sum(2 ** (x - M) for x in xs))

def params(k, d, e):
    n = floor((7 / 4 + d) * k)
    T = ceil((3 / 4 + e) * k)
    r = n - k - T
    P = 4 * T - 3 * k - 5
    return n, T, r, P

def check(k, d, e):
    n, T, r, P = params(k, d, e)
    if r < 1 or P < 1 or 6 * n >= 11 * k:
        return None
    lNb = lc(k + r, r)
    lL = lsum([lc(n, w) for w in range(0, P) if (w - k) % 2 == 0])
    lS = lc(n, k + r)               # log2 #(k+r)-sets
    lnS = lS * log(2)
    lm = lNb + log2(2 * (n * n + n + 1)) + 1          # (N), with 2^m/N_b >= 4(n^2+n+1)
    lp = log2(2 * lnS) - lNb + 0.01                   # (C)
    lH = log2(3) + 2 * lp + lm + lL                   # (H): must be <= log2 0.1
    okU = lH <= log2(0.1)
    okL = lL + log2(2 * lnS) < lNb
    # seven-count exponent: Fano colourings with balanced classes, each R_u (|R_u|=4n/7) hits Gamma
    R = (4 * n) // 7
    if R >= k:
        lcol = (lgamma(n + 1) - 7 * lgamma(n / 7 + 1)) / log(2)
        lhit = min(0.0, lp + lc(R, R - k))
        l7 = lcol + 7 * lhit
    else:
        l7 = float('-inf')
    return dict(n=n, T=T, r=r, P=P, lam=P / r, okU=okU, okL=okL, margU=log2(0.1) - lH,
                margL=lNb - lL - log2(2 * lnS), l7=l7, lNb=lNb, lL=lL, lm=lm)

def eps_max(k, d, key):
    best = None
    e = 0.0
    while e < d / 3:
        c = check(k, d, e)
        if c and c[key]:
            best = (e, c)
        e += 1.0 / k
    return best

def main():
    ks = [int(a) for a in sys.argv[1:]] or [2000, 10000, 100000]
    ds = [0.01, 0.02, 0.04, 0.06, 0.08]
    print("columns: k d | U: eps*/d lam=P/r r P margin(bits) seven-exp(bits) | L: eps*/d lam | lam=1 at eps=d/5; PEN(1/2) kills lam>=3/2 (eps>=3d/11)")
    for k in ks:
        for d in ds:
            u = eps_max(k, d, 'okU')
            l = eps_max(k, d, 'okL')
            su = "none" if not u else "%.3f %.3f r=%d P=%d marg=%.1f 7exp=%.0f" % (
                u[0] / d, u[1]['lam'], u[1]['r'], u[1]['P'], u[1]['margU'], u[1]['l7'])
            sl = "none" if not l else "%.3f %.3f" % (l[0] / d, l[1]['lam'])
            print("k=%d d=%.2f | U: %s | L: %s" % (k, d, su, sl))
    # asymptotic (entropy) version: lam*(d) for eps -> 0 limit of rho
    print("\nasymptotic, eps/d fixed: largest lam with h(lam*om/N) N < (1+om) h(om/(1+om)) (U and L coincide at rate level)")
    from math import log2 as L2
    def h(x):
        return 0.0 if x <= 0 or x >= 1 else -x * L2(x) - (1 - x) * L2(1 - x)
    for d in ds:
        lo, hi = 0.0, 0.3
        for _ in range(60):
            e = (lo + hi) / 2
            om = d - e
            N = 7 / 4 + d
            lam = 4 * e / om
            ok = N * h(min(0.5, lam * om / N)) < (1 + om) * h(om / (1 + om))
            lo, hi = (e, hi) if ok else (lo, e)
        print("d=%.2f  eps*/d=%.3f  lam*=%.3f" % (d, lo / d, 4 * lo / (d - lo)))

if __name__ == '__main__':
    main()
