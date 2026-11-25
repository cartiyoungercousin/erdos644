r"""Table of least pencil weight w* versus 4T-3k on known seven-free families (PROGRAMME4_P1.md, Section 1).
T = tau - 1, e = tau - 3k/4, P1 bound: w* >= 4T-3k-5.  All values exact.
 - complete K_n^(k): tau = n-k+1, seven-freeness by the exact two-block ILP (J = all), w* by profile enumeration;
 - FKW (k = 4m, n = 7m+1, odd on X): two-block ILP and enumeration;
 - two-block H_J scan: every J, every split a <= b, n in [3k/2, 11k/6) (Fano range: the ILP is exact there).
usage: p1_table.py kmax_complete kmax_twoblock"""
import sys, os
from functools import lru_cache
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'programme2', 'C'))
from twoblock import seven, tau as tau_slow

INF = 10 ** 9
NMAXF = 2.0

@lru_cache(maxsize=None)
def w3(s1, s2, s3, m):
    """least number of once-covered points of three sets of sizes s1,s2,s3 in an m-set, empty triple intersection."""
    best = INF
    for d12 in range(min(s1, s2) + 1):
        for d13 in range(min(s1 - d12, s3) + 1):
            e1 = s1 - d12 - d13
            for d23 in range(min(s2 - d12, s3 - d13) + 1):
                e2 = s2 - d12 - d23; e3 = s3 - d13 - d23
                if e1 + e2 + e3 + d12 + d13 + d23 <= m:
                    best = min(best, e1 + e2 + e3)
    return best

def wstar(J, a, b, k):
    J = [j for j in J if j <= a and k - j <= b]
    best = INF
    for i, j1 in enumerate(J):
        for i2 in range(i, len(J)):
            for i3 in range(i2, len(J)):
                j2, j3 = J[i2], J[i3]
                wx = w3(j1, j2, j3, a)
                if wx >= best: continue
                wy = w3(k - j1, k - j2, k - j3, b)
                best = min(best, wx + wy)
    return best

def tau_fast(J, a, b, k):
    n = a + b
    c = [min(a, J[0] - 1) + b, a + min(b, k - J[-1] - 1)]
    for i in range(len(J) - 1):
        c.append(min(a, J[i + 1] - 1) + min(b, k - J[i] - 1))
    return n - max(c)

def row(name, J, a, b, k):
    t = tau_slow(J, a, b, k); T = t - 1; sv = seven(J, a, b, k)
    w = wstar(J, a, b, k)
    return f'| {name} | {k} | {a+b} | {t} | {t - 3*k/4:+.2f} | {4*T-3*k} | {w} | {"seven" if sv else "none"} |'

def main(kc, kt):
    print('| family | k | n | tau | e | 4T-3k | w* | Fano seven |')
    print('|---|---|---|---|---|---|---|---|')
    for k in range(4, kc + 1):           # largest seven-free complete family in the Fano range
        best = None
        for n in range((3 * k + 1) // 2, -(-11 * k // 6)):
            if seven(range(k + 1), 1, n - 1, k) is None: best = n
        if best: print(row(f'K_{best}^({k})', list(range(k + 1)), 1, best - 1, k))
    for m in range(2, 5):
        k = 4 * m; print(row(f'FKW m={m}', list(range(1, k + 1, 2)), k, 3 * m + 1, k))
    print(f'\ntwo-block scan, n in [3k/2, {NMAXF}k]: max 4T-3k over H_J with NO Fano-type seven, least w* there')
    for k in range(5, kt + 1):
        cands = []
        for n in range((3 * k + 1) // 2, int(NMAXF * k) + 1):
            for a in range(1, n // 2 + 1):
                b = n - a; lo, hi = max(0, k - b), min(a, k); W = hi - lo + 1
                for mask in range(1, 1 << W):
                    J = [lo + i for i in range(W) if mask >> i & 1]
                    v = 4 * (tau_fast(J, a, b, k) - 1) - 3 * k
                    if v >= -4: cands.append((v, n, a, J))
        cands.sort(key=lambda c: -c[0])
        top = None; wbest = INF; ex = None; nsev = 0
        for v, n, a, J in cands:
            if top is not None and v < top: break
            if seven(J, a, n - a, k) is not None: nsev += 1; continue
            w = wstar(J, a, n - a, k)
            if top is None: top = v
            if w < wbest: wbest, ex = w, (n, a, J)
        print(f'k={k}: {len(cands)} cands with 4T-3k>=-4, {nsev} checked had a seven; max 4T-3k with no Fano seven = {top}, '
              f'least w* there = {wbest} (P1: >= {None if top is None else top - 5}); e.g. n,a,J = {ex}', flush=True)

if __name__ == '__main__':
    # sanity: w3 respects the counting lower bound max(0, S-2m, 2max-S) + parity
    for m in range(0, 9):
        for s1 in range(m + 1):
            for s2 in range(s1, m + 1):
                for s3 in range(s2, m + 1):
                    S = s1 + s2 + s3; lb = max(0, S - 2 * m, 2 * s3 - S); lb += (S - lb) % 2
                    v = w3(s1, s2, s3, m); assert v == INF or v >= lb
    main(int(sys.argv[1]), int(sys.argv[2]))
