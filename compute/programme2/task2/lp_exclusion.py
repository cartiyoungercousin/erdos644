"""Exclusion of (r, rho_par) for small k by Delsarte's LP bound, with an exact rational certificate.

Setting: a covering coset family H (every (k+r)-set contains a member), n = k + r + T. Replace C by its even
subcode C_ev (H stays inside a + C_ev; this is the parity-correct coset). Lemma A: for every nonzero c in C_ev,
rho_par <= r + |wt(c) - (k+r)|. So rho_par >= rho0 forces C_ev to have no word of weight u with
|u - (k+r)| <= rho0 - r - 1, and all weights even. Also |C_ev| >= |H| >= C(n,k+r)/C(n-k,r).
Delsarte: if f(x) = 1 + sum_{j>=1} y_j K_j(x), y_j >= 0, has f(i) <= 0 at every allowed nonzero weight i,
then every linear code with weights in the allowed set has |C| <= f(0). We solve the dual LP with HiGHS,
round y to rationals, and re-check f(i) <= 0 and f(0) < |H|_lowerbound EXACTLY with Fractions.
Usage: py -3.14 lp_exclusion.py
"""
import sys
from fractions import Fraction
from math import comb
import numpy as np
from scipy.optimize import linprog

def kraw(n):
    K = [[0]*(n+1) for _ in range(n+1)]   # K[j][i] = K_j(i)
    for j in range(n+1):
        for i in range(n+1):
            K[j][i] = sum((-1)**t * comb(i, t) * comb(n-i, j-t) for t in range(0, j+1))
    return K

def lp_bound(n, allowed, K):
    # minimise sum_j y_j C(n,j)  s.t.  sum_j y_j K_j(i) <= -1 for allowed i, y >= 0
    js = list(range(1, n+1))
    c = np.array([comb(n, j) for j in js], dtype=float)
    A = np.array([[K[j][i] for j in js] for i in allowed], dtype=float)
    b = -np.ones(len(allowed))
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)]*n, method='highs')
    if res.status != 0:
        return None, None
    return 1 + res.fun, res.x

def exact_cert(n, allowed, K, y, target):
    # rationalise, scale slightly to absorb rounding, verify exactly
    for scale in (Fraction(1), Fraction(1001, 1000), Fraction(101, 100), Fraction(11, 10)):
        yq = [max(Fraction(0), Fraction(v).limit_denominator(10**9)) * scale for v in y]
        ok = all(1 + sum(yq[j-1]*K[j][i] for j in range(1, n+1)) <= 0 for i in allowed)
        if ok:
            f0 = 1 + sum(yq[j-1]*comb(n, j) for j in range(1, n+1))
            return f0 < target, f0
    return False, None

def check(k, T, r, rho0, K=None):
    n = k + r + T; w = k + r
    if K is None: K = kraw(n)
    LB = Fraction(comb(n, w), comb(n-k, r))     # |H| >= LB
    allowed = [i for i in range(2, n+1, 2) if abs(i - w) > rho0 - r - 1]
    val, y = lp_bound(n, allowed, K)
    if val is None:
        return dict(n=n, status='lp-fail')
    ok, f0 = exact_cert(n, allowed, K, y, LB)
    return dict(n=n, lp=val, LB=float(LB), excluded=ok, cert=float(f0) if f0 else None)

if __name__ == '__main__':
    # Targets beating FKW at k = 4m (T = 3m+1): 7 rho > 12 (r + 1), rho even, rho <= min(2r, k).
    print('k=4m, T=3m+1: every (r, rho) with 7rho > 12(r+1), rho_par even <= min(2r,k)')
    for m in range(4, 13):
        k, T = 4*m, 3*m+1
        n0 = k + T
        Kcache = {}
        res_m = []
        for r in range(1, k):
            rho0 = 12*(r+1)//7 + 1
            if rho0 % 2: rho0 += 1
            if rho0 > min(2*r, k):
                continue
            n = k + r + T
            if n not in Kcache: Kcache[n] = kraw(n)
            R = check(k, T, r, rho0, Kcache[n])
            res_m.append((r, rho0, R.get('excluded'), R.get('lp'), R.get('LB')))
        bad = [x for x in res_m if not x[2]]
        print(f'm={m} k={k}: checked {len(res_m)} values of r; NOT excluded by LP: {bad}')
        sys.stdout.flush()
