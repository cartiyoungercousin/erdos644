"""Lemma PAIR windows and Delsarte certificates.
Lemma PAIR: H k-uniform, (k+r)-covering on n points, A,B in H with |A&B| = j.  Colour A&B, A-B, B-A by the pairs
{p3,p3+w}, {p1,p1+w}, {p2,p2+w} (p3 = p1+p2) with splits alpha, the outside O by w.  Then R_u = A, R_v = B,
R_{u+v} = A^B, and the four lines x with x.w = 1 have |R_x| = |O| + sum_i (s_i ? alpha_i : size_i - alpha_i),
s ranging over the even-weight patterns.  If |A^B| >= k+r and some alpha makes all four >= k+r, H has a Fano seven.
window(n,k,r) = the set of j for which this holds (exact, by brute force over alpha).
Delsarte: |H| <= 1 + sum beta (dual certificate, verified in exact rationals with an explicit slack term),
versus the covering count |H| >= C(n,k+r)/C(n-k,r)."""
import sys
from fractions import Fraction as Fr
from math import comb
import numpy as np
import highspy

def window(n, k, r):
    W = []
    for j in range(0, k + 1):
        if 2 * k - 2 * j < k + r or n - 2 * k + j < 0:
            continue
        sizes = (j, k - j, k - j); O = n - 2 * k + j
        pats = [(0, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)]
        ok = False
        for a0 in range(sizes[0] + 1):
            for a1 in range(sizes[1] + 1):
                for a2 in range(sizes[2] + 1):
                    al = (a0, a1, a2)
                    if all(O + sum(al[i] if s[i] else sizes[i] - al[i] for i in range(3)) >= k + r for s in pats):
                        ok = True; break
                if ok: break
            if ok: break
        if ok:
            W.append(j)
    return W

def eberlein(n, k, i, m):
    return sum((-1) ** t * comb(m, t) * comb(k - m, i - t) * comb(n - k - m, i - t) for t in range(0, i + 1))

def delsarte_cert(n, k, forb_int):
    D = min(k, n - k)
    forb = {k - j for j in forb_int}  # distances
    q = [[Fr(eberlein(n, k, i, m), comb(k, i) * comb(n - k, i)) for i in range(D + 1)] for m in range(D + 1)]
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    inf = highspy.kHighsInf
    for i in range(D + 1):
        h.addVar(1.0 if i == 0 else 0.0, 1.0 if i == 0 else (0.0 if i in forb else inf))
    h.changeColsCost(D + 1, np.arange(D + 1, dtype=np.int32), -np.ones(D + 1))
    for m in range(1, D + 1):
        h.addRow(0, inf, D + 1, np.arange(D + 1, dtype=np.int32), np.array([float(x) for x in q[m]]))
    h.run()
    lpval = -h.getInfo().objective_function_value
    duals = h.getSolution().row_dual
    beta = [Fr(abs(float(b))).limit_denominator(10 ** 9) for b in duals]  # beta_m >= 0
    # F(i) = 1 + sum beta_m q_m(i); |H| <= F(0) + sum_{allowed i>=1} v_i * max(F(i), 0)   (a_i <= v_i)
    bound = Fr(1) + sum(beta)
    for i in range(1, D + 1):
        if i in forb:
            continue
        F = 1 + sum(beta[m - 1] * q[m][i] for m in range(1, D + 1))
        if F > 0:
            bound += comb(k, i) * comb(n - k, i) * F
    return lpval, bound

if __name__ == '__main__':
    for k in range(8, 17):
        T = (3 * k + 5) // 4  # a record needs tau >= T+1, i.e. (k+r)-covering with n = k + T + r
        for r in range(1, 4):
            n = k + T + r
            W = window(n, k, r)
            need = -(-comb(n, k + r) // comb(n - k, r))
            if not W:
                print(f"k={k} T={T} r={r} n={n}: pair window empty"); continue
            lpv, b = delsarte_cert(n, k, W)
            verdict = 'NO RECORD at this n (cert)' if b < need else 'inconclusive'
            print(f"k={k} T={T} r={r} n={n}: window j in {W}; Delsarte LP {lpv:.1f}, exact cert bound {float(b):.1f}; covering needs {need}: {verdict}", flush=True)
