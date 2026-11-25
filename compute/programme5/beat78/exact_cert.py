"""Exact (rational) certificates for the obstruction profile {c, 0+, 0+}.

f1(c) := t*_+(0+,0+,c): anchors x, x' with |x cap x'| = ck, third anchor w meeting x and x' in >= 1 but o(k)
points each (and missing x cap x').  Regions (Xa, Xb, Xc, Ea, Eb, Ec) have masses (0, 0, c, 1-c, 1-c, 1), but Xa, Xb
are NONEMPTY, so their patterns constrain Ea, Eb (blockers).
(1) LOWER BOUND f1(c) >= (c+3)/4 on [1/2, 1], for every one of the block configs: a certificate per config is
    either one linear form (lambda vertex) >= target at both endpoints, or two forms with slopes of opposite signs
    whose zero-slope convex combination is >= 0.  All checked in exact arithmetic (fractions).
    Validity at finite k: for ANY pattern assignment, max_g load_g >= sum_g lambda_g load_g
    >= sum_R |R| min_{S in A_R} lambda(S) (weighted average), so the bound holds up to O(1/k).
(2) UPPER BOUND f1(c) <= max((c+3)/4, c+1/3) via the explicit config Xc:{123}, Ec:{1},{2},{3}, Xa = Xb:{1234},
    Ea, Eb: singletons (filler).  Hence f1 = (c+3)/4 exactly on [1/2, 5/9]; f1(5/9) = 8/9.
usage: py -3.14 exact_cert.py  -> logs/exact_cert.log"""
import os, sys
from fractions import Fraction as Fr
import numpy as np
import tstar
HERE = os.path.dirname(os.path.abspath(__file__))

def lines_for_config(T, ci):
    """line (alpha, beta) per lambda vertex: value = alpha + beta*c for masses (0,0,c,1-c,1-c,1)"""
    i, j, l = T['configs'][ci]
    blk, coefF = T['blk'], T['coefF']
    regs = [i, j, l, blk[i], blk[j], blk[l]]
    out = []
    for q in range(len(T['LAM'])):
        k = [coefF[r][q] for r in regs]
        # m = (0, 0, c, 1-c, 1-c, 1)
        alpha = k[3] + k[4] + k[5]
        beta = k[2] - k[3] - k[4]
        out.append((alpha, beta))
    return out

def certify(lines, p, s, a, b):
    """prove max_q (alpha_q + beta_q c) - (p + s c) >= 0 on [a,b]; return certificate or None"""
    L = [(al - p, be - s) for al, be in lines]
    for (al, be) in L:
        if al + be * a >= 0 and al + be * b >= 0: return ('one', al, be)
    neg = [(al, be) for al, be in L if be < 0]
    pos = [(al, be) for al, be in L if be > 0]
    best = None
    for a1, b1 in neg:
        for a2, b2 in pos:
            th = b2 / (b2 - b1)            # th*b1 + (1-th)*b2 = 0
            const = th * a1 + (1 - th) * a2
            if const >= 0: return ('two', (a1, b1), (a2, b2), const)
    return None

if __name__ == '__main__':
    T = tstar.tab()
    log = open(os.path.join(HERE, 'logs', 'exact_cert.log'), 'w')
    def P(*a):
        print(*a); print(*a, file=log, flush=True)
    a, b = Fr(1, 2), Fr(1)
    p, s = Fr(3, 4), Fr(1, 4)            # target (c+3)/4
    fails = 0
    for ci in range(len(T['configs'])):
        cert = certify(lines_for_config(T, ci), p, s, a, b)
        if cert is None:
            fails += 1; P('NO CERT config', ci, tstar.describe(ci))
    P('lower bound f1(c) >= (c+3)/4 on [1/2,1]: configs', len(T['configs']), 'uncertified', fails)
    # exact values at sample points (min over configs of max over lambda vertices, rational)
    for c in [Fr(1, 2), Fr(17, 32), Fr(5, 9), Fr(9, 16), Fr(3, 5), Fr(2, 3), Fr(3, 4), Fr(1)]:
        v, cfg = tstar.tstar_exact((Fr(0), Fr(0), c))
        P('f1(%s) = %s = %.6f   (c+3)/4 = %s, c+1/3 = %s   optimal config: %s' %
          (c, v, float(v), (c + 3) / 4, c + Fr(1, 3), tstar.describe(cfg)))
    # profiles used by the obstruction at t = 7/8: c in (1/2, 9/16]
    P('threshold: (c+3)/4 > t  <=>  c > 4t-3;  c <= 1 - t/2 needed for covering;  4t-3 < 1-t/2 <=> t < 8/9')
    log.close()
