r"""Anchor-keeping Q' finish (CORE Theorem Q with three of the four free co-edges = the anchors).

Anchors B1,B2,B3 (empty triple intersection), V = union, |V| = N = 3 - p.  Labelling: 1,2,3 = anchors,
4 = the next reply, 5,6,7 = diagonal points of the quadrangle 1234; m_c = {ab, c4}.
Round 4: she requests sigma_ab inside P_ab and rho_c inside Q_c (total <= t); K_4 = S_4 + additions.
Loads of rounds 5,6,7 (CORE §4):  L_c = |P_ab n K4| + |Q_c \ K4| + |P \ K4| + tau_c,
tau = |Q n K4| freely split.  Every addition of the adversary weakly lowers the binding quantities
(P-additions lower two base loads and the total by 2, Q-additions move one unit of base load into the
free pool tau) [proved by hand, notes/LIFT.md §2], so the worst case is 'no additions in P, none in the
binding Q_c' and the certificate is the LP below:
   sum sigma + sum rho <= t,  3 + p - 2 sum sigma <= 3t,
   b_c := q_c - rho_c + p - sigma_ac - sigma_bc <= t   (c = 1,2,3).
Returns the minimal t' at which the LP is feasible (bisection-free: LP in (sigma, rho, t'))."""
import sys
import numpy as np
from scipy.optimize import linprog

def q_value(p12, p13, p23):
    """min t such that the anchored Q' certificate exists (first order)."""
    p = p12 + p13 + p23
    q = [1 - p12 - p13, 1 - p12 - p23, 1 - p13 - p23]   # Q1, Q2, Q3
    # vars: s12 s13 s23 r1 r2 r3 t
    # pair opposite c: c=1 -> P23, c=2 -> P13, c=3 -> P12; the two others are 'sigma_ac + sigma_bc'
    others = {0: [0, 1], 1: [0, 2], 2: [1, 2]}          # indices of P12,P13,P23 meeting B_c... see below
    # b_1 involves sigma_12 + sigma_13 (P's inside B_1), b_2: sigma_12 + sigma_23, b_3: sigma_13 + sigma_23
    A, b = [], []
    A.append([1, 1, 1, 1, 1, 1, -1]); b.append(0)                      # budget
    A.append([-2, -2, -2, 0, 0, 0, -3]); b.append(-(3 + p))            # total
    for c in range(3):
        row = [0] * 7
        for i in others[c]: row[i] = -1
        row[3 + c] = -1; row[6] = -1
        A.append(row); b.append(-(q[c] + p))
    bounds = [(0, p12), (0, p13), (0, p23), (0, max(q[0], 0)), (0, max(q[1], 0)), (0, max(q[2], 0)), (0, None)]
    res = linprog([0, 0, 0, 0, 0, 0, 1], A_ub=A, b_ub=b, bounds=bounds, method='highs')
    return res.fun, res.x

if __name__ == '__main__':
    for sh in sys.argv[1:]:
        s = tuple(map(eval, sh.split(',')))
        v, x = q_value(*s)
        print(s, 'N = %.4f' % (3 - sum(s)), 'Q-anchored value %.5f' % v, np.round(x, 4))
