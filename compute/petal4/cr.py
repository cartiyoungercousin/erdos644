"""PETAL §40: the corrected certificate for blow-up two-class families (Theorem CR, 40.2).
Integer form, k-uniform, T requests.  For a petal class P (other class Q) and a point region A with r_i points in atom i:
  beta_P(A)  = max_{e in P} sum_i min(e_i, s_i - r_i)      (most points a P-edge can have outside A)
  h_abs(A)   = |A| - (k - beta_P) + 1                       (EVERY subset of A of this size meets every P-edge)
  gamma_Q(A) = max_{e in Q} sum_i min(e_i, r_i)             (most points a Q-edge can have inside A)
  cost_P(A)  = min( max(h_abs, 2 gamma_Q), tau_P + 2 gamma_Q ) + ceil(8 beta_P / 3)
Petal phase: b = ceil(k/3); class P is forced if tau_Q + b <= T; unforced running intersections always fit (2b <= T for
k = 12, 16), but then the petal class is not hers to choose, so both classes need cost <= T.
WIN(H) iff some forced P has min_A cost_P <= T, or both classes have min_A cost <= T.
NOTE: search.py's AP cost used h = least hitting set INSIDE the region. That is not what AP's proof needs (its G_j must contain
the earlier traces and still hit; only absorption, or tau + traces, guarantees that). cr.py uses the valid quantities."""
import itertools
import numpy as np
from search import comps, killset


def tau_types(s, types):
    """exact tau of the blow-up family (all k-sets of the given types) by request enumeration (small cases)"""
    if not types: return 0
    for t in range(0, sum(s) + 1):
        for x in comps(t, s):
            if all(killset(s, e, x) for e in types): return t
    return sum(s)


def all_regions(s):
    return np.array(list(itertools.product(*[range(v + 1) for v in s])), dtype=np.int32)


def cost_table(s, k, P, Q, tauP, R=None):
    S = np.array(s, dtype=np.int32)
    R = all_regions(s) if R is None else R
    EP = np.array(P, dtype=np.int32); EQ = np.array(Q, dtype=np.int32)
    beta = np.zeros(len(R), dtype=np.int32); gam = np.zeros(len(R), dtype=np.int32)
    for i in range(0, len(R), 4096):
        Rc = R[i:i + 4096]
        out = np.minimum(EP[None, :, :], (S[None, :] - Rc)[:, None, :]).sum(2).max(1)
        ins = np.minimum(EQ[None, :, :], Rc[:, None, :]).sum(2).max(1)
        beta[i:i + 4096] = out; gam[i:i + 4096] = ins
    size = R.sum(1)
    habs = size - (k - beta) + 1
    seal = -(-8 * beta // 3)
    cost = np.minimum(np.maximum(habs, 2 * gam), tauP + 2 * gam) + seal
    j = int(np.argmin(cost))
    return int(cost[j]), dict(r=tuple(int(v) for v in R[j]), beta=int(beta[j]), gamma=int(gam[j]), habs=int(habs[j]),
                              tauP=tauP)


def cr_win(s, X, Y, k, T, R=None):
    b = -(-k // 3)
    tX = tau_types(s, X); tY = tau_types(s, Y)
    cX, wX = cost_table(s, k, X, Y, tX, R)
    cY, wY = cost_table(s, k, Y, X, tY, R)
    forcedX = tY + b <= T; forcedY = tX + b <= T
    win = (forcedX and cX <= T) or (forcedY and cY <= T) or (cX <= T and cY <= T)
    return win, dict(tauX=tX, tauY=tY, costX=cX, costY=cY, forcedX=forcedX, forcedY=forcedY, witX=wX, witY=wY)


if __name__ == '__main__':
    s = [13, 13, 2, 2]
    X = [(0, 9, 2, 1), (0, 10, 0, 2), (0, 10, 1, 1), (0, 10, 2, 0), (0, 11, 0, 1), (0, 11, 1, 0), (0, 12, 0, 0), (1, 10, 1, 0), (1, 11, 0, 0)]
    Y = [(9, 0, 1, 2), (10, 0, 0, 2), (10, 0, 1, 1), (10, 0, 2, 0), (10, 1, 0, 1), (11, 0, 0, 1), (11, 0, 1, 0), (11, 1, 0, 0), (12, 0, 0, 0)]
    print('§25 pseudo-hit', cr_win(s, X, Y, 12, 9))
