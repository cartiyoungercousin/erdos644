"""PETAL §40.5: one-class structure test (the reduced structure lemma SL1 of §40.3), blow-up classes.
A class = all k-sets of a chosen set of types on atoms s (sorted); pairwise overlaps >= c; tau >= tau0 (the least tau a
petal class can have in the two-class setting: k=12 -> 5, k=16 -> 7).  By Lemma YC (40.2) the other class has at most
h_abs + k - c - T points in any absorbing region, so the class is FINISHED by Theorem CR if some point region r has
  Phi1(r) = max(h_abs, 2*h_abs - 2*(T - k + c)) + ceil(8*beta/3) <= T,   h_abs = |r| - k + beta + 1,
  beta = max_e sum_i min(e_i, s_i - r_i).
SAT over type subsets + CEGAR on Phi1 <= T (no-good: some chosen type has out-mass > beta at the witness region).
A HIT = a class with no such region: a candidate non-arena class.
usage: py single_cr.py k m_max n_lo n_hi min_m stride residue per_instance_timeout_s"""
import sys, time
import numpy as np
from pysat.solvers import Glucose4
from search import partitions, comps
from cr import all_regions


def phi1(s, k, c, T, types, R, S):
    E = np.array(types, dtype=np.int32); best = None
    for i in range(0, len(R), 8192):
        Rc = R[i:i + 8192]
        beta = np.minimum(E[None, :, :], (S[None, :] - Rc)[:, None, :]).sum(2).max(1)
        habs = Rc.sum(1) - (k - beta) + 1
        cost = np.maximum(habs, 2 * habs - 2 * (T - k + c)) + (-(-8 * beta // 3))
        j = int(np.argmin(cost))
        if best is None or cost[j] < best[0]:
            best = (int(cost[j]), tuple(int(v) for v in Rc[j]), int(beta[j]), int(habs[j]))
    return best


def solve(s, k, c, T, tau0, deadline):
    types = comps(k, s); S = np.array(s, dtype=np.int32)
    E = np.array(types, dtype=np.int32); E = E[np.maximum(0, 2 * E - S).sum(1) >= c]; N = len(E)
    if N == 0: return dict(status='INFEAS', N=0)
    types = [tuple(int(v) for v in r) for r in E]
    sol = Glucose4(); v = lambda i: i + 1
    for x in comps(tau0 - 1, s):   # every request of size tau0-1 is avoided by some chosen type
        surv = np.nonzero((E <= (S - np.array(x))[None, :]).all(1))[0]
        if len(surv) == 0: sol.delete(); return dict(status='INFEAS', N=N)
        sol.add_clause([v(int(i)) for i in surv])
    for a0 in range(0, N, 128):
        A = E[a0:a0 + 128]
        mn = np.maximum(0, A[:, None, :] + E[None, :, :] - S[None, None, :]).sum(2)
        for a, b in zip(*np.nonzero(mn < c)):
            a = int(a) + a0; b = int(b)
            if a < b: sol.add_clause([-v(a), -v(b)])
    R = all_regions(s); cg = 0
    while True:
        if time.time() > deadline: sol.delete(); return dict(status='TIMEOUT', N=N, cegar=cg)
        if not sol.solve():
            sol.delete(); return dict(status='INFEAS' if cg == 0 else 'NO_HIT_FEASIBLE', N=N, cegar=cg)
        mdl = set(l for l in sol.get_model() if l > 0)
        X = [types[i] for i in range(N) if v(i) in mdl]
        cost, r, beta, habs = phi1(s, k, c, T, X, R, S)
        if cost > T:
            sol.delete(); return dict(status='HIT', N=N, cegar=cg, X=X, phi1=cost, wit=(r, beta, habs))
        cg += 1
        bad = [v(i) for i in range(N) if sum(min(types[i][j], s[j] - r[j]) for j in range(len(s))) > beta]
        sol.add_clause(bad)


if __name__ == '__main__':
    k, m_max, n_lo, n_hi, min_m, stride, res = map(int, sys.argv[1:8]); pit = float(sys.argv[8])
    c = {12: 7, 16: 9}[k]; T = 3 * k // 4; tau0 = {12: 5, 16: 7}[k]
    sizes = [tuple(p) for n in range(n_lo, n_hi + 1) for p in partitions(n, m_max, 2 * k) if len(p) >= min_m]
    print('single-class CR k', k, 'c', c, 'T', T, 'tau0', tau0, 'vectors', len(sizes), 'stride', stride, 'res', res, flush=True)
    stats = {}; t0 = time.time()
    for idx in range(len(sizes)):
        if idx % stride != res: continue
        s = sizes[idx]; t1 = time.time()
        r = solve(list(s), k, c, T, tau0, time.time() + pit)
        st = r['status']; stats[st] = stats.get(st, 0) + 1
        if st in ('HIT', 'TIMEOUT'):
            print(idx, s, r, '%.1fs' % (time.time() - t1), flush=True)
    print('DONE STATS', stats, 'elapsed %.0fs' % (time.time() - t0), flush=True)
