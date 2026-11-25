"""PETAL §40.4: the §24/§25 blow-up search redone with the VALID certificate of Theorem CR (cr.py) in place of the AP cost.
Same range model as search.py (SAT over all type subsets: tau(H) >= T+1, same-class overlap >= c, cross <= mu = c-1, both
classes nonempty, X/Y symmetry broken), CEGAR on "no CR certificate". A model is a HIT iff cr_win is False.
No-goods are sound: a certificate (role P, region r, values beta_P, gamma_Q, and the tau witnesses it relies on) stays valid
for every selection whose P-types have out-mass <= beta_P (and are killed by the tau_P witness if that branch was used) and
whose Q-types have in-mass <= gamma_Q (and are killed by the tau_Q witness if forcing was used).
usage: py search_cr.py k m_max n_lo n_hi min_m start stride residue per_instance_timeout_s"""
import sys, time
import numpy as np
from pysat.solvers import Glucose4
from search import partitions, comps, killset
from cr import all_regions

def tau_wit(s, types):
    if not types: return 0, [0] * len(s)
    for t in range(0, sum(s) + 1):
        for x in comps(t, s):
            if all(killset(s, e, x) for e in types): return t, x
    return sum(s), list(s)


def best_cost(s, k, P, Q, tauP, R, S):
    EP = np.array(P, dtype=np.int32); EQ = np.array(Q, dtype=np.int32)
    best = None
    for i in range(0, len(R), 4096):
        Rc = R[i:i + 4096]
        beta = np.minimum(EP[None, :, :], (S[None, :] - Rc)[:, None, :]).sum(2).max(1)
        gam = np.minimum(EQ[None, :, :], Rc[:, None, :]).sum(2).max(1)
        habs = Rc.sum(1) - (k - beta) + 1
        seal = -(-8 * beta // 3)
        cA = np.maximum(habs, 2 * gam) + seal; cB = tauP + 2 * gam + seal
        cost = np.minimum(cA, cB); j = int(np.argmin(cost))
        if best is None or cost[j] < best[0]:
            best = (int(cost[j]), tuple(int(v) for v in Rc[j]), int(beta[j]), int(gam[j]), bool(cB[j] < cA[j]))
    return best


def certificate(s, k, T, X, Y, R, S):
    b = -(-k // 3)
    tX, wX = tau_wit(s, X); tY, wY = tau_wit(s, Y)
    cX = best_cost(s, k, X, Y, tX, R, S); cY = best_cost(s, k, Y, X, tY, R, S)
    info = dict(tauX=tX, tauY=tY, costX=cX, costY=cY)
    if tY + b <= T and cX[0] <= T: return [('X', cX, wX, wY, True)], info
    if tX + b <= T and cY[0] <= T: return [('Y', cY, wY, wX, True)], info
    if cX[0] <= T and cY[0] <= T: return [('X', cX, wX, wY, False), ('Y', cY, wY, wX, False)], info
    return None, info


def solve_size(s, k, c, mu, T, deadline):
    m = len(s)
    types = comps(k, s)
    E = np.array(types, dtype=np.int32); S = np.array(s, dtype=np.int32)
    E = E[np.maximum(0, 2 * E - S).sum(1) >= c]; N = len(E)
    if N == 0: return dict(status='INFEAS', N=0)
    types = [tuple(int(v) for v in r) for r in E]
    reqs = comps(T, s); Rq = np.array(reqs, dtype=np.int32); comp = S[None, :] - Rq
    sol = Glucose4(); xv = lambda i: i + 1; yv = lambda i: N + i + 1
    for r in range(len(reqs)):
        surv = np.nonzero((E <= comp[r][None, :]).all(1))[0]
        if len(surv) == 0: sol.delete(); return dict(status='INFEAS', N=N)
        sol.add_clause([xv(int(i)) for i in surv] + [yv(int(i)) for i in surv])
    for a0 in range(0, N, 128):
        A = E[a0:a0 + 128]
        mn = np.maximum(0, A[:, None, :] + E[None, :, :] - S[None, None, :]).sum(2)
        mx = np.minimum(A[:, None, :], E[None, :, :]).sum(2)
        for a, bb in zip(*np.nonzero(mn < c)):
            a = int(a) + a0; bb = int(bb)
            if a < bb: sol.add_clause([-xv(a), -xv(bb)]); sol.add_clause([-yv(a), -yv(bb)])
        for a, bb in zip(*np.nonzero(mx > mu)):
            sol.add_clause([-xv(int(a) + a0), -yv(int(bb))])
    sol.add_clause([xv(i) for i in range(N)]); sol.add_clause([yv(i) for i in range(N)])
    for t in range(N): sol.add_clause([-yv(t)] + [xv(u) for u in range(t)])
    R = all_regions(s); info = dict(N=N, cegar=0)
    while True:
        if time.time() > deadline: sol.delete(); info['status'] = 'TIMEOUT'; return info
        if not sol.solve():
            sol.delete(); info['status'] = 'INFEAS' if info['cegar'] == 0 else 'NO_HIT_RANGE_FEASIBLE'; return info
        mdl = set(l for l in sol.get_model() if l > 0)
        X = [types[i] for i in range(N) if xv(i) in mdl]; Y = [types[i] for i in range(N) if yv(i) in mdl]
        cert, ci = certificate(s, k, T, X, Y, R, S)
        if cert is None:
            sol.delete(); info.update(status='HIT', X=X, Y=Y, **ci); return info
        info['cegar'] += 1
        okX = set(range(N)); okY = set(range(N))
        for role, (cost, r, beta, gam, usedtau), wP, wQ, forced in cert:
            okP = set(i for i in range(N) if sum(min(types[i][j], s[j] - r[j]) for j in range(m)) <= beta
                      and (not usedtau or killset(s, types[i], wP)))
            okQ = set(i for i in range(N) if sum(min(types[i][j], r[j]) for j in range(m)) <= gam
                      and (not forced or killset(s, types[i], wQ)))
            if role == 'X': okX &= okP; okY &= okQ
            else: okY &= okP; okX &= okQ
        sol.add_clause([xv(i) for i in range(N) if i not in okX] + [yv(i) for i in range(N) if i not in okY])


if __name__ == '__main__':
    k, m_max, n_lo, n_hi, min_m, start, stride, res = map(int, sys.argv[1:9]); pit = float(sys.argv[9])
    c = {12: 7, 16: 9}[k]; T = 3 * k // 4; mu = c - 1
    sizes = [tuple(p) for n in range(n_lo, n_hi + 1) for p in partitions(n, m_max, 2 * k) if len(p) >= min_m]
    print('CR search k', k, 'c', c, 'mu', mu, 'T', T, 'vectors', len(sizes), 'stride', stride, 'res', res, flush=True)
    stats = {}; t0 = time.time()
    for idx in range(start, len(sizes)):
        if idx % stride != res: continue
        s = sizes[idx]; t1 = time.time()
        r = solve_size(list(s), k, c, mu, T, time.time() + pit)
        st = r['status']; stats[st] = stats.get(st, 0) + 1
        if st != 'INFEAS':
            print(idx, s, st, {a: b for a, b in r.items() if a not in ('X', 'Y')}, 'X', r.get('X'), 'Y', r.get('Y'),
                  '%.1fs' % (time.time() - t1), flush=True)
    print('DONE STATS', stats, 'elapsed %.0fs' % (time.time() - t0), flush=True)
