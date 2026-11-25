"""The composable-lemma game ("pair-tree game"), asymptotic, units of k, grid version.

Requester's covering moves (all lemmas of the brief, k -> infinity):
  START(u): from a member x1, request u points of x1 + (t-u) outside  ->  x2 with j=|x1 cap x2| in
            W(u) = [max(0, 1-u-rho), 1-u], 0 < u <= t.          (two-stage start, pencil-bound start)
  DUMP(h1,h2) on a pair (x1,x2) with j <= t: U = (x1 cap x2) + (1-j-h_i) of x_i - x_{3-i} + rest outside, so
            A_i := x_i - x_{3-i} - U has mass h_i in [1-t, 1-j], h1+h2 in [2-t-j, min(2-2j, 1+rho)].
            Answer y: y_i = |y cap x_i| in [0, h_i], y1+y2 <= 1, y1+y2 >= h1+h2-rho  (|A| = 1+rho).
            Pencil (x1,x2,y) has profile {j, y1, y2}; new pairs (x1,y), (x2,y) with intersections y1, y2.
            (pair bound = DUMP with h_i = 1-j; window/centred dump = DUMP with h1 = h2 = h; FW pairs are not
            available for nu >= 2.2, see fw_c0.py.)
Good-seven lemmas: all static three-anchor finishes, t*_+(profile) <= t (P1, HUB, 11/6, 15/8 classes, ...).
Adversary wins iff some set S of pair intersections meets every START window and every j in S, j <= t,
survives every DUMP with a response in S x S of t*_+ > t.  Greatest fixed point on the grid.
usage: py -3.14 pairgame.py G nu t   (or: scan G)"""
import sys, os, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))

def load(G):
    return np.load(os.path.join(HERE, 'logs', 't3_%d.npy' % G))

def solve(T3, G, nu, t, verbose=False):
    rho = nu - 1 - t
    g = np.arange(G + 1) / G
    S = np.ones(G + 1, bool)
    bad = np.nan_to_num(T3, nan=0.0) > t + 1e-9           # adversary-good profiles
    feas = ~np.isnan(T3)
    hmin = 1 - t
    while True:
        changed = False
        for jj in range(G + 1):
            j = g[jj]
            if not S[jj] or j > t + 1e-12: continue
            good = bad[jj] & feas[jj] & S[:, None] & S[None, :]
            good &= (g[:, None] + g[None, :]) <= 1 + 1e-12
            val = np.where(good, g[:, None] + g[None, :], -1e9)
            M = np.maximum.accumulate(np.maximum.accumulate(val, 0), 1)   # max y1+y2 over y <= (h1,h2)
            lost = False
            for h1 in range(G + 1):
                if g[h1] < hmin - 1e-12 or g[h1] > 1 - j + 1e-12: continue
                for h2 in range(h1, G + 1):
                    if g[h2] > 1 - j + 1e-12: break
                    s = g[h1] + g[h2]
                    if s < 2 - t - j - 1e-12 or s > 1 + rho + 1e-12: continue
                    if M[h1, h2] < s - rho - 1e-12:
                        lost = True; break
                if lost: break
            if lost:
                S[jj] = False; changed = True
                if verbose: print('  remove j=%d/%d (box h=(%d,%d))' % (jj, G, h1, h2))
        if not changed: break
    # START windows
    ok = True; witness = None
    for uu in range(1, G + 1):
        u = g[uu]
        if u > t + 1e-12: break
        lo, hi = max(0.0, 1 - u - rho), 1 - u
        if not np.any(S & (g >= lo - 1e-12) & (g <= hi + 1e-12)):
            ok = False; witness = u; break
    return ok, S, witness

if __name__ == '__main__':
    G = int(sys.argv[1]); T3 = load(G)
    if sys.argv[2] == 'scan':
        for nu in [2.0, 2.1, 2.2, 2.25, 2.3, 2.4, 2.5, 2.6, 2.7, 2.8, 2.9, 3.0, 3.5, 5.0, 100.0]:
            lo_t = None
            for tt in range(int(0.75 * G), G + 1):
                t = tt / G
                ok, S, w = solve(T3, G, nu, t)
                if not ok: lo_t = t; break
            print('nu=%.3f  first grid t where requester wins: %s  (eps=%s)' % (nu, lo_t, None if lo_t is None else lo_t - .75), flush=True)
    else:
        nu, t = float(sys.argv[2]), float(sys.argv[3])
        ok, S, w = solve(T3, G, nu, t, verbose=True)
        print('adversary wins' if ok else 'requester wins (START u=%s)' % w)
        print('S =', [j for j in range(G + 1) if S[j]])
