"""Which DUMP answers (y, z) survive at the critical pairs q, at the old fixed point S* (sgame.py, unchanged)?
For each critical q and each DUMP split, list the surviving answers; report the split whose survivors have the
smallest max z.  [computed, grid]   usage: py crit_answers.py G nu t"""
import sys, os, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'adapt'))
import sgame
G = int(sys.argv[1]); nu = float(sys.argv[2]); t = float(sys.argv[3]); EPS = sgame.EPS
T3 = sgame.load_static(G); gm = sgame.Game(G, T3)
adv, S, (CL, lem, Hv) = sgame.solve(G, T3, nu, t, game=gm); g = gm.g
print('t', t, 'S*', sgame.compact(S, G), flush=True)
bad = (~CL) & gm.feas & S[None, :, None] & S[None, None, :]
rho = nu - 1 - t
Y_, Z_ = np.meshgrid(g, g, indexing='ij')
import json
out = {}
for qi in range(G):
    if not S[qi] or g[qi] > t: continue
    q = g[qi]
    if not (t / 2 < q <= 3 - 3 * t + 1e-9): continue
    best = None
    for h1 in range(G + 1):
        H1 = g[h1]
        if H1 < 1 - t - EPS or H1 > 1 - q + EPS: continue
        lo2 = max(1 - t, 2 - t - q - H1); hi2 = min(1 - q, 1 + rho - H1)
        for j2 in range(G + 1):
            H2 = g[j2]
            if H2 < lo2 - EPS or H2 > hi2 + EPS: continue
            M = bad[qi] & (Y_ <= H1 + EPS) & (Z_ <= H2 + EPS) & (Y_ + Z_ >= H1 + H2 - rho - EPS)
            sv = np.argwhere(M)
            nonA = int(((q + g[sv[:, 0]] + g[sv[:, 1]]) > t + EPS).sum()) if len(sv) else 0
            key = (nonA, len(sv))
            if best is None or key < best[0]: best = (key, h1, j2, sv)
    (nonA, n), h1, j2, sv = best
    print('q=%d: best DUMP (h1,h2)=(%d,%d): %d survivors, %d with q+y+z > t; y %d..%d, z %d..%d (1/%d)' % (
        qi, h1, j2, n, nonA, sv[:, 0].min(), sv[:, 0].max(), sv[:, 1].min(), sv[:, 1].max(), G), flush=True)
    out[qi] = {'h': [h1, j2], 'surv': sv.tolist()}
json.dump(out, open('logs/crit_survivors_t%s.json' % sys.argv[3], 'w'))
