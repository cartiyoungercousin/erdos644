"""Which grid first requests at K* are refuted by a mapped state that is static-invulnerable AND stage2-ADV?
usage: py kstar_cover.py h [ka]  -> logs/kstar_unrefuted_h<h>.json"""
import json, sys, itertools
import numpy as np
H = float(sys.argv[1]); KA = float(sys.argv[2]) if len(sys.argv) > 2 else 20 / 3
C7 = ['X', 'Y', 'A', 'B', 'Ep', 'Fd', 'Gd']; L = ['X', 'Y', 'A', 'B']
S = {'X': 6.0, 'Y': 5.0, 'A': KA, 'B': 7.0, 'Ep': 3.0, 'Fd': 1.0, 'Gd': 9.0 - KA}; T = 12 - 0.002
SV = np.array([S[c] for c in C7])
def grid_requests(H):
    def grid(m):
        v = [round(x, 9) for x in np.arange(0, m + 1e-9, H)]
        if m - v[-1] > 1e-9: v.append(m)
        return v
    reqs = set()
    dopt = {c: sorted({0.0, S[c], np.floor(S[c] / 2 / H) * H}) for c in ('Ep', 'Fd', 'Gd')}
    for dv in itertools.product(dopt['Ep'], dopt['Fd'], dopt['Gd']):
        for free in range(4):
            oth = [i for i in range(4) if i != free]
            for vals in itertools.product(*[grid(S[L[i]]) for i in oth]):
                rem = T - sum(vals) - sum(dv)
                if rem < -1e-9: continue
                r = [0.0] * 7
                for i, v in zip(oth, vals): r[i] = v
                r[free] = min(rem, S[L[free]]); r[4:] = dv
                if sum(r) < T - 1e-9 and r[free] < S[L[free]] - 1e-9: continue
                reqs.add(tuple(round(x, 6) for x in r))
    return np.array(sorted(reqs))
reqs = grid_requests(H)
good = []
for l in open('logs/kstar_states.jsonl'):
    d = json.loads(l)
    if d['static_ok'] and d['stage2'] == 'ADV': good.append(d['M1'][:7])
M = np.array(good); out = np.zeros(len(reqs), bool)
for i in range(0, len(reqs), 2000):
    R = reqs[i:i + 2000]
    out[i:i + 2000] = np.any(np.all(M[:, None, :] + R[None, :, :] <= SV + 1e-6, axis=2), axis=0)
print('K* ka=%.4f: %d good states; grid h=%g: %d requests, refuted %d, unrefuted %d' % (KA, len(good), H, len(reqs), out.sum(), (~out).sum()))
json.dump(reqs[~out].tolist(), open('logs/kstar_unrefuted_h%g.json' % H, 'w'))
for r in reqs[~out][:15]: print('  unrefuted', dict(zip(C7, r)))
