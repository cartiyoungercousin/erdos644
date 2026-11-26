"""Which grid first requests (after K) keep an ADV M1 state that also survives every static drop-one frame?"""
import json, sys, itertools
import numpy as np
sys.path.insert(0, '../jointmilp')
import jm
S = jm.sizes(7.0); T = 12 - 0.002; SV = np.array([S[c] for c in jm.C7])
H = float(sys.argv[1]); thr = T + 1e-6
rows = [json.loads(l) for l in open('logs/states_static.jsonl')]
def ok(r, frames):
    return all(r['static'][f] is not None and r['static'][f] > thr for f in frames)
FR_ALL = ['FGKM1', 'EGKM1', 'EFKM1', 'EFGM1']
import importlib.util
spec = importlib.util.spec_from_file_location('rc', '../jointmilp/run_cover2.py')
# reuse grid_requests without running the driver: copy of its logic
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
            for vals in itertools.product(*[grid(S[jm.L[i]]) for i in oth]):
                rem = T - sum(vals) - sum(dv)
                if rem < -1e-9: continue
                r = [0.0] * 7
                for i, v in zip(oth, vals): r[i] = v
                r[free] = min(rem, S[jm.L[free]]); r[4:] = dv
                if sum(r) < T - 1e-9 and r[free] < S[jm.L[free]] - 1e-9: continue
                reqs.add(tuple(round(x, 6) for x in r))
    return np.array(sorted(reqs))
reqs = grid_requests(H)
def mask(states):
    if not states: return np.zeros(len(reqs), bool)
    M = np.array([s[:7] for s in states]); out = np.zeros(len(reqs), bool)
    for i in range(0, len(reqs), 2000):
        R = reqs[i:i + 2000]
        out[i:i + 2000] = np.any(np.all(M[:, None, :] + R[None, :, :] <= SV + 1e-6, axis=2), axis=0)
    return out
print('states', len(rows), 'requests', len(reqs))
allm = mask([r['M1'] for r in rows]); print('covered by all ADV states:', allm.sum())
for fr in [[f] for f in FR_ALL] + [FR_ALL]:
    good = [r['M1'] for r in rows if ok(r, fr)]
    m = mask(good)
    print('frames', fr, ': invulnerable states', len(good), '; requests still refuted', m.sum(), 'of', len(reqs))
    if fr == FR_ALL:
        bad = reqs[~m]; json.dump(bad.tolist(), open('logs/unrefuted_h%g.json' % H, 'w'))
        for b in bad[:20]: print('   unrefuted R1', dict(zip(jm.C7, b)))
vul = sorted(rows, key=lambda r: min(r['static'][f] or 99 for f in FR_ALL))[:10]
for r in vul: print('most vulnerable', [round(x,3) for x in r['M1']], {k: round(v,3) for k, v in r['static'].items()})
