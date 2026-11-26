"""Depth-2 adaptive closures of the critical pencil (x, y, 0+) (default x = 3/7, y = 5/14), keep-all two-block finish.

Round 1: she requests R1 (Z always, free: rule R0), masses on X, Y, E', F', G' (grid s1, maximal: total t).
He answers K inside V (maximal: |K cap V| = 1), i.e. he excludes ex = |V| - t - 1 of the unrequested mass
(grid s1 over the cells; all such answers are tried, best-first).  Round 2 + two static blocks: fast2.depth1x
(her R2 on grid h, live types only, maximal; his L exact by MILP).  K is a spoiler if the depth-1 value exceeds t.
R1 is refuted once a spoiler is found; otherwise it is reported as a closure candidate (to be verified).
usage: py -3.14 depth2.py delta s1 h NPROC [x14 y14]      (delta, s1, h, x14, y14 in units of k/14)"""
import sys, os, itertools, time, numpy as np
from multiprocessing import Pool
import fast2

EPS = 1e-9
K14 = 14.0

def cells(x14, y14):
    return {'X': x14, 'Y': y14, 'E': K14 - x14 - y14, 'F': K14 - x14, 'G': K14 - y14}
TY = {'X': 3, 'Y': 5, 'E': 1, 'F': 2, 'G': 4}
ORDER = 'XYEFG'

def grid(m, s):
    n = int(np.floor(m / s + EPS)); v = [i * s for i in range(n + 1)]
    if m - v[-1] > EPS: v.append(m)
    return v

def requests(C, t, s):
    out = []
    for free in range(5):
        others = [c for i, c in enumerate(ORDER) if i != free]
        for vals in itertools.product(*[grid(C[c], s) for c in others]):
            rem = t - sum(vals)
            if rem < -EPS or rem > C[ORDER[free]] + EPS: continue
            R = dict(zip(others, vals)); R[ORDER[free]] = max(0.0, rem)
            key = tuple(round(R[c], 6) for c in ORDER)
            out.append(key)
    return sorted(set(out))

def answers(C, R, t, s):
    """exclusion vectors (beyond R) of total ex = |V| - t - 14, best-first heuristic order"""
    avail = {c: C[c] - R[i] for i, c in enumerate(ORDER)}
    ex = sum(avail.values()) - K14
    if ex <= EPS: return [{c: 0.0 for c in ORDER}]
    out = []
    cs = [c for c in ORDER if avail[c] > EPS]
    for free in range(len(cs)):
        others = [c for i, c in enumerate(cs) if i != free]
        for vals in itertools.product(*[grid(avail[c], s) for c in others]):
            rem = ex - sum(vals)
            if rem < -EPS or rem > avail[cs[free]] + EPS: continue
            e = {c: 0.0 for c in ORDER}; e.update(dict(zip(others, vals))); e[cs[free]] = max(0.0, rem)
            out.append(tuple(round(e[c], 6) for c in ORDER))
    out = sorted(set(out))
    # heuristic: exclusions on hubs last
    out.sort(key=lambda e: (e[0] + e[1], -e[2]))
    return [dict(zip(ORDER, e)) for e in out]

def pos4(C, R, e):
    """types over (E,F,G,K) after K = avail - e (Z requested, out of K)."""
    types = {6: 0.0}
    for i, c in enumerate(ORDER):
        m = C[c]; r = R[i]; kin = m - r - e[c]
        if m - r > EPS: types[TY[c] | 8] = types.get(TY[c] | 8, 0) + kin / K14
        types[TY[c]] = types.get(TY[c], 0) + (m - kin) / K14
    return fast2.Pos4(types)

def work(args):
    C, R, t, s1, hc, hf = args
    tn = t / K14
    for e in answers(C, R, t, s1):
        P = pos4(C, R, e)
        v, R2, L, _ = fast2.depth1f(P, tn, hc / K14, want=tn)
        if v <= tn + EPS: continue
        v2, R2, L, _ = fast2.depth1f(P, tn, hf / K14, want=tn)
        if v2 > tn + EPS:
            return (R, e, v2 * K14)
    return (R, None, None)

if __name__ == '__main__':
    delta, s1, h, NP = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    x14, y14 = (float(sys.argv[5]), float(sys.argv[6])) if len(sys.argv) > 6 else (6.0, 5.0)
    t = 12.0 - delta
    C = cells(x14, y14)
    Rs = requests(C, t, s1)
    print('x=%g/14 y=%g/14 z=0+  t=%g/14  R1 grid %g: %d requests, R2 grid %g' % (x14, y14, t, s1, len(Rs), h), flush=True)
    t0 = time.time(); bad = 0; cand = []
    with Pool(NP) as p:
        for i, (R, e, v) in enumerate(p.imap_unordered(work, [(C, R, t, s1, max(h, 1.0), h) for R in Rs], chunksize=4)):
            if e is None:
                cand.append(R); print('  CANDIDATE R1 %s: no spoiler found' % (R,), flush=True)
            else: bad += 1
            if i % 200 == 0: print('  %d/%d done, %d refuted, %.0fs' % (i, len(Rs), bad, time.time() - t0), flush=True)
    print('refuted %d of %d R1; candidates %d: %s  (%.0fs)' % (bad, len(Rs), len(cand), cand[:20], time.time() - t0))
