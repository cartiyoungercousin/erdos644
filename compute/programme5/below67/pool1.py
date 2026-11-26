"""Depth-1 game from a 4-member position with a MILP-exact two-block finish (any graph size), labelling pool.
Her requests: structured (some live types requested fully, plus one partial fill up to t), or a given list.
His answers: candidate exclusions (fast2._excl_cands) ranked by the pool value (an upper bound on her cost), top ones
checked exactly by MILP (engine.finish).  An R2 is refuted only by an exact MILP value > t (sound for him).
An R2 none of whose candidates refutes it is a CANDIDATE closure (his candidate list is heuristic)."""
import itertools, numpy as np
import engine, fast2
EPS = 1e-9

def atoms5(P, r, lin):
    out = []
    for i, ty in enumerate(P.live):
        m = P.types[ty]
        full = (m <= EPS) or (r[i] >= m - EPS)
        if not full: out.append((ty | 16, lin[i], True))
        out.append((ty, m - lin[i], True))
    return out

def structured_requests(P, t, fills=(1.0,), maxn=4000):
    live = P.live; m = np.array([P.types[ty] for ty in live]); n = len(live)
    pos = [i for i in range(n) if m[i] > EPS]
    out = set()
    for k in range(len(pos) + 1):
        for S in itertools.combinations(pos, k):
            base = sum(m[i] for i in S)
            if base > t + EPS: continue
            rest = t - base
            others = [i for i in pos if i not in S]
            if not others or rest <= EPS:
                r = np.zeros(n); r[list(S)] = m[list(S)]; out.add(tuple(np.round(r, 9))); continue
            for j in others:
                if m[j] <= rest + EPS: continue      # would be full: covered by a larger S
                r = np.zeros(n); r[list(S)] = m[list(S)]; r[j] = rest
                out.add(tuple(np.round(r, 9)))
            # two partial fills split evenly
            for j1, j2 in itertools.combinations(others, 2):
                if m[j1] > rest / 2 + EPS and m[j2] > rest / 2 + EPS:
                    r = np.zeros(n); r[list(S)] = m[list(S)]; r[j1] = rest / 2; r[j2] = rest / 2
                    out.add(tuple(np.round(r, 9)))
    return [np.array(r) for r in list(out)[:maxn]]

def refute(P, t, r, rng, ntop=3):
    live = P.live; m = np.array([P.types[ty] for ty in live])
    avail = m - r; need = avail.sum() - 1.0
    E = np.zeros((1, len(m))) if need <= EPS else fast2._excl_cands(avail, need, rng, nrand=30)
    Lin = np.maximum(avail[None, :] - E, 0)
    # rank by a cheap proxy: total alive in-mass weighted (no pool): just try all, MILP on a spread subset
    best = -1; bestL = None
    order = rng.permutation(len(Lin))[:ntop * 4] if len(Lin) > ntop * 4 else range(len(Lin))
    for k in order:
        v = engine.finish(atoms5(P, r, Lin[k]), 31, 2)
        if v > best: best, bestL = v, Lin[k]
        if v > t + EPS: return v, Lin[k]
    return best, bestL

def depth1_milp(P, t, reqs=None, seed=0, verbose=False):
    rng = np.random.default_rng(seed)
    reqs = reqs if reqs is not None else structured_requests(P, t)
    cands = []
    for r in reqs:
        v, L = refute(P, t, r, rng)
        if v <= t + EPS:
            cands.append((r, v))
            if verbose: print('   candidate R2 %s (best spoil found %.4f)' % (np.round(r, 4), v), flush=True)
    return cands, len(reqs)
