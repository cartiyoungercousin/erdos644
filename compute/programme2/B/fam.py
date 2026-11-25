r"""Families for piece B: coset families with MANY point classes (most cells singletons), with and without planted
structure, plus exact minimum-weight disjoint Omegas (BFS in syndrome space) and an exact covering certificate.

Covering certificate [exact]: if no affine hyperplane of the column set contains k + r points and r >= e, then every
(k+r)-set S has E_S = E, |S| >= 2e+1, e <= k <= |S| - e, so by Lemma C (Task 2) S contains a member. So
r_cert = max(e, maxside - k + 1), where maxside = max over functionals lambda nonconstant on the columns of the larger side.
Then H is T-covering for T = n - k - r_cert (the true T can only be larger).
"""
import os, sys, random
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'task3'))
from core import Coset, evenise, popc

def coset_from_columns(n, cols, R, alpha, name=''):
    rows = [sum(1 << x for x in range(n) if cols[x] >> i & 1) for i in range(R)]
    return Coset(n, rows, alpha, name)

def gen(kind, n, M, rng, q=0, cellpool=0):
    """columns in F2^(M + q); returns (cols, R, forced zero alpha bits)"""
    if kind == 'rand':
        cols = [rng.getrandbits(M) for _ in range(n)]; extra = 0
    elif kind == 'mix':        # half the points from a small pool of cell columns, half singletons
        pool = [rng.getrandbits(M) for _ in range(cellpool)]
        cols = [rng.choice(pool) if rng.random() < 0.5 else rng.getrandbits(M) for _ in range(n)]; extra = 0
    elif kind in ('series', 'sparse'):
        cols = [rng.getrandbits(M) for _ in range(n)]
        # q planted rows with small supports (series pairs: support 2; sparse: support 3..6); alpha bit 0 there
        for t in range(q):
            sz = 2 if kind == 'series' else rng.randint(3, 6)
            for x in rng.sample(range(n), sz): cols[x] |= 1 << (M + t)
        extra = q
    else: raise ValueError(kind)
    return cols, M + extra, extra

def bfs_min(cols_avail, R, target):
    """min-weight subset (of points, each used once) with column sum = target; exact (shortest path in the Cayley
    graph on distinct column values: a shortest path never repeats a generator)."""
    vals = {}
    for x, c in cols_avail: vals.setdefault(c, x)
    gens = np.array(list(vals.keys()), dtype=np.int64); pts = list(vals.values())
    size = 1 << R
    par_g = np.full(size, -1, dtype=np.int64); seen = np.zeros(size, dtype=bool)
    seen[0] = True; frontier = np.array([0], dtype=np.int64)
    while not seen[target]:
        if len(frontier) == 0: return None
        new_states = []; new_par = []
        for c0 in range(0, len(frontier), max(1, 4_000_000 // max(1, len(gens)))):
            fr = frontier[c0:c0 + max(1, 4_000_000 // max(1, len(gens)))]
            nxt = (fr[:, None] ^ gens[None, :]).ravel()
            gi = np.tile(np.arange(len(gens)), len(fr))
            mask = ~seen[nxt]
            nxt, gi = nxt[mask], gi[mask]
            u, idx = np.unique(nxt, return_index=True)
            seen[u] = True; par_g[u] = gi[idx]; new_states.append(u)
        frontier = np.concatenate(new_states) if new_states else np.array([], dtype=np.int64)
    S, st = [], target
    while st != 0:
        g = par_g[st]; S.append(pts[g]); st ^= int(gens[g])
    assert len(set(S)) == len(S)
    return S

def omegas(cs, R):
    col = [cs.cls(x) for x in range(cs.n)]
    used = set(); Os = []
    for i in range(3):
        S = bfs_min([(x, col[x]) for x in range(cs.n) if x not in used], R, cs.alpha)
        if S is None: return None
        used |= set(S); Os.append(sum(1 << x for x in S))
    return Os

def cover_cert(cs, k):
    col = np.array([cs.cls(x) for x in range(cs.n)], dtype=np.int64)
    R = cs.r
    # e = dim span of differences
    from b1 import rank
    e = rank([int(c) ^ int(col[0]) for c in col])
    maxside = 0
    lam_all = np.arange(1, 1 << R, dtype=np.int64)
    for c0 in range(0, len(lam_all), 4096):
        lam = lam_all[c0:c0 + 4096]
        andv = lam[:, None] & col[None, :]
        par = np.zeros(andv.shape, dtype=np.int64)
        v = andv.copy()
        while v.any():
            par ^= v & 1; v >>= 1
        ones = par.sum(axis=1); zeros = cs.n - ones
        nonconst = (ones > 0) & (zeros > 0)
        if nonconst.any():
            maxside = max(maxside, int(np.maximum(ones, zeros)[nonconst].max()))
    r_cert = max(e, maxside - k + 1)
    return dict(e=e, maxside=maxside, r_cert=r_cert, T_cert=cs.n - k - r_cert)

def omegas_mitm(cs, maxw=5):
    """three disjoint min-weight (<= maxw) subsets with column sum alpha, found greedily one after another,
    each exactly minimal among subsets of the remaining points (meet in the middle over subsets of size <= 3)."""
    import itertools
    col = [cs.cls(x) for x in range(cs.n)]
    used = set(); Os = []
    for _ in range(3):
        avail = [x for x in range(cs.n) if x not in used]
        best = None
        # tables of sums of subsets of size j (j <= 3)
        tabs = {0: (np.array([0], dtype=np.int64), [()])}
        for j in (1, 2, 3):
            subs = list(itertools.combinations(avail, j)) if j < 3 else None
            if j < 3:
                sums = np.array([np.bitwise_xor.reduce([col[x] for x in sb]) for sb in subs], dtype=np.int64)
                tabs[j] = (sums, subs)
        for wgt in range(1, maxw + 1):
            for a in range(0, min(wgt, 2) + 1):
                b = wgt - a
                if b > 3 or b < a: continue
                if b < 3:
                    sb, lb = tabs[b]
                    lookup = {}
                    for i, v in enumerate(sb.tolist()): lookup.setdefault(v, []).append(i)
                    if a == 3: continue
                    sa, la = tabs[a]
                    for i, v in enumerate(sa.tolist()):
                        for jdx in lookup.get(v ^ cs.alpha, [])[:50]:
                            S = set(la[i]) | set(lb[jdx])
                            if len(S) == wgt: best = S; break
                        if best: break
                else:
                    # b = 3: enumerate triples by first element, using the pair table
                    s2, l2 = tabs[2]
                    sa, la = tabs[a]
                    want = {}
                    for i, v in enumerate(sa.tolist()): want.setdefault(v ^ cs.alpha, []).append(i)
                    for x in avail:
                        hits = np.nonzero(np.isin(s2 ^ col[x], np.array(list(want.keys()), dtype=np.int64)))[0]
                        for jdx in hits[:200]:
                            v = int(s2[jdx] ^ col[x])
                            for i in want[v][:20]:
                                S = set(la[i]) | set(l2[jdx]) | {x}
                                if len(S) == wgt: best = S; break
                            if best: break
                        if best: break
                if best: break
            if best: break
        if best is None: return None
        used |= best; Os.append(sum(1 << x for x in best))
    for O in Os: assert cs.syn(O) == cs.alpha
    return Os
