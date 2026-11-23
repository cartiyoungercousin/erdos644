"""Exact pattern tables for static closures.

A static closure with r requests assigns to every class c of points an up-closed family F_c of
labels (nonempty subsets of [r]); candidate classes must have cross-intersecting families; the
points of c are then split among the labels of F_c.  LP duality gives, for fixed families,

    cost(mass) = max_{lambda in simplex} sum_c mass_c * w_{F_c}(lambda),
    w_F(lambda) = min_{L in F} lambda(L)                      (w = 0 for an unlabelled class),

and the maximum is attained at a vertex of the hyperplane arrangement
{lambda(A) = lambda(B) : A, B disjoint} inside the simplex, a fixed finite set LAMBDA_r of
rational points.  So   closure value = min_pattern max_{lambda in LAMBDA_r} W[pattern,lambda] . mass
with rational W: it can be evaluated exactly.

Triple (4 requests): classes X,Y,Z,PE,PF,PG.  Free choice: (F_X,F_Y,F_Z) pairwise
cross-intersecting; privates take the blocker (all labels meeting every label of the opposite
pair cell), which is the largest admissible family, hence optimal.
Four edges E,F,G,K (3 requests): classes c+ = c&K, c- = c\\K for the six cells, and N.
Candidate pairs: (c+,d+), (c+,d-) for distinct pair cells c,d; (P+, opp+), (P+, opp-),
(P-, opp+) for a private part P and its opposite pair cell.  Free choice: the six families of
X+-,Y+-,Z+-; privates take blockers.  A structurally absent class has the empty family.
"""
from __future__ import annotations
import itertools, functools, os, pickle
from fractions import Fraction as Fr
import numpy as np


@functools.lru_cache(None)
def lambdas(r):
    """Vertices of the arrangement {lambda(A)=lambda(B)} in the simplex, as tuples of Fractions."""
    planes = set()
    for A in range(1 << r):
        for B in range(1 << r):
            if A & B or A == B or A > B: continue
            v = tuple((1 if (A >> j) & 1 else 0) - (1 if (B >> j) & 1 else 0) for j in range(r))
            # normalize sign
            first = next(x for x in v if x != 0)
            if first < 0: v = tuple(-x for x in v)
            planes.add(v)
    planes = sorted(planes)
    verts = set()
    for comb in itertools.combinations(planes, r - 1):
        M = [list(map(Fr, row)) + [Fr(0)] for row in comb] + [[Fr(1)] * r + [Fr(1)]]
        sol = _solve(M, r)
        if sol is not None and min(sol) >= 0: verts.add(tuple(sol))
    return sorted(verts)


def _solve(M, n):
    M = [row[:] for row in M]
    for col in range(n):
        piv = next((i for i in range(col, n) if M[i][col] != 0), None)
        if piv is None: return None
        M[col], M[piv] = M[piv], M[col]
        p = M[col][col]; M[col] = [v / p for v in M[col]]
        for i in range(n):
            if i != col and M[i][col] != 0:
                f = M[i][col]; M[i] = [a - f * b for a, b in zip(M[i], M[col])]
    return [M[i][n] for i in range(n)]


@functools.lru_cache(None)
def upsets(r):
    """Nonempty up-closed families of nonempty subsets of [r], as bitmasks over labels (bit L)."""
    full = (1 << r) - 1
    out = []
    labs = list(range(1, full + 1))
    # generate from antichains: closure of each subset of labels, dedupe
    seen = set()
    def up(gen):
        m = 0
        for L in labs:
            if any(L & g == g for g in gen): m |= 1 << L
        return m
    # BFS over up-sets: start from {full}, add one more minimal element at a time
    start = up([full]); seen.add(start); stack = [start]
    while stack:
        m = stack.pop()
        for L in labs:
            if not (m >> L) & 1:
                m2 = m | up([L])
                if m2 not in seen: seen.add(m2); stack.append(m2)
    return sorted(seen)


def compat(r, F, G):
    full = (1 << r) - 1
    for L in range(1, full):
        if (F >> L) & 1 and (G >> (full ^ L)) & 1: return False
    return True


def blocker(r, F):
    """Largest family cross-intersecting F.  Returns -1 ("unlabelled", weight 0) if F is empty."""
    if F == 0: return -1
    full = (1 << r) - 1
    m = 0
    for L in range(1, full + 1):
        if all(L & M for M in range(1, full + 1) if (F >> M) & 1): m |= 1 << L
    return m


@functools.lru_cache(None)
def weight_table(r):
    """dict family mask -> tuple of Fractions over lambdas(r); mask 0 and -1 -> zeros."""
    lam = lambdas(r); full = (1 << r) - 1
    lamL = [[sum(l[j] for j in range(r) if (L >> j) & 1) for L in range(full + 1)] for l in lam]
    tab = {0: tuple(Fr(0) for _ in lam), -1: tuple(Fr(0) for _ in lam)}
    for F in upsets(r):
        tab[F] = tuple(min(ll[L] for L in range(1, full + 1) if (F >> L) & 1) for ll in lamL)
    return tab


def _perm_family(r, F, perm):
    m = 0
    for L in range(1, 1 << r):
        if (F >> L) & 1:
            L2 = 0
            for j in range(r):
                if (L >> j) & 1: L2 |= 1 << perm[j]
            m |= 1 << L2
    return m


@functools.lru_cache(None)
def _perm_maps(r):
    U = [0] + list(upsets(r))
    return [{F: _perm_family(r, F, perm) for F in U} for perm in itertools.permutations(range(r))]


def _canon(r, tup):
    return min(tuple(pm[F] for F in tup) for pm in _perm_maps(r))


def prune_dominated(W):
    """indices of patterns not dominated (entrywise) by another pattern."""
    n = len(W); flat = W.reshape(n, -1)
    order = np.argsort(flat.sum(1), kind="stable")
    kept = []; K = np.empty((0, flat.shape[1]))
    for i in order:
        if len(kept) and np.any(np.all(K <= flat[i] + 1e-12, axis=1)): continue
        kept.append(i); K = np.vstack([K, flat[i]])
    return sorted(kept)


def _weights(r, full):
    wt = weight_table(r)
    fl = {F: [float(v) for v in w] for F, w in wt.items()}
    return np.array([[fl[F] for F in p] for p in full]).transpose(0, 2, 1)   # [pattern, lambda, class]


def exact_weights(r, pat):
    """rows over lambdas(r), columns over classes, Fractions."""
    wt = weight_table(r)
    return [[wt[F][l] for F in pat] for l in range(len(lambdas(r)))]


CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cache")


def _cached(name, build):
    os.makedirs(CACHE, exist_ok=True)
    fn = os.path.join(CACHE, name + ".pkl")
    if os.path.exists(fn):
        with open(fn, "rb") as f: return pickle.load(f)
    val = build()
    tmp = fn + f".{os.getpid()}.tmp"
    with open(tmp, "wb") as f: pickle.dump(val, f)
    os.replace(tmp, fn)
    return val


@functools.lru_cache(None)
def triple_table(absent=()):
    """Patterns (up to label symmetry) for a good triple, 4 requests.  absent: pair cells (0,1,2 = X,Y,Z)
    that are structurally empty.  Returns (patterns, W[nT, nLam, 6]); class order X,Y,Z,PE,PF,PG."""
    def build():
        r = 4; U = upsets(r)
        opts = [[0] if c in absent else list(U) for c in range(3)]
        cps = {F: {G for G in [0] + list(U) if compat(r, F, G)} for F in [0] + list(U)}
        pms = _perm_maps(r)
        pats = []
        for FX in opts[0]:
            for FY in opts[1]:
                if FY not in cps[FX]: continue
                for FZ in opts[2]:
                    if FZ not in cps[FX] or FZ not in cps[FY]: continue
                    t = (FX, FY, FZ)
                    if all(t <= (pm[FX], pm[FY], pm[FZ]) for pm in pms): pats.append(t)
        full = [(FX, FY, FZ, blocker(r, FZ), blocker(r, FY), blocker(r, FX)) for FX, FY, FZ in pats]
        return full, _weights(r, full)
    return _cached("triple_" + "".join(map(str, absent)), build)


QUAD_CLASSES = ["X+", "X-", "Y+", "Y-", "Z+", "Z-", "PE+", "PE-", "PF+", "PF-", "PG+", "PG-", "N"]


@functools.lru_cache(None)
def quad_table(sig=(2, 2, 2)):
    """Patterns (up to label symmetry) for E,F,G,K with 3 requests.  sig[c] for pair cell c: 2 = c+ and c-
    present, 1 = only c- present (c sealed), 0 = cell empty.  Returns (patterns, W[nT, nLam, 13]);
    class order = QUAD_CLASSES = the 13 regions of game.py."""
    def build():
        r = 3; U = list(upsets(r)); wt = weight_table(r)
        fl = {F: np.array([float(v) for v in w]) for F, w in wt.items()}
        cps = {F: {G for G in [0] + U if compat(r, F, G)} for F in [0] + U}
        plus = [U if s == 2 else [0] for s in sig]
        minus = [U if s >= 1 else [0] for s in sig]
        pms = _perm_maps(r)
        def options(cands, Fp):
            # (family, weight of c-, weight of the private + class), dominated options removed
            o = [(F, fl[F], fl[blocker(r, Fp | F)]) for F in cands]
            keep = []
            for i, (F, a, b) in enumerate(o):
                dom = False
                for j, (F2, a2, b2) in enumerate(o):
                    if j != i and np.all(a2 <= a + 1e-12) and np.all(b2 <= b + 1e-12) and                        (j < i or np.any(a2 < a - 1e-12) or np.any(b2 < b - 1e-12)):
                        dom = True; break
                if not dom: keep.append(F)
            return keep
        full = []
        for Xp in plus[0]:
            for Yp in plus[1]:
                if Yp not in cps[Xp]: continue
                for Zp in plus[2]:
                    if Zp not in cps[Xp] or Zp not in cps[Yp]: continue
                    t = (Xp, Yp, Zp)
                    if not all(t <= (pm[Xp], pm[Yp], pm[Zp]) for pm in pms): continue
                    Xm = options([F for F in minus[0] if F in cps[Yp] and F in cps[Zp]], Xp)
                    Ym = options([F for F in minus[1] if F in cps[Xp] and F in cps[Zp]], Yp)
                    Zm = options([F for F in minus[2] if F in cps[Xp] and F in cps[Yp]], Zp)
                    for a in Xm:
                        for b in Ym:
                            for c in Zm:
                                full.append((Xp, a, Yp, b, Zp, c,
                                             blocker(r, Zp | c), blocker(r, Zp),      # PE+ sees Z+,Z- ; PE- sees Z+
                                             blocker(r, Yp | b), blocker(r, Yp),      # PF
                                             blocker(r, Xp | a), blocker(r, Xp),      # PG
                                             -1))
        return full, _weights(r, full), len(full)
    res = _cached("quad_" + "".join(map(str, sig)), build)
    return res[0], res[1]


def _sample_triple(absent, n, rng):
    out = []
    while len(out) < n:
        v = rng.random(3) * rng.choice([0.3, 0.6, 1.0])
        if rng.random() < 0.5: v = np.round(v * 40) / 40
        for c in absent: v[c] = 0.0
        x, y, z = v
        if x + y > 1 or x + z > 1 or y + z > 1: continue
        out.append([x, y, z, 1 - x - y, 1 - x - z, 1 - y - z])
    return np.array(out)


def _sample_quad(sig, n, rng):
    out = []
    while len(out) < n:
        v = rng.random(3) * rng.choice([0.3, 0.6, 1.0])
        if rng.random() < 0.5: v = np.round(v * 40) / 40
        for c in range(3):
            if sig[c] == 0: v[c] = 0.0
        x, y, z = v
        if x + y > 1 or x + z > 1 or y + z > 1: continue
        mass = [x, y, z, 1 - x - y, 1 - x - z, 1 - y - z]
        cap = [m * rng.random() ** rng.choice([0.3, 1, 3]) for m in mass]
        for c in range(3):
            if sig[c] <= 1: cap[c] = 0.0
        kv = np.array([cp * rng.choice([0, 1, 1]) * rng.random() ** rng.choice([0.2, 1]) for cp in cap])
        if rng.random() < 0.3: kv = np.minimum(kv, np.array(cap))
        if kv.sum() > 1: kv = kv / kv.sum()
        rm = []
        for i in range(6): rm += [kv[i], mass[i] - kv[i]]
        rm.append(1 - kv.sum())
        out.append(rm)
    return np.array(out)


def fast_index(kind, key, nsample=12000, top=2, seed=1):
    """Indices of the patterns that are among the `top` best at some sampled mass vector.
    A heuristic sub-table: closures restricted to it are still valid requester strategies (so
    requester wins are unaffected); adversary wins found with it are re-verified with the full
    tables (game.play and exact_check.py)."""
    def build():
        pats, W = (triple_table(key) if kind == "triple" else quad_table(key))
        rng = np.random.default_rng(seed)
        S = _sample_triple(key, nsample, rng) if kind == "triple" else _sample_quad(key, nsample, rng)
        keep = set()
        nT, nL, nc = W.shape
        W2 = W.reshape(nT * nL, nc)
        step = max(1, int(2e8 // (nT * nL)))
        for a in range(0, len(S), step):
            V = (W2 @ S[a:a + step].T).reshape(nT, nL, -1).max(axis=1)      # [nT, samples]
            idx = np.argpartition(V, min(top, nT - 1), axis=0)[:top]
            keep.update(idx.ravel().tolist())
        return sorted(keep)
    return _cached(f"fast_{kind}_" + "".join(map(str, key)), build)


if __name__ == "__main__":
    import time
    for r in (3, 4):
        print("r", r, "lambdas", len(lambdas(r)), "upsets", len(upsets(r)))
    t0 = time.time(); full, W = quad_table((2, 2, 2)); print("quad patterns", len(full), W.shape, time.time() - t0, flush=True)
    t0 = time.time(); k = fast_index("quad", (2, 2, 2)); print(" fast", len(k), time.time() - t0, flush=True)
    t0 = time.time(); full, W = triple_table(()); print("triple patterns", len(full), W.shape, time.time() - t0)
    t0 = time.time(); k = fast_index("triple", ()); print(" fast", len(k), time.time() - t0, flush=True)
