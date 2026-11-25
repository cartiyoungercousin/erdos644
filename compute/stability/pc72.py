r"""Exact bitset DFS for 'do <= r member complements cover all pairs' (numba).  Branch on an uncovered pair; candidates
covering it; canonical ordering (earlier candidates excluded in later branches); bound: sum of the r best marginal gains
must reach |U|."""
import numpy as np
from numba import njit

@njit
def popc(x):
    x = x - ((x >> np.uint64(1)) & np.uint64(0x5555555555555555))
    x = (x & np.uint64(0x3333333333333333)) + ((x >> np.uint64(2)) & np.uint64(0x3333333333333333))
    x = (x + (x >> np.uint64(4))) & np.uint64(0x0F0F0F0F0F0F0F0F)
    return (x * np.uint64(0x0101010101010101)) >> np.uint64(56)

@njit
def rec(cov, surv, ns, U, r, chosen, depth, nodes, limit):
    W = cov.shape[1]
    nu = 0
    for w in range(W): nu += popc(U[w])
    if nu == 0: return 1
    if r == 0: return 0
    nodes[0] += 1
    if nodes[0] > limit: return -1
    # marginal gains, compaction
    gains = np.empty(ns, np.int64); keep = np.empty(ns, np.int32); nk = 0
    for t in range(ns):
        m = surv[t]; g = 0
        for w in range(W): g += popc(cov[m, w] & U[w])
        if g > 0:
            keep[nk] = m; gains[nk] = g; nk += 1
    if nk == 0: return 0
    # bound: sum of r largest gains >= nu
    g2 = np.sort(gains[:nk])
    s = 0
    for i in range(min(r, nk)): s += g2[nk - 1 - i]
    if s < nu: return 0
    # branching pair: among uncovered pairs the one with fewest candidates (exact count over keep) when r>=5, else first
    P = W * 64
    best_p = -1; best_c = 1 << 30
    if r >= 5:
        cnt = np.zeros(P, np.int32)
        for t in range(nk):
            m = keep[t]
            for w in range(W):
                x = cov[m, w] & U[w]
                while x != 0:
                    b = x & (~x + np.uint64(1))
                    bi = 0
                    y = b
                    while y > np.uint64(1):
                        y >>= np.uint64(1); bi += 1
                    cnt[w * 64 + bi] += 1
                    x ^= b
        for p in range(P):
            if (U[p >> 6] >> np.uint64(p & 63)) & np.uint64(1):
                if cnt[p] < best_c: best_c = cnt[p]; best_p = p
    else:
        for p in range(P):
            if (U[p >> 6] >> np.uint64(p & 63)) & np.uint64(1):
                best_p = p; break
    pw = best_p >> 6; pb = np.uint64(best_p & 63)
    # candidates covering best_p, sorted by gain desc
    cl = np.empty(nk, np.int32); cg = np.empty(nk, np.int64); nc = 0
    for t in range(nk):
        m = keep[t]
        if (cov[m, pw] >> pb) & np.uint64(1):
            cl[nc] = m; cg[nc] = gains[t]; nc += 1
    order = np.argsort(-cg[:nc])
    excl = np.zeros(cov.shape[0], np.uint8) if False else None
    removed = np.zeros(nc, np.uint8)
    for a in range(nc):
        m = cl[order[a]]
        U2 = U.copy()
        for w in range(W): U2[w] = U[w] & ~cov[m, w]
        # survivors: keep minus candidates processed earlier (including m itself)
        sv = np.empty(nk, np.int32); k2 = 0
        for t in range(nk):
            q = keep[t]
            if q == m: continue
            if (cov[q, pw] >> pb) & np.uint64(1):
                # q is a candidate for best_p; excluded iff earlier in order
                skip = False
                for b2 in range(a):
                    if cl[order[b2]] == q: skip = True; break
                if skip: continue
            sv[k2] = q; k2 += 1
        chosen[depth] = m
        res = rec(cov, sv[:k2], k2, U2, r - 1, chosen, depth + 1, nodes, limit)
        if res != 0: return res
    return 0

def covmasks(M, n):
    M = np.asarray(M, dtype=np.int64)
    P = n * (n - 1) // 2; W = (P + 63) // 64
    cov = np.zeros((len(M), W), np.uint64); p = 0
    bit = [((M >> i) & 1) == 0 for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            sel = bit[i] & bit[j]
            cov[sel, p >> 6] |= np.uint64(1) << np.uint64(p & 63); p += 1
    return cov, P, W

def find_cover_dfs(M, n, r, forced=None, limit=2_000_000_000):
    """list of <= r member indices whose complements (plus complement of forced, if given) cover all pairs; None if none;
    raises on node limit."""
    M = np.asarray(M, dtype=np.int64)
    cov, P, W = covmasks(M, n)
    U = np.zeros(W, np.uint64)
    for p in range(P): U[p >> 6] |= np.uint64(1) << np.uint64(p & 63)
    if forced is not None:
        fc, _, _ = covmasks(np.array([forced], dtype=np.int64), n)
        U = U & ~fc[0]
    chosen = np.full(r + 1, -1, np.int64); nodes = np.zeros(1, np.int64)
    res = rec(cov, np.arange(len(M), dtype=np.int32), len(M), U, r, chosen, 0, nodes, limit)
    if res == -1: raise RuntimeError('node limit')
    if res == 0: return None
    return [int(x) for x in chosen if x >= 0]

@njit
def _setcov(s, n, W, out):
    p = 0
    for w in range(W): out[w] = 0
    for i in range(n):
        for j in range(i + 1, n):
            if ((s >> i) & 1) == 0 and ((s >> j) & 1) == 0:
                out[p >> 6] |= np.uint64(1) << np.uint64(p & 63)
            p += 1

@njit
def greedy_core(order, n, W, P, init_cov, ninit, init_masks, maxN, node_limit, seed_dummy):
    """order: candidate masks.  Start with the (certified-(7,2)) initial family.  Returns accepted masks array."""
    cov = np.zeros((maxN, W), np.uint64); masks = np.zeros(maxN, np.int64)
    N = ninit
    for i in range(ninit):
        masks[i] = init_masks[i]
        for w in range(W): cov[i, w] = init_cov[i, w]
    allU = np.zeros(W, np.uint64)
    for p in range(P): allU[p >> 6] |= np.uint64(1) << np.uint64(p & 63)
    fc = np.zeros(W, np.uint64); chosen = np.full(8, -1, np.int64); nodes = np.zeros(1, np.int64)
    surv = np.empty(maxN, np.int32)
    for c in range(len(order)):
        s = order[c]
        _setcov(s, n, W, fc)
        U = allU.copy()
        for w in range(W): U[w] = allU[w] & ~fc[w]
        for i in range(N): surv[i] = i
        nodes[0] = 0
        res = rec(cov, surv[:N].copy(), N, U, 6, chosen, 0, nodes, node_limit)
        if res == 0 and N < maxN:
            masks[N] = s
            for w in range(W): cov[N, w] = fc[w]
            N += 1
    return masks[:N]

def greedy_extend(order, n, init=None, maxN=200000, node_limit=200000):
    """order: array of candidate masks.  init: certified (7,2) family (or None)."""
    P = n * (n - 1) // 2; W = (P + 63) // 64
    if init is None or len(init) == 0:
        init = np.zeros(0, np.int64); ic = np.zeros((1, W), np.uint64)
    else:
        init = np.asarray(init, dtype=np.int64); ic, _, _ = covmasks(init, n)
    return greedy_core(np.asarray(order, dtype=np.int64), n, W, P, ic, len(init), init, maxN, node_limit, 0)
