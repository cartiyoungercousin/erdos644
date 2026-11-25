r"""Lemma 2 colourings: chi: V -> Fano points; line l has L_l = chi^-1(l); a member B with B & L_l = 0 can be B_l.  If every line has
such a member, H has a Fano-type good seven (so H is NOT (7,2)).  Heuristic search only; it never certifies (7,2)."""
import numpy as np, random
FANO = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
def line_masks(chi, n):
    cls = [0] * 7
    for v in range(n): cls[chi[v]] |= 1 << v
    return [cls[a] | cls[b] | cls[c] for a, b, c in FANO]
def missing(M, chi, n):
    return sum(0 if np.any((M & L) == 0) else 1 for L in line_masks(chi, n))
def find_fano(M, n, rng, tries=30, steps=200):
    M = np.asarray(M, dtype=np.int64)
    for _ in range(tries):
        perm = list(range(n)); rng.shuffle(perm); chi = [0] * n
        for pos, v in enumerate(perm): chi[v] = pos % 7
        cost = missing(M, chi, n)
        for _s in range(steps):
            if cost == 0: return chi
            v = rng.randrange(n); old = chi[v]; best = (cost, old)
            for c in range(7):
                if c == old: continue
                chi[v] = c; cc = missing(M, chi, n)
                if cc < best[0] or (cc == best[0] and rng.random() < 0.3): best = (cc, c)
            chi[v] = best[1]; cost = best[0]
        if cost == 0: return chi
    return None
def colouring_members(M, chi, n):
    """for each line the members avoiding L_l (indices)."""
    return [np.flatnonzero((M & L) == 0) for L in line_masks(chi, n)]

from numba import njit
FANO_A = np.array(FANO, dtype=np.int64)
@njit
def _cost(M, chi, n, FA):
    cls = np.zeros(7, np.int64)
    for v in range(n): cls[chi[v]] |= np.int64(1) << v
    miss = 0
    for l in range(7):
        L = cls[FA[l, 0]] | cls[FA[l, 1]] | cls[FA[l, 2]]; found = False
        for i in range(M.shape[0]):
            if (M[i] & L) == 0: found = True; break
        if not found: miss += 1
    return miss
@njit
def find_fano_nb(M, n, FA, seed, tries, steps):
    np.random.seed(seed)
    chi = np.zeros(n, np.int64)
    for _ in range(tries):
        perm = np.random.permutation(n)
        for pos in range(n): chi[perm[pos]] = pos % 7
        cost = _cost(M, chi, n, FA)
        for _s in range(steps):
            if cost == 0: return chi, True
            v = np.random.randint(n); old = chi[v]; bc = cost; bv = old
            for c in range(7):
                if c == old: continue
                chi[v] = c; cc = _cost(M, chi, n, FA)
                if cc < bc or (cc == bc and np.random.random() < 0.3): bc = cc; bv = c
            chi[v] = bv; cost = bc
        if cost == 0: return chi, True
    return chi, False
def find_fano_fast(M, n, rng, tries=40, steps=300):
    chi, ok = find_fano_nb(np.asarray(M, dtype=np.int64), n, FANO_A, rng.randrange(1 << 30), tries, steps)
    return [int(x) for x in chi] if ok else None
