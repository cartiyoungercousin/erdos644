"""Explicit test-bed families for 7INV (n <= 23), as arrays of member bitmasks.

SPEC:  fkw:m | taskb:FILE:n:k | covrand:n:k:r:seed | coset:n:k:codim:seed | quad:n:k:seed | mod4:n:k:a:res
       | thresh:n:k:a:t | star:n:k:r:seed (members through point 0 plus a covering patch)
coset: random code C of codimension `codim`; the k-layer of the coset of C whose layer covers at the lowest level.
quad:  {B : q(B) = 1}, q(x) = sum_{i<j} a_ij x_i x_j + sum_i b_i x_i, a, b uniform.
mod4:  {B : |B cap [a]| = res (mod 4)}.
"""
import sys
import os
import numpy as np
from math import comb, log
from itertools import combinations

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'seven'))
from mc_colour import popcount, upset_table  # noqa: E402

TASKB = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'programme3', 'taskB', 'out')


def kmasks(n, k):
    return np.array([sum(1 << i for i in c) for c in combinations(range(n), k)], dtype=np.int64)


def bitsof(M, n):
    return ((M[:, None] >> np.arange(n, dtype=np.int64)) & 1).astype(np.int64)


def cover_level(n, k, M):
    U = upset_table(n, M)
    pc = popcount(np.arange(1 << n, dtype=np.int64))
    for m in range(k, n + 1):
        if U[pc == m].all():
            return m, U, pc
    return n + 1, U, pc


def patch_cover(n, k, r, M, rng):
    pc = popcount(np.arange(1 << n, dtype=np.int64))
    while True:
        U = upset_table(n, M)
        unc = np.nonzero((~U) & (pc == k + r))[0]
        if len(unc) == 0:
            return M
        add = []
        for S in unc[:2000]:
            bits = [i for i in range(n) if S >> i & 1]
            drop = rng.choice(len(bits), size=r, replace=False)
            add.append(int(S) - sum(1 << bits[d] for d in drop))
        M = np.unique(np.concatenate([M, np.array(add, dtype=np.int64)]))


def build(spec):
    p = spec.split(':')
    t = p[0]
    if t == 'fkw':
        m = int(p[1])
        n, k = 7 * m + 1, 4 * m
        A = kmasks(n, k)
        X = (1 << (4 * m)) - 1
        return n, k, A[popcount(A & X) % 2 == 1], 'FKW m=%d' % m
    if t == 'taskb':
        n, k = int(p[2]), int(p[3])
        return n, k, np.unique(np.load(os.path.join(TASKB, p[1]))), 'TASKB ' + p[1]
    n, k = int(p[1]), int(p[2])
    A = kmasks(n, k)
    if t == 'covrand':
        r, seed = int(p[3]), int(p[4])
        rng = np.random.default_rng(seed)
        dens = 1.5 * log(comb(n, k + r)) / comb(k + r, r)
        M = A[rng.random(len(A)) < dens]
        return n, k, patch_cover(n, k, r, M, rng), 'covrand r=%d s=%d' % (r, seed)
    if t == 'star':
        r, seed = int(p[3]), int(p[4])
        rng = np.random.default_rng(seed)
        M = A[(A & 1) == 1]
        M = M[rng.random(len(M)) < 0.3]
        return n, k, patch_cover(n, k, r, M, rng), 'star+patch r=%d s=%d' % (r, seed)
    if t == 'coset':
        c, seed = int(p[3]), int(p[4])
        rng = np.random.default_rng(seed)
        P = rng.integers(0, 2, (c, n))                 # parity-check matrix
        syn = (bitsof(A, n) @ P.T) % 2 @ (1 << np.arange(c))
        best = None
        for s in range(1 << c):
            M = A[syn == s]
            if len(M) == 0:
                continue
            cl = cover_level(n, k, M)[0]
            if best is None or cl < best[0]:
                best = (cl, s, M)
        return n, k, best[2], 'coset codim=%d s=%d (syndrome %d)' % (c, seed, best[1])
    if t == 'quad':
        seed = int(p[3])
        rng = np.random.default_rng(seed)
        a = np.triu(rng.integers(0, 2, (n, n)), 1)
        b = rng.integers(0, 2, n)
        X = bitsof(A, n)
        q = (np.einsum('bi,ij,bj->b', X, a, X) + X @ b) % 2
        return n, k, A[q == 1], 'quad s=%d' % seed
    if t == 'mod4':
        a, res = int(p[3]), int(p[4])
        return n, k, A[popcount(A & ((1 << a) - 1)) % 4 == res], 'mod4 |X|=%d res=%d' % (a, res)
    if t == 'thresh':
        a, tt = int(p[3]), int(p[4])
        return n, k, A[popcount(A & ((1 << a) - 1)) >= tt], 'thresh |A|=%d t=%d' % (a, tt)
    raise ValueError(spec)
