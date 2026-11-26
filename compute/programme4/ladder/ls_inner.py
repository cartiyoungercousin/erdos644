r"""Local search for a good seven in a G-invariant family given by orbit representatives (heuristic, not exhaustive).
State: 7 members.  Move: re-choose block i as the best of `sample` random members (random representative of a chosen
orbit moved by a random group element) for covering the pairs the other six leave uncovered; ties/plateaus accepted.
Block 0 stays an orbit representative (allowed by invariance).  Returns (blocks, orbits) or None.
"""
import numpy as np


def uncovered_masks(blocks, n, skip=None):
    full = (1 << n) - 1; U = [full & ~(1 << x) for x in range(n)]
    for j, B in enumerate(blocks):
        if j == skip: continue
        for x in range(n):
            if B >> x & 1: U[x] &= ~B
    return U


def best_of(U, reps_bits, chs, G, nr, sample, n):
    ri = chs[nr.integers(0, len(chs), sample)]; g = G[nr.integers(0, len(G), sample)]
    bm = reps_bits[ri]; imgs = np.zeros(sample, dtype=np.int64)
    for x in range(n): imgs |= bm[:, x] << g[:, x]
    score = np.zeros(sample, dtype=np.int64)
    for x in range(n):
        if U[x]: score += ((imgs >> x) & 1) * np.bitwise_count(imgs & U[x]).astype(np.int64)
    j = int(np.argmax(score)); return int(imgs[j]), int(ri[j]), int(score[j]) // 2


def local_search(reps_all, reps_bits, chs, G, n, nr, m=7, starts=20, steps=400, sample=3000):
    for st in range(starts):
        o0 = int(chs[st % len(chs)]); blocks = [int(reps_all[o0])]; orbs = [o0]
        for _ in range(m - 1):
            U = uncovered_masks(blocks, n); B, o, _s = best_of(U, reps_bits, chs, G, nr, sample, n)
            blocks.append(B); orbs.append(o)
        for step in range(steps):
            U = uncovered_masks(blocks, n)
            unc = sum(bin(u).count("1") for u in U) // 2
            if unc == 0: return blocks, orbs
            i = 1 + step % (m - 1)
            Ui = uncovered_masks(blocks, n, skip=i)
            B, o, s = best_of(Ui, reps_bits, chs, G, nr, sample, n)
            tot_i = sum(bin(u).count("1") for u in Ui) // 2
            old = blocks[i]; olds = sum(bin(Ui[x] & old).count("1") for x in range(n) if old >> x & 1) // 2
            if s >= olds: blocks[i], orbs[i] = B, o
    return None
