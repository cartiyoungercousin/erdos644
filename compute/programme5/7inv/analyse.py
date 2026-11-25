"""7INV numerics on a test-bed family: Fourier bias (member level and up-set level), kappa, cone test (Prop Q).

  beta_H   = max_{a != 0, 1_V} |E_{B in H}(-1)^{a.B} - E_{B in slice_k}(-1)^{a.B}|  (hyperplane-coset bias; FKW ~1)
  base_H   = sqrt(2 n ln 2 / |H|)                            (typical max for a random |H|-subset of the slice)
  beta_U(m)= max_{a != 0, 1_V} |E_{R in U_m}(-1)^{a.R} - E_{R in slice_m}(-1)^{a.R}|,  U_m = U cap C(V, m)
  kappa    = log10(P(all 7 R_u in U) / prod_u P(R_u in U)) under balanced colourings (class sizes equal +-1)
  cone(m)  = dim{deg<=2 polys constant on U_m} - dim{deg<=2 polys constant on C(V,m)}   (Prop Q predicts 0
             for k+2 <= m <= n-2 when H is T-covering, T >= 4)
Usage: py -3.14 analyse.py SPEC [samples] [seed]      (SPEC as in fam.py)
"""
import sys
import numpy as np
from math import comb, log, log10, sqrt
from fam import build, cover_level, popcount
from mc_colour import r_masks


def wht(f):
    H = f.astype(np.float64).copy()
    h = 1
    N = len(H)
    while h < N:
        H = H.reshape(-1, 2, h)
        a, b = H[:, 0].copy(), H[:, 1].copy()
        H[:, 0], H[:, 1] = a + b, a - b
        H = H.reshape(-1)
        h *= 2
    return H


def bias(n, ind, ref=None):
    W = wht(ind) / ind.sum()
    if ref is not None:
        W -= wht(ref) / ref.sum()
    W[0] = 0
    W[(1 << n) - 1] = 0
    j = int(np.argmax(np.abs(W)))
    return float(abs(W[j])), bin(j).count('1')


def gf2_dim_const(n, rows_masks, rng, cap=5000):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    nv = len(pairs) + n + 1

    def mono(R):
        v = 1 << (nv - 1)
        for t, (i, j) in enumerate(pairs):
            if (R >> i) & (R >> j) & 1:
                v |= 1 << t
        for i in range(n):
            if R >> i & 1:
                v |= 1 << (len(pairs) + i)
        return v
    rows = rows_masks if len(rows_masks) <= cap else rows_masks[rng.choice(len(rows_masks), cap, replace=False)]
    r0 = mono(int(rows[0]))
    basis = {}
    for R in rows[1:]:
        v = mono(int(R)) ^ r0
        while v:
            p = v.bit_length() - 1
            if p in basis:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    return nv - len(basis)


def balanced(n, S, rng):
    base = np.array([1 + (i % 7) for i in range(n)], dtype=np.uint8)
    return np.array([rng.permutation(base) for _ in range(S)], dtype=np.uint8)


def main():
    spec = sys.argv[1]
    S = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = np.random.default_rng(seed)
    n, k, M, name = build(spec)
    cl, U, pc = cover_level(n, k, M)
    tau = n - cl + 1
    print('== %s  n=%d k=%d |H|=%d  cover level %d (r=%d)  tau=%d  4n-7k=%d  4T-3k=%d' % (
        name, n, k, len(M), cl, cl - k, tau, 4 * n - 7 * k, 4 * (tau - 1) - 3 * k))
    print('   phi:', ' '.join('%d:%.3g' % (m, U[pc == m].mean()) for m in range(k, min(cl, n) + 1)))
    ind = np.zeros(1 << n)
    ind[M] = 1
    bH, wH = bias(n, ind, (pc == k).astype(float))
    print('   beta_H = %.4f (|a|=%d)  base_H = %.4f' % (bH, wH, sqrt(2 * n * log(2) / len(M))))
    mm = sorted(set(m for m in (k + 1, k + 2, round(4 * n / 7)) if k < m < cl))
    for m in mm:
        um = (U & (pc == m)).astype(float)
        sl = (pc == m).astype(float)
        bU, wU = bias(n, um, sl)
        print('   beta_U(%d) = %.4f (|a|=%d)  phi=%.3g' % (m, bU, wU, um.sum() / sl.sum()))
    for m in range(k, min(cl, n - 1)):
        Um = np.nonzero(U & (pc == m))[0]
        Sm = np.nonzero(pc == m)[0]
        d1, d0 = gf2_dim_const(n, Um, rng), gf2_dim_const(n, Sm, rng)
        print('   cone(%d): dim const-on-U_m %d, const-on-slice %d, excess %d' % (m, d1, d0, d1 - d0))
    col = balanced(n, S, rng)
    R = r_masks(col, n)
    G = np.array([U[R[u]] for u in range(7)])
    marg = G.mean(axis=1)
    joint = G.all(axis=0).mean()
    prod = float(np.prod(marg))
    kap = log10(joint / prod) if joint > 0 else float('-inf')
    print('   balanced S=%d: marg %s  prod %.3e  cert %.3e  kappa %s' % (
        S, ' '.join('%.3f' % x for x in marg), prod, joint, '%.2f' % kap if joint > 0 else '-inf'), flush=True)


if __name__ == '__main__':
    main()
