"""Codeword families from RM(2,m) (members = supports of weight-k codewords = quadratic forms with |supp| = k):
covering needs |H| >= C(n,k+r)/C(n-k,r) with r = n-k-T, T = ceil(3k/4).  Weight-(2^{m-1}+2^{m-1-h}) words of RM(2,m)
come from rank-2h quadratic forms: A = N_alt(m,2h) * 2^m (half of the 2^{m+1} affine shifts)."""
from math import comb, ceil, log10
def alt_count_brute(m):
    import itertools, numpy as np
    from collections import Counter
    idx = [(i, j) for i in range(m) for j in range(i + 1, m)]
    c = Counter()
    for bits in range(1 << len(idx)):
        M = [[0] * m for _ in range(m)]
        for t, (i, j) in enumerate(idx):
            if bits >> t & 1: M[i][j] = M[j][i] = 1
        # rank over F_2
        rows = [sum(M[i][j] << j for j in range(m)) for i in range(m)]; r = 0
        for b in range(m):
            piv = next((x for x in range(r, m) if rows[x] >> b & 1), None)
            if piv is None: continue
            rows[r], rows[piv] = rows[piv], rows[r]
            for x in range(m):
                if x != r and rows[x] >> b & 1: rows[x] ^= rows[r]
            r += 1
        c[r] += 1
    return c
for m in (5, 6):
    c = alt_count_brute(m)
    n = 2 ** m
    for rank in sorted(c):
        if rank == 0: continue
        h = rank // 2
        for k in (n // 2 + n // 2 ** (h + 1), n // 2 - n // 2 ** (h + 1)):
            if not (1.70 <= n / k <= 2.0): continue
            A = c[rank] * 2 ** m
            T = ceil(3 * k / 4); r = n - k - T
            need = comb(n, k + r) // comb(n - k, r) if r >= 0 else None
            print(f"RM(2,{m}) n={n} k={k} N={n/k:.3f} rank={rank}: words={A}  covering at T=ceil(3k/4) needs >= {need} (10^{log10(need):.1f})")
