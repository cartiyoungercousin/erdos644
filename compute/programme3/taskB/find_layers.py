"""List single-parity layers {B : |B cap X| = p mod 2}, |X| = a, that are T-covering (exact)."""
import sys, numpy as np
from taskb import ksets, pc, zeta_sub
k, T, n = map(int, sys.argv[1:4])
allk = ksets(n, k); allS = ksets(n, n - T)
for a in range(1, n):
    X = (1 << a) - 1
    for p in (0, 1):
        L = allk[(pc(allk & X) % 2) == p]
        g = np.zeros(1 << n, np.int32); g[L] = 1; g = zeta_sub(g, n)
        if g[allS].min() >= 1: print(f'a={a} p={p} size={len(L)} covering')
