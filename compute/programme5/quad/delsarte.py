"""Delsarte LP bound for k-uniform families on n points avoiding given intersection sizes, vs the covering
lower bound |H| >= C(n,k+r)/C(n-k,r)... (each member lies in C(n-k,r) (k+r)-sets).  Usage: py delsarte.py n k r j1 [j2 ...]"""
import sys
from math import comb
import numpy as np
import highspy

def eberlein(n, k, i, m):
    return sum((-1) ** t * comb(m, t) * comb(k - m, i - t) * comb(n - k - m, i - t) for t in range(0, i + 1))

def lp(n, k, forb):
    D = min(k, n - k)
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    inf = highspy.kHighsInf
    for i in range(D + 1):
        lo = 1.0 if i == 0 else 0.0
        hi = 1.0 if i == 0 else (0.0 if (k - i) in forb else inf)
        h.addVar(lo, hi)
    h.changeColsCost(D + 1, np.arange(D + 1, dtype=np.int32), -np.ones(D + 1))
    for m in range(1, D + 1):
        coef = np.array([eberlein(n, k, i, m) / (comb(k, i) * comb(n - k, i)) for i in range(D + 1)])
        h.addRow(0, inf, D + 1, np.arange(D + 1, dtype=np.int32), coef)
    h.run()
    return -h.getInfo().objective_function_value

n, k, r = map(int, sys.argv[1:4]); forb = set(map(int, sys.argv[4:]))
need = -(-comb(n, k + r) // comb(n - k, r))
print(f"n={n} k={k} forbid |A&B| in {sorted(forb)}: Delsarte LP bound {lp(n,k,forb):.2f}; covering needs |H| >= {need}  (slice {comb(n,k)})")
