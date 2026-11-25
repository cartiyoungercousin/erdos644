"""Scan o in [lo,hi] with robust3's level-3 test.  Usage: py -3.14 scan3.py t N lo hi n"""
import sys
t, N, lo, hi, n = sys.argv[1], sys.argv[2], float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
sys.argv = ['robust3', t, N]
import robust3 as r
from fano import need, pair_cells
print(f"t={r.t} N={r.N} omega={r.om:.4f} Z=[N-2t,3t-2]=[{r.N-2*r.t:.4f},{3*r.t-2:.4f}]", flush=True)
for i in range(n + 1):
    o = lo + (hi - lo) * i / n
    z = need(pair_cells(r.N, r.c, o), {0: 0, 1: 1}, r.t); res = r.o_wins(o)
    print(f"o={o:.4f} pairneed={z:.4f}", (res[1], res[2], {k: round(v, 4) for k, v in res[0].items()}) if res else '-', flush=True)
