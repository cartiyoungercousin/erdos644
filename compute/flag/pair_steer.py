"""Level-2 truncation at the lower window end (CORE §77): pair need as a function of o."""
import sys, numpy as np
from fano import need, pair_cells
t = float(sys.argv[1]); N = float(sys.argv[2])
c = N - 1; om = N - 1 - t; eps = t - 0.75
print(f"t={t} N={N} omega={om:.4f} 4eps={4*eps:.4f} base={om-4*eps:.4f}")
zs = []
for o in np.linspace(max(0, 2*c-N), c, 401):
    v = need(pair_cells(N, c, o), {0: 0, 1: 1}, t)
    if v is not None and v <= 1e-9: zs.append(o)
if zs: print(f"zero set of pair need (static 5-line finish): o in [{min(zs):.4f}, {max(zs):.4f}], width {max(zs)-min(zs):.4f} vs omega {om:.4f}")
else: print("zero set empty")
for o in np.linspace(max(0,2*c-N), c, 11):
    print(f"  o={o:.4f} need={need(pair_cells(N,c,o),{0:0,1:1},t)}")
