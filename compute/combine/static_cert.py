"""Exact certification of line type A (static 4-request closure of the anchor) at t = 21/25 over BOXES.

Region R: x >= y >= z > 0, x <= 14/25, x + y + z <= 33/25 (profiles, k = 1).
Lattice boxes of side 1/H.  A box is CERTIFIED if one pattern p of the triple table (no absent cell)
satisfies  w_lambda(p) . mass(x,y,z) <= t  for all lambda at all 8 corners, in exact rational
arithmetic (weights from tables.exact_weights; the forms are affine in (x,y,z), so this proves the
closure on the whole closed box, hence for every profile in it with z > 0).
Output: certified volume fraction of R, and the list of pattern ids used.
usage: py static_cert.py [H=100]
"""
import sys, os, json, itertools
from fractions import Fraction as Fr
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "r1"))
import numpy as np, tables

H = int(sys.argv[1]) if len(sys.argv) > 1 else 100
T = Fr(21, 25); XM = 14 * H // 25; SM = 33 * H // 25
pats, W = tables.triple_table(())
exact = {}
def ex(i):
    if i not in exact: exact[i] = tables.exact_weights(4, pats[i])
    return exact[i]
def mass(i, j, l): return [Fr(i, H), Fr(j, H), Fr(l, H), 1 - Fr(i + j, H), 1 - Fr(i + l, H), 1 - Fr(j + l, H)]
def closes(p, corners):
    for m in corners:
        for row in ex(p):
            if sum(a * b for a, b in zip(row, m)) > T: return False
    return True
vol = Fr(0); cert = Fr(0); used = {}; unc = []
for i in range(XM):
    for j in range(i + 1):
        for l in range(j + 1):
            if i + j + l + 3 > SM: continue
            wgt = Fr(1) if i > j > l else (Fr(1, 6) if i == j == l else Fr(1, 2))
            vol += wgt
            corners = [mass(i + a, j + b, l + c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]
            fm = np.array([[float(v) for v in m] for m in corners])          # 8 x 6
            val = np.einsum("pls,cs->pcl", W, fm).max(axis=(1, 2))            # worst corner, worst lambda
            ok = None
            for p in np.argsort(val)[:4]:
                if val[p] > float(T) + 1e-9: break
                if closes(int(p), corners): ok = int(p); break
            if ok is None: unc.append((i, j, l))
            else: cert += wgt; used[ok] = used.get(ok, 0) + 1
print(f"H={H}: boxes weight {vol}, certified {cert}, fraction {float(cert / vol):.4f}; patterns used: {len(used)}")
print("patterns (id: boxes):", dict(sorted(used.items(), key=lambda a: -a[1])))
json.dump(dict(H=H, used={str(k): v for k, v in used.items()}, patterns={str(k): [str(f) for f in pats[k]] for k in used},
               uncertified=unc), open(os.path.join(here, f"static_cert_{H}.json"), "w"))
