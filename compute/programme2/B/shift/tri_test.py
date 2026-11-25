"""Schur-triangle step of Theorem S0 alone, in the large-codimension range k/4 < e < k/2 (covering not certified:
the triangle lemma needs only e <= (k-1)/2 and, for k = 2 mod 4, x1 not in C0-perp).  Output checked directly:
three distinct members (size k, zero syndrome under the original rows), x1+x2+x3 = 0, empty triple intersection."""
import random, json, sys, os
from s0 import instance, schur_triangle, popc
from b1 import rank
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
out = {}
for (n, k, M, planted, reps) in [(80, 40, 14, 0, 20), (84, 42, 15, 0, 20), (120, 60, 22, 0, 15), (124, 62, 24, 0, 15),
                                 (120, 60, 20, 6, 15), (170, 82, 34, 0, 10), (170, 80, 30, 8, 10), (400, 200, 90, 0, 4)]:
    for _ in range(reps):
        cols, rows, R = instance(n, k, M, rng, planted)
        e = rank([c ^ cols[0] for c in cols])
        tri, why = schur_triangle(n, k, cols, e, rng)
        if tri is None:
            res = 'fail: ' + why
        else:
            g = tri[:3]
            ok = len(set(g)) == 3 and all(popc(x) == k for x in g) and g[0] ^ g[1] ^ g[2] == 0 and g[0] & g[1] & g[2] == 0
            ok = ok and all(all(popc(x & h) % 2 == 0 for h in rows) for x in g)
            res = 'verified' if ok else 'CHECK-FAIL'
        key = (n, k, planted, 'e<=k/4' if 4 * e <= k else ('e<=(k-1)/2' if 2 * e <= k - 1 else 'e>k/2'))
        out.setdefault(key, {}).setdefault(res, 0); out[key][res] += 1
for key in sorted(out): print(key, out[key])
