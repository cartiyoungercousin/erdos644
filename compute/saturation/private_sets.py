r"""Private sets (MINIMAL_FRAME Lemma 3) in the near-pool 2-cell profile families at (10,8,21). [computed exact]
Co-edge form: K needs S_K inside K, |S_K| <= T = 8, contained in no OTHER co-edge. In a profile family the number of
co-edges containing a set S of profile s is  sum over q in P, q >= s, of C(18 - s_A, q_A - s_A) * C(3 - s_Y, q_Y - s_Y);
S is private to K iff this number is 1. Usage: py -3.14 private_sets.py"""
import itertools
from math import comb
for r in range(4):
    for sub in itertools.combinations([(9, 2), (10, 1), (11, 0)], r):
        P = [(8, 3)] + list(sub)
        out = []
        for p in P:
            ok = any(sum(comb(18 - a, q[0] - a) * comb(3 - b, q[1] - b) for q in P if q[0] >= a and q[1] >= b) == 1
                     for a in range(p[0] + 1) for b in range(p[1] + 1) if a + b <= 8)
            out.append(f"{p}:{'yes' if ok else 'NO'}")
        print(f"P = {P}: private set exists for co-edge profile", ', '.join(out))
