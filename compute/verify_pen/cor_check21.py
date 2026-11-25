"""Exact check of Corollary (slope 3/11): for every k<=K, k<=n<=nmax(k) and every T with
T+1 > (3n+3k+24)/11, 0<=T<=n-k, Theorem PEN (with its exact size conditions) yields a pencil of
weight <= 4T-3k-6 (Lemma P1 threshold), giving a good seven -> contradiction with (7,2).
Reports failures. usage: cor_check.py K [ratio_num ratio_den]  (n up to ratio*k, default 2)"""
import sys
from fractions import Fraction as F
from cond import pen_ok
C = 21
K = int(sys.argv[1]); num, den = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (2, 1)
fails = []; fails_any = []; cnt = 0
for k in range(1, K + 1):
    for n in range(k, num * k // den + 1):
        for T in range(0, n - k + 1):
            if not (11 * (T + 1) > 3 * n + 3 * k + C): continue
            r = n - k - T; P = 4 * T - 3 * k - 6; cnt += 1
            ok, info = pen_ok(n, k, r, P)
            if not ok:
                fails.append((k, n, T, r, P, info))
                ok2, info2 = pen_ok(n, k, r, P, any_interval=True)
                if not ok2: fails_any.append((k, n, T, r, P))
print(f"K={K} n<= {num}/{den} k: cases={cnt} fails(note interval)={len(fails)} fails(any interval)={len(fails_any)}")
for f in fails[:40]: print('  note-I fail', f)
for f in fails_any[:40]: print('  ANY-I fail', f)
if fails_any:
    print('  max k with ANY-I fail:', max(f[0] for f in fails_any))
