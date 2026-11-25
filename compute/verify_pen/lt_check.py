"""(LT) via Theorem PEN, exact: k<=K, k<=n, 6n<11k, every T with 4T>3k (e=T-3k/4>0), r=n-k-T>=0.
Light: weight <= (12n-21k)/7.  Report (k,n,T) where PEN's conditions fail or r+D > (12n-21k)/7."""
import sys
from fractions import Fraction as F
from cond import pen_ok
K = int(sys.argv[1]); fails = []; cnt = 0
for k in range(1, K + 1):
    for n in range(k, (11 * k - 1) // 6 + 1):
        for T in range(0, n - k + 1):
            if 4 * T <= 3 * k: continue
            r = n - k - T; thr = F(12 * n - 21 * k, 7)
            if thr < 0: fails.append((k, n, T, r, 'thr<0')); cnt += 1; continue
            P = int(thr) if thr >= 0 else -1; cnt += 1
            ok, info = pen_ok(n, k, r, P)
            if not ok:
                ok2, _ = pen_ok(n, k, r, P, any_interval=True)
                if not ok2: fails.append((k, n, T, r, float(thr), info))
print(f"K={K}: cases={cnt} fails={len(fails)}")
for f in fails[:25]: print('  ', f)
from collections import Counter
print('patterns (r, 4T-3k):', Counter((f[3], 4 * f[2] - 3 * f[0]) for f in fails))
