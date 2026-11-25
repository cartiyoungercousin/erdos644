"""Check: the clean sufficient condition  r>=1, 4T >= 2k+5r+3, 3r <= 2k-2  implies every exact size
condition of Theorem PEN (note interval).  usage: suff_check.py K"""
import sys
from cond import pen_ok
K = int(sys.argv[1]); bad = []; cnt = 0
for k in range(1, K + 1):
    for r in range(1, k + 1):
        if 3 * r > 2 * k - 2: break
        for T in range(0, 3 * k):
            if 4 * T < 2 * k + 5 * r + 3: continue
            n = T + k + r; cnt += 1
            ok, info = pen_ok(n, k, r)
            if not ok: bad.append((k, r, T, info))
print(f"K={K}: cases={cnt} failures={len(bad)}", bad[:10])
