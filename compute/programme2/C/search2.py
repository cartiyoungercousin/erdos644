r"""Exhaustive search over two-block families H_J (all J, all splits a <= b) at fixed (k, n):
the largest tau among Fano-seven-free H_J (exact), and the best-halfspace fraction of the extremal ones.
usage: search2.py k n [maxkeep]"""
import sys
from twoblock import seven, best_halfspace, tau

def tau_fast(J, a, b, k):
    n = a + b
    if not J: return 0
    c = [min(a, J[0] - 1) + b, a + min(b, k - J[-1] - 1)]
    for i in range(len(J) - 1):
        c.append(min(a, J[i + 1] - 1) + min(b, k - J[i] - 1))
    return n - max(c)

def run(k, n, maxkeep=6):
    best = -1; keep = []
    for a in range(1, n // 2 + 1):
        b = n - a; lo, hi = max(0, k - b), min(a, k); W = hi - lo + 1
        if W <= 0: continue
        cands = []
        for mask in range(1, 1 << W):
            J = [lo + i for i in range(W) if mask >> i & 1]
            t = tau_fast(J, a, b, k)
            if t >= best: cands.append((t, J))
        cands.sort(key=lambda c: -c[0])
        for t, J in cands:
            if t < best: break
            if seven(J, a, b, k) is None:
                if t > best: best = t; keep = []
                if len(keep) < maxkeep: keep.append((a, J))
    return best, keep

if __name__ == '__main__':
    k, n = int(sys.argv[1]), int(sys.argv[2]); mk = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    best, keep = run(k, n, mk)
    print(f'k={k} n={n} N={n/k:.3f} max tau seven-free (two-block) = {best}  3k/4 = {3*k/4}')
    for a, J in keep:
        f = best_halfspace(J, a, n - a, k)
        assert tau(J, a, n - a, k) == best
        print(f'   a={a} J={J} best-halfspace frac={f[0]:.4f} (t,s)={f[1:]}')
