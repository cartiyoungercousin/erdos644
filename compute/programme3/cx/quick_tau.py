"""Fast tau bracket for E1/E2 families: LP lower bound tau* and a greedy transversal (upper bound).
usage: py -3.14 quick_tau.py   (prints JSON rows; families as in coset_fams.py / deep_union.py)"""
import json, numpy as np
from tools import tau_lp, popcount64
from coset_fams import CODES as C1, span
import deep_union as du

def greedy(fam, n):
    A = np.array(fam, dtype=np.uint64); T = 0; alive = np.ones(len(A), bool)
    while alive.any():
        cnt = [int(((A[alive] >> np.uint64(x)) & np.uint64(1)).sum()) for x in range(n)]
        x = int(np.argmax(cnt)); T += 1
        alive &= ((A >> np.uint64(x)) & np.uint64(1)) == 0
    return T

def rows_coset(name, ntrial=1500):
    rows, n = C1[name](); C = span(rows); rng = np.random.default_rng(1)
    best = max((int(popcount64(C ^ np.uint64(a)).min()), a) for a in
               (int(rng.integers(0, 2 ** 62)) & ((1 << n) - 1) for _ in range(ntrial)))
    co = C ^ np.uint64(best[1]); w = popcount64(co)
    for k in range(int(np.ceil(n / 1.95)), int(n / 1.72) + 1):
        fam = [int(v) for v in co[w == k]]
        if fam:
            yield dict(fam=f'{name} coset rho={best[0]}', n=n, k=k, N=round(n / k, 3), M=len(fam),
                       tau_lp=round(tau_lp(fam, n), 2), tau_greedy=greedy(fam, n), k34=0.75 * k)

def rows_union(name, w0):
    rows, n = du.CODES[name](); piv = du.echelon([r for r in rows if r])
    V = np.arange(1 << n, dtype=np.uint32); rep = V.copy()
    for p, b in sorted(piv, reverse=True):
        rep ^= ((rep >> np.uint32(p)) & np.uint32(1)) * np.uint32(b)
    wt = popcount64(V.astype(np.uint64)).astype(np.int8)
    cw = np.full(1 << n, 127, dtype=np.int8); np.minimum.at(cw, rep, wt); cwv = cw[rep]
    for k in range(int(np.ceil(n / 1.95)), int(n / 1.72) + 1):
        fam = [int(v) for v in V[(wt == k) & (cwv >= w0)]]
        if fam:
            yield dict(fam=f'{name} union cw>={w0}', n=n, k=k, N=round(n / k, 3), M=len(fam),
                       tau_lp=round(tau_lp(fam, n), 2), tau_greedy=greedy(fam, n), k34=0.75 * k)

if __name__ == '__main__':
    import sys
    gen = rows_coset(sys.argv[1]) if len(sys.argv) == 2 else rows_union(sys.argv[1], int(sys.argv[2]))
    for r in gen:
        print(json.dumps(r), flush=True)
