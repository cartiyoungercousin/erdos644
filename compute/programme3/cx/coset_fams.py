"""Experiment E1: coset families of structured codes (RM, BCH/QR cyclic) at n = 23..32.
H = weight-k vectors of a + C, for a deep coset a (max coset weight found) and for k with 1.7 <= n/k <= 2.1.
Reports tau (exact ILP), tau-3k/4, coset weight rho, W/P (triple / pencil sum minima), Lemma Q threshold,
general good-seven SAT.   usage: py -3.14 coset_fams.py CODE   (CODE in rm25, bch31, qr31, qr23x, rm25s)
"""
import sys, itertools, time, json
import numpy as np
from tools import tau_ilp, triple_stats, seven_sat, check_seven, popcount64

def rm_gen(r, m):
    pts = list(itertools.product([0, 1], repeat=m)); rows = []
    for d in range(r + 1):
        for S in itertools.combinations(range(m), d):
            rows.append(sum(1 << i for i, p in enumerate(pts) if all(p[j] for j in S)))
    return rows, 2 ** m

def cyclic_gen(n, gpoly):
    deg = gpoly.bit_length() - 1
    return [gpoly << i for i in range(n - deg)], n

def polymul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r

def span(rows):
    words = np.zeros(1, dtype=np.uint64)
    for g in rows:
        words = np.concatenate([words, words ^ np.uint64(g)])
    return words

CODES = {
    'rm25': lambda: rm_gen(2, 5),               # [32,16,8]
    'rm15': lambda: rm_gen(1, 5),               # [32,6,16]
    'bch31': lambda: cyclic_gen(31, polymul(polymul(0b100101, 0b111101), 0b110111)),  # [31,16,7]
    'bch31b': lambda: cyclic_gen(31, polymul(0b100101, 0b111101)),  # [31,21,5]
}

def main(name, ntrial=1500, budget=400_000):
    rows, n = CODES[name]()
    C = span(rows); dim = len(rows)
    rng = np.random.default_rng(1)
    best = []
    for _ in range(ntrial):
        a = int(rng.integers(0, 2 ** 62)) & ((1 << n) - 1)
        w = int(popcount64(C ^ np.uint64(a)).min())
        best.append((w, a))
    best.sort(reverse=True)
    rho_max = best[0][0]
    print(f'{name}: n={n} dim={dim} codim={n-dim} max coset weight seen={rho_max}', flush=True)
    out = []
    for rho_target in sorted(set(w for w, _ in best[:200]), reverse=True)[:1]:
        a = next(a for w, a in best if w == rho_target)
        coset = C ^ np.uint64(a)
        wts = popcount64(coset)
        for k in range(int(np.ceil(n / 1.95)), int(n / 1.72) + 1):
            fam = [int(v) for v in coset[wts == k]]
            if not fam: continue
            t0 = time.time()
            tau, lb, st = tau_ilp(fam, n, 60)
            W, P, ex = triple_stats(fam, maxpairs=20_000)
            thrQ = (12 * n - 21 * k) / 7
            res, sv = seven_sat(fam, n, budget)
            if sv: assert check_seven(sv, n)
            row = dict(code=name, n=n, k=k, N=round(n / k, 3), rho=rho_target, M=len(fam), tau=tau, tau_lb=lb,
                       status=st, excess=tau - 0.75 * k, W=W, P=P, exact_WP=ex, lemmaQ_thr=round(thrQ, 2),
                       seven=res, secs=round(time.time() - t0, 1))
            print(json.dumps(row), flush=True); out.append(row)
    return out

if __name__ == '__main__':
    main(sys.argv[1])
