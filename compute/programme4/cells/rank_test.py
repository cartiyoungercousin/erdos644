r"""Route 3 rank test (short run).  For a family M (members as bitmasks on n points) compute the rank over F_p
(p = 2, 3, 7) of the member-point incidence matrix, and the worst deficit over restrictions: delete a point set D
(|D| <= 2, all D), keep members disjoint from D, columns V \ D.  deficit = (#columns) - rank.
Seven-free families vs covering families WITH good sevens (same k, same n, same cell structure where possible).
usage: rank_test.py  (writes certs/rank_test.json and prints a table)"""
import itertools, json, os, random, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
from brute import members, tau_brute, seven_brute
import cells


def rank_mod(rows, n, p):
    if not rows:
        return 0
    A = np.array([[(B >> v) & 1 for v in range(n)] for B in rows], dtype=np.int64) % p
    r = 0
    for c in range(n):
        piv = np.nonzero(A[r:, c])[0]
        if len(piv) == 0:
            continue
        i = r + piv[0]
        A[[r, i]] = A[[i, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        nz = np.nonzero(A[:, c])[0]
        nz = nz[nz != r]
        if len(nz):
            A[nz] = (A[nz] - np.outer(A[nz, c], A[r])) % p
        r += 1
        if r == A.shape[0]:
            break
    return r


def profile(M, n, cap=2, Mfull=None):
    out = {}
    for p in (2, 3, 7):
        full = n - rank_mod(Mfull if Mfull is not None else M, n, p)
        worst = 0
        for d in range(1, cap + 1):
            for D in itertools.combinations(range(n), d):
                dm = sum(1 << v for v in D)
                sub = [B for B in M if not B & dm]
                cols = [v for v in range(n) if not (dm >> v) & 1]
                rows = [sum(((B >> v) & 1) << t for t, v in enumerate(cols)) for B in sub]
                worst = max(worst, len(cols) - rank_mod(rows, len(cols), p))
        out[p] = (full, worst)
    return out


def coedge_file(fn, n):
    full = (1 << n) - 1
    return [full ^ sum(1 << int(v) for v in line.split()) for line in open(fn) if line.strip()]


def sample_rows(M, cap, rng):
    return M if len(M) <= cap else rng.sample(M, cap)


if __name__ == '__main__':
    rng = random.Random(5)
    cases = []
    # seven-free: complete families (tau = n-k+1) and two-cell families found by the search; controls: covering
    # two-cell families on the same split that DO contain a good seven (J proposed during CEGAR / complete at n+).
    specs = [  # (label, a, k, J or None=complete)
        ('complete k8 n13', (13,), 8, None), ('complete k9 n16', (16,), 9, None), ('complete k10 n17', (17,), 10, None),
        ('complete k12 n20', (20,), 12, None),
        ('complete k8 n14 (seven)', (14,), 8, None), ('complete k10 n18 (seven)', (18,), 10, None),
    ]
    odd = lambda a, k: [j for j in cells.universe(a, k) if j[0] % 2 == 1]
    specs += [('parity k12 (11,11) [seven-free]', (11, 11), 12, odd((11, 11), 12)),
              ('parity k12 (10,12) [seven-free]', (10, 12), 12, odd((10, 12), 12)),
              ('2-cell k8 (6,7) J=1..6 [seven-free]', (6, 7), 8, [(i, 8 - i) for i in range(1, 7)]),
              ('complete k12 (11,11) n22 (seven)', (11, 11), 12, None)]
    # controls: random covering J (tau > T) on the same split that DO have a good seven
    for a, k, T, cnt in [((11, 11), 12, 9, 3), ((10, 12), 12, 9, 2), ((6, 7), 8, 5, 2)]:
        U = cells.universe(a, k); got = 0
        while got < cnt:
            J = [j for j in U if rng.random() < 0.6]
            if J and cells.tau_of(a, k, J) > T and cells.find_seven(a, k, J, 120)[0] == 'FOUND':
                specs.append((f'random covering {a} k{k} (seven) #{got}', a, k, J)); got += 1
    res = []
    for label, a, k, J in specs:
        n = sum(a)
        J = cells.universe(a, k) if J is None else J
        Mf = members(a, k, J)
        M = sample_rows(Mf, 6000, rng)   # restrictions use a 6000-row sample (rank of a sample <= true rank)
        pr = profile(M, n, 2 if n <= 20 else 1, Mfull=Mf)
        res.append(dict(label=label, a=a, k=k, n=n, rank=pr))
        print(f"{label:42s} n={n:2d}  F2 {pr[2]}  F3 {pr[3]}  F7 {pr[7]}   (deficit full, worst over |D|<=2)", flush=True)
    # the (8,6,15) family
    fn = os.path.join(HERE, '..', '..', 'core9', 'logs', 'fam_8_6_15_rev.txt')
    M = coedge_file(fn, 15)
    pr = profile(M, 15, 2)
    print(f"{'fam_8_6_15 (core9, seven-free)':42s} n=15  F2 {pr[2]}  F3 {pr[3]}  F7 {pr[7]}")
    res.append(dict(label='fam_8_6_15', n=15, k=8, rank=pr))
    json.dump(res, open(os.path.join(HERE, 'certs', 'rank_test.json'), 'w'), indent=1, default=str)
