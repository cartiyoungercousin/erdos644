r"""CORE 56.3: adversarially structured selectors = SAT-optimal pencil-free selectors for a greedy rule with R classes (two_ground_sat).
For each such selector: build the family (rule verbatim), search a good seven (seven members covering all pairs, brute-force masks),
forbid it (clause on the seven members) and re-solve.  Stops when UNSAT (= every selector for these orders has a pencil or one of the
found sevens: exact) or after `iters` rounds, or when the local search finds no good seven (reported, NOT a proof of absence).
Usage: py escape_check.py k T n R mode iters [seed]
"""
import itertools, sys, time, random
from pysat.solvers import Cadical153
from two_ground_sat import three_partitions, mask

def main(k, T, n, R, mode, iters, seed=0):
    om = n - k - T; ker = n - 3 * k // 2; h = k // 2; rng = random.Random(seed)
    if mode == "rev": orders = [list(range(n)), list(range(n - 1, -1, -1))][:R]
    else: orders = [rng.sample(range(n), n) for _ in range(R)]
    s = Cadical153(); nv = 0; mem = {}; req = []
    def mv(K):
        nonlocal nv
        if K not in mem: nv += 1; mem[K] = nv
        return mem[K]
    for S in itertools.combinations(range(n), T):
        ms = mask(S); Ks = []
        for o in orders:
            K = ms; c = 0
            for x in o:
                if not (ms >> x) & 1:
                    K |= 1 << x; c += 1
                    if c == om: break
            Ks.append(K)
        vs = []
        for c in range(R):
            nv += 1; vs.append(nv); s.add_clause([-nv, mv(Ks[c])])
        s.add_clause(vs); req.append((vs, Ks))
    for kap in itertools.combinations(range(n), ker):
        mk = mask(kap); X = [x for x in range(n) if not (mk >> x) & 1]
        for P in three_partitions(X, h):
            L = [mk | mask(p) for p in P]
            if all(l in mem for l in L): s.add_clause([-mem[l] for l in L])
    pairs = [(x, y) for x in range(n) for y in range(x, n)]
    def cov(K):
        m = 0
        for i, (x, y) in enumerate(pairs):
            if (K >> x) & 1 and (K >> y) & 1: m |= 1 << i
        return m
    covc = {}
    FULL = (1 << len(pairs)) - 1
    t0 = time.time(); found = 0
    for it in range(iters):
        if not s.solve():
            print(f"k={k} T={T} n={n} R={R} {mode}: UNSAT after {found} forbidden sevens: every selector has a pencil or one of them [exact] ({time.time()-t0:.0f}s)"); return
        model = s.get_model(); pos = set(v for v in model if v > 0)
        fam = set()
        for vs, Ks in req:                       # the rule verbatim: the member is the reply of the selected class
            c = next(c for c in range(R) if vs[c] in pos); fam.add(Ks[c])
        fam = list(fam)
        for K in fam:
            if K not in covc: covc[K] = cov(K)
        cm = [covc[K] for K in fam]
        best = None
        for restart in range(60):
            cur = [rng.randrange(len(fam)) for _ in range(7)]
            for step in range(200):
                i = rng.randrange(7); base = 0
                for j in range(7):
                    if j != i: base |= cm[cur[j]]
                if rng.random() < 0.15: cur[i] = rng.randrange(len(fam))
                else:
                    bv = -1; bi = []
                    for a, m in enumerate(cm):
                        v = (base | m).bit_count()
                        if v > bv: bv = v; bi = [a]
                        elif v == bv and len(bi) < 50: bi.append(a)
                    cur[i] = rng.choice(bi)
                tot = 0
                for j in range(7): tot |= cm[cur[j]]
                if tot == FULL: best = [fam[j] for j in cur]; break
            if best: break
        if not best:
            print(f"k={k} T={T} n={n} R={R} {mode}: round {it}: pencil-free family of {len(fam)} members, local search found NO good seven "
                  f"(not a proof) ({time.time()-t0:.0f}s)", flush=True); return
        found += 1
        s.add_clause([-mem[K] for K in set(best)])
        if it % 20 == 0: print(f"  round {it}: family {len(fam)} members, good seven found and forbidden ({time.time()-t0:.0f}s)", flush=True)
    print(f"k={k} T={T} n={n} R={R} {mode}: {found}/{iters} rounds: every pencil-free selector produced had a good seven; not exhausted ({time.time()-t0:.0f}s)")

if __name__ == "__main__":
    a = sys.argv
    main(int(a[1]), int(a[2]), int(a[3]), int(a[4]), a[5], int(a[6]), int(a[7]) if len(a) > 7 else 0)
