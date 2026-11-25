r"""FABLE_A T1: rerun of core9/escape_check (two-class reversed-order rule, SAT over selectors, pencil clauses,
lazy cuts on found good sevens) with each forbidden seven classified by pool: a = contains the first om points
(Y_a) only, b = contains the last om points (Y_b) only, ab = both.  Usage: py t1_mixed.py k T n iters"""
import itertools, sys, time, random, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "core9"))
from pysat.solvers import Cadical153
from two_ground_sat import three_partitions, mask

def main(k, T, n, iters, seed=0):
    om = n - k - T; ker = n - 3 * k // 2; h = k // 2; rng = random.Random(seed)
    orders = [list(range(n)), list(range(n - 1, -1, -1))]
    YA = (1 << om) - 1; YB = YA << (n - om)
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
        for c in range(2):
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
    covc = {}; FULL = (1 << len(pairs)) - 1; t0 = time.time(); stats = {}
    for it in range(iters):
        if not s.solve():
            print(f"UNSAT after {it} forbidden sevens ({time.time()-t0:.0f}s)"); break
        pos = set(v for v in s.get_model() if v > 0); fam = set()
        for vs, Ks in req: fam.add(Ks[0] if vs[0] in pos else Ks[1])
        fam = list(fam)
        for K in fam:
            if K not in covc: covc[K] = cov(K)
        cm = [covc[K] for K in fam]; best = None
        for restart in range(200):
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
        if not best: print(f"round {it}: no good seven found by local search (not a proof)"); break
        best = sorted(set(best))
        ty = tuple(sorted(("ab" if (K & YA) == YA and (K & YB) == YB else "a" if (K & YA) == YA else "b") for K in best))
        key = (ty.count("a"), ty.count("b"), ty.count("ab"))
        stats[key] = stats.get(key, 0) + 1
        # co-type sizes of pool points
        ca = [sum((K >> x) & 1 for K in best) for x in range(om)]; cb = [sum((K >> x) & 1 for K in best) for x in range(n - om, n)]
        print(f"round {it}: (#a,#b,#ab)={key} cotype sizes Y_a {ca} Y_b {cb} members {[format(K, '0%db' % n)[::-1] for K in best]}")
        s.add_clause([-mem[K] for K in best])
    print("summary (#a,#b,#ab) -> count:", stats)

if __name__ == "__main__":
    a = sys.argv; main(int(a[1]), int(a[2]), int(a[3]), int(a[4]))
