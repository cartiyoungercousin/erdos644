r"""CORE 55.5: decide EXACTLY whether the first pencil-free family produced by escape_check.py (round 0) has a good seven.
Rebuilds the same SAT instance in the same clause order (Cadical is deterministic), extracts the family (rule verbatim),
re-checks T-covering and pencil-freeness on the family itself, then asks a second SAT solver: are there 7 members covering
all pairs of V?  Also computes the minimum number of members covering all pairs (iterating the bound).
Usage: py decide_family.py k T n R mode [seed] [outfile]
"""
import itertools, sys, time, random
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from two_ground_sat import three_partitions, mask

def build(k, T, n, R, mode, seed=0):
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
        s.add_clause(vs); req.append((ms, vs, Ks))
    for kap in itertools.combinations(range(n), ker):
        mk = mask(kap); X = [x for x in range(n) if not (mk >> x) & 1]
        for P in three_partitions(X, h):
            L = [mk | mask(p) for p in P]
            if all(l in mem for l in L): s.add_clause([-mem[l] for l in L])
    assert s.solve()
    pos = set(v for v in s.get_model() if v > 0)
    fam = set(); sel = {}
    for ms, vs, Ks in req:
        c = next(c for c in range(R) if vs[c] in pos); fam.add(Ks[c]); sel[ms] = c
    return sorted(fam), sel, orders

def pencils(fam, n, k):
    """count perfect pencils inside fam (three members, pairwise intersection = common kernel of size n-3k/2, union V)."""
    ker = n - 3 * k // 2; F = set(fam); cnt = 0; full = (1 << n) - 1
    for a, b in itertools.combinations(fam, 2):
        kap = a & b
        if kap.bit_count() != ker: continue
        c = (full & ~(a | b)) | kap
        if c in F and c > b: cnt += 1
    return cnt

def min_cover(fam, n, k, lo=7, upto=8):
    """lo is the Schoenheim bound ceil(n/(n-k) ceil((n-1)/(n-k-1))), passed in.
    Implied constraints added (sound for every cover by m members of size c = n-k): each point in >= ceil((n-1)/(c-1)) members."""
    pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]
    res = {}; c = n - k; rmin = -(-(n - 1) // (c - 1))
    for m in range(lo, upto + 1):
        cl = [[i + 1 for i, K in enumerate(fam) if (K >> x) & 1 and (K >> y) & 1] for (x, y) in pairs]
        enc = CardEnc.atmost(lits=list(range(1, len(fam) + 1)), bound=m, top_id=len(fam), encoding=EncType.seqcounter)
        cl += enc.clauses; top = max(enc.nv, len(fam))
        for x in range(n):
            e = CardEnc.atleast(lits=[i + 1 for i, K in enumerate(fam) if (K >> x) & 1], bound=rmin, top_id=top, encoding=EncType.seqcounter)
            cl += e.clauses; top = max(top, e.nv)
        s = Cadical153(bootstrap_with=cl)
        t0 = time.time(); ok = s.solve(); dt = time.time() - t0
        sol = [fam[v - 1] for v in s.get_model() if 0 < v <= len(fam)] if ok else None
        res[m] = (ok, sol, dt)
        print(f"   cover by <= {m} members: {'SAT' if ok else 'UNSAT'} ({dt:.1f}s)", flush=True)
        if ok: break
    return res

if __name__ == "__main__":
    a = sys.argv; k, T, n, R, mode = int(a[1]), int(a[2]), int(a[3]), int(a[4]), a[5]
    seed = int(a[6]) if len(a) > 6 else 0
    fam, sel, orders = build(k, T, n, R, mode, seed)
    print(f"k={k} T={T} n={n} R={R} {mode} seed={seed}: family {len(fam)} members of size {n-k}", flush=True)
    # T-covering re-check from the family alone
    Fl = fam
    unc = sum(1 for S in itertools.combinations(range(n), T) if not any((K & mask(S)) == mask(S) for K in Fl))
    print(f"   T-sets not inside any member: {unc}   perfect pencils inside the family: {pencils(fam, n, k)}")
    from collections import Counter
    print(f"   class counts: {Counter(sel.values())}")
    if len(a) > 7:
        with open(a[7], "w") as f:
            for K in fam: f.write(" ".join(str(x) for x in range(n) if (K >> x) & 1) + "\n")
        print(f"   family written to {a[7]}", flush=True)
    c = n - k; lo = -(-n * (-(-(n - 1) // (c - 1))) // c)
    print(f"   Schoenheim bound for covering pairs of {n} points by {c}-sets: {lo}", flush=True)
    res = min_cover(fam, n, k, lo=lo, upto=max(lo, 7) + 1)
