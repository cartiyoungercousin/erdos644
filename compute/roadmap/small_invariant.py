"""Group-invariant variant of small_exact.py: search for a k-uniform family on [n], invariant under
a permutation group G, with tau > T and property (7,2).  Variables = G-orbits of k-sets.
SAT answers are genuine witnesses (brute-force verified); UNSAT only excludes G-invariant families.
usage: py small_invariant.py k T n group     group in: cyc (Z_n), cycfix (Z_{n-1} + fixed point),
                                              dih (D_n), aff (AGL(1,n) for prime n), afffix
"""
import itertools, sys, time
from pysat.solvers import Glucose4
from small_exact import find_bad, brute_check

def gens(n, name):
    if name == "cyc":    return [tuple((i + 1) % n for i in range(n))]
    if name == "cycfix": return [tuple(((i + 1) % (n - 1)) if i < n - 1 else i for i in range(n))]
    if name == "dih":    return [tuple((i + 1) % n for i in range(n)), tuple((-i) % n for i in range(n))]
    if name == "aff":
        g = next(a for a in range(2, n) if len({pow(a, e, n) for e in range(n - 1)}) == n - 1)
        return [tuple((i + 1) % n for i in range(n)), tuple((g * i) % n for i in range(n))]
    if name == "afffix":
        m = n - 1
        g = next(a for a in range(2, m) if len({pow(a, e, m) for e in range(m - 1)}) == m - 1)
        return [tuple(((i + 1) % m) if i < m else i for i in range(n)),
                tuple(((g * i) % m) if i < m else i for i in range(n))]
    raise ValueError(name)

def run(k, T, n, name, max_iters=200000):
    G = gens(n, name)
    edges = list(itertools.combinations(range(n), k))
    orb = {}
    for e in edges:
        if e in orb: continue
        stack, comp = [e], {e}
        while stack:
            f = stack.pop()
            for g in G:
                h = tuple(sorted(g[v] for v in f))
                if h not in comp: comp.add(h); stack.append(h)
        oid = len(set(orb.values())) + 1
        for f in comp: orb[f] = oid
    s = Glucose4()
    for W in itertools.combinations(range(n), n - T):
        s.add_clause(sorted({orb[e] for e in itertools.combinations(W, k)}))
    t0 = time.time()
    for it in range(1, max_iters + 1):
        if not s.solve(): return "UNSAT(invariant)", it, time.time() - t0, None
        mod = set(l for l in s.get_model() if l > 0)
        H = [e for e in edges if orb[e] in mod]
        bad = find_bad(H, n)
        if bad is None:
            assert brute_check(H, n, T)
            return "SAT", it, time.time() - t0, H
        s.add_clause(sorted({-orb[e] for e in bad}))
    return "UNKNOWN", it, time.time() - t0, None

if __name__ == "__main__":
    k, T, n = map(int, sys.argv[1:4]); name = sys.argv[4]
    st, it, tm, H = run(k, T, n, name)
    print(f"k={k} T={T} n={n} group={name}: {st} after {it} iterations, {tm:.1f}s")
    if H: print("  edges:", len(H), H if len(H) <= 80 else H[:80])
