"""Exact small cases by CEGAR-SAT: is there a k-uniform family on [n] with property (7,2) and tau > T?

  main SAT: x_e for every k-subset e of [n];  every (n-T)-subset contains an edge.
  refinement: find <=7 chosen edges with no 2-point transversal (set cover over point pairs);
  forbid it together with all its images under S_n (orbit clauses), repeat.
UNSAT => no such family on n points.  SAT with no bad subfamily => witness (verified by brute force).
usage: py small_exact.py k T n [max_iters]
"""
import itertools, sys, time
from pysat.solvers import Cadical153, Glucose4
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def find_bad(H, n, p=7):
    """Return a list of <= p edges of H with no 2-point transversal, smallest first; None if none."""
    pairs = list(itertools.combinations(range(n), 2))
    miss = []
    for (u, v) in pairs:
        S = [i for i, e in enumerate(H) if u not in e and v not in e]
        if not S: return None            # {u,v} is a transversal of all of H: no bad subfamily at all
        miss.append(S)
    for size in range(3, p + 1):
        pool = IDPool(start_from=len(H) + 1)
        with Glucose4() as s:
            for S in miss: s.add_clause([i + 1 for i in S])
            for cl in CardEnc.atmost(lits=list(range(1, len(H) + 1)), bound=size, vpool=pool,
                                     encoding=EncType.seqcounter).clauses:
                s.add_clause(cl)
            if s.solve():
                mod = set(l for l in s.get_model() if 0 < l <= len(H))
                return [H[i - 1] for i in sorted(mod)]
    return None

def brute_check(H, n, T):
    k = len(H[0])
    # tau > T : every (n-T)-set contains an edge
    Hs = [frozenset(e) for e in H]
    for W in itertools.combinations(range(n), n - T):
        Ws = set(W)
        if not any(e <= Ws for e in Hs): return False
    return find_bad(H, n) is None

def run(k, T, n, max_iters=100000, use_orbits=True):
    edges = list(itertools.combinations(range(n), k))
    idx = {e: i + 1 for i, e in enumerate(edges)}
    s = Glucose4()
    for W in itertools.combinations(range(n), n - T):
        s.add_clause([idx[e] for e in itertools.combinations(W, k)])
    perms = list(itertools.permutations(range(n))) if (use_orbits and n <= 9) else None
    seen = set(); t0 = time.time(); it = 0
    while it < max_iters:
        it += 1
        if not s.solve():
            return ("UNSAT", it, time.time() - t0)
        mod = s.get_model()
        H = [e for e in edges if mod[idx[e] - 1] > 0]
        bad = find_bad(H, n)
        if bad is None:
            assert brute_check(H, n, T)
            return ("SAT", it, time.time() - t0, H)
        if perms is None:
            s.add_clause([-idx[e] for e in bad])
        else:
            for pm in perms:
                img = frozenset(tuple(sorted(pm[v] for v in e)) for e in bad)
                if img not in seen:
                    seen.add(img); s.add_clause([-idx[e] for e in img])
        if it % 20 == 0:
            print(f"  iter {it}, |H|={len(H)}, bad size {len(bad)}, clauses {len(seen)}, {time.time()-t0:.0f}s", flush=True)
    return ("UNKNOWN", it, time.time() - t0)

if __name__ == "__main__":
    k, T, n = map(int, sys.argv[1:4])
    mi = int(sys.argv[4]) if len(sys.argv) > 4 else 100000
    res = run(k, T, n, mi)
    print(f"k={k} T={T} n={n}: {res[0]} after {res[1]} iterations, {res[2]:.1f}s")
    if res[0] == "SAT":
        print("  family (tau >= T+1, property (7,2)):", len(res[3]), "edges"); print("  ", res[3])
