"""CORE 48.1: is the perfect-sunflower hypergraph R-colourable?
Vertices: T-subsets of a ground set G, |G| = k + T.  Edges: triples S1, S2, S3 with a common pairwise intersection (kernel, T - k/2
points) and union G (three petals of k/2 points).  R-colourable <=> a selector with R classes can avoid every pencil frame of one
head.  SAT (python-sat).  Usage: py sunflower_ramsey.py k T R
"""
import itertools, sys, time
from pysat.solvers import Cadical153


def three_partitions(X, h):
    X = list(X)
    first = X[0]
    for A in itertools.combinations(X[1:], h - 1):
        P1 = (first,) + A
        rest = [x for x in X if x not in P1]
        f2 = rest[0]
        for B in itertools.combinations(rest[1:], h - 1):
            P2 = (f2,) + B
            P3 = tuple(x for x in rest if x not in P2)
            yield P1, P2, P3


def run(k, T, R):
    g = k + T; q = T - k // 2; h = k // 2
    idx = {}
    def vid(S, c):
        key = frozenset(S)
        if key not in idx: idx[key] = len(idx)
        return idx[key] * R + c + 1
    s = Cadical153(); ne = 0; t0 = time.time()
    for kap in itertools.combinations(range(g), q):
        X = [x for x in range(g) if x not in kap]
        for P in three_partitions(X, h):
            vs = [frozenset(kap + p) for p in P]
            for c in range(R): s.add_clause([-vid(v, c) for v in vs])
            ne += 1
    for key, i in idx.items(): s.add_clause([i * R + c + 1 for c in range(R)])
    # symmetry breaking: first vertex colour 0
    s.add_clause([1])
    ok = s.solve()
    print(f"k={k} T={T} |G|={g}: {len(idx)} vertices, {ne} sunflowers; {R}-colourable: {ok}  ({time.time()-t0:.0f}s)", flush=True)
    if ok:
        m = set(x for x in s.get_model() if x > 0)
        col = {key: next(c for c in range(R) if i * R + c + 1 in m) for key, i in idx.items()}
        return col
    return None


if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
