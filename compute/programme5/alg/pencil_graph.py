"""Pencil 3-graph of a family H: vertices = members, edges = triples with empty common intersection.

In the Fano range (n < 11k/6) H is (7,2) iff its pencil 3-graph P(H) contains no Fano plane
(PROGRAMME5_ALG.md, section 1).  The Fano plane is not 2-colourable, so a 2-colourable P(H)
(H = H1 + H2 with both parts 3-wise intersecting) is Fano-free.  This script asks, for the
seven-free complete families K^(k)_n, whether P(H) is 2-colourable (and 3-colourable), i.e.
whether the Turan-extremal ("bipartite") structure of Fano-free 3-graphs is present.

usage: py -3.14 pencil_graph.py k n [colours]
"""
import sys, itertools, time
from pysat.solvers import Solver


def complete_family(n, k):
    return [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)]


def pencil_edges(H, n):
    """Triples (indices) of members with empty common intersection, via complements."""
    full = (1 << n) - 1
    comp = [full & ~b for b in H]
    index = {c: i for i, c in enumerate(comp)}
    c = bin(comp[0]).count("1")
    edges = []
    m = len(H)
    for i in range(m):
        for j in range(i + 1, m):
            u = comp[i] | comp[j]
            rest = full & ~u
            r = bin(rest).count("1")
            if r > c:
                continue
            # S3 must contain rest; choose c-r further points from u
            upts = [p for p in range(n) if (u >> p) & 1]
            for extra in itertools.combinations(upts, c - r):
                s3 = rest | sum(1 << p for p in extra)
                l = index.get(s3)
                if l is not None and l > j:
                    edges.append((i, j, l))
    return edges


def colourable(m, edges, q):
    """Is the 3-graph q-colourable with no monochromatic edge?"""
    var = lambda v, col: v * q + col + 1
    s = Solver(name="cadical153")
    for v in range(m):
        s.add_clause([var(v, col) for col in range(q)])
        for a in range(q):
            for b in range(a + 1, q):
                s.add_clause([-var(v, a), -var(v, b)])
    for (i, j, l) in edges:
        for col in range(q):
            s.add_clause([-var(i, col), -var(j, col), -var(l, col)])
    # symmetry breaking: vertex 0 gets colour 0
    s.add_clause([var(0, 0)])
    ok = s.solve()
    model = s.get_model() if ok else None
    s.delete()
    if not ok:
        return False, None
    pos = set(x for x in model if x > 0)
    return True, [next(col for col in range(q) if var(v, col) in pos) for v in range(m)]


if __name__ == "__main__":
    k, n = int(sys.argv[1]), int(sys.argv[2])
    qs = [int(x) for x in sys.argv[3:]] or [2, 3]
    t0 = time.time()
    H = complete_family(n, k)
    E = pencil_edges(H, n)
    print(f"K^({k})_{n}: |H|={len(H)} pencils={len(E)} density={len(E)/((len(H)*(len(H)-1)*(len(H)-2))/6):.4f}"
          f" ({time.time()-t0:.1f}s)", flush=True)
    for q in qs:
        t0 = time.time()
        ok, col = colourable(len(H), E, q)
        print(f"  {q}-colourable: {ok} ({time.time()-t0:.1f}s)", flush=True)
        if ok and q == 2:
            # describe the classes: sizes, common points, transversal numbers by brute force
            for c in range(2):
                cls = [H[v] for v in range(len(H)) if col[v] == c]
                inter = (1 << n) - 1
                for b in cls:
                    inter &= b
                print(f"   class {c}: size {len(cls)}, common point(s) {bin(inter).count('1')}")
            break
