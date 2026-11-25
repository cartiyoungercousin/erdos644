"""Toy (triple) version of the proposed colouring complex N(H), and its low homology over F_3.

Toy complex N_toy(H): a vertex is (i, c) with B_i a member and c: B_i -> {0,1,2} NOT surjective
(c misses some colour s; "vertex serves s").  Two vertices are adjacent iff the colourings agree on
B_i cap B_j (same member, different colouring: not adjacent).  N_toy is the clique complex.
This is exactly the reviewer's construction for F_2^2 (Singer cycle Z_3 in GL_2(F_2)); colour s
is identified with the unique u in F_2^2 \\ 0 orthogonal to the point's colour.

A simplex serving all three colours = three members with empty common intersection (good triple).
Criterion (Dold/Volovikov, p = 3): Htilde_0 = Htilde_1 = 0 over F_3  ==>  good triple.

We compute b0 - 1 and dim H_1(N_toy; F_3) via: spanning forest, projection of triangle boundaries
onto non-tree edges, sparse elimination mod 3 with early stop.
"""
import itertools, sys, random
from collections import defaultdict


def vertices(fam):
    V = []
    for i, B in enumerate(fam):
        Bs = sorted(B)
        for c in itertools.product(range(3), repeat=len(Bs)):
            if len(set(c)) < 3:
                V.append((i, dict(zip(Bs, c))))
    return V


def build(fam):
    V = vertices(fam)
    by_member = defaultdict(list)
    for idx, (i, c) in enumerate(V):
        by_member[i].append(idx)
    m = len(fam)
    adj = [set() for _ in V]
    for i in range(m):
        for j in range(i + 1, m):
            I = sorted(fam[i] & fam[j])
            key = defaultdict(list)
            for a in by_member[i]:
                key[tuple(V[a][1][p] for p in I)].append(a)
            for b in by_member[j]:
                for a in key.get(tuple(V[b][1][p] for p in I), ()):
                    adj[a].add(b); adj[b].add(a)
    return V, adj


def homology(fam, want_triangles_limit=None):
    """Return (n_vertices, n_edges, reduced b0, b1) over F_3."""
    V, adj = build(fam)
    n = len(V)
    # spanning forest
    parent = [-1] * n; seen = [False] * n; comps = 0
    tree = set()
    for s in range(n):
        if seen[s]:
            continue
        comps += 1; seen[s] = True; stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if not seen[y]:
                    seen[y] = True; tree.add((min(x, y), max(x, y))); stack.append(y)
    edges = [(a, b) for a in range(n) for b in adj[a] if a < b]
    eid = {}
    for e in edges:
        if e not in tree:
            eid[e] = len(eid)
    zdim = len(eid)  # dim Z_1
    piv = {}  # pivot (max index) -> reduced column dict
    rank = 0
    for a in range(n):
        if rank == zdim:
            break
        for b in adj[a]:
            if b <= a:
                continue
            common = [c for c in adj[a] & adj[b] if c > b]
            for c in common:
                # boundary of [a,b,c] = [b,c] - [a,c] + [a,b]
                col = {}
                for (e, s) in (((b, c), 1), ((a, c), 2), ((a, b), 1)):
                    k = eid.get(e)
                    if k is not None:
                        col[k] = (col.get(k, 0) + s) % 3
                col = {k: v for k, v in col.items() if v}
                while col:
                    p = max(col)
                    if p not in piv:
                        inv = col[p]  # 1 or 2, self-inverse mod 3
                        piv[p] = {k: (v * inv) % 3 for k, v in col.items()}
                        rank += 1
                        break
                    f = col[p]; P = piv[p]
                    for k, v in P.items():
                        nv = (col.get(k, 0) - f * v) % 3
                        if nv:
                            col[k] = nv
                        else:
                            col.pop(k, None)
                if rank == zdim:
                    break
            if rank == zdim:
                break
    return n, len(edges), comps - 1, zdim - rank


def tau(fam):
    pts = sorted(set().union(*fam))
    for t in range(len(pts) + 1):
        for T in itertools.combinations(pts, t):
            S = set(T)
            if all(B & S for B in fam):
                return t


def good_triple(fam):
    for a, b, c in itertools.combinations_with_replacement(range(len(fam)), 3):
        if not (fam[a] & fam[b] & fam[c]):
            return True
    return False


def report(name, fam):
    fam = [frozenset(B) for B in fam]
    k = max(len(B) for B in fam)
    n, e, rb0, b1 = homology(fam)
    print(f"{name:28s} k={k} m={len(fam):3d} tau={tau(fam)} (k+1)/2={(k+1)/2:.1f} good_triple={good_triple(fam)}"
          f" |V|={n} |E|={e}  rb0={rb0} b1={b1}  criterion_fires={rb0 == 0 and b1 == 0}", flush=True)
    return rb0, b1


if __name__ == "__main__":
    C = itertools.combinations
    tests = []
    for nn in (2, 3, 4):
        tests.append((f"K^(1)_{nn}", [{i} for i in range(nn)]))
    tests += [
        ("star K_1,3", [{0, 1}, {0, 2}, {0, 3}]),
        ("2 disjoint edges", [{0, 1}, {2, 3}]),
        ("triangle K_3", [{0, 1}, {1, 2}, {0, 2}]),
        ("3 disjoint edges", [{0, 1}, {2, 3}, {4, 5}]),
        ("K_4", [set(e) for e in C(range(4), 2)]),
        ("K_5", [set(e) for e in C(range(5), 2)]),
        ("K^(3)_4 (no triple)", [set(e) for e in C(range(4), 3)]),
        ("K^(3)_5", [set(e) for e in C(range(5), 3)]),
        ("Fano lines", [{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]),
        ("K^(3)_6", [set(e) for e in C(range(6), 3)]),
    ]
    which = sys.argv[1:] or None
    for name, fam in tests:
        if which and name not in which:
            continue
        report(name, fam)
