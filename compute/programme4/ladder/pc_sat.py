r"""Point-level SAT for "does a family F of c-subsets of [n] contain m members covering every pair of [n]?"
(Rung 0 inner check.  A good seven of k-sets on [n] = seven co-edges (c = n - k) covering all pairs.)
Variables y[x][i] = point x lies in block i (n*m variables).  Block i has exactly c points and must be a member of F:
for every c-set G NOT in F a clause "some point of G is missing from block i" (|G| = c = |block|, so this is exact).
Pairs: aux p[x,z,i] -> y[x][i], y[z][i]; clause OR_i p[x,z,i].  Implied: r_x >= ceil((n-1)/(c-1)).
Block symmetry broken by strict lex order of the columns (y[0][i], y[1][i], ...) decreasing in i.
Usage: py pc_sat.py famfile n m [solver]   (famfile: one c-set per line, points 0..n-1)
Prints SAT + the m blocks (re-checked by plain code) or UNSAT.
"""
import sys, itertools, time
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def build(fam, n, m, c, rmin=None, lex=True):
    pool = IDPool(); cl = []
    y = [[pool.id(("y", x, i)) for i in range(m)] for x in range(n)]
    famset = set(frozenset(f) for f in fam)
    for i in range(m):
        col = [y[x][i] for x in range(n)]
        cl += CardEnc.equals(lits=col, bound=c, vpool=pool, encoding=EncType.seqcounter).clauses
        for G in itertools.combinations(range(n), c):
            if frozenset(G) not in famset:
                cl.append([-y[x][i] for x in G])
    for x, z in itertools.combinations(range(n), 2):
        ps = []
        for i in range(m):
            p = pool.id(("p", x, z, i)); ps.append(p)
            cl.append([-p, y[x][i]]); cl.append([-p, y[z][i]])
        cl.append(ps)
    if rmin:
        for x in range(n):
            cl += CardEnc.atleast(lits=y[x], bound=rmin, vpool=pool, encoding=EncType.seqcounter).clauses
    if lex:  # column i >_lex column i+1 (strict; blocks are distinct in a minimum cover)
        for i in range(m - 1):
            a = [y[x][i] for x in range(n)]; b = [y[x][i + 1] for x in range(n)]
            # e_j: prefixes equal up to j-1.  e_0 = true.  For each j: e_j -> (a_j >= b_j); strictness: not all equal.
            e = [pool.id(("e", i, j)) for j in range(n + 1)]
            cl.append([e[0]])
            for j in range(n):
                cl.append([-e[j], a[j], -b[j]])          # e_j -> a_j >= b_j
                cl.append([-e[j], -a[j], -b[j], e[j + 1]])  # equal-1 continues
                cl.append([-e[j], a[j], b[j], e[j + 1]])    # equal-0 continues
            cl.append([-e[n]])                            # strict
    return pool, y, cl


def check_cover(blocks, n):
    cov = set()
    for B in blocks:
        for p in itertools.combinations(sorted(B), 2): cov.add(p)
    return len(cov) == n * (n - 1) // 2


def solve(fam, n, m, solver="cd15", rmin=None, verbose=True):
    c = len(fam[0]); t0 = time.time()
    if rmin is None: rmin = -(-(n - 1) // (c - 1))
    pool, y, cl = build(fam, n, m, c, rmin)
    if verbose: print(f"vars {pool.top} clauses {len(cl)} build {time.time()-t0:.1f}s", flush=True)
    with Solver(name=solver, bootstrap_with=cl) as s:
        ok = s.solve()
        if verbose: print(f"solve {time.time()-t0:.1f}s ->", "SAT" if ok else "UNSAT", flush=True)
        if not ok: return None
        mod = set(v for v in s.get_model() if v > 0)
        blocks = [tuple(x for x in range(n) if y[x][i] in mod) for i in range(m)]
        fs = set(frozenset(f) for f in fam)
        assert all(frozenset(B) in fs for B in blocks) and check_cover(blocks, n)
        return blocks


if __name__ == "__main__":
    fam = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
    n, m = int(sys.argv[2]), int(sys.argv[3]); solver = sys.argv[4] if len(sys.argv) > 4 else "cd15"
    print(f"family {len(fam)} sets of size {len(fam[0])} on n={n}, m={m}, solver {solver}")
    r = solve(fam, n, m, solver)
    print("blocks:", r)
