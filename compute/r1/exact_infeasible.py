"""Exact (rational) verification of "contradiction wins".

A record  win = adaptive  with an EMPTY pattern pool claims that for the recorded first request D
NO response satisfies the rules (capacities, looseness, and the extremal-anchor rule
`poth:a,b,c`): the mere existence of a response contradicts the choice of the anchor.
Here this is re-proved with exact rational arithmetic and no MILP solver.  The response set is a
union of polytopes in the variables k_X..k_PG (k_N = 1 - sum >= 0): for every sealed cell c the
adversary picks one branch
     |K & A1| >= 1/2   or   |K & A2| >= 1/2          (new triple outside the class: no constraint;
                                                     closed, i.e. slightly generous to him)
  or an ordering v1 >= v2 >= v3 of (|c|, |K & A1|, |K & A2|) with a*v1 + b*v2 + c*v3 <= Phi(anchor).
Each combination of branches is an LP; all of them are shown infeasible by an exact two-phase
simplex (Bland's rule) over Fractions.

usage: py exact_infeasible.py out/grid_poth....jsonl a,b,c T [--dden N]
"""
import sys, json, itertools
from fractions import Fraction as Fr

CELL_MEM = [3, 5, 6, 1, 2, 4]
TRIPLE_EDGES = {0: (1, 2), 1: (1, 4), 2: (2, 4)}


def feasible(A, b):
    """is {x >= 0 : A x <= b} non-empty?  exact two-phase simplex, Bland's rule."""
    m, n = len(A), len(A[0])
    # rows: A x + s = b ; make rhs >= 0 ; add artificials where the slack has coefficient -1
    rows = []; art = []
    for i in range(m):
        r = list(A[i]) + [Fr(0)] * m; r[n + i] = Fr(1); rhs = b[i]
        if rhs < 0: r = [-v for v in r]; rhs = -rhs; art.append(i)
        rows.append((r, rhs))
    na = len(art); N = n + m + na
    T = []
    basis = []
    for i, (r, rhs) in enumerate(rows):
        row = r + [Fr(0)] * na
        if i in art:
            j = n + m + art.index(i); row[j] = Fr(1); basis.append(j)
        else:
            basis.append(n + i)
        T.append(row + [rhs])
    if na == 0: return True
    # phase-1 objective: minimize sum of artificials  ->  reduced costs
    cost = [Fr(0)] * (N + 1)
    for i in range(m):
        if basis[i] >= n + m:
            for j in range(N + 1): cost[j] -= T[i][j]
    while True:
        enter = next((j for j in range(n + m) if cost[j] < 0), None)      # Bland: smallest index
        if enter is None: break
        best = None
        for i in range(m):
            if T[i][enter] > 0:
                ratio = T[i][N] / T[i][enter]
                if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]):
                    best = (ratio, i)
        if best is None: break                       # unbounded cannot happen in phase 1
        i = best[1]; p = T[i][enter]
        T[i] = [v / p for v in T[i]]
        for k in range(m):
            if k != i and T[k][enter] != 0:
                f = T[k][enter]; T[k] = [a - f * c for a, c in zip(T[k], T[i])]
        f = cost[enter]; cost = [a - f * c for a, c in zip(cost, T[i])]
        basis[i] = enter
    return -cost[N] == 0          # optimal phase-1 value = sum of artificials


def trace(a):
    return [Fr(1) if CELL_MEM[i] & a else Fr(0) for i in range(6)]


def no_response(mass, d, t, pot):
    """True iff provably no admissible response exists.  Returns (bool, number of branch LPs)."""
    cap = [mass[c] - d[c] for c in range(6)]
    base_A = []; base_b = []
    for c in range(6):
        row = [Fr(0)] * 6; row[c] = Fr(1); base_A.append(row); base_b.append(cap[c])
    base_A.append([Fr(1)] * 6); base_b.append(Fr(1))
    sealed = [c for c in range(3) if d[c] == mass[c]]
    s1, s2, s3 = sorted(mass[:3], reverse=True)
    pot0 = pot[0] * s1 + pot[1] * s2 + pot[2] * s3
    branches = []
    for c in sealed:
        a1, a2 = TRIPLE_EDGES[c]; ta, tb = trace(a1), trace(a2)
        # looseness (always)
        base_A.append([u + v for u, v in zip(ta, tb)]); base_b.append(3 - 2 * t - mass[c])
        if mass[c] > Fr(1, 2): continue
        opts = [([[-v for v in ta]], [-Fr(1, 2)]), ([[-v for v in tb]], [-Fr(1, 2)])]
        items = [(None, mass[c]), (ta, Fr(0)), (tb, Fr(0))]       # (coefficient vector, constant)
        def lin(it):          # value = const + coef.k
            return ([Fr(0)] * 6 if it[0] is None else it[0]), it[1]
        for perm in itertools.permutations(range(3)):
            (c1, k1), (c2, k2), (c3, k3) = (lin(items[i]) for i in perm)
            A = []; b = []
            A.append([y - x for x, y in zip(c1, c2)]); b.append(k1 - k2)          # v2 - v1 <= 0
            A.append([y - x for x, y in zip(c2, c3)]); b.append(k2 - k3)          # v3 - v2 <= 0
            A.append([pot[0] * x + pot[1] * y + pot[2] * z for x, y, z in zip(c1, c2, c3)])
            b.append(pot0 - (pot[0] * k1 + pot[1] * k2 + pot[2] * k3))
            opts.append((A, b))
        branches.append(opts)
    n = 0
    for combo in itertools.product(*branches):
        A = [r[:] for r in base_A]; b = base_b[:]
        for (Ax, bx) in combo: A += Ax; b += bx
        n += 1
        if feasible(A, b): return False, n
    return True, n


if __name__ == "__main__":
    args = sys.argv[1:]; dden = None
    if "--dden" in args:
        k = args.index("--dden"); dden = int(args[k + 1]); del args[k:k + 2]
    fn, potstr, tstr = args[:3]
    pot = tuple(Fr(v) for v in potstr.split(","))
    t = Fr(tstr); pden = int(fn.replace("\\", "/").split("_")[-2])
    if dden is None: dden = 2 * pden if pden < 40 else pden
    ok = bad = lps = 0
    for line in open(fn):
        r = json.loads(line)
        if r.get("win") != "adaptive" or r["pool"]: continue
        i, j, l = r["p"]; x, y, z = Fr(i, pden), Fr(j, pden), Fr(l, pden)
        mass = [x, y, z, 1 - x - y, 1 - x - z, 1 - y - z]
        d = [Fr(round(v * dden * 1000), dden * 1000) for v in r["D"]]
        assert sum(d) == t, (r["p"], sum(d))
        res, n = no_response(mass, d, t, pot); lps += n
        if res: ok += 1
        else: bad += 1; print("  a response exists (exact):", r["p"], r["D"])
    print(f"{fn}: contradiction wins verified exactly: {ok}; failed: {bad}; branch LPs solved: {lps}")
