# CORE Part IV: bad 7-tuples (co-types pairwise intersecting) by ground-set size N (k = 1).
#   py spectrum.py nonfano      -> min N for supports not inside the up-set of any Fano plane
#   py spectrum.py enum [Nmax]  -> minimal supports in increasing N (float MILP + exact LP per support)
import sys, itertools, pulp
from fractions import Fraction as Fr
pts = range(7)
subsets = [frozenset(s) for r in range(1, 8) for s in itertools.combinations(pts, r)]
base = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
planes = set()
for p in itertools.permutations(pts):
    planes.add(frozenset(frozenset(p[i] for i in L) for L in base))
planes = list(planes)
PERMS = list(itertools.permutations(pts))
def lineless(F, P): return not any(L <= F for L in P)

def model(nonfano=False, cuts=(), extra=None):
    pr = pulp.LpProblem("m", pulp.LpMinimize)
    m = {F: pr.add_variable("m%d" % i, 0, 7) for i, F in enumerate(subsets)}
    y = {F: pr.add_variable("y%d" % i, cat="Binary") for i, F in enumerate(subsets)}
    pr += pulp.lpSum(m.values())
    for F in subsets: pr += m[F] <= 7 * y[F]
    for F, G in itertools.combinations(subsets, 2):
        if not (F & G): pr += y[F] + y[G] <= 1
    for i in pts: pr += pulp.lpSum(m[F] for F in subsets if i not in F) == 1
    if nonfano:
        for P in planes: pr += pulp.lpSum(y[F] for F in subsets if lineless(F, P)) >= 1
    for C in cuts: pr += pulp.lpSum(y[F] for F in C) <= len(C) - 1
    if extra: extra(pr, m, y)
    st = pr.solve(pulp.HiGHS(msg=False))
    if not st.has_solution: return None, None
    return sum(v.value() for v in m.values()), {F: m[F].value() for F in subsets if m[F].value() > 1e-7}

def exact_min(support):
    """exact min of sum m over m >= 0 on the support with every edge of mass 1 (vertex enumeration)"""
    S = list(support); best = None
    rows = [[Fr(0 if i in F else 1) for F in S] for i in pts]
    def solve(cols):
        # Gaussian elimination on the 7 x len(cols) system; unique solution required
        A = [[rows[i][c] for c in cols] + [Fr(1)] for i in pts]; n = len(cols); r = 0; piv = []
        for c in range(n):
            p = next((i for i in range(r, 7) if A[i][c] != 0), None)
            if p is None: return None
            A[r], A[p] = A[p], A[r]; A[r] = [x / A[r][c] for x in A[r]]
            for i in range(7):
                if i != r and A[i][c] != 0: A[i] = [x - A[i][c] * z for x, z in zip(A[i], A[r])]
            piv.append(c); r += 1
        if any(A[i][n] != 0 for i in range(r, 7)): return None
        return [A[i][n] for i in range(n)]
    for size in range(1, min(7, len(S)) + 1):
        for cols in itertools.combinations(range(len(S)), size):
            x = solve(cols)
            if x is not None and min(x) > 0:
                v = sum(x)
                if best is None or v < best[0]: best = (v, {S[c]: xi for c, xi in zip(cols, x)})
    return best

def canon(support):
    best = None
    for p in PERMS:
        img = tuple(sorted(sum(1 << p[i] for i in F) for F in support))
        if best is None or img < best: best = img
    return best
def images(support):
    out = set()
    for p in PERMS: out.add(frozenset(frozenset(p[i] for i in F) for F in support))
    return out
def describe(sol):
    return "  ".join("%s:%s" % ("".join(str(i + 1) for i in sorted(F)), w) for F, w in sorted(sol.items(), key=lambda z: (len(z[0]), sorted(z[0]))))
def fano_planes_containing(support):
    return sum(1 for P in planes if all(not lineless(F, P) for F in support))

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "nonfano":
        v, sup = model(nonfano=True)
        ex = exact_min(sup.keys())
        print("min N over supports not Fano-supported: float %.6f, exact on that support %s" % (v, ex[0]))
        print("   ", describe(ex[1]))
    if mode == "enum":
        Nmax = float(sys.argv[2]) if len(sys.argv) > 2 else 2.25
        nonf = len(sys.argv) > 3
        cuts = []; seen = {}
        while True:
            v, sup = model(nonfano=nonf, cuts=cuts)
            if v is None or v > Nmax + 1e-9: print("stop at", v); break
            ex = exact_min(sup.keys())
            core = frozenset(ex[1].keys())
            cls = canon(core)
            tag = "new" if cls not in seen else "REPEAT"
            seen[cls] = ex[0]
            print("N = %-7s (float %.5f) sizes %s  Fano planes containing it: %d  %s\n     %s"
                  % (ex[0], v, sorted(len(F) for F in core), fano_planes_containing(core), tag, describe(ex[1])), flush=True)
            cuts.extend(images(core))
