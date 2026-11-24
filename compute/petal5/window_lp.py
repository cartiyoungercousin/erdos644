"""PETAL §28.1: limit of the 4+3 window-and-seal method (PS/PS2 family) as an exact LP.

Model (mass units, k = 1).  R_X has mass n = 1 + t/2 - delta.  Windows W_a = S_a cap R_X, |W_a| <= t/2 - sig_a, where
sig_4 = s (request 4 also seals the common points of petals 1-3 outside R_X, mass s) and sig_a = 0 otherwise.  Atoms
mu_M (M = set of petals MISSING the atom, M nonempty; M = [4] allowed = point in no petal), sum mu_M = n,
|W_a| = sum_{M contains a} mu_M.  Triple cell T_a cap R_X = mu_{{a}}.
Leak structure (adversary): singles of petal a, mass sing_a; common points of petals 1-3 (type {1,2,3}), mass s;
sing_a = delta - s for a <= 3, sing_4 = delta.
Centres j = 1, 2, 3: forcing set G_j in R_X, |G_j| >= t/2, |G_j| >= z_j + sum_{a in A_j} mu_{{a}}, z_j = (j - 1) delta
(earlier centres' R_X-traces).  Petal a in A_j ("S-petal of request j"): its singles sealed once, in request j.  Other
petals' singles and the type-{1,2,3} points: sealed in two requests (any split); type-{1,2,3} points must include the
request of petal 4 if petal 4 is an S-petal.
cost_j = |G_j| + load_j;  value = min over assignments (each petal: D, S1, S2, S3) and LP variables of max_j cost_j.
She chooses W_1..W_3 before s is known; W_4 and the centre plan after.  Robust version: one set of mu_M for petals 1-3's
windows is shared over the scenarios s in S_GRID (mu restricted to petals 1-3 coordinates is shared via the window masses
w_{a,M'} ... simplified: we share the full projection onto petals 1-3, i.e. the masses nu_{M'} = sum over M with
M cap [3] = M' of mu_M).
"""
import itertools, sys
import numpy as np
import highspy

TYPES = [frozenset(M) for r in range(1, 5) for M in itertools.combinations(range(4), r)]
PAIRS = [frozenset(P) for P in itertools.combinations(range(3), 2)] + [frozenset(range(3))]


class LP:
    def __init__(s):
        s.h = highspy.Highs(); s.h.setOptionValue("output_flag", False); s.n = 0
    def var(s, lo=0.0, hi=highspy.kHighsInf):
        s.h.addVar(lo, hi); s.n += 1; return s.n - 1
    def row(s, coefs, lo, hi):
        idx = np.array(list(coefs.keys()), dtype=np.int32); val = np.array(list(coefs.values()), dtype=float)
        s.h.addRow(lo, hi, len(idx), idx, val)
    def solve(s, obj):
        s.h.changeColCost(obj, 1.0); s.h.run()
        st = s.h.modelStatusToString(s.h.getModelStatus())
        return st, s.h.getInfo().objective_function_value, s.h.getSolution().col_value


def build(t, d, assign_by_s, s_grid):
    """assign_by_s[s] = tuple of 4 entries in {'D', 0, 1, 2}; returns optimal max cost (robust over s_grid)."""
    m = LP(); L = m.var(-highspy.kHighsInf)
    INF = highspy.kHighsInf
    n = 1 + t / 2 - d
    # shared projection onto petals 1-3
    proj = {Mp: m.var() for Mp in [frozenset(M) for r in range(0, 4) for M in itertools.combinations(range(3), r)]}
    for a in range(3):
        m.row({proj[Mp]: 1.0 for Mp in proj if a in Mp}, -INF, t / 2)
    for s in s_grid:
        assign = assign_by_s[s]
        mu = {M: m.var() for M in TYPES}
        m.row({mu[M]: 1.0 for M in TYPES}, n, n)
        for Mp in proj:
            c = {mu[M]: 1.0 for M in TYPES if M & frozenset(range(3)) == Mp}
            c[proj[Mp]] = -1.0
            m.row(c, 0, 0)
        m.row({mu[M]: 1.0 for M in TYPES if 3 in M}, -INF, t / 2 - s)
        G = [m.var(t / 2) for _ in range(3)]
        for j in range(3):
            c = {mu[frozenset([a])]: 1.0 for a in range(4) if assign[a] == j}
            c[G[j]] = -1.0
            m.row(c, -INF, -j * d)
        # D-type masses: singles of D petals, and s-points (type {1,2,3})
        items = [(("sing", a), (d - s) if a < 3 else d) for a in range(4) if assign[a] == 'D']
        items.append((("T4", None), s))
        load = [dict() for _ in range(3)]
        const = [0.0, 0.0, 0.0]
        for a in range(4):
            if assign[a] != 'D':
                const[assign[a]] += (d - s) if a < 3 else d
        for key, mass in items:
            if mass <= 0: continue
            pats = PAIRS
            if key[0] == "T4" and assign[3] != 'D':
                pats = [P for P in PAIRS if assign[3] in P]
            xs = {P: m.var() for P in pats}
            m.row({xs[P]: 1.0 for P in pats}, mass, mass)
            for P, v in xs.items():
                for j in P: load[j][v] = load[j].get(v, 0) + 1.0
        for j in range(3):
            c = dict(load[j]); c[G[j]] = c.get(G[j], 0) + 1.0; c[L] = -1.0
            m.row(c, -INF, -const[j])
    st, val, sol = m.solve(L)
    return val if st == "Optimal" else float("inf")


ASSIGN = list(itertools.product(['D', 0, 1, 2], repeat=4))


def value(t, d, s_grid=(0.0,)):
    """min over assignments chosen per scenario (she sees s before the centre phase) -- robust in the windows."""
    if len(s_grid) == 1:
        return min(build(t, d, {s_grid[0]: A}, s_grid) for A in ASSIGN)
    # per-scenario assignment: coordinate search (exact enumeration is 256^|grid|); start from best single assignments
    best = {s: min(ASSIGN, key=lambda A: build(t, d, {s: A}, (s,))) for s in s_grid}
    cur = build(t, d, best, s_grid)
    improved = True
    while improved:
        improved = False
        for s in s_grid:
            for A in ASSIGN:
                trial = dict(best); trial[s] = A
                v = build(t, d, trial, s_grid)
                if v < cur - 1e-9: cur, best, improved = v, trial, True
    return cur


def dmax(t, s_frac=(0.0,), lo=0.0, hi=None):
    hi = 1 - t if hi is None else hi
    for _ in range(30):
        mid = (lo + hi) / 2
        grid = tuple(f * mid for f in s_frac)
        if value(t, mid, grid) <= t + 1e-12: lo = mid
        else: hi = mid
    return lo


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "scan"
    if mode == "scan":
        print("t, 1-t, t/4, dmax (s = 0, all singles), dmax robust over s in {0, delta/2, delta}")
        for t in [0.75, 0.76, 0.77, 0.78, 0.79, 0.8]:
            d0 = dmax(t)
            d1 = dmax(t, (0.0, 0.5, 1.0))
            print("%.3f %.4f %.4f %.5f %.5f" % (t, 1 - t, t / 4, d0, d1), flush=True)


# ---------------- robust check over all leak structures (fixed assignment => convex in the leak masses) ----------------
BTYPES = [frozenset([a]) for a in range(4)] + [frozenset(J) for r in (2, 3) for J in itertools.combinations(range(4), r)]
BPATS = [frozenset(P) for r in (1, 2, 3) for P in itertools.combinations(range(3), r)]


def leak_vertices():
    A = np.array([[1.0 if a in J else 0.0 for J in BTYPES] for a in range(4)])
    seen, out = set(), []
    for r in range(0, 5):
        for supp in itertools.combinations(range(len(BTYPES)), r):
            for tight in itertools.combinations(range(4), r):
                if r == 0:
                    m = np.zeros(len(BTYPES))
                else:
                    M = A[np.ix_(tight, supp)]
                    if abs(np.linalg.det(M)) < 1e-9: continue
                    x = np.linalg.solve(M, np.ones(r))
                    if (x < -1e-9).any(): continue
                    m = np.zeros(len(BTYPES)); m[list(supp)] = x
                if (A @ m > 1 + 1e-9).any(): continue
                key = tuple(np.round(m, 9))
                if key not in seen: seen.add(key); out.append(m)
    return out


VERTS = None


def robust(t, d, assign, ret_plan=False):
    """least max request over all leak structures, for a fixed assignment (tuple: 'D' or request index per petal)."""
    global VERTS
    if VERTS is None: VERTS = leak_vertices()
    m = LP(); L = m.var(-highspy.kHighsInf); INF = highspy.kHighsInf
    n = 1 + t / 2 - d
    proj = {Mp: m.var() for Mp in [frozenset(M) for r in range(0, 4) for M in itertools.combinations(range(3), r)]}
    for a in range(3):
        m.row({proj[Mp]: 1.0 for Mp in proj if a in Mp}, -INF, t / 2)
    for vert in VERTS:
        mass = {J: d * x for J, x in zip(BTYPES, vert)}
        s = mass[frozenset(range(3))]
        mu = {M: m.var() for M in TYPES}
        m.row({mu[M]: 1.0 for M in TYPES}, n, n)
        for Mp in proj:
            c = {mu[M]: 1.0 for M in TYPES if M & frozenset(range(3)) == Mp}; c[proj[Mp]] = -1.0
            m.row(c, 0, 0)
        m.row({mu[M]: 1.0 for M in TYPES if 3 in M}, -INF, t / 2 - s)
        G = [m.var(t / 2) for _ in range(3)]
        for j in range(3):
            c = {mu[frozenset([a])]: 1.0 for a in range(4) if assign[a] == j}; c[G[j]] = -1.0
            m.row(c, -INF, -j * d)
        load = [dict() for _ in range(3)]
        for J, ms in mass.items():
            if ms <= 1e-12: continue
            pats = []
            for P in BPATS:
                ok = len(P) >= 2
                if len(J) == 1:
                    a = next(iter(J))
                    if assign[a] != 'D' and assign[a] in P: ok = True
                if len(J) == 3:
                    a = next(iter(frozenset(range(4)) - J))
                    if assign[a] != 'D' and assign[a] not in P: ok = False
                if ok: pats.append(P)
            xs = {P: m.var() for P in pats}
            m.row({xs[P]: 1.0 for P in pats}, ms, ms)
            for P, v in xs.items():
                for j in P: load[j][v] = load[j].get(v, 0) + 1.0
        for j in range(3):
            c = dict(load[j]); c[G[j]] = c.get(G[j], 0) + 1.0; c[L] = -1.0
            m.row(c, -INF, 0)
    st, val, sol = m.solve(L)
    if ret_plan:
        return val, {Mp: sol[v] for Mp, v in proj.items()}
    return val if st == "Optimal" else float("inf")


def robust_dmax(t, assigns):
    best = (0, None)
    for A in assigns:
        lo, hi = 0.0, 1 - t
        if robust(t, lo, A) > t + 1e-12: continue
        for _ in range(25):
            mid = (lo + hi) / 2
            if robust(t, mid, A) <= t + 1e-12: lo = mid
            else: hi = mid
        if lo > best[0]: best = (lo, A)
    return best


def scan2(ts):
    print("t | 1-t | t/4 | upper: dmax vs all-singles adversary (best assignment) | lower: dmax robust over all 94 leak vertices, that assignment")
    for t in ts:
        lo, hi = 0.0, 1 - t
        bestA = None
        for _ in range(22):
            mid = (lo + hi) / 2
            vals = [(build(t, mid, {0.0: A}, (0.0,)), A) for A in ASSIGN]
            v, A = min(vals, key=lambda z: z[0])
            if v <= t + 1e-12: lo, bestA = mid, A
            else: hi = mid
        up = lo
        # robust for all assignments achieving the optimum at 'up' (try the best few)
        vals = sorted(((build(t, up, {0.0: A}, (0.0,)), i) for i, A in enumerate(ASSIGN)))[:12]
        cands = [ASSIGN[i] for v, i in vals if v <= t + 1e-9]
        rd, rA = robust_dmax(t, cands)
        print("%.3f | %.4f | %.4f | %.5f %s | %.5f %s" % (t, 1 - t, t / 4, up, bestA, rd, rA), flush=True)


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "scan2":
    scan2([0.75, 0.76, 0.77, 0.775, 0.78, 0.785, 0.79, 0.8])
