"""Independent LPs for PETAL 28 (Theorem PS3 and the 'limit of window-and-seal' claim).  Own code.

Part A  (limit claim).  Model of the method, adversary = all singles (s = 0), mass units, k = 1:
   R_X (mass n = 1 + t/2 - delta) is cut into atoms mu_M (M nonempty subset of {1,2,3,4} = petals missing the atom);
   window |W_a| = sum_{M ni a} mu_M <= t/2;   triple cell  T_a n R_X = mu_{{a}}.
   each petal is D (its singles are requested in 2 of the 3 centre requests) or S_j (singles requested once, in
   centre request j in {5,6,7}, together with T_a n R_X).
   centre request j:  G_j >= t/2,  G_j >= (j-5) delta + sum_{a in S_j} mu_{{a}}   (traces of earlier centres + cells),
   load_j = delta*#S_j + (loads of D singles), a D petal splits 2 delta over requests with <= delta each.
   value = min over assignments (4^4 = 256) and atoms of  max_j (G_j + load_j).   delta*(t) = sup{delta : value <= t}.
Part B  (PS3 for general leaks).  Strategy fixed as in 28.2: petal 1 D; petal 2 S5; petal 3 S6; petal 4 S7;
   windows W_1, W_2 private (t/2), W_3 = P u Sigma0, W_4 = P' u (Sigma0 minus s), p = 1 - t - delta, s = leak mass common to
   petals 1-3 outside R_X (seen before request 4).  Exact adversary set Q (petals 1-3 leak exactly delta, since
   |R_X - W_i| = 1 - delta; petal 4: leak l4 in [delta - s, delta]); T_3 n R_X = p + (delta - l4), T_4 n R_X = p, T_2 n R_X = t/2.
   cost_j = G_j + load_j with G_5 = t/2, G_6 = max(t/2, delta + T_3), G_7 = max(t/2, 2 delta + p); B points of type
   [4]-{a} for a = 2,3,4 must be requested in 5,6,7 resp. with |P| >= 2; singles of petal 2/3/4 may have P = {5}/{6}/{7};
   all other B points |P| >= 2.  f(structure) = min over patterns of max cost_j is convex in the structure, so the vertices of Q suffice.
"""
import itertools, sys
from fractions import Fraction as Fr
import highspy

INF = highspy.kHighsInf


def lp(cols, rows, obj):
    """cols: list of (lo,hi); rows: list of (lo,hi,{col:coef}); obj {col:cost}; returns (status ok, value, x)"""
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    for lo, hi in cols: h.addVar(lo, hi)
    for c, v in obj.items(): h.changeColCost(c, v)
    for lo, hi, d in rows:
        idx = list(d); h.addRow(lo, hi, len(idx), idx, [d[i] for i in idx])
    h.run()
    st = h.getModelStatus()
    if st != highspy.HighsModelStatus.kOptimal: return None, None, None
    return True, h.getInfo().objective_function_value, list(h.getSolution().col_value)


# ---------------------------------------------------------------- Part A
SUBS = [frozenset(c) for r in (1, 2, 3, 4) for c in itertools.combinations((1, 2, 3, 4), r)]


def method_value(t, d, assign):
    """assign: tuple of 4 entries in {'D',5,6,7} for petals 1..4"""
    n = 1 + t / 2 - d
    cols = []; rows = []
    mu = {}
    for M in SUBS: mu[M] = len(cols); cols.append((0.0, INF))
    L = len(cols); cols.append((0.0, INF))
    g = {j: len(cols) + i for i, j in enumerate((5, 6, 7))}
    for j in (5, 6, 7): cols.append((t / 2, INF))
    Dp = [a for a in (1, 2, 3, 4) if assign[a - 1] == 'D']
    lD = {}
    for a in Dp:
        for j in (5, 6, 7): lD[a, j] = len(cols); cols.append((0.0, d))
    rows.append((n, n, {mu[M]: 1.0 for M in SUBS}))
    for a in (1, 2, 3, 4):
        rows.append((-INF, t / 2, {mu[M]: 1.0 for M in SUBS if a in M}))
    for a in Dp: rows.append((2 * d, 2 * d, {lD[a, j]: 1.0 for j in (5, 6, 7)}))
    for j in (5, 6, 7):
        Sj = [a for a in (1, 2, 3, 4) if assign[a - 1] == j]
        # g_j >= (j-5) d + sum mu_{a}
        row = {g[j]: 1.0}
        for a in Sj: row[mu[frozenset({a})]] = row.get(mu[frozenset({a})], 0) - 1.0
        rows.append(((j - 5) * d, INF, row))
        # L >= g_j + load_j
        row = {L: 1.0, g[j]: -1.0}
        for a in Dp: row[lD[a, j]] = -1.0
        rows.append((d * len(Sj), INF, row))
    ok, val, x = lp(cols, rows, {L: 1.0})
    return val


def best_method(t, d):
    best = (1e9, None)
    for assign in itertools.product(['D', 5, 6, 7], repeat=4):
        v = method_value(t, d, assign)
        if v is not None and v < best[0] - 1e-12: best = (v, assign)
    return best


def delta_star_method(t):
    lo, hi = 0.0, 1 - t
    if best_method(t, hi - 1e-9)[0] <= t + 1e-9: return hi
    for _ in range(30):
        mid = (lo + hi) / 2
        if best_method(t, mid)[0] <= t + 1e-9: lo = mid
        else: hi = mid
    return lo


# ---------------------------------------------------------------- Part B
TYPES = [frozenset(c) for r in (1, 2, 3) for c in itertools.combinations((1, 2, 3, 4), r)]
PATS = [frozenset(c) for r in (1, 2, 3) for c in itertools.combinations((5, 6, 7), r)]
SROLE = {2: 5, 3: 6, 4: 7}          # S-petal -> centre request


def allowed3(J):
    out = []
    forced = None
    if len(J) == 3:
        a = next(iter(frozenset({1, 2, 3, 4}) - J))
        forced = SROLE.get(a)
    for P in PATS:
        if len(P) == 1:
            if len(J) == 1:
                a = next(iter(J))
                if SROLE.get(a) == next(iter(P)): out.append(P)
            continue
        if forced is not None and forced not in P: continue
        out.append(P)
    return out


def cost_structure(t, d, m, l4):
    """m: dict type -> mass (list of 14), l4 = leak of petal 4.  returns min over patterns of max cost."""
    p = 1 - t - d
    s = m[TYPES.index(frozenset({1, 2, 3}))]
    T3 = p + (d - l4)
    G = {5: t / 2, 6: max(t / 2, d + T3), 7: max(t / 2, 2 * d + p)}
    cols = []; x = {}
    cols.append((0.0, INF))  # L
    for ti, J in enumerate(TYPES):
        if m[ti] <= 1e-12: continue
        for P in allowed3(J):
            x[ti, P] = len(cols); cols.append((0.0, INF))
    rows = []
    for ti, J in enumerate(TYPES):
        if m[ti] <= 1e-12: continue
        rows.append((m[ti], m[ti], {x[ti, P]: 1.0 for P in allowed3(J)}))
    for j in (5, 6, 7):
        row = {0: 1.0}
        for (ti, P), c in x.items():
            if j in P: row[c] = -1.0
        rows.append((G[j], INF, row))
    ok, val, _ = lp(cols, rows, {0: 1.0})
    return val


def solve_fr(A, b):
    n = len(A)
    M = [list(map(Fr, A[i])) + [Fr(b[i])] for i in range(n)]
    for c in range(n):
        pv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if pv is None: return None
        M[c], M[pv] = M[pv], M[c]
        q = M[c][c]; M[c] = [v / q for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [u - f * v for u, v in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]


def vertices_Q():
    """Q = {m >= 0 (14); sum_{J ni i} m_J = 1 (i=1,2,3); l4 := sum_{J ni 4} m_J <= 1; l4 + m_{123} >= 1}  (delta = 1)"""
    i123 = TYPES.index(frozenset({1, 2, 3}))
    ineq = []
    for ti in range(14):
        r = [0] * 14; r[ti] = 1; ineq.append((r, 0, 'ge'))
    ineq.append(([1 if 4 in J else 0 for J in TYPES], 1, 'le'))
    r = [1 if 4 in J else 0 for J in TYPES]; r[i123] += 1
    ineq.append((r, 1, 'ge'))
    eq = [([1 if i in J else 0 for J in TYPES], 1) for i in (1, 2, 3)]
    out = set()
    for act in itertools.combinations(range(len(ineq)), 14 - len(eq)):
        A = [e[0] for e in eq] + [ineq[c][0] for c in act]
        b = [e[1] for e in eq] + [ineq[c][1] for c in act]
        sol = solve_fr(A, b)
        if sol is None or any(v < 0 for v in sol): continue
        ok = True
        for (row, rhs, kind) in ineq:
            v = sum(a * x for a, x in zip(row, sol))
            if (kind == 'le' and v > rhs) or (kind == 'ge' and v < rhs): ok = False; break
        if ok: out.add(tuple(sol))
    return sorted(out)


def max_over_vertices(t, d, V):
    worst = 0; arg = None
    for v in V:
        m = [float(x) * d for x in v]
        l4 = sum(mm for mm, J in zip(m, TYPES) if 4 in J)
        c = cost_structure(t, d, m, l4)
        if c is None: return 1e9, v
        if c > worst: worst = c; arg = v
    return worst, arg


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'B'
    if mode == 'A':
        for t in (0.75, 0.76, 0.77, 0.775, 0.78, 0.79, 0.80):
            ds = delta_star_method(t)
            v, asg = best_method(t, min(ds + 0.002, 1 - t - 1e-9))
            print('t=%.3f  delta*(method, all singles, 256 assignments) = %.5f   t/2-1/6 = %.5f   1-t = %.3f   best assignment just above: %s' % (t, ds, t / 2 - 1 / 6, 1 - t, asg), flush=True)
        # value below delta*: assignment
        t = 0.75
        for d in (0.18, 0.2, 0.2083, 0.21, 0.23):
            v, a = best_method(t, d); print('t=0.75 delta=%.4f best value %.5f (T=%.2f, (1+6d)/3=%.5f)  assignment %s' % (d, v, t, (1 + 6 * d) / 3, a))
    else:
        V = vertices_Q()
        print('Q: vertices', len(V), flush=True)
        for t in (0.75, 0.76, 0.77, 0.775, 0.78):
            hi = min(1 - t - 1e-9, 0.3); lo = 0.0
            # max over vertices of f is nondecreasing in delta; find delta where it crosses t
            w, a = max_over_vertices(t, hi, V)
            if w <= t + 1e-9:
                print('t=%.3f  max over vertices <= t up to delta=1-t' % t); continue
            for _ in range(24):
                mid = (lo + hi) / 2
                w, a = max_over_vertices(t, mid, V)
                if w <= t + 1e-9: lo = mid
                else: hi = mid
            w, a = max_over_vertices(t, lo, V)
            print('t=%.3f  delta_PS3 (vertex LP) = %.5f   t/2-1/6 = %.5f   (1+6d)/3 at that delta = %.5f ; worst vertex %s' % (
                t, lo, t / 2 - 1 / 6, (1 + 6 * lo) / 3, [(sorted(J), str(x)) for J, x in zip(TYPES, a) if x]), flush=True)
