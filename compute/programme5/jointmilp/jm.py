r"""Joint 3-request game after Theorem P's K (route A, class-A first request), with spectrum forcing.  Library.
Units k/14: members have mass 14, request budget t = 12 - delta.  State after K (alpha = |A|, beta = 14 - alpha):
  live  X=6 (E,F)  Y=5 (E,G)  A=alpha (G,K)  B=beta (F,K);   alive pairs X x A  u  Y x B
  dead  Ep=3 (E)  Fd=alpha-6 (F)  Gd=9-alpha (G);  Z = 0+ ignored;  outside points unlimited (nu = inf)
Game: R1 -> M1, R2 -> M2 (adaptive), R3 -> M3.  Every answer avoids its request, has mass 14, and meets every earlier
member (E, F, G, K, earlier answers) in a size from S* = [0,45/12] u [5,73/12] u [80/12,14].  M3 needs only 0+ of a
type, so she closes iff after M2 the vertex set U of still-alive pairs has |U| <= t (then R3 = U).
oracle2 = his exact best M2 (max |U|); master2 = her R2 against a list of his answer patterns (pattern P answers R2
by keeping min(P_c, |c| - R2_c) on every refined cell c and filling with fresh outside points).
"""
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import coo_matrix

SPEC = [(0.0, 45 / 12), (5.0, 73 / 12), (80 / 12, 14.0)]
NOSPEC = [(0.0, 14.0)]
C7 = ['X', 'Y', 'A', 'B', 'Ep', 'Fd', 'Gd']
L = ['X', 'Y', 'A', 'B']
MEM = {'E': ['X', 'Y', 'Ep'], 'F': ['X', 'B', 'Fd'], 'G': ['Y', 'A', 'Gd'], 'K': ['A', 'B']}
BIC = [('X', 'A'), ('Y', 'B')]
BIG = 40.0


def sizes(al):
    return {'X': 6.0, 'Y': 5.0, 'A': al, 'B': 14.0 - al, 'Ep': 3.0, 'Fd': al - 6.0, 'Gd': 9.0 - al}


class Model:
    def __init__(s):
        s.lb, s.ub, s.it = [], [], []; s.ri, s.ci, s.va = [], [], []; s.lo, s.hi = [], []
    def v(s, lb=0.0, ub=np.inf, integ=0):
        s.lb.append(lb); s.ub.append(max(lb, ub)); s.it.append(integ); return {len(s.lb) - 1: 1.0}
    def b(s):
        return s.v(0, 1, 1)
    def row(s, e, lo=-np.inf, hi=np.inf):
        c = e.get('c', 0.0); r = len(s.lo)
        for k, a in e.items():
            if k != 'c' and a != 0: s.ri.append(r); s.ci.append(k); s.va.append(a)
        s.lo.append(lo - c); s.hi.append(hi - c)
    def solve(s, obj, tl=120, gap=1e-9):
        n = len(s.lb); A = coo_matrix((s.va, (s.ri, s.ci)), shape=(len(s.lo), n)).tocsr()
        c = np.zeros(n)
        for k, a in obj.items():
            if k != 'c': c[k] += a
        r = None
        for pre in (True, False):          # HiGHS occasionally reports a solve error with presolve; retry without
            r = milp(c, constraints=LinearConstraint(A, s.lo, s.hi), integrality=np.array(s.it),
                     bounds=Bounds(s.lb, s.ub), options={'time_limit': tl, 'mip_rel_gap': gap, 'presolve': pre})
            if r.status != 4: return r
        return s.solve_ortools(c, tl)

    def solve_ortools(s, c, tl):
        """fallback MILP solver (OR-Tools SCIP) for the rare HiGHS 'solve error'; returns a milp-like object"""
        from ortools.linear_solver import pywraplp
        from types import SimpleNamespace
        sv = pywraplp.Solver.CreateSolver('SCIP'); inf = sv.infinity()
        xs = [(sv.IntVar if it else sv.NumVar)(lb, ub if np.isfinite(ub) else inf, '') for lb, ub, it in zip(s.lb, s.ub, s.it)]
        rows = {}
        for r_, c_, v_ in zip(s.ri, s.ci, s.va): rows.setdefault(r_, []).append((c_, v_))
        for r_, (lo, hi) in enumerate(zip(s.lo, s.hi)):
            ct = sv.Constraint(lo if np.isfinite(lo) else -inf, hi if np.isfinite(hi) else inf)
            for c_, v_ in rows.get(r_, []): ct.SetCoefficient(xs[c_], ct.GetCoefficient(xs[c_]) + v_)
        ob = sv.Objective()
        for i, a in enumerate(c):
            if a: ob.SetCoefficient(xs[i], float(a))
        ob.SetMinimization(); sv.SetTimeLimit(int(tl * 1000))
        st = sv.Solve()
        if st in (pywraplp.Solver.OPTIMAL,):
            return SimpleNamespace(status=0, x=np.array([v.solution_value() for v in xs]), fun=ob.Value(), message='ortools')
        if st == pywraplp.Solver.INFEASIBLE: return SimpleNamespace(status=2, x=None, fun=None, message='ortools infeasible')
        return SimpleNamespace(status=1, x=None, fun=None, message='ortools other %d' % st)


def ex(*terms):
    out = {}
    for coef, e in terms:
        for k, a in e.items(): out[k] = out.get(k, 0.0) + coef * a
    return out
def K(c): return {'c': c}
def val(x, e): return sum(a * (x[k] if k != 'c' else 1.0) for k, a in e.items())


def interval(m, T, spec):
    """trace T lies in one closed interval of spec"""
    if len(spec) == 1: m.row(T, spec[0][0], spec[0][1]); return
    ys = [m.b() for _ in spec]
    m.row(ex(*[(1, y) for y in ys]), 1, 1)
    m.row(ex((1, T), *[(-lo, y) for (lo, hi), y in zip(spec, ys)]), 0)
    m.row(ex((1, T), *[(-hi, y) for (lo, hi), y in zip(spec, ys)]), -np.inf, 0)


def gaps(spec):
    return [(spec[j][1], spec[j + 1][0]) for j in range(len(spec) - 1)]


def in_spec(v, spec, tol=1e-7):
    return any(lo - tol <= v <= hi + tol for lo, hi in spec)


# ---------------------------------------------------------------- stage 1: his answer to R1
def oracle1(S, r1, spec, w=None, wpad=None, extra=None):
    """legal M1 minimising weighted live drops (w) + tiny pad cost; returns (m1 dict, o1)."""
    w = w or {c: 1.0 for c in L}; wpad = wpad or {}
    m = Model(); mm = {c: m.v(0, max(0.0, S[c] - r1.get(c, 0.0))) for c in C7}; o = m.v(0, 14)
    m.row(ex(*[(1, mm[c]) for c in C7], (1, o)), 14, 14)
    for P, cs in MEM.items(): interval(m, ex(*[(1, mm[c]) for c in cs]), spec)
    if extra: extra(m, mm, o)
    obj = ex(*[(-w[c], mm[c]) for c in L], *[(wpad.get(c, 0.0), mm[c]) for c in C7 if c not in L])
    res = m.solve(obj, 60)
    if res.status != 0: return None
    x = res.x; return {c: max(0.0, val(x, mm[c])) for c in C7}, max(0.0, val(x, o))


def refined(S, m1, o1):
    sz = {}
    for c in C7: sz[(c, 1)] = m1[c]; sz[(c, 0)] = S[c] - m1[c]
    return sz


def types_unc():
    """list of (U-type, W-type) refined-type pairs still alive after M1, M2: type = (cell, inM1, inM2)"""
    out = []
    for U, W in BIC:
        for a1 in (0, 1):
            for a2 in (0, 1):
                for c1 in (0, 1):
                    for c2 in (0, 1):
                        if (a1 or c1) and (a2 or c2): out.append(((U, a1, a2), (W, c1, c2)))
    return out
UNC = types_unc()
TYPES = [(c, b1, b2) for c in L for b1 in (0, 1) for b2 in (0, 1)]


# ---------------------------------------------------------------- stage 2: his exact best answer to R2
def oracle2(S, m1, o1, r2, r2O, t, spec, eps=1e-3, margin=0.0):
    """max |U| over legal M2 avoiding R2.  r2: dict (cell,b)->amount, r2O: amount of M1's outside points requested.
    margin > 0: traces must keep distance margin from every gap endpoint (robust answers).  Returns (U, M2, mO1)."""
    sz = refined(S, m1, o1)
    m = Model(); mm = {k: m.v(0, max(0.0, sz[k] - r2.get(k, 0.0))) for k in sz}
    w = m.v(0, max(0.0, o1 - r2O)); o0 = m.v(0, 14)
    m.row(ex(*[(1, e) for e in mm.values()], (1, w), (1, o0)), 14, 14)
    sp = spec if margin <= 0 else [(lo + (margin if lo > 0 else 0), hi - (margin if hi < 14 else 0)) for lo, hi in spec]
    trs = [ex(*[(1, mm[(c, b)]) for c in cs for b in (0, 1)]) for cs in MEM.values()]
    trs.append(ex(*[(1, mm[(c, 1)]) for c in C7], (1, w)))
    for T in trs: interval(m, T, sp)
    mass = {}
    for (c, b1, b2) in TYPES:
        mass[(c, b1, b2)] = mm[(c, b1)] if b2 else ex((1, K(sz[(c, b1)])), (-1, mm[(c, b1)]))
    e = {}; z = {}; u = {}
    for T in TYPES:
        e[T] = m.b(); m.row(ex((1, mass[T]), (-eps, e[T])), 0)
        u[T] = m.b(); z[T] = m.v(0, 14)
        m.row(ex((1, z[T]), (-1, mass[T])), -np.inf, 0); m.row(ex((1, z[T]), (-14, u[T])), -np.inf, 0)
    part = {T: [] for T in TYPES}
    for P, Q in UNC: part[P].append(Q); part[Q].append(P)
    for T in TYPES:
        m.row(ex((1, u[T]), *[(-1, e[Q]) for Q in part[T]]), -np.inf, 0)
    res = m.solve(ex(*[(-1, z[T]) for T in TYPES]), 150)
    if res.status != 0: return None
    x = res.x
    return -res.fun, {k: max(0.0, val(x, e_)) for k, e_ in mm.items()}, max(0.0, val(x, w))


def oracle2_robust(S, m1, o1, r2, r2O, t, spec, eps=1e-3, need=0.5):
    """legal M2 avoiding R2 with |U| >= t + need, maximising the least distance mu of any trace to a gap end
    (robust answer).  Returns (U, M2, mO1, mu) or None."""
    sz = refined(S, m1, o1)
    m = Model(); mm = {k: m.v(0, max(0.0, sz[k] - r2.get(k, 0.0))) for k in sz}
    w = m.v(0, max(0.0, o1 - r2O)); o0 = m.v(0, 14); mu = m.v(0, 3)
    m.row(ex(*[(1, e) for e in mm.values()], (1, w), (1, o0)), 14, 14)
    trs = [ex(*[(1, mm[(c, b)]) for c in cs for b in (0, 1)]) for cs in MEM.values()]
    trs.append(ex(*[(1, mm[(c, 1)]) for c in C7], (1, w)))
    for T in trs:
        ys = [m.b() for _ in spec]
        m.row(ex(*[(1, y) for y in ys]), 1, 1)
        for (lo, hi), y in zip(spec, ys):
            if lo > 0: m.row(ex((1, T), (-1, mu), (-20, y)), lo - 20)      # y=1 -> T >= lo + mu
            else: m.row(ex((1, T), (-20, y)), lo - 20)
            if hi < 14: m.row(ex((1, T), (1, mu), (20, y)), -np.inf, hi + 20)
            else: m.row(ex((1, T), (20, y)), -np.inf, hi + 20)
    mass = {}
    for (c, b1, b2) in TYPES:
        mass[(c, b1, b2)] = mm[(c, b1)] if b2 else ex((1, K(sz[(c, b1)])), (-1, mm[(c, b1)]))
    e = {}; z = {}; u = {}
    for T in TYPES:
        e[T] = m.b(); m.row(ex((1, mass[T]), (-eps, e[T])), 0)
        u[T] = m.b(); z[T] = m.v(0, 14)
        m.row(ex((1, z[T]), (-1, mass[T])), -np.inf, 0); m.row(ex((1, z[T]), (-14, u[T])), -np.inf, 0)
    part = {T: [] for T in TYPES}
    for P, Q in UNC: part[P].append(Q); part[Q].append(P)
    for T in TYPES: m.row(ex((1, u[T]), *[(-1, e[Q]) for Q in part[T]]), -np.inf, 0)
    m.row(ex(*[(1, z[T]) for T in TYPES]), t + need)
    res = m.solve(ex((-1, mu)), 60, gap=1e-4)
    if res.status != 0: return None
    x = res.x
    m2 = {k: max(0.0, val(x, e_)) for k, e_ in mm.items()}
    return U_of(S, m1, o1, m2), m2, max(0.0, val(x, w)), val(x, mu)


def U_of(S, m1, o1, m2):
    """exact |U| for explicit M1 (m1) and M2 (m2 on refined cells)"""
    sz = refined(S, m1, o1); mass = {}
    for (c, b1, b2) in TYPES:
        mass[(c, b1, b2)] = m2[(c, b1)] if b2 else sz[(c, b1)] - m2[(c, b1)]
    inU = set()
    for P, Q in UNC:
        if mass[P] > 1e-9 and mass[Q] > 1e-9: inU.add(P); inU.add(Q)
    return sum(mass[T] for T in inU)


# ---------------------------------------------------------------- stage 2: her R2 against patterns
def realize(rel, sz, o1, eps=1e-3):
    """relative pattern -> amounts on this state: code 0 | 'e' (eps) | 'f' (full cell) | float lam (fraction)"""
    def one(code, size):
        if code == 0 or size <= 1e-9: return 0.0
        if code == 'e': return min(eps, size)
        if code == 'f': return size
        return code * size
    return {k: one(rel[0].get('%s%d' % k, 0), sz[k]) for k in sz}, one(rel[1], o1)


def relativize(P, PO, sz, o1, eps=1e-3):
    def one(p, size):
        if p <= 1e-7: return 0
        if p <= 1.5 * eps: return 'e'
        if p >= size - 1e-7: return 'f'
        return round(p / size, 6)
    return ({'%s%d' % k: one(P.get(k, 0.0), sz[k]) for k in sz if one(P.get(k, 0.0), sz[k]) != 0}, one(PO, o1))


def master2(S, m1, o1, pats, t, spec, epsm=1e-6, tl=120, fix=None):
    """find R2 (continuous, |R2| <= t) such that every pattern answer (P minus R2, outside fill) is inapplicable
    (mass > 14), illegal (a trace in a gap) or leaves |U| <= t.  pats: list of (P amounts, PO).  None = infeasible."""
    sz = refined(S, m1, o1)
    m = Model(); r = {k: m.v(0, sz[k]) for k in sz}; rO = m.v(0, o1)
    m.row(ex(*[(1, e) for e in r.values()], (1, rO)), -np.inf, t)
    if fix: fix(m, r, rO)
    G = gaps(spec)
    def cap(p, size, rr):            # keep = min(p, size - rr) = p - max(0, p + rr - size)
        if p <= 1e-9: return {}
        if p >= size - 1e-12: return ex((1, K(size)), (-1, rr))
        v = m.v(0, p); bb = m.b(); d = ex((1, rr), (1, K(p - size))); M_ = p
        m.row(ex((1, v), (-1, d)), 0)
        m.row(ex((1, v), (-1, d), (size - p + 1e-6, bb)), -np.inf, size - p + 1e-6)   # bb=1 -> v <= d (v = d)
        m.row(ex((1, v), (-M_, bb)), -np.inf, 0)                                    # bb=0 -> v <= 0 (v = 0)
        return ex((1, K(p)), (-1, v))
    for P, PO in pats:
        keep = {k: cap(P.get(k, 0.0), sz[k], r[k]) for k in sz}
        kO = cap(PO, o1, rO)
        trs = [ex(*[(1, keep[(c, b)]) for c in cs for b in (0, 1)]) for cs in MEM.values()]
        trs.append(ex(*[(1, keep[(c, 1)]) for c in C7], (1, kO)))
        ys = []
        for T in trs:
            for (g0, g1) in G:
                y = m.b(); ys.append(y)
                m.row(ex((1, T), (-(g0 + 1), y)), g0 - epsm - (g0 + 1))
                m.row(ex((1, T), (15 - g1, y)), -np.inf, g1 + epsm + 15 - g1)
        tot = ex(*[(1, e) for e in keep.values()], (1, kO))
        if sum(P.values()) + PO > 14 + 1e-6:       # pattern may be inapplicable: mass of P minus R2 above 14
            y = m.b(); ys.append(y)
            m.row(ex((1, tot), (-30, y)), 14 + epsm - 30)          # y=1 -> mass >= 14 (inapplicable)
        mass = {}
        for (c, b1, b2) in TYPES:
            mass[(c, b1, b2)] = keep[(c, b1)] if b2 else ex((1, K(sz[(c, b1)])), (-1, keep[(c, b1)]))
        e = {}; z = {}; u = {}
        for T in TYPES:
            cmax = sz[(T[0], T[1])]
            if cmax <= 1e-9: e[T] = None; continue
            e[T] = m.b(); m.row(ex((1, mass[T]), (-cmax, e[T])), -np.inf, 0)
            u[T] = m.b(); z[T] = m.v(0, cmax)
            m.row(ex((1, z[T]), (-1, mass[T]), (-cmax, u[T])), -cmax)
        for Pp, Q in UNC:
            if e[Pp] is None or e[Q] is None: continue
            m.row(ex((1, u[Pp]), (-1, e[Q])), 0); m.row(ex((1, u[Q]), (-1, e[Pp])), 0)
        m.row(ex(*[(1, z[T]) for T in z], *[(-14, y) for y in ys]), -np.inf, t)
    res = m.solve({}, tl)
    if res.status == 2: return None             # infeasible
    if res.status != 0: return 'TIMEOUT'
    x = res.x
    return {k: max(0.0, val(x, e_)) for k, e_ in r.items()}, max(0.0, val(x, rO))


def stage2(S, m1, o1, t, spec, maxit=300, log=None, robust=True, pool=None, tl=120):
    """CEGAR: 'ADV' (her master infeasible: certificate = pattern list), 'REQ' (R2 closes vs his exact best), or '?'.
    pool: list of relative patterns used as initial cuts.  Returns (verdict, info, iterations, new relative patterns)"""
    sz = refined(S, m1, o1)
    pats = [realize(rp, sz, o1) for rp in (pool or [])]
    newrel = []
    for it in range(maxit):
        sol = master2(S, m1, o1, pats, t, spec, tl=tl)
        if sol is None: return 'ADV', pats, it, newrel
        if sol == 'TIMEOUT': return '?', pats, it, newrel
        r2, r2O = sol
        o = oracle2(S, m1, o1, r2, r2O, t, spec)
        if o is None: o = oracle2(S, m1, o1, r2, r2O, t, spec, eps=1e-4)
        if o is None: return 'ORACLE_FAIL', (r2, r2O, (None,)), it, newrel
        if o[0] <= t + 1e-6: return 'REQ', (r2, r2O, o), it, newrel
        cand = [(o[1], o[2])]
        if robust:
            for nd in (0.5, 3.0):
                o2 = oracle2_robust(S, m1, o1, r2, r2O, t, spec, need=nd)
                if o2 is not None and o2[0] > t + 1e-6: cand.append((o2[1], o2[2]))
        for P, PO in cand:
            pats.append((P, PO)); newrel.append(relativize(P, PO, sz, o1))
        if log: log('   it %d |U|=%.4f R2=%s' % (it, o[0], {('%s%d' % k): round(v, 3) for k, v in r2.items() if v > 1e-6}))
    return '?', pats, maxit, newrel
