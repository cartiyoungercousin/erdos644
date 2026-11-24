"""Independent re-derivation of the PS2 'B-load' step (PETAL 27.2).
Types J subset {1,2,3,4}, nonempty proper (14).  Leak polytope  Pol = { m >= 0 : sum_{J ni i} m_J <= 1 (i=1..4) }  (delta = 1).
Design for S-petal a in {1,2,3}: every B point of type J gets a pattern P subset {5,6,7}, P nonempty:
   J = {a}       : P = {5} or |P| >= 2
   J = {4}       : P = {6} or |P| >= 2
   J = [4]-{a}   : |P| >= 2, 5 in P
   J = [4]-{4}   : |P| >= 2, 6 in P
   otherwise     : |P| >= 2
f_a(m) = min over splits of max_j load_j.   Claim to test: max over Pol of min_a f_a = 2.
Steps: (1) vertex enumeration of Pol (exact Fractions), count; (2) f_a at every vertex by LP; (3) closed form
f_a = max(Hall-type bounds) vs LP; (4) bilevel check max_m min_a f_a (convex-concave ascent from many starts);
(5) integer version: exhaustive over integer structures for small d.
"""
import itertools, random, sys
from fractions import Fraction as Fr

TYPES = [frozenset(c) for r in (1, 2, 3) for c in itertools.combinations((1, 2, 3, 4), r)]
assert len(TYPES) == 14
PATS = [frozenset(c) for r in (1, 2, 3) for c in itertools.combinations((5, 6, 7), r)]


def allowed(J, a):
    ps = []
    for P in PATS:
        if len(P) == 1:
            if J == frozenset({a}) and P == frozenset({5}): ps.append(P)
            elif J == frozenset({4}) and P == frozenset({6}): ps.append(P)
            continue
        if J == frozenset({1, 2, 3, 4}) - {a} and 5 not in P: continue
        if J == frozenset({1, 2, 3}) and 6 not in P: continue
        ps.append(P)
    return ps


def f_lp(m, a, integer=False):
    import highspy
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    INF = highspy.kHighsInf
    cols = []  # (ti,P)
    h.addVar(0.0, INF)   # L = col 0
    for ti, J in enumerate(TYPES):
        if m[ti] == 0: continue
        for P in allowed(J, a):
            h.addVar(0.0, INF); cols.append((ti, P))
            if integer: h.changeColIntegrality(len(cols), highspy.HighsVarType.kInteger)
    h.changeColCost(0, 1.0)
    for ti, J in enumerate(TYPES):
        if m[ti] == 0: continue
        idx = [1 + c for c, (t2, P) in enumerate(cols) if t2 == ti]
        h.addRow(m[ti], m[ti], len(idx), idx, [1.0] * len(idx))
    for j in (5, 6, 7):
        idx = [1 + c for c, (t2, P) in enumerate(cols) if j in P]
        h.addRow(-INF, 0.0, len(idx) + 1, [0] + idx, [-1.0] + [1.0] * len(idx))
    h.run()
    return h.getInfo().objective_function_value


def solve_fr(A, b):
    n = len(A)
    M = [list(map(Fr, A[i])) + [Fr(b[i])] for i in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return None
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [v / pv for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [u - f * v for u, v in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]


def vertices():
    # constraints: m_J >= 0 (14) ; budget_i : sum m_J = 1 (4)   ->  vertices from choosing 14 active
    cons = []
    for ti in range(14):
        row = [0] * 14; row[ti] = 1; cons.append((row, 0))
    for i in (1, 2, 3, 4):
        cons.append(([1 if i in J else 0 for J in TYPES], 1))
    out = set()
    for act in itertools.combinations(range(18), 14):
        sol = solve_fr([cons[c][0] for c in act], [cons[c][1] for c in act])
        if sol is None: continue
        if any(v < 0 for v in sol): continue
        if any(sum(r * v for r, v in zip(cons[14 + i][0], sol)) > 1 for i in range(4)): continue
        out.add(tuple(sol))
    return sorted(out)


def closed_form(m, a):
    """derived: singles of a on 5, singles of 4 on 6, forced T_a (5 in pair), forced T_4 (6 in pair), rest pairs."""
    idx = {J: i for i, J in enumerate(TYPES)}
    sa = m[idx[frozenset({a})]]; s4 = m[idx[frozenset({4})]]
    Fa = m[idx[frozenset({1, 2, 3, 4}) - {a}]]; F4 = m[idx[frozenset({1, 2, 3})]]
    Q = sum(m) - sa - s4
    return max((sa + s4 + 2 * Q) / 3, sa + Fa, s4 + F4, (sa + s4 + Fa + F4) / 2)


if __name__ == '__main__':
    V = vertices()
    print('vertices of the leak polytope (delta=1):', len(V), '(incl. zero vector: %s)' % (tuple([0] * 14) in V))
    nz = [v for v in V if any(v)]
    print('nonzero vertices:', len(nz))
    worst = {a: Fr(0) for a in (1, 2, 3)}; worstmin = 0; arg = None; cfmis = 0
    for v in nz:
        fv = [f_lp([float(x) for x in v], a) for a in (1, 2, 3)]
        for a, f in zip((1, 2, 3), fv):
            worst[a] = max(worst[a], f)
            c = closed_form([float(x) for x in v], a)
            if abs(c - f) > 1e-7: cfmis += 1
        if min(fv) > worstmin + 1e-9: worstmin = min(fv); arg = v
    print('max over vertices of f_a for each a:', {a: float(w) for a, w in worst.items()})
    print('max over vertices of min_a f_a :', worstmin, arg)
    print('closed form disagrees with LP at', cfmis, 'vertex/a pairs')
    # random interior points
    rng = random.Random(1); mxr = 0; mis = 0
    for _ in range(3000):
        w = [rng.random() ** rng.choice([1, 3]) for _ in V]; s = sum(w)
        m = [sum(w[q] * float(V[q][ti]) for q in range(len(V))) / s for ti in range(14)]
        for a in (1, 2, 3):
            f = f_lp(m, a); mxr = max(mxr, f)
            if abs(closed_form(m, a) - f) > 1e-7: mis += 1
    print('random convex combinations: max f_a =', mxr, 'closed-form mismatches', mis)
    # integer version: exhaustive over integer structures with petal budget d (closed-form integer: brute force splits)
    for d in (1, 2, 3):
        cnt = 0; worstint = 0; arg = None
        def rec(ti, rem, m):
            global cnt, worstint, arg
            if ti == 14:
                cnt += 1
                if cnt % 1 == 0:
                    pass
                fa = [f_lp(m, a, True) for a in (1, 2, 3)]
                val = min(fa)
                if val > worstint: worstint = val; arg = list(m)
                return
            J = TYPES[ti]
            mx = min(rem[i - 1] for i in J)
            for q in range(mx + 1):
                r2 = list(rem)
                for i in J: r2[i - 1] -= q
                rec(ti + 1, r2, m + [q])
        if d <= 2:
            rec(0, [d] * 4, [])
            print('integer d=%d: structures %d, max over structures of min_a (integer-optimal max load) = %s (2d = %d) arg %s' % (d, cnt, worstint, 2 * d, arg))
