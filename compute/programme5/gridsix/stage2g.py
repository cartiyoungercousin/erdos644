"""Exact depth-2 drop-frame test for one fixed (K, R1, M1) and one second request R2.  [computed exact; SCIP]
Cells after M1 are (base cell, inM1); M1's own outside points form cell 'O1' (in M1 only, in no alive pair).
His M2: amounts per refined cell (avoiding R2) + fresh outside, mass 14, S*-legal against E, F, G, K and M1.
Her finishes after M2 (static, relative full-support plans, linear in M2):
  * E-frame {E,F,G,K,M1,M2} + 1 request;
  * the five-member frames {three of E,F,G,K} + M1 + M2 and {E,F,G,K,M2} + 2 requests.
INFEASIBLE = every legal M2 is closed: (K, R1, M1, R2) closes at depth 2."""
import itertools, time
from ortools.linear_solver import pywraplp
from cover import min_t
import cover as _cv
from stage1g import MEMB as BMEMB, SPEC, ZEPS

TINY = 1e-6
FR2 = {'EFGK12': ('EFGK12', 1), 'FGK12': ('FGK12', 2), 'EGK12': ('EGK12', 2), 'EFK12': ('EFK12', 2),
       'EFG12': ('EFG12', 2), 'EFGK2': ('EFGK2', 2)}


def inm(atom, mem):
    c, b1, b2 = atom
    if mem == '1': return b1 == 1
    if mem == '2': return b2 == 1
    if c == 'O1': return False
    return mem in BMEMB[c]


def alive(atl, frame):
    return [(p, q) for p, q in itertools.combinations_with_replacement(atl, 2)
            if all(inm(p, m) or inm(q, m) for m in frame)]


class Stage2:
    def __init__(s, S, m1, o1, r2, t):
        """S: base sizes (stage1g cells), m1: M1 amounts per base cell, o1: M1 outside mass, r2: {(cell,b1): amt}
        (cell 'O1' with b1 = 1 for M1's outside points)."""
        s.t = t; s.r2 = r2; s.plans = []
        s.ref = {}
        for c in BMEMB:
            if c == 'Z': continue
            s.ref[(c, 1)] = m1.get(c, 0.0); s.ref[(c, 0)] = S[c] - m1.get(c, 0.0)
        s.ref[('O1', 1)] = o1
        s.keys = [k for k, v in s.ref.items() if v > 1e-9]
        s.possible = [k + (1,) for k in s.keys if s.ref[k] - r2.get(k, 0.0) > 1e-9] + [k + (0,) for k in s.keys]
        s.possible += [('Z', b1, b2) for b1 in (0, 1) for b2 in (0, 1)]

    def atoms(s, m2):
        at = {}
        for k in s.keys:
            at[k + (1,)] = m2.get(k, 0.0); at[k + (0,)] = s.ref[k] - m2.get(k, 0.0)
        for b1 in (0, 1):
            for b2 in (0, 1): at[('Z', b1, b2)] = ZEPS / 4
        return at

    def best(s, m2):
        at = s.atoms(m2); sz = {a: v for a, v in at.items() if v > 1e-9}; out = {}
        for nm, (fr, r) in FR2.items():
            tt, _ = min_t(sz, alive(list(sz), fr), r, tl=60); out[nm] = tt
        return out

    def plan_for(s, m2, nm):
        fr, r = FR2[nm]; at = s.atoms(m2)
        for mode in ('full', 'actual'):
            if mode == 'full': full = {a: max(at[a], TINY) for a in s.possible}; need = []
            else:
                full = {a: at[a] for a in s.possible if at[a] > 1e-9}; need = [a for a in s.possible if at[a] <= 1e-9]
            tt, pl = min_t(full, alive(list(full), fr), r, tl=60)
            if tt is None or tt > s.t + 1e-9: continue
            sup = set(_cv.SUPPORT); vec = {}
            for (a, v), n in pl.items():
                if (a, v) in sup: vec.setdefault(a, []).append([list(v), n / full[a]])
            for a in set(a for a, v in sup):
                if a not in vec: vec[a] = [[list(v), 0.0] for b, v in sup if b == a][:1]
            for a in list(vec):
                tot = sum(e[1] for e in vec[a])
                vec[a] = [[v, f / tot] for v, f in vec[a]] if tot > 0 else [[vec[a][0][0], 1.0]]
            szs = [sum(sum(f for v, f in lst if v[i]) * full[a] for a, lst in vec.items()) for i in range(r)]
            if max(szs) <= s.t + 1e-9: return (nm, vec, need)
        return None

    def adversary(s, eta=1e-5, tl=150):
        sv = pywraplp.Solver.CreateSolver('SCIP')
        m = {k: sv.NumVar(0, max(0.0, s.ref[k] - s.r2.get(k, 0.0)), '') for k in s.keys}
        o = sv.NumVar(0, 14, ''); sv.Add(sum(m.values()) + o == 14)
        def tr(P):
            if P == '1': return sum(v for k, v in m.items() if k[1] == 1)
            return sum(v for k, v in m.items() if k[0] != 'O1' and P in BMEMB[k[0]])
        for P in 'EFGK1':
            T_ = tr(P); ys = [sv.BoolVar('') for _ in SPEC]; sv.Add(sum(ys) == 1)
            sv.Add(T_ >= sum(lo * y for (lo, hi), y in zip(SPEC, ys)))
            sv.Add(T_ <= sum(hi * y for (lo, hi), y in zip(SPEC, ys)))
        mu = sv.NumVar(0, 3, '')
        def size(a):
            if a[0] == 'Z': return ZEPS / 4
            k = a[:2]
            return m[k] if a[2] == 1 else s.ref[k] - m[k]
        for nm, vec, need in s.plans:
            r = FR2[nm][1]; ys = []
            for a in need:
                y = sv.BoolVar(''); ys.append(y); sv.Add(size(a) >= 1e-6 * y)
            for i in range(r):
                L = sum(sum(f for v, f in lst if v[i]) * size(a) for a, lst in vec.items())
                y = sv.BoolVar(''); ys.append(y); sv.Add(L >= s.t + eta + mu - 40 * (1 - y))
            sv.Add(sum(ys) >= 1)
        sv.Maximize(mu); sv.SetTimeLimit(int(tl * 1000))
        st = sv.Solve()
        if st == pywraplp.Solver.INFEASIBLE: return 'INFEASIBLE', None
        if st not in (pywraplp.Solver.OPTIMAL, pywraplp.Solver.FEASIBLE): return 'TIMEOUT', None
        return 'OK', ({k: max(0.0, v.solution_value()) for k, v in m.items()}, max(0.0, o.solution_value()))

    def run(s, maxit=150, wall=600):
        t0 = time.time()
        for it in range(maxit):
            if time.time() - t0 > wall: return 'WALL', None
            st, sol = s.adversary()
            if st != 'OK': return st, it
            m2, o2 = sol
            bs = s.best(m2)
            closing = [nm for nm, v in bs.items() if v is not None and v <= s.t + 1e-9]
            if not closing: return 'ESCAPE', (m2, o2, bs)
            added = 0
            for nm in closing:
                p = s.plan_for(m2, nm)
                if p: s.plans.append(p); added += 1
            if not added: return 'STUCK', (m2, o2, bs)
        return 'MAXIT', None
