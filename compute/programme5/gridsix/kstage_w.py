"""[kstage_w: variable triple cells X=q, Y=y, Z=z via env QYZ; Z is a real cell; forced ranges kb in (t-y, 14-t+y], a > t-q]
K-level exact CEGAR (static drop-one finishes after M1).  [computed exact; SCIP]
After her class-A first request R0 = X | Y | Z | F'_{1-delta} (extra all on F'), his K has
  A = K&G' (a), B = K&F' (kb), EpK = K&E' (e), OK = K-outside (o),  a + kb + e + o = 14,
with  7 - delta < kb <= 7 + delta  (R0 / E-frame, proved by hand),  a > 6 - delta (E-frame), a, kb, e in S*.
Her second request R1 comes from a few relative families (linear in K):
  XAH: A, E'&K, K-outside in full, X the rest;   YBH: B, E'&K, K-outside in full, Y the rest;
  XA : A in full, X the rest;                    YB : B in full, Y the rest.
His joint MILP: one K and, for every family f, an answer M1_f (avoids R1_f(K), mass 14, S*-legal vs E,F,G,K)
escaping every static plan collected for f.  Plans are relative full-support covers (sizes linear in K and M1).
INFEASIBLE = for every K in the range some family's R1 closes statically.
usage: py kstage.py tag [families csv] [delta]"""
import sys, json, time, itertools
from ortools.linear_solver import pywraplp
from cover import min_t
import cover as _cv
import os
from stage1g import MEMB, SPEC, FRAMES, alive
QY = [float(v) for v in os.environ.get('QYZ', '6,5,0.001').split(',')]   # triple cells X = q, Y = y, Z = z (k/14)
QQ, YY, ZZ = QY


def sizes_K(a, kb, e, o):
    return {'X': QQ, 'Y': YY, 'Z': ZZ, 'A': a, 'Gd': 14 - YY - ZZ - a, 'B': kb, 'Fd': 14 - QQ - ZZ - kb, 'EpK': e,
            'Ep': 14 - QQ - YY - e, 'OK': o}


def atoms(S, m1):
    out = {}
    for c in MEMB:
        out[(c, 1)] = m1.get(c, 0.0); out[(c, 0)] = S[c] - m1.get(c, 0.0)
    return out

CELLS = list(MEMB)   # Z is a real cell here (mass z)
TINY = 1e-6


def r1_of(fam, K, t):
    a, kb, e, o = K
    if fam == 'XAH': return {'A': a, 'EpK': e, 'OK': o, 'X': t - a - e - o}
    if fam == 'YBH': return {'B': kb, 'EpK': e, 'OK': o, 'Y': t - kb - e - o}
    if fam == 'XA': return {'A': a, 'X': t - a}
    if fam == 'YB': return {'B': kb, 'Y': t - kb}
    raise ValueError(fam)


FULL = {'XAH': ['A', 'EpK', 'OK'], 'YBH': ['B', 'EpK', 'OK'], 'XA': ['A'], 'YB': ['B']}


def possible(fam):
    return [(c, 1) for c in CELLS if c not in FULL[fam]] + [(c, 0) for c in CELLS]


def best_static(S, m1, t):
    at = atoms(S, m1); sz = {x: v for x, v in at.items() if v > 1e-9}; out = {}
    for nm, (fr, r) in FRAMES.items():
        tt, _ = min_t(sz, alive(list(sz), fr), r, tl=60); out[nm] = tt
    return out


def plan_for(S, m1, nm, fam, t):
    fr, r = FRAMES[nm]; at = atoms(S, m1)
    for mode in ('full', 'actual'):
        if mode == 'full':
            full = {x: max(at[x], TINY) for x in possible(fam)}; need = []
        else:
            full = {x: at[x] for x in possible(fam) if at[x] > 1e-9}; need = [x for x in possible(fam) if at[x] <= 1e-9]
        tt, pl = min_t(full, alive(list(full), fr), r, tl=60)
        if tt is None or tt > t + 1e-9: continue
        sup = set(_cv.SUPPORT); vec = {}
        for (x, v), n in pl.items():
            if (x, v) in sup: vec.setdefault(x, []).append([list(v), n / full[x]])
        for x in set(x for x, v in sup):
            if x not in vec: vec[x] = [[list(v), 0.0] for y, v in sup if y == x][:1]
        for x in list(vec):
            tot = sum(e[1] for e in vec[x])
            vec[x] = [[v, f / tot] for v, f in vec[x]] if tot > 0 else [[vec[x][0][0], 1.0]]
        szs = [sum(sum(f for v, f in lst if v[i]) * full[x] for x, lst in vec.items()) for i in range(r)]
        if max(szs) <= t + 1e-9: return (nm, vec, need)
    return None


def band(sv, T_):
    ys = [sv.BoolVar('') for _ in SPEC]; sv.Add(sum(ys) == 1)
    sv.Add(T_ >= sum(lo * y for (lo, hi), y in zip(SPEC, ys)))
    sv.Add(T_ <= sum(hi * y for (lo, hi), y in zip(SPEC, ys)))


def adversary(fams, plans, t, delta, eta=1e-5, tl=170, fixK=None, box=None):
    sv = pywraplp.Solver.CreateSolver('SCIP')
    alo, ahi, elo, ehi = box if box else (6 - delta + 1e-6, 7 + delta, 0.0, 3.0)
    a = sv.NumVar(max(alo, t - QQ + 1e-6), min(ahi, 14 - YY - ZZ), 'a'); kb = sv.NumVar(t - YY + 1e-6, 14 - t + YY, 'kb')
    e = sv.NumVar(elo, ehi, 'e'); o = sv.NumVar(0, 14, 'o'); sv.Add(a + kb + e + o == 14)
    if fixK:
        for v, val in zip((a, kb, e, o), fixK): sv.Add(v == val)
    band(sv, a); band(sv, kb); band(sv, e)
    S = {'X': QQ, 'Y': YY, 'Z': ZZ, 'A': a, 'Gd': 14 - YY - ZZ - a, 'B': kb, 'Fd': 14 - QQ - ZZ - kb, 'EpK': e, 'Ep': 14 - QQ - YY - e, 'OK': o}
    for v in S.values():
        if not isinstance(v, float): sv.Add(v >= 0)
    mu = sv.NumVar(0, 3, 'mu'); M = {}
    for f in fams:
        r1 = r1_of(f, (a, kb, e, o), t)
        for c, v in r1.items():
            if c not in FULL[f]: sv.Add(v >= 0); sv.Add(v <= S[c])
        m = {}
        for c in CELLS:
            m[c] = sv.NumVar(0, 14, '')
            if c in FULL[f]: sv.Add(m[c] == 0)
            else: sv.Add(m[c] <= S[c] - r1.get(c, 0.0))
        oo = sv.NumVar(0, 14, ''); sv.Add(sum(m.values()) + oo == 14)
        for P in 'EFGK': band(sv, sum(m[c] for c in CELLS if P in MEMB[c]))
        M[f] = (m, oo)
        def size(x, m=m):
            c, b = x
            return m[c] if b == 1 else S[c] - m[c]
        for nm, vec, need in plans[f]:
            r = FRAMES[nm][1]; ys = []
            for x in need:
                y = sv.BoolVar(''); ys.append(y); sv.Add(size(x) >= 1e-6 * y)
            for i in range(r):
                L = sum(sum(fr for v, fr in lst if v[i]) * size(x) for x, lst in vec.items())
                y = sv.BoolVar(''); ys.append(y); sv.Add(L >= t + eta + mu - 60 * (1 - y))
            sv.Add(sum(ys) >= 1)
    sv.Maximize(mu); sv.SetTimeLimit(int(tl * 1000))
    st = sv.Solve()
    if st == pywraplp.Solver.INFEASIBLE: return 'INFEASIBLE', None
    if st not in (pywraplp.Solver.OPTIMAL, pywraplp.Solver.FEASIBLE): return 'TIMEOUT', None
    K = tuple(max(0.0, v.solution_value()) for v in (a, kb, e, o))
    return 'OK', (K, {f: ({c: max(0.0, v.solution_value()) for c, v in m.items()}, max(0.0, oo.solution_value()))
                      for f, (m, oo) in M.items()}, mu.solution_value())


def run(tag, fams, delta=0.002, maxit=400, fixK=None, box=None):
    t = 12 - delta; plans = {f: [] for f in fams}; t0 = time.time()
    log = open('logs/kstagew_%s.out' % tag, 'w')
    def P(*x):
        s = ' '.join(map(str, x)); print(s, flush=True); log.write(s + '\n'); log.flush()
    P('QYZ', QY, 'families', fams, 't', t, 'fixK', fixK, 'box (a lo,hi, e lo,hi)', box)
    for it in range(maxit):
        st, sol = adversary(fams, plans, t, delta, fixK=fixK, box=box)
        if st != 'OK':
            P('it %d: adversary %s; plans %s (%.0fs)' % (it, st, {f: len(p) for f, p in plans.items()}, time.time() - t0))
            return st, plans, None
        K, Ms, mu = sol
        S = sizes_K(*K)
        escaped = {}; added = 0
        for f in fams:
            m1, o1 = Ms[f]; m1 = dict(m1)
            bs = best_static(S, m1, t)
            closing = [nm for nm, v in bs.items() if v is not None and v <= t + 1e-9]
            if not closing: escaped[f] = (m1, o1, bs); continue
            for nm in closing:
                p = plan_for(S, m1, nm, f, t)
                if p: plans[f].append(p); added += 1
        if it % 5 == 0 or len(escaped) == len(fams):
            P('it %d: K=(a %.4f, kb %.4f, e %.4f, o %.4f) mu %.4f escaped %s (%.0fs)' % ((it,) + K + (mu, list(escaped), time.time() - t0)))
        if len(escaped) == len(fams):
            P('K SURVIVES statically:', K)
            for f, (m1, o1, bs) in escaped.items():
                P('  ', f, 'R1', {c: round(v, 4) for c, v in r1_of(f, K, t).items()}, 'M1', {c: round(v, 4) for c, v in m1.items() if v > 1e-7},
                  'out %.4f' % o1, 'static', {k: round(v, 4) for k, v in bs.items()})
            return 'SURVIVES', plans, (K, escaped)
        if not added:
            P('stuck at', K); return 'STUCK', plans, (K, escaped)
    return 'MAXIT', plans, None


def dump(tag, res, plans, extra):
    json.dump({'result': res, 'extra': extra if extra is None else [extra[0], {f: list(v) for f, v in extra[1].items()}],
               'plans': {f: [[nm, {'|'.join(map(str, x)): v for x, v in vec.items()}, ['|'.join(map(str, x)) for x in need]]
                             for nm, vec, need in pl] for f, pl in plans.items()}}, open('logs/kstagew_%s.json' % tag, 'w'))


if __name__ == '__main__':
    tag = sys.argv[1]
    fams = sys.argv[2].split(',') if len(sys.argv) > 2 else ['XAH', 'YBH', 'XA', 'YB']
    delta = float(sys.argv[3]) if len(sys.argv) > 3 else 0.002
    box = tuple(float(x) for x in sys.argv[4].split(',')) if len(sys.argv) > 4 else None
    res, plans, extra = run(tag, fams, delta, box=box)
    print('RESULT', res, flush=True); dump(tag, res, plans, extra)
