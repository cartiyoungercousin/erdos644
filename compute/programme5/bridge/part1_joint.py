r"""Part 1: joint MILP over the three adaptive requests after Theorem P's K (route A, class-A first request).
Units k/14.  Cells: live X=6 (E,F), Y=5 (E,G), A=al (G,K), B=14-al (F,K); dead Ep=3 (E), Fd=8-be (F), Gd=9-al (G);
outside unlimited.  Spectrum S* = [0,45/12] u [60/12,73/12] u [80/12,14] for every trace of an answer with every
earlier member (E,F,G,K and the earlier answers; answer-answer traces may be raised by shared outside points).
Game: R1 -> M1, R2 -> M2 (adaptive, any legal answers), R3 -> M3.  M3's forced drops are useless (he keeps 0+ of any
needed type), so she needs R3 to contain every type incident to an uncovered pair of X x A u Y x B.
Requester-FAVOURABLE relaxation: she also picks M1, M2 among the MIN-KILL legal answers (kill = live mass not in M).
Min-kill is enforced by lazily generated cuts (CEGAR): an oracle MILP computes his min-kill answer M' for her request;
the cut says: for every request R, the answer M'' = M' minus what R takes from it (cellwise min) is legal unless one
of its traces falls into a gap below its interval, so kill <= kill(M') + (live mass taken).  Cuts are valid.
Objective: minimise tau' = max |R_i|.  tau' >= 12 at convergence  =>  no strategy closes at any t < 6/7 against an
adversary playing min-kill answers (certificate = this cut list).  tau' < 12 => she beats min-kill (then check).
usage: py -3.14 part1_joint.py alpha [grid h or 0 for continuous] [maxit] [delta]   (budget t = 12 - delta)"""
import sys, time, json, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
AL = float(sys.argv[1]); H = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0
MAXIT = int(sys.argv[3]) if len(sys.argv) > 3 else 400
TB = 12 - float(sys.argv[4]) if len(sys.argv) > 4 else 12.0   # request budget t = 12 - delta
BE = 14 - AL
S = {'X': 6, 'Y': 5, 'A': AL, 'B': BE, 'Ep': 3, 'Fd': 8 - BE, 'Gd': 9 - AL}
C = list(S); L = ['X', 'Y', 'A', 'B']
MEM = {'E': ['X', 'Y', 'Ep'], 'F': ['X', 'B', 'Fd'], 'G': ['Y', 'A', 'Gd'], 'K': ['A', 'B']}
INT = [(0, 45 / 12), (60 / 12, 73 / 12), (80 / 12, 14)]
BIG = 30.0; EPS = 1e-3; TOL = 1e-5

class Model:
    def __init__(s): s.lb, s.ub, s.it, s.R, s.lo, s.hi = [], [], [], [], [], []
    def v(s, lb=0.0, ub=np.inf, integ=0):
        s.lb.append(lb); s.ub.append(ub); s.it.append(integ); return {len(s.lb) - 1: 1.0}
    def b(s): return s.v(0, 1, 1)
    def row(s, e, lo=-np.inf, hi=np.inf):
        e = dict(e); c = e.pop('c', 0.0); s.R.append(e); s.lo.append(lo - c); s.hi.append(hi - c)
    def solve(s, obj, tl=600):
        n = len(s.lb); A = lil_matrix((len(s.R), n))
        for i, e in enumerate(s.R):
            for k, a in e.items(): A[i, k] += a
        c = np.zeros(n)
        for k, a in obj.items(): c[k] += a
        r = milp(c, constraints=LinearConstraint(A.tocsr(), s.lo, s.hi), integrality=np.array(s.it),
                 bounds=Bounds(s.lb, s.ub), options={'time_limit': tl, 'mip_rel_gap': 1e-7})
        return r
def ex(*terms):
    out = {}
    for coef, e in terms:
        for k, a in e.items(): out[k] = out.get(k, 0.0) + coef * a
    return out
def const(c): return {'c': c}
def val(x, e): return sum(a * (x[k] if k != 'c' else 1.0) for k, a in e.items())
def interval(m, T):
    ys = [m.b() for _ in INT]
    m.row(ex(*[(1, y) for y in ys]), 1, 1)
    m.row(ex((1, T), *[(-lo, y) for (lo, hi), y in zip(INT, ys)]), 0)
    m.row(ex((1, T), *[(-hi, y) for (lo, hi), y in zip(INT, ys)]), -np.inf, 0)
def lower_end(T):           # (lo of the interval containing T, hi of the previous interval)
    for j, (lo, hi) in enumerate(INT):
        if lo - 1e-7 <= T <= hi + 1e-7: return lo, (INT[j - 1][1] if j else None)
    raise ValueError(T)

# ---------------- oracles: his min-kill answer ----------------
def oracle1(r1):
    m = Model(); mm = {c: m.v(0, max(0.0, S[c] - r1[c])) for c in C}; o = m.v()
    m.row(ex(*[(1, mm[c]) for c in C], (1, o)), 14, 14)
    for P, cs in MEM.items(): interval(m, ex(*[(1, mm[c]) for c in cs]))
    res = m.solve(ex(*[(-1, mm[c]) for c in L]), 120)
    assert res.status == 0, res.message
    x = res.x; return {c: val(x, mm[c]) for c in C}, val(x, o)
def oracle2(r1, m1, o1, r2, r2O):
    m = Model(); sz = {}
    for c in C: sz[(c, 1)] = S[c] - m1[c]; sz[(c, 0)] = m1[c]
    mm = {k: m.v(0, max(0.0, sz[k] - r2[k])) for k in sz}
    w = m.v(0, max(0.0, o1 - r2O)); o2 = m.v()
    m.row(ex((1, o2), (-1, w)), 0)
    m.row(ex(*[(1, e) for e in mm.values()], (1, o2)), 14, 14)
    for P, cs in MEM.items(): interval(m, ex(*[(1, mm[(c, b)]) for c in cs for b in (0, 1)]))
    interval(m, ex(*[(1, mm[(c, 0)]) for c in C], (1, w)))
    res = m.solve(ex(*[(-1, mm[(c, b)]) for c in L for b in (0, 1)]), 120)
    assert res.status == 0, res.message
    x = res.x; return {k: val(x, e) for k, e in mm.items()}, val(x, w)

# ---------------- master ----------------
cuts1, cuts2 = [], []
def build():
    m = Model(); tau = m.v(0, TB)
    r1 = {c: m.v(0, S[c]) for c in C}; m1 = {c: m.v(0, S[c]) for c in C}; o1 = m.v(0, 14)
    if H > 0:
        for c in L:      # grid requests on live cells (multiples of H) or the full cell
            n = m.v(0, int(S[c] / H + 1e-9), 1); f = m.b()
            m.row(ex((1, r1[c]), (-H, n), (-S[c], f)), 0, 0); m.row(ex((1, n), (BIG / H, f)), -np.inf, BIG / H)
    for c in C: m.row(ex((1, r1[c]), (1, m1[c])), -np.inf, S[c])
    m.row(ex(*[(1, m1[c]) for c in C], (1, o1)), 14, 14)
    m.row(ex(*[(1, r1[c]) for c in C], (-1, tau)), -np.inf, 0)
    for P, cs in MEM.items(): interval(m, ex(*[(1, m1[c]) for c in cs]))
    sz = {}
    for c in C: sz[(c, 1)] = ex((1, const(S[c])), (-1, m1[c])); sz[(c, 0)] = m1[c]
    r2 = {k: m.v(0, 14) for k in sz}; m2 = {k: m.v(0, 14) for k in sz}; r2O = m.v(0, 14); w = m.v(0, 14); o2 = m.v(0, 14)
    for k in sz: m.row(ex((1, r2[k]), (1, m2[k]), (-1, sz[k])), -np.inf, 0)
    m.row(ex((1, r2O), (1, w), (-1, o1)), -np.inf, 0); m.row(ex((1, o2), (-1, w)), 0)
    m.row(ex(*[(1, e) for e in m2.values()], (1, o2)), 14, 14)
    m.row(ex(*[(1, e) for e in r2.values()], (1, r2O), (-1, tau)), -np.inf, 0)
    for P, cs in MEM.items(): interval(m, ex(*[(1, m2[(c, b)]) for c in cs for b in (0, 1)]))
    interval(m, ex(*[(1, m2[(c, 0)]) for c in C], (1, w)))
    # types (in S1, in S2) for live cells; round 3 split z (in R3)
    typ = {}
    for c in L:
        typ[(c, 1, 1)] = ex((1, sz[(c, 1)]), (-1, m2[(c, 1)])); typ[(c, 1, 0)] = m2[(c, 1)]
        typ[(c, 0, 1)] = ex((1, m1[c]), (-1, m2[(c, 0)])); typ[(c, 0, 0)] = m2[(c, 0)]
    mu, e3 = {}, {}
    for (c, a, b), te in typ.items():
        for z in (0, 1):
            mu[(c, a, b, z)] = m.v(0, 14); e3[(c, a, b, z)] = m.b()
            m.row(ex((1, mu[(c, a, b, z)]), (-14, e3[(c, a, b, z)])), -np.inf, 0)
        m.row(ex((1, mu[(c, a, b, 0)]), (1, mu[(c, a, b, 1)]), (-1, te)), 0, 0)
    pats = [(a, b, z) for a in (0, 1) for b in (0, 1) for z in (0, 1)]
    for U, W in (('X', 'A'), ('Y', 'B')):
        for P in pats:
            for Q in pats:
                if not any(p and q for p, q in zip(P, Q)): m.row(ex((1, e3[(U,) + P]), (1, e3[(W,) + Q])), -np.inf, 1)
    m.row(ex(*[(1, mu[k]) for k in mu if k[3] == 1], (-1, tau)), -np.inf, 0)
    kill1 = ex(*[(1, const(S[c])) for c in L], *[(-1, m1[c]) for c in L])
    kill2 = ex(*[(1, const(S[c])) for c in L], *[(-1, m2[(c, b)]) for c in L for b in (0, 1)])
    # ---- cuts
    def add_cut(kill, cells, cap, mp, killp, traces):
        # cells: key -> (expr of 'room' = capacity - request, ...); viol_k = max(0, mp_k - room_k)
        viol = {}
        for k, room in cap.items():
            if mp[k] <= 1e-9: continue
            vv = m.v(0, mp[k]); bb = m.b(); d = ex((1, const(mp[k])), (-1, room))
            m.row(ex((1, vv), (-1, d)), 0)
            m.row(ex((1, vv), (-1, d), (BIG, bb)), -np.inf, BIG)
            m.row(ex((1, vv), (-BIG, bb)), -np.inf, 0)
            viol[k] = vv
        us = []
        for keys, T0 in traces:
            lo, prevhi = lower_end(T0)
            if lo <= 1e-9: continue
            vs = [viol[k] for k in keys if k in viol]
            if not vs: continue
            u = m.b(); us.append(u)
            tr = ex((1, const(T0)), *[(-1, x) for x in vs])
            m.row(ex((1, tr), (BIG, u)), -np.inf, lo - EPS + BIG)          # u=1 -> trace'' <= lo - eps
            m.row(ex((1, tr), (-BIG, u)), prevhi + EPS - BIG)               # u=1 -> trace'' >= prevhi + eps
        m.row(ex((1, kill), *[(-1, viol[k]) for k in viol if k[0] in L or (isinstance(k, tuple) and k[0] in L)],
                 *[(-BIG, u) for u in us]), -np.inf, killp)
    for (mp, op) in cuts1:
        cap = {c: ex((1, const(S[c])), (-1, r1[c])) for c in C}
        traces = [(cs, sum(mp[c] for c in cs)) for cs in MEM.values()]
        add_cut(kill1, None, cap, mp, sum(S[c] - mp[c] for c in L), traces)
    def vmax(d, ub):           # exact max(0, d) with one binary
        vv = m.v(0, ub); bb = m.b()
        m.row(ex((1, vv), (-1, d)), 0); m.row(ex((1, vv), (-1, d), (BIG, bb)), -np.inf, BIG)
        m.row(ex((1, vv), (-BIG, bb)), -np.inf, 0); return vv
    GAPS = [(INT[j][1], INT[j + 1][0]) for j in range(len(INT) - 1)]
    for (lam, wp) in cuts2:      # proportional answer: keep lam_k of every subcell (minus what R2 takes)
        keep = {}; killb = []
        for k in sz:
            if lam[k] <= 1e-9: keep[k] = {}; killb.append((1, sz[k])) if k[0] in L else None; continue
            vv = vmax(ex((1, r2[k]), (-(1 - lam[k]), sz[k])), 14)
            keep[k] = ex((lam[k], sz[k]), (-1, vv))
            if k[0] in L: killb += [(1 - lam[k], sz[k]), (1, vv)]
        ww = ex((1, const(wp)), (-1, vmax(ex((1, const(wp)), (-1, o1), (1, r2O)), 14))) if wp > 1e-9 else {}
        trs = [ex(*[(1, keep[(c, b)]) for c in cs for b in (0, 1)]) for cs in MEM.values()]
        trs.append(ex(*[(1, keep[(c, 0)]) for c in C], (1, ww)))
        us = []
        for T in trs:
            for (g0, g1) in GAPS:
                u = m.b(); us.append(u)
                m.row(ex((1, T), (-BIG, u)), g0 + EPS - BIG); m.row(ex((1, T), (BIG, u)), -np.inf, g1 - EPS + BIG)
        u = m.b(); us.append(u)
        m.row(ex(*[(1, e) for e in keep.values()], (1, ww), (-BIG, u)), 14 + EPS - BIG)
        m.row(ex((1, kill2), *[(-a, e) for a, e in killb], *[(-BIG, u) for u in us]), -np.inf, 0)
    return m, dict(tau=tau, r1=r1, m1=m1, o1=o1, r2=r2, m2=m2, r2O=r2O, w=w, kill1=kill1, kill2=kill2, mu=mu)

def main():
    tag = 'a%g_h%g_t%g' % (AL, H, TB); log = open('logs/part1_joint_%s.log' % tag, 'w')
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); log.write(s + '\n'); log.flush()
    P('alpha=%g beta=%g cells %s; grid h=%g (0 = continuous requests)' % (AL, BE, S, H))
    t0 = time.time()
    for it in range(MAXIT):
        m, V = build(); res = m.solve(V['tau'], 900)
        if res.status not in (0, 1) or res.x is None: P('master status', res.status, res.message, '=> INFEASIBLE: no closure vs min-kill answers at t=%g' % TB); break
        x = res.x; g = lambda e: val(x, e)
        tau = g(V['tau']); r1 = {c: g(V['r1'][c]) for c in C}; m1 = {c: g(V['m1'][c]) for c in C}; o1 = g(V['o1'])
        r2 = {k: g(e) for k, e in V['r2'].items()}; r2O = g(V['r2O'])
        k1 = g(V['kill1']); k2 = g(V['kill2'])
        mp1, op1 = oracle1(r1); K1 = sum(S[c] - mp1[c] for c in L)
        new = False
        if k1 > K1 + TOL: cuts1.append((mp1, op1)); new = True
        mp2, wp2 = oracle2(r1, m1, o1, r2, r2O); K2 = sum(S[c] for c in L) - sum(mp2[(c, b)] for c in L for b in (0, 1))
        if k2 > K2 + TOL:
            szv = {}
            for c in C: szv[(c, 1)] = S[c] - m1[c]; szv[(c, 0)] = m1[c]
            for fill in (0.0, 1.0):
                lam = {k: (mp2[k] / szv[k] if szv[k] > 1e-9 else fill) for k in szv}
                cuts2.append((lam, wp2))
            new = True
        P('it %d  tau*=%.4f  kill1 %.3f vs min %.3f  kill2 %.3f vs min %.3f  cuts %d/%d  %.0fs' %
          (it, tau, k1, K1, k2, K2, len(cuts1), len(cuts2), time.time() - t0))
        if not new:
            P('CONVERGED: tau* = %.5f (12 = 6/7 boundary)' % tau)
            P('R1', {c: round(v, 4) for c, v in r1.items()}); P('M1', {c: round(v, 4) for c, v in m1.items()}, 'o1', round(o1, 4))
            P('R2', {('%s%d' % k): round(v, 4) for k, v in r2.items() if v > 1e-6}, 'r2O', round(r2O, 4))
            P('M2', {('%s%d' % k): round(g(e), 4) for k, e in V['m2'].items() if g(e) > 1e-6}, 'w', round(g(V['w']), 4))
            P('R3 types', {('%s%d%d' % k[:3]): round(g(e), 4) for k, e in V['mu'].items() if k[3] == 1 and g(e) > 1e-6})
            P('all types', {('%s%d%d%d' % k): round(g(e), 4) for k, e in V['mu'].items() if g(e) > 1e-6})
            break
    json.dump({'cuts1': [[mp, op] for mp, op in cuts1], 'cuts2': [[{'%s|%d' % k: v for k, v in mp.items()}, wp] for mp, wp in cuts2]},
              open('logs/part1_cuts_%s.json' % tag, 'w'))
main()
