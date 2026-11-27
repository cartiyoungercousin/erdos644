"""Independent checker for a kstage INFEASIBLE certificate (logs/kstage_<tag>.json + the box in logs/kstage_<tag>.out).
No code shared with kstage.py / stage1g.py / cover.py.
 (1) plan coverage: every alive atom pair of the plan's frame among its support atoms has intersecting used
     vectors, and every such atom is fully placed;
 (2) SCIP re-solve, written from scratch: is there K in the box and, per family, an S*-legal M1 avoiding R1_f(K)
     that escapes every plan of that family (some request > t, or some required-empty atom nonempty)?  Feasibility
     only, escape margin 0 (stricter than the CEGAR's 1e-5);
 (3) sampled check: on a grid of K in the box and random M1, some family has an applicable plan <= t.
usage: py verify_kstage.py tag [nK] [nM]"""
import sys, json, itertools, re
import numpy as np
from ortools.linear_solver import pywraplp

MEMB = {'X': 'EF', 'Y': 'EG', 'Z': 'FG', 'A': 'GK', 'Gd': 'G', 'B': 'FK', 'Fd': 'F', 'EpK': 'EK', 'Ep': 'E', 'OK': 'K'}
CELLS = [c for c in MEMB if c != 'Z']
FR = {'FGKM1': ('FGKM', 3), 'EGKM1': ('EGKM', 3), 'EFKM1': ('EFKM', 3), 'EFGM1': ('EFGM', 3), 'EFGKM1': ('EFGKM', 2)}
BANDS = [(0.0, 45 / 12), (5.0, 73 / 12), (80 / 12, 14.0)]
FULL = {'XAH': ['A', 'EpK', 'OK'], 'YBH': ['B', 'EpK', 'OK'], 'XA': ['A'], 'YB': ['B']}
ZH = 1e-3 / 2
DELTA = 0.002; T = 12 - DELTA


def sizes(a, kb, e, o):
    return {'X': 6.0, 'Y': 5.0, 'A': a, 'Gd': 9.0 - a, 'B': kb, 'Fd': 8.0 - kb, 'EpK': e, 'Ep': 3.0 - e, 'OK': o}


def r1(f, a, kb, e, o):
    return {'XAH': {'A': a, 'EpK': e, 'OK': o, 'X': T - a - e - o}, 'YBH': {'B': kb, 'EpK': e, 'OK': o, 'Y': T - kb - e - o},
            'XA': {'A': a, 'X': T - a}, 'YB': {'B': kb, 'Y': T - kb}}[f]


def inm(x, mem):
    return (x[1] == 1) if mem == 'M' else (mem in MEMB[x[0]])


def main(tag, nK=6, nM=20000):
    d = json.load(open('logs/kstage_%s.json' % tag))
    hdr = open('logs/kstage_%s.out' % tag).readline()
    box = tuple(float(v) for v in re.search(r'e lo,hi\) \(([^)]*)\)', hdr).group(1).split(','))
    print(tag, 'result', d['result'], 'box', box)
    plans = {}
    bad = 0
    for f, pl in d['plans'].items():
        poss = [(c, 1) for c in CELLS if c not in FULL[f]] + [(c, 0) for c in CELLS] + [('Z', 0), ('Z', 1)]
        L = []
        for nm, vec, need in pl:
            vec = {(k.split('|')[0], int(k.split('|')[1])): v for k, v in vec.items()}
            need = [(k.split('|')[0], int(k.split('|')[1])) for k in need]
            sup = [x for x in poss if x not in need]
            al = [(p, q) for p, q in itertools.combinations_with_replacement(sup, 2) if all(inm(p, m) or inm(q, m) for m in FR[nm][0])]
            for x in set(y for pq in al for y in pq):
                if x not in vec or abs(sum(fr for _, fr in vec[x]) - 1) > 1e-6: bad += 1
            for p, q in al:
                for v, fv in vec.get(p, []):
                    for w, gw in vec.get(q, []):
                        if fv > 1e-12 and gw > 1e-12 and not any(s and u for s, u in zip(v, w)): bad += 1
            r = FR[nm][1]
            L.append(({x: [sum(fr for v, fr in lst if v[i]) for i in range(r)] for x, lst in vec.items()}, need, r))
        plans[f] = L
    print('  plans', {f: len(p) for f, p in plans.items()}, 'coverage violations', bad)
    fams = list(plans)
    alo, ahi, elo, ehi = box

    # (2) independent SCIP re-solve
    sv = pywraplp.Solver.CreateSolver('SCIP')
    a = sv.NumVar(max(alo, 6 - DELTA), min(ahi, 7 + DELTA), ''); kb = sv.NumVar(7 - DELTA, 7 + DELTA, '')
    e = sv.NumVar(elo, ehi, ''); o = sv.NumVar(0, 14, ''); sv.Add(a + kb + e + o == 14)
    def inband(expr):
        ys = [sv.BoolVar('') for _ in BANDS]; sv.Add(sum(ys) == 1)
        sv.Add(expr >= sum(lo * y for (lo, hi), y in zip(BANDS, ys))); sv.Add(expr <= sum(hi * y for (lo, hi), y in zip(BANDS, ys)))
    for v in (a, kb, e): inband(v)
    S = sizes(a, kb, e, o)
    for f in fams:
        R = r1(f, a, kb, e, o)
        for c, v in R.items(): sv.Add(v >= 0); sv.Add(v <= S[c])
        m = {c: sv.NumVar(0, 14, '') for c in CELLS}; out = sv.NumVar(0, 14, '')
        sv.Add(sum(m.values()) + out == 14)
        for c in CELLS:
            sv.Add(m[c] <= S[c] - R.get(c, 0.0))
        for P in 'EFGK': inband(sum(m[c] for c in CELLS if P in MEMB[c]))
        def sz(x, m=m):
            if x[0] == 'Z': return ZH
            return m[x[0]] if x[1] == 1 else S[x[0]] - m[x[0]]
        for coef, need, r in plans[f]:
            ys = []
            for x in need:
                y = sv.BoolVar(''); ys.append(y); sv.Add(sz(x) >= 1e-7 * y)
            for i in range(r):
                y = sv.BoolVar(''); ys.append(y)
                sv.Add(sum(coef[x][i] * sz(x) for x in coef) >= T - 80 * (1 - y))
            sv.Add(sum(ys) >= 1)
    sv.SetTimeLimit(170000)
    st = sv.Solve()
    names = {pywraplp.Solver.INFEASIBLE: 'INFEASIBLE', pywraplp.Solver.OPTIMAL: 'FEASIBLE', pywraplp.Solver.FEASIBLE: 'FEASIBLE'}
    scip = names.get(st, 'NOT SOLVED (%d)' % st)
    print('  independent SCIP re-solve (margin 0):', scip, ('K=' + str([round(v.solution_value(), 4) for v in (a, kb, e, o)])) if scip == 'FEASIBLE' else '')

    # (3) sampled check
    rng = np.random.default_rng(0); worstK = -np.inf; nk = 0
    for av in np.linspace(max(alo, 6 - DELTA + 1e-6), min(ahi, 7 + DELTA), nK):
        if not any(lo - 1e-9 <= av <= hi + 1e-9 for lo, hi in BANDS): continue
        for kbv in (7 - DELTA + 1e-6, 7.0, 7 + DELTA):
            for ev in np.linspace(elo, ehi, nK):
                ov = 14 - av - kbv - ev
                if ov < -1e-12: continue
                nk += 1; Sz = sizes(av, kbv, ev, max(ov, 0.0)); bestf = np.inf
                for f in fams:
                    R = r1(f, av, kbv, ev, max(ov, 0.0))
                    if any(v < -1e-9 or v > Sz[c] + 1e-9 for c, v in R.items()): continue
                    cap = np.array([max(0.0, Sz[c] - R.get(c, 0.0)) if c not in FULL[f] else 0.0 for c in CELLS])
                    Mm = rng.random((nM, len(CELLS))) * cap
                    Mm = np.where(rng.random(Mm.shape) < .25, cap, Mm); Mm = np.where(rng.random(Mm.shape) < .25, 0, Mm)
                    ok = Mm.sum(1) <= 14 + 1e-9
                    for P in 'EFGK':
                        tr = sum(Mm[:, j] for j, c in enumerate(CELLS) if P in MEMB[c])
                        ok &= np.any([(tr >= lo - 1e-9) & (tr <= hi + 1e-9) for lo, hi in BANDS], axis=0)
                    Mm = Mm[ok]
                    if not len(Mm): bestf = min(bestf, -1); continue
                    s = {}
                    for j, c in enumerate(CELLS): s[(c, 1)] = Mm[:, j]; s[(c, 0)] = Sz[c] - Mm[:, j]
                    s[('Z', 0)] = s[('Z', 1)] = np.full(len(Mm), ZH)
                    best = np.full(len(Mm), np.inf)
                    for coef, need, r in plans[f]:
                        Lm = np.max([sum(coef[x][i] * s[x] for x in coef) for i in range(r)], axis=0)
                        app = np.ones(len(Mm), bool)
                        for x in need: app &= s[x] <= 1e-12
                        best = np.minimum(best, np.where(app, Lm, np.inf))
                    bestf = min(bestf, best.max() - T)
                worstK = max(worstK, bestf)
    print('  sampled: %d K points; worst over K of (best family: worst M1 best plan - t) = %.5f' % (nk, worstK))
    print('  VERDICT', 'OK' if bad == 0 and scip == 'INFEASIBLE' and worstK <= 1e-9 else 'CHECK')


if __name__ == '__main__':
    main(sys.argv[1], *(int(x) for x in sys.argv[2:]))
