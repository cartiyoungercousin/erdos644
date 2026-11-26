"""Generic exact stage-1 CEGAR (static finishes only) after a general K.  [computed exact; SCIP]
State after the critical triple E, F, G and K: base cells with membership in {E, F, G, K} and sizes (units k/14):
  X (E,F) 6, Y (E,G) 5, Z (F,G) 0+, A = G'&K, Gd = G'-K, B = F'&K, Fd = F'-K, EpK = E'&K, Ep = E'-K, OK = K-only
  (K's outside points).  Fresh outside points (in no base member) are unlimited.
Her R1 (amounts per base cell), his M1 (amounts per base cell + fresh outside), S*-legal vs E, F, G, K.
Her static finishes after M1: the four drop-one frames with 3 requests and {E,F,G,K,M1} with 2 requests; plans are
relative full-support covers, so a plan closes M1 iff its largest request (linear in M1) is <= t.
INFEASIBLE (SCIP) = every legal M1 is closed by a listed plan: R1 closes at depth 1 (static finish)."""
import sys, os, json, time, itertools
from ortools.linear_solver import pywraplp
from cover import min_t

SPEC = [(0.0, 45 / 12), (5.0, 73 / 12), (80 / 12, 14.0)]
MEMB = {'X': 'EF', 'Y': 'EG', 'Z': 'FG', 'A': 'GK', 'Gd': 'G', 'B': 'FK', 'Fd': 'F', 'EpK': 'EK', 'Ep': 'E', 'OK': 'K'}
CELLS = list(MEMB)
ZEPS = 1e-3
FRAMES = {'FGKM1': ('FGKM', 3), 'EGKM1': ('EGKM', 3), 'EFKM1': ('EFKM', 3), 'EFGM1': ('EFGM', 3), 'EFGKM1': ('EFGKM', 2)}
TINY = 1e-6
for _f in os.environ.get('FRAMES_OFF', '').split(','):
    FRAMES.pop(_f, None)


def sizes_K(ka, kb, ke, ko):
    return {'X': 6.0, 'Y': 5.0, 'Z': ZEPS, 'A': ka, 'Gd': 9.0 - ka, 'B': kb, 'Fd': 8.0 - kb, 'EpK': ke,
            'Ep': 3.0 - ke, 'OK': ko}


def inm(atom, mem):
    c, b = atom
    return (b == 1) if mem == 'M' else (mem in MEMB[c])


def atoms(S, m1):
    out = {}
    for c in CELLS:
        if c == 'Z': out[('Z', 1)] = ZEPS / 2; out[('Z', 0)] = ZEPS / 2; continue
        out[(c, 1)] = m1.get(c, 0.0); out[(c, 0)] = S[c] - m1.get(c, 0.0)
    return out


def alive(atl, frame):
    return [(p, q) for p, q in itertools.combinations_with_replacement(atl, 2)
            if all(inm(p, m) or inm(q, m) for m in frame)]


class Stage1:
    def __init__(s, S, r1, t, log=lambda *a: print(*a, flush=True)):
        s.S, s.r1, s.t, s.log = S, r1, t, log
        s.possible = [(c, 1) for c in CELLS if c != 'Z' and S[c] - r1.get(c, 0.0) > 1e-9] + \
                     [(c, 0) for c in CELLS if c != 'Z' and S[c] > 1e-9] + [('Z', 0), ('Z', 1)]
        s.plans = []

    def best_static(s, m1):
        at = atoms(s.S, m1); sz = {a: v for a, v in at.items() if v > 1e-9}; out = {}
        for nm, (fr, r) in FRAMES.items():
            tt, _ = min_t(sz, alive(list(sz), fr), r, tl=60); out[nm] = tt
        return out

    def plan_for(s, m1, nm):
        """full-support plan if it closes; else the actual-support plan, valid only while the possible atoms it
        leaves out stay empty (returned in the third slot)"""
        fr, r = FRAMES[nm]
        at = atoms(s.S, m1)
        full = {a: max(at[a], TINY) for a in s.possible}
        tt, pl = min_t(full, alive(list(full), fr), r, tl=60)
        need = []
        if tt is None or tt > s.t + 1e-9:
            full = {a: at[a] for a in s.possible if at[a] > 1e-9}
            need = [a for a in s.possible if at[a] <= 1e-9]
            tt, pl = min_t(full, alive(list(full), fr), r, tl=60)
            if tt is None or tt > s.t + 1e-9: return None
        import cover as _cv
        sup = set(_cv.SUPPORT); vec = {}
        for (a, v), n in pl.items():          # keep only vectors whose support binary is 1 (coverage is then exact)
            if (a, v) in sup: vec.setdefault(a, []).append([list(v), n / full[a]])
        for a in set(a for a, v in sup):
            if a not in vec: vec[a] = [[list(v), 0.0] for b, v in sup if b == a][:1]
        for a in list(vec):                  # renormalise to a partition of the atom
            tot = sum(e[1] for e in vec[a])
            vec[a] = [[v, f / tot] for v, f in vec[a]] if tot > 0 else [[vec[a][0][0], 1.0]]
        sz = {i: sum(sum(f for v, f in lst if v[i]) * full[a] for a, lst in vec.items()) for i in range(r)}
        if max(sz.values()) > s.t + 1e-9: return None
        return (nm, vec, need)

    def adversary(s, eta=1e-5, tl=150):
        sv = pywraplp.Solver.CreateSolver('SCIP')
        m = {c: sv.NumVar(0, max(0.0, s.S[c] - s.r1.get(c, 0.0)), c) for c in CELLS if c != 'Z'}
        o = sv.NumVar(0, 14, 'o'); sv.Add(sum(m.values()) + o == 14)
        for P in 'EFGK':
            T_ = sum(m[c] for c in m if P in MEMB[c]); ys = [sv.BoolVar('') for _ in SPEC]
            sv.Add(sum(ys) == 1)
            sv.Add(T_ >= sum(lo * y for (lo, hi), y in zip(SPEC, ys)))
            sv.Add(T_ <= sum(hi * y for (lo, hi), y in zip(SPEC, ys)))
        mu = sv.NumVar(0, 3, 'mu')
        def size(a):
            c, b = a
            if c == 'Z': return ZEPS / 2
            return m[c] if b == 1 else s.S[c] - m[c]
        for nm, vec, need in s.plans:
            r = FRAMES[nm][1]; ys = []
            for a in need:                       # escape: make a left-out atom nonempty
                y = sv.BoolVar(''); ys.append(y); sv.Add(size(a) >= 1e-6 * y)
            for i in range(r):
                L = sum(sum(f for v, f in lst if v[i]) * size(a) for a, lst in vec.items())
                y = sv.BoolVar(''); ys.append(y)
                sv.Add(L >= s.t + eta + mu - 40 * (1 - y))
            sv.Add(sum(ys) >= 1)
        sv.Maximize(mu); sv.SetTimeLimit(int(tl * 1000))
        st = sv.Solve()
        if st == pywraplp.Solver.INFEASIBLE: return 'INFEASIBLE', None
        if st not in (pywraplp.Solver.OPTIMAL, pywraplp.Solver.FEASIBLE): return 'TIMEOUT', None
        return 'OK', ({c: max(0.0, v.solution_value()) for c, v in m.items()}, max(0.0, o.solution_value()),
                      mu.solution_value())

    def run(s, maxit=300):
        t0 = time.time()
        for it in range(maxit):
            st, sol = s.adversary()
            if st != 'OK':
                s.log('  it %d: adversary %s, %d plans (%.0fs)' % (it, st, len(s.plans), time.time() - t0))
                return st, None
            m1, o1, mu = sol
            bs = s.best_static(m1)
            closing = [nm for nm, v in bs.items() if v is not None and v <= s.t + 1e-9]
            if it % 5 == 0 or not closing:
                s.log('  it %d: M1 %s o=%.3f mu=%.4f | %s' % (it, {c: round(v, 3) for c, v in m1.items() if v > 1e-6},
                                                              o1, mu, {k: round(v, 3) for k, v in bs.items()}))
            if not closing: return 'INVULNERABLE', (m1, o1, bs)
            added = 0
            for nm in closing:
                p = s.plan_for(m1, nm)
                if p: s.plans.append(p); added += 1
            if not added: return 'STUCK', (m1, o1, bs)
        return 'MAXIT', None

    def dump(s, fn, result, extra=None):
        json.dump({'S': s.S, 'R1': s.r1, 't': s.t, 'result': result, 'extra': extra,
                   'plans': [[nm, {'|'.join(map(str, a)): v for a, v in vec.items()}, ['|'.join(map(str, a)) for a in need]] for nm, vec, need in s.plans]},
                  open(fn, 'w'))


if __name__ == '__main__':
    ka, kb, ke, ko = [float(x) for x in sys.argv[1].split(',')]
    r1 = dict(zip(CELLS, [float(x) for x in sys.argv[2].split(',')]))
    t = 12 - float(sys.argv[3]); tag = sys.argv[4]
    S = sizes_K(ka, kb, ke, ko)
    s1 = Stage1(S, r1, t)
    print('K (ka,kb,ke,ko) =', (ka, kb, ke, ko), 'R1 =', {c: v for c, v in r1.items() if v}, '|R1| =', sum(r1.values()), 't =', t, flush=True)
    res, info = s1.run()
    print('RESULT', res, info if info else '', flush=True)
    s1.dump('logs/stage1g_%s.json' % tag, res, info)
