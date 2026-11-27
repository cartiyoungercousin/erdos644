"""General exact CEGAR at the critical triple: variable triple cells, a chosen first-request type R0, every K, R1
families, static finishes.  [computed exact; SCIP]   Units k/14, t = 12 - delta.
Cells are membership strings over E, F, G, K: the triple's base cells EF (=X, q), EG (=Y, y), FG (=Z, z),
E (14-q-y), F (14-q-z), G (14-y-z), each split by K ('EFK' = X & K, ...), and 'K' = K's own outside points.
  R0 (her first request, a relative shape of the base cells) -> K avoids R0; K amounts k_b on every base cell + k_out.
  R1 families (relative: cells taken in full, then one fill cell up to t) -> M1_f avoids R1_f, mass 14.
All of K, M1_f are S*-legal against E, F, G and each other as needed (K vs E, F, G; M1 vs E, F, G, K).
Her static finishes (relative full-support plans, sizes linear in all variables):
  K level  : {E,F,G,K} + 3 requests; {F,G,K}, {E,G,K}, {E,F,K} + 4 requests;
  M1 level : the four drop-one frames {three of E,F,G,K} + M1 + 3 requests; {E,F,G,K,M1} + 2 requests.
A frame is unusable while some atom lying in every one of its members is nonempty (such an atom pairs with a
common fresh point of the later answers, which no request can contain) -- encoded as a required-empty atom.
His joint MILP: (q, y, z) in the box, K, and one M1 per family, escaping every plan.  INFEASIBLE = every triple in
the box closes against every K.
usage: py kgen.py tag R0type fams qlo,qhi,ylo,yhi,zlo,zhi [delta]"""
import sys, os, json, time, itertools
from ortools.linear_solver import pywraplp
from cover import min_t
import cover as _cv

SPEC = [(0.0, 45 / 12), (5.0, 73 / 12), (80 / 12, 14.0)]
BASE = ['EF', 'EG', 'FG', 'E', 'F', 'G']
CELLS = BASE + [b + 'K' for b in BASE] + ['K']
TINY = 1e-6
TL0 = float(os.environ.get('KGEN_TL0', '170')); TLMAX = float(os.environ.get('KGEN_TLMAX', '2720'))
FR_M = {'FGKM': 3, 'EGKM': 3, 'EFKM': 3, 'EFGM': 3, 'EFGKM': 2}
FR_K = {'EFGK': 3, 'FGK': 4, 'EGK': 4, 'EFK': 4}


def base_size(b, q, y, z):
    return {'EF': q, 'EG': y, 'FG': z, 'E': 14 - q - y, 'F': 14 - q - z, 'G': 14 - y - z}[b]


# her first-request types: amounts on base cells as functions of (q, y, z, t)
R0TYPES = {
    'A': lambda q, y, z, t: {'EF': q, 'EG': y, 'FG': z, 'F': t - q - y - z},        # class A, extra on F'
    'A_G': lambda q, y, z, t: {'EF': q, 'EG': y, 'FG': z, 'G': t - q - y - z},      # class A, extra on G'
    'noZ': lambda q, y, z, t: {'EF': q, 'EG': y, 'F': t - q - y},                    # drops Z
    'partY': lambda q, y, z, t: {'EF': q, 'FG': z, 'EG': t - q - z},                 # part of Y
    'partYnoZ': lambda q, y, z, t: {'EF': q, 'EG': t - q},                           # part of Y, no Z
    'partX': lambda q, y, z, t: {'EG': y, 'FG': z, 'EF': t - y - z},                 # part of X
}
# R1 families: (cells in full, fill cell)
FAMS = {'XAH': (['GK', 'EK', 'K'], 'EF'), 'YBH': (['FK', 'EK', 'K'], 'EG'), 'XA': (['GK'], 'EF'), 'YB': (['FK'], 'EG'),
        'XAY': (['GK', 'EGK', 'EK', 'K'], 'EF'), 'YBX': (['FK', 'EFK', 'EK', 'K'], 'EG'),
        'XAZ': (['GK', 'FGK', 'EK', 'K'], 'EF'), 'YBZ': (['FK', 'FGK', 'EK', 'K'], 'EG')}


def enc1(a): return '%s|%d' % a


def dec(x):
    c, b = x.rsplit('|', 1); return (c, int(b))


def inm(atom, m):
    c, b = atom
    return (b == 1) if m == 'M' else (m in c)


def dead_atoms(atl, frame):
    """atoms lying in every member of the frame"""
    return [a for a in atl if all(inm(a, m) for m in frame)]


def alive(atl, frame):
    return [(p, q) for p, q in itertools.combinations_with_replacement(atl, 2) if all(inm(p, m) or inm(q, m) for m in frame)]


def katoms(S):
    return {(c, 0): S[c] for c in CELLS}          # K-level: no M1 (bit 0 = 'not in M1', M not in frame)


def matoms(S, m1, o1=0.0):
    out = {('', 1): o1}
    for c in CELLS: out[(c, 1)] = m1.get(c, 0.0); out[(c, 0)] = S[c] - m1.get(c, 0.0)
    return out


def best_plan(at, frame, r, possible, t, full_support=True):
    """relative plan for this frame at these atom sizes: (vec, need) or None"""
    for mode in (('full', 'actual') if full_support else ('actual',)):
        if mode == 'full':
            use = {a: max(at.get(a, 0.0), TINY) for a in possible}
        else:
            use = {a: at[a] for a in possible if at.get(a, 0.0) > 1e-9}
        dead = dead_atoms(list(use), frame)
        need = [a for a in possible if a not in use] + dead
        use = {a: v for a, v in use.items() if a not in dead}
        if any(at.get(a, 0.0) > 1e-9 for a in dead): return None
        tt, pl = min_t(use, alive(list(use), frame), r, tl=60)
        if tt is None or tt > t + 1e-9: continue
        sup = set(_cv.SUPPORT); vec = {}
        for (a, v), n in pl.items():
            if (a, v) in sup: vec.setdefault(a, []).append([list(v), n / use[a]])
        for a in set(a for a, v in sup):
            if a not in vec: vec[a] = [[list(v), 0.0] for b, v in sup if b == a][:1]
        for a in list(vec):
            tot = sum(e[1] for e in vec[a]); vec[a] = [[v, f / tot] for v, f in vec[a]] if tot > 0 else [[vec[a][0][0], 1.0]]
        szs = [sum(sum(f for v, f in lst if v[i]) * use[a] for a, lst in vec.items()) for i in range(r)]
        if max(szs) <= t + 1e-9: return vec, sorted(set(need))
    return None


def band(sv, T_):
    ys = [sv.BoolVar('') for _ in SPEC]; sv.Add(sum(ys) == 1)
    sv.Add(T_ >= sum(lo * y for (lo, hi), y in zip(SPEC, ys))); sv.Add(T_ <= sum(hi * y for (lo, hi), y in zip(SPEC, ys)))


class KGen:
    def __init__(s, r0type, fams, box, t, krange='all', plan_file=None):
        s.r0 = R0TYPES[r0type]; s.fams = fams; s.box = box; s.t = t; s.krange = krange
        s.kplans = []; s.mplans = {f: [] for f in fams}; s.pf = plan_file
        if plan_file and os.path.exists(plan_file):          # resume: reload plans written so far
            for line in open(plan_file):
                d = json.loads(line); vec = {dec(a): v for a, v in d['vec'].items()}; need = [dec(a) for a in d['need']]
                item = (d['frame'], d['r'], vec, need)
                if d['lvl'] == 'K': s.kplans.append(item)
                elif d['lvl'] in s.mplans: s.mplans[d['lvl']].append(item)
        s.pfh = open(plan_file, 'a') if plan_file else None

    def save(s, lvl, item):
        if s.pfh:
            fr, r, vec, need = item
            s.pfh.write(json.dumps({'lvl': lvl, 'frame': fr, 'r': r, 'vec': {enc1(a): v for a, v in vec.items()},
                                    'need': [enc1(a) for a in need]}) + chr(10)); s.pfh.flush()

    def model(s, tl=170, fix=None, objective=True):
        sv = pywraplp.Solver.CreateSolver('SCIP'); t = s.t
        qlo, qhi, ylo, yhi, zlo, zhi = s.box
        q = sv.NumVar(qlo, qhi, 'q'); y = sv.NumVar(ylo, yhi, 'y'); z = sv.NumVar(zlo, zhi, 'z')
        if fix: [sv.Add(v == val) for v, val in zip((q, y, z), fix)]
        r0 = s.r0(q, y, z, t)
        k = {b: sv.NumVar(0, 14, 'k' + b) for b in BASE}; ko = sv.NumVar(0, 14, 'ko')
        S = {}
        for b in BASE:
            bs = base_size(b, q, y, z); sv.Add(bs >= 0)
            sv.Add(k[b] <= bs - r0.get(b, 0.0))
            if b in r0: sv.Add(r0[b] >= 0); sv.Add(r0[b] <= bs)
            S[b + 'K'] = k[b]; S[b] = bs - k[b]
        S['K'] = ko
        sv.Add(sum(k.values()) + ko == 14)
        for P in 'EFG': band(sv, sum(k[b] for b in BASE if P in b))
        if s.krange == 'hand':        # E-frame-forced ranges (class A): |K&F'| > t - y, |K&G'| > t - q
            sv.Add(k['F'] >= t - y + 1e-6); sv.Add(k['G'] >= t - q + 1e-6)
        elif s.krange == 'comp':      # the complement: |K&F'| <= t - y or |K&G'| <= t - q
            w = sv.BoolVar('comp')
            sv.Add(k['F'] <= t - y + 80 * w); sv.Add(k['G'] <= t - q + 80 * (1 - w))
        mu = sv.NumVar(0, 3, 'mu')
        def esc(plans, size):
            for frame, r, vec, need in plans:
                ys = []
                for a in need:
                    yy = sv.BoolVar(''); ys.append(yy); sv.Add(size(a) >= 1e-6 * yy)
                for i in range(r):
                    L = sum(sum(f for v, f in lst if v[i]) * size(a) for a, lst in vec.items())
                    yy = sv.BoolVar(''); ys.append(yy); sv.Add(L >= t + 1e-5 + mu - 80 * (1 - yy))
                sv.Add(sum(ys) >= 1)
        esc(s.kplans, lambda a: S[a[0]])
        M = {}
        for f in s.fams:
            fullc, fill = FAMS[f]
            # applicable iff the full cells fit in t (app = 0 forces fillamt < 0); if the fill amount exceeds the
            # fill cell, the fill cell is taken in full (cap = 1) and the request is simply smaller
            app = sv.BoolVar('app_' + f); cap = sv.BoolVar('cap_' + f)
            fillamt = t - sum(S[c] for c in fullc)
            sv.Add(fillamt >= -80 * (1 - app)); sv.Add(fillamt <= -1e-6 + 80 * app)
            sv.Add(fillamt <= S[fill] + 80 * cap); sv.Add(fillamt >= S[fill] - 80 * (1 - cap))
            m = {c: sv.NumVar(0, 14, '') for c in CELLS}; oo = sv.NumVar(0, 14, '')
            sv.Add(sum(m.values()) + oo == 14)
            for c in CELLS:
                sv.Add(m[c] <= S[c])
                if c in fullc: sv.Add(m[c] <= 80 * (1 - app))
                elif c == fill:
                    sv.Add(m[c] <= S[c] - fillamt + 80 * cap + 80 * (1 - app)); sv.Add(m[c] <= 80 * (1 - cap) + 80 * (1 - app))
            for P in 'EFGK': band(sv, sum(m[c] for c in CELLS if P in c))
            def size(a, m=m, oo=oo):
                c, b = a
                if c == '': return oo                       # M1's own outside points (in M1 only)
                return m[c] if b == 1 else S[c] - m[c]
            # plans need only be escaped when the family applies: relax with app
            for frame, r, vec, need in s.mplans[f]:
                ys = [sv.BoolVar('')]; sv.Add(ys[0] <= 1 - app)
                for a in need:
                    yy = sv.BoolVar(''); ys.append(yy); sv.Add(size(a) >= 1e-6 * yy)
                for i in range(r):
                    L = sum(sum(fr for v, fr in lst if v[i]) * size(a) for a, lst in vec.items())
                    yy = sv.BoolVar(''); ys.append(yy); sv.Add(L >= t + 1e-5 + mu - 80 * (1 - yy))
                sv.Add(sum(ys) >= 1)
            M[f] = (m, oo, app)
        if objective: sv.Maximize(mu)
        sv.SetTimeLimit(int(tl * 1000))
        st = sv.Solve()
        if st == pywraplp.Solver.INFEASIBLE: return 'INFEASIBLE', None
        if st not in (pywraplp.Solver.OPTIMAL, pywraplp.Solver.FEASIBLE): return 'TIMEOUT', None
        val = lambda e: e.solution_value() if hasattr(e, 'solution_value') else float(e)
        qv, yv, zv = q.solution_value(), y.solution_value(), z.solution_value()
        kv = {b: k[b].solution_value() for b in BASE}
        Sv = {}
        for b in BASE:
            Sv[b + 'K'] = max(0.0, kv[b]); Sv[b] = max(0.0, base_size(b, qv, yv, zv) - kv[b])
        Sv['K'] = max(0.0, ko.solution_value())
        Ms = {f: ({c: max(0.0, v.solution_value()) for c, v in m.items()}, oo.solution_value(), app.solution_value() > 0.5)
              for f, (m, oo, app) in M.items()}
        return 'OK', ((qv, yv, zv), Sv, Ms, mu.solution_value())

    def poss_K(s):
        return [(c, 0) for c in CELLS]

    def poss_M(s, f):
        fullc, fill = FAMS[f]
        return [(c, 1) for c in CELLS if c not in fullc] + [(c, 0) for c in CELLS] + [('', 1)]

    def step(s, sol):
        trip, S, Ms, mu = sol; t = s.t; added = 0
        at = katoms(S)
        kclose = []
        for fr, r in FR_K.items():
            p = best_plan(at, fr, r, s.poss_K(), t)
            if p: s.kplans.append((fr, r, p[0], p[1])); s.save('K', s.kplans[-1]); added += 1; kclose.append(fr)
        if kclose: return added, 'K-closed by %s' % kclose
        escaped = []
        for f in s.fams:
            m1, o1, app = Ms[f]
            if not app: escaped.append(f + '(n/a)'); continue
            atm = matoms(S, m1, o1); got = 0
            for fr, r in FR_M.items():
                p = best_plan(atm, fr, r, s.poss_M(f), t)
                if p: s.mplans[f].append((fr, r, p[0], p[1])); s.save(f, s.mplans[f][-1]); added += 1; got += 1
            if not got: escaped.append(f)
        return added, 'escaped %s' % escaped

    def run(s, log, maxit=400):
        t0 = time.time()
        for it in range(maxit):
            st, sol = s.model(tl=TL0)
            tl = TL0
            while st == 'TIMEOUT' and tl < TLMAX:     # retry: pure feasibility, doubling time limit; never exit on a timeout
                tl *= 2
                log('it %d: adversary TIMEOUT -> retry as feasibility problem, time limit %ds' % (it, tl))
                st, sol = s.model(tl=tl, objective=False)
            if st == 'TIMEOUT':
                log('it %d: adversary TIMEOUT at the maximal limit %ds; continuing to retry' % (it, tl)); continue
            if st != 'OK':
                log('it %d: adversary %s; plans K %d, M1 %s (%.0fs)' % (it, st, len(s.kplans), {f: len(p) for f, p in s.mplans.items()}, time.time() - t0))
                return st, None
            added, info = s.step(sol)
            trip, S, Ms, mu = sol
            if it % 5 == 0 or not added:
                log('it %d: triple %s K %s mu %.4f | %s (%.0fs)' % (it, tuple(round(v, 4) for v in trip),
                    {c: round(v, 3) for c, v in S.items() if 'K' in c and v > 1e-6}, mu, info, time.time() - t0))
            if not added:
                log('SURVIVES (statically):', trip, S, {f: ({c: round(v, 4) for c, v in m.items() if v > 1e-7}, round(o, 4), a) for f, (m, o, a) in Ms.items()})
                return 'SURVIVES', sol
        return 'MAXIT', None

    def dump(s, fn, res, extra):
        enc = lambda vec: {'|'.join(map(str, a)): v for a, v in vec.items()}
        json.dump({'box': s.box, 't': s.t, 'fams': s.fams, 'result': res, 'extra': repr(extra),
                   'kplans': [[fr, r, enc(v), ['|'.join(map(str, a)) for a in nd]] for fr, r, v, nd in s.kplans],
                   'mplans': {f: [[fr, r, enc(v), ['|'.join(map(str, a)) for a in nd]] for fr, r, v, nd in pl] for f, pl in s.mplans.items()}},
                  open(fn, 'w'))


if __name__ == '__main__':
    tag, r0type, fams, box = sys.argv[1], sys.argv[2], sys.argv[3].split(','), tuple(float(x) for x in sys.argv[4].split(','))
    delta = float(sys.argv[5]) if len(sys.argv) > 5 else 0.002
    lf = open('logs/kgen_%s.out' % tag, 'a')
    def log(*a):
        m = ' '.join(map(str, a)); print(m, flush=True); lf.write(m + '\n'); lf.flush()
    kr = os.environ.get('KRANGE', 'all')
    fams = [f for f in fams if f in FAMS]
    log('R0', r0type, 'families', fams, 'box (q lo,hi, y lo,hi, z lo,hi)', box, 't', 12 - delta, 'krange', kr)
    g = KGen(r0type, fams, box, 12 - delta, krange=kr, plan_file='logs/kgen_%s.plans.jsonl' % tag)
    res, extra = g.run(log)
    log('RESULT', res)
    g.dump('logs/kgen_%s.json' % tag, res, extra)
