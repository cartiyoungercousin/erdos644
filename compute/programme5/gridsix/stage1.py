"""Exact stage-1 CEGAR for one first request R1 after Theorem P's K (units k/14).  [computed exact; SCIP]
Her moves after M1: a static cover ('plan') of a frame's alive atom pairs, frames = the four drop-one frames with
3 requests and the E-frame {E,F,G,K,M1} with 2 requests.  A plan is relative: phi[atom][i] = fraction of the atom in
request i, with full support (every atom of the frame is placed, so coverage does not depend on M1: alive pairs
depend only on atom membership).  Its request sizes are linear in M1, so 'plan p closes M1' is max_i L_i^p(M1) <= t.
His MILP: a legal M1 (avoids R1, mass 14, S*-traces vs E, F, G, K) defeating every plan so far (some request > t + eta).
Loop: his M1 -> her exact best static value per frame (cover.min_t); if some frame closes, add that plan; else M1 is
statically invulnerable (then jm.stage2 decides the E-frame adaptive game).  INFEASIBLE (SCIP) = every M1 is closed
by one of the listed static plans: R1 closes at depth 1."""
import sys, os, json, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'jointmilp'))
import itertools
from ortools.linear_solver import pywraplp
import jm
from frames import base_sizes, refine, alive, ZEPS
from cover import min_t

ALPHA = float(os.environ.get("ALPHA", "7.0"))
S = jm.sizes(ALPHA); C7 = jm.C7; SPEC = jm.SPEC
FRAMES = {'FGKM1': (['F', 'G', 'K', 'M1'], 3), 'EGKM1': (['E', 'G', 'K', 'M1'], 3),
          'EFKM1': (['E', 'F', 'K', 'M1'], 3), 'EFGM1': (['E', 'F', 'G', 'M1'], 3),
          'EFGKM1': (['E', 'F', 'G', 'K', 'M1'], 2)}
TINY = 1e-6
VEC = {}


def atoms_of(m1):
    mm = dict(m1); mm['Z'] = ZEPS / 2
    return refine(base_sizes(ALPHA), [{(c,): v for c, v in mm.items()}])


POSSIBLE = None   # set of atoms that can be nonempty for the current R1 (set in run)


def full_atoms(m1):
    at = atoms_of(m1)
    return {a: max(s, TINY) for a, s in at.items() if s > 1e-9 or POSSIBLE is None or a in POSSIBLE}


def plan_for(m1, frame, r):
    """best full-support relative plan for this M1: (value at m1, phi {atom: [frac per request]})"""
    at = full_atoms(m1)
    tt, pl = min_t(at, alive(at, FRAMES[frame][0]), r, tl=60)
    if tt is None: return None, None
    phi = {}; vec = {}
    for (a, v), n in pl.items():
        f = n / at[a]
        p = phi.setdefault(a, [0.0] * r)
        for i in range(r):
            if v[i]: p[i] += f
        vec.setdefault(a, []).append([list(v), f])
    VEC[id(phi)] = vec
    return tt, phi


def best_static(m1, t):
    """her exact best static value per frame for this M1 (true atom sizes, Z 0+)"""
    at = atoms_of(m1); sz = {a: s for a, s in at.items() if s > 1e-9}; out = {}
    for nm, (fr, r) in FRAMES.items():
        tt, _ = min_t(sz, alive(at, fr), r, tl=60); out[nm] = tt
    return out


def adversary(r1, plans, t, eta=1e-5, tl=120, maximize_margin=True):
    sv = pywraplp.Solver.CreateSolver('SCIP'); inf = sv.infinity()
    m = {c: sv.NumVar(0, max(0.0, S[c] - r1[c]), c) for c in C7}; o = sv.NumVar(0, 14, 'o')
    sv.Add(sum(m.values()) + o == 14)
    for P, cs in jm.MEM.items():                 # traces in S*
        T_ = sum(m[c] for c in cs); ys = [sv.BoolVar('') for _ in SPEC]
        sv.Add(sum(ys) == 1)
        sv.Add(T_ >= sum(lo * y for (lo, hi), y in zip(SPEC, ys)))
        sv.Add(T_ <= sum(hi * y for (lo, hi), y in zip(SPEC, ys)))
    mu = sv.NumVar(0, 3, 'mu')
    def size(a):
        c = a[0]
        if c == 'Z': return ZEPS / 2
        return m[c] if a[1] == 1 else S[c] - m[c]
    for frame, phi in plans:
        ys = []
        r = len(next(iter(phi.values())))
        for i in range(r):
            L = sum(p[i] * size(a) for a, p in phi.items() if p[i] > 0) + sum(p[i] * TINY for a, p in phi.items())
            y = sv.BoolVar(''); ys.append(y)
            sv.Add(L >= t + eta + mu - 40 * (1 - y))
        sv.Add(sum(ys) >= 1)
    if maximize_margin: sv.Maximize(mu)
    sv.SetTimeLimit(int(tl * 1000))
    st = sv.Solve()
    if st == pywraplp.Solver.INFEASIBLE: return 'INFEASIBLE', None
    if st not in (pywraplp.Solver.OPTIMAL, pywraplp.Solver.FEASIBLE): return 'TIMEOUT', None
    return 'OK', ({c: max(0.0, m[c].solution_value()) for c in C7}, max(0.0, o.solution_value()), mu.solution_value())


def run(r1, t, maxit=200, log=lambda *a: print(*a, flush=True), stage2=True):
    global POSSIBLE
    POSSIBLE = set([(c, 1) for c in C7 if S[c] - r1[c] > 1e-9] + [(c, 0) for c in C7 if S[c] > 1e-9] + [('Z', 0), ('Z', 1)])
    plans = []; t0 = time.time(); found = []
    for it in range(maxit):
        st, sol = adversary(r1, plans, t)
        if st != 'OK':
            log('it %d: adversary %s with %d plans (%.0fs)' % (it, st, len(plans), time.time() - t0))
            return st, plans, found
        m1, o1, mu = sol
        bs = best_static(m1, t)
        closing = [nm for nm, v in bs.items() if v is not None and v <= t + 1e-9]
        log('it %d: M1 %s o=%.3f margin %.4f | static %s' % (it, {c: round(v, 4) for c, v in m1.items()}, o1, mu,
                                                              {k: round(v, 3) for k, v in bs.items()}))
        if closing:
            added = 0
            for nm in closing:
                tt, phi = plan_for(m1, nm, FRAMES[nm][1])
                if tt is not None and tt <= t + 1e-9: plans.append((nm, phi)); added += 1
            if not added:
                log('   full-support plans do not close (%s); stuck' % closing); return 'STUCK', plans, found
            continue
        res = 'skip'
        if stage2:
            res, info, its, _ = jm.stage2(S, m1, o1, t, SPEC, maxit=150, tl=100, wall=400)
        log('   statically invulnerable M1; E-frame stage2: %s' % res)
        found.append((m1, o1, bs, res))
        return 'ADV' if res == 'ADV' else 'INVULNERABLE_' + res, plans, found
    return 'MAXIT', plans, found


if __name__ == '__main__':
    r = dict(zip(C7, [float(x) for x in sys.argv[1].split(',')]))
    t = 12 - float(sys.argv[2]) if len(sys.argv) > 2 else 12 - 0.002
    st, plans, found = run(r, t)
    print('RESULT', st, 'plans', len(plans))
    tag = sys.argv[3] if len(sys.argv) > 3 else 'x'
    json.dump({'R1': r, 't': t, 'result': st, 'plans': [[nm, {'|'.join(map(str, a)): p for a, p in phi.items()},
               {'|'.join(map(str, a)): v for a, v in VEC[id(phi)].items()}] for nm, phi in plans], 'found': [[m1, o1, bs, res] for m1, o1, bs, res in found]},
              open('logs/stage1_%s.json' % tag, 'w'))
