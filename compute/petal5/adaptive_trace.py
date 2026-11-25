"""PETAL §31: adaptive trace release, as an exact 3-stage game MIP.

Question (§30.6): can request 7, chosen after seeing traces z_1, z_2, save one full delta of trace seal?

Model: 4 class-X petals, all-singles adversary (leaks on fresh R_Y points), split S-petals allowed, centres forced
class Y by G_j in R_X (|G_j| >= t/2).  Cells mu_M of R_X (M = petals missing the point).  Heavy cells: |M| = 1 (triple
cells, N = a whole petal, never releasable) and |M| = 2 (pair cells {a,b}, N = cells M' with M' cap {a,b} = 0).

Stages.  1: windows mu, G_5 (g5_M), hosting y5_a (T_a in G_5), release flags rho5_ab (G_5 holds N_ab).
  Adversary: z_1 in heavy cells outside G_5, mass delta, greedy fill in an order from ORDERS.
  2: G_6 >= z_1 cell by cell, except "skip" (pair-cell z_1 left out of G_6; then G_7 must hold N_ab and the point);
     hosting y6, release rho6.
  Adversary: z_2 in heavy cells outside G_6 (and not on skipped points), greedy fill in an order from ORDERS.
  3 (leaf): G_7 holds z_1 and z_2 except releases (z_1 pair part released if rho6, z_2 pair part released if rho5),
     hosting y7, rho7 (for skips); singles' patterns (once in j needs T_a in G_j; any pattern of size >= 2).
Requester-generous relaxations (so "value > t" means the adversary wins in the model against EVERY adaptive release):
  - singles' patterns are chosen at the leaf, with hindsight (loads of requests 5, 6 may differ across leaves);
  - the adversary is restricted to the finite order family ORDERS (a restriction of him);
  - he never uses light cells (a restriction of him);
  - skipped z_1 points are not reusable by z_2 (a restriction of him).
  - loads: request 5's single load ell5 is a stage-1 quantity, ell6 stage 2 (identities of the singles: hindsight);
  - capacity: a centre's R_X-trace is theta = min(delta, 1 - 4 delta + ell_j) (it must also hold the unrequested
    singles); "nocap" switches this off (theta = delta).
Usage: py adaptive_trace.py t [eps] [orders: first|first2] [timelimit] [cap|nocap]
"""
import itertools, sys, time
import numpy as np
import highspy

P4 = range(4)
TYPES = [frozenset(M) for r in range(1, 5) for M in itertools.combinations(P4, r)]
TRIP = [frozenset([a]) for a in P4]
PAIR = [frozenset(M) for M in itertools.combinations(P4, 2)]
HEAVY = PAIR + TRIP
NB = {M: [frozenset(Mp) for Mp in TYPES if not (Mp & M)] for M in PAIR}      # neighbourhood cells of a pair cell
PATS = [frozenset(P) for r in (1, 2, 3) for P in itertools.combinations(range(3), r)]


class MIP:
    def __init__(s):
        s.h = highspy.Highs(); s.h.setOptionValue("output_flag", False); s.n = 0
    def var(s, lo=0.0, hi=highspy.kHighsInf, integer=False):
        s.h.addVar(lo, hi)
        if integer: s.h.changeColIntegrality(s.n, highspy.HighsVarType.kInteger)
        s.n += 1; return s.n - 1
    def bin(s): return s.var(0, 1, True)
    def row(s, coefs, lo, hi):
        c = {}
        for k, v in coefs:
            c[k] = c.get(k, 0.0) + v
        idx = np.array(list(c.keys()), dtype=np.int32); val = np.array(list(c.values()), dtype=float)
        s.h.addRow(lo, hi, len(idx), idx, val)


INF = highspy.kHighsInf
FLOOR = 1.0   # 1: centre requests force class Y (|G_j| >= t/2).  0: unforced centre requests allowed; the adversary A_T
              # still answers class Y (its choice), so the model stays a valid game against A_T.


def orders(kind):
    rest_pt = PAIR + TRIP
    rest_tp = TRIP + PAIR
    if kind == "two":
        return [rest_pt, rest_tp]
    if kind == "canon":
        return [rest_pt, rest_tp, rest_pt[::-1], rest_tp[::-1]]
    if kind == "canon2":
        return [PAIR + TRIP, TRIP + PAIR, PAIR[::-1] + TRIP[::-1], TRIP[::-1] + PAIR[::-1],
                PAIR[3:] + PAIR[:3] + TRIP[2:] + TRIP[:2], TRIP[2:] + TRIP[:2] + PAIR[3:] + PAIR[:3]]
    out = []
    for M in HEAVY:
        out.append([M] + [X for X in rest_pt if X != M])
        if kind == "first2":
            out.append([M] + [X for X in rest_tp if X != M])
    return out


def greedy(m, cap, d, order, theta=None):
    """cap: dict M -> list of (var, coef); greedy fill of mass d (or of the variable theta); returns dict M -> z var."""
    z = {}
    r = m.var()
    if theta is None: m.row([(r, 1.0)], d, d)
    else: m.row([(r, 1.0), (theta, -1.0)], 0, 0)
    for M in order:
        zi = m.var(); b = m.bin()
        cterms = cap[M]
        # zi <= cap
        m.row([(zi, 1.0)] + [(v, -c) for v, c in cterms], -INF, 0)
        m.row([(zi, 1.0), (r, -1.0)], -INF, 0)
        # zi >= cap - 2b ;  zi >= r - 2(1-b)
        m.row([(zi, 1.0), (b, 2.0)] + [(v, -c) for v, c in cterms], 0, INF)
        m.row([(zi, 1.0), (r, -1.0), (b, -2.0)], -2.0, INF)
        r2 = m.var(); m.row([(r2, 1.0), (r, -1.0), (zi, 1.0)], 0, 0)
        z[M] = zi; r = r2
    return z


def trace_mass(m, d, ell):
    """theta = min(d, 1 - 4d + ell): a class-Y centre holding every unrequested single (4d - ell of them, in R_Y) has
    only 1 - (4d - ell) left for its R_X-trace.  (Omitting singles instead is the adversary's other option; giving the
    requester the trace reduction is the generous reading, see §31.)"""
    th = m.var(); b = m.bin()
    m.row([(th, 1.0)], -INF, d)
    m.row([(th, 1.0), (ell, -1.0)], -INF, 1 - 4 * d)
    m.row([(th, 1.0), (b, 2.0)], d, INF)
    m.row([(th, 1.0), (ell, -1.0), (b, -2.0)], 1 - 4 * d - 2.0, INF)
    return th


def solve(t, d, kind="first", tlim=600.0, capmode=True, fix=None, ord1=None, ord2=None):
    """fix: dict of stage-1 values (mu, g5, y5, rho5, ell5 by key) to hold fixed; ord1/ord2: explicit order lists."""
    m = MIP(); L = m.var(-INF)
    n = 1 + t / 2 - d
    mu = {M: m.var() for M in TYPES}
    m.row([(mu[M], 1.0) for M in TYPES], n, n)
    for a in P4:
        m.row([(mu[M], 1.0) for M in TYPES if a in M], -INF, t / 2)

    def gset(tag):
        g = {M: m.var() for M in TYPES}
        for M in TYPES: m.row([(g[M], 1.0), (mu[M], -1.0)], -INF, 0)
        m.row([(g[M], 1.0) for M in TYPES], FLOOR * t / 2, INF)
        y = {a: m.bin() for a in P4}
        for a in P4: m.row([(g[TRIP[a]], 1.0), (mu[TRIP[a]], -1.0), (y[a], -1.0)], -1.0, INF)
        rho = {M: m.bin() for M in PAIR}
        for M in PAIR:
            for Mp in NB[M]: m.row([(g[Mp], 1.0), (mu[Mp], -1.0), (rho[M], -1.0)], -1.0, INF)
        return g, y, rho

    g5, y5, rho5 = gset(5)
    k1, k2 = (kind.split("/") + [kind])[:2]
    ORD, ORD2 = orders(k1), orders(k2)
    if ord1 is not None: ORD = ord1
    if ord2 is not None: ORD2 = ord2
    ell5 = m.var(); th1 = trace_mass(m, d, ell5) if capmode else None
    if fix is not None:
        for M in TYPES:
            m.h.changeColBounds(mu[M], fix["mu"][M], fix["mu"][M]); m.h.changeColBounds(g5[M], fix["g5"][M], fix["g5"][M])
        for a in P4: m.h.changeColBounds(y5[a], fix["y5"][a], fix["y5"][a])
        for M in PAIR: m.h.changeColBounds(rho5[M], fix["rho5"][M], fix["rho5"][M])
        m.h.changeColBounds(ell5, fix["ell5"], fix["ell5"])
    for o1 in ORD:
        z1 = greedy(m, {M: [(mu[M], 1.0), (g5[M], -1.0)] for M in HEAVY}, d, o1, th1)
        g6, y6, rho6 = gset(6)
        ell6 = m.var(); th2 = trace_mass(m, d, ell6) if capmode else None
        skip = {M: m.var() for M in PAIR}
        for M in HEAVY:
            terms = [(g6[M], 1.0), (z1[M], -1.0)] + ([(skip[M], 1.0)] if M in PAIR else [])
            m.row(terms, 0, INF)
        for M in PAIR: m.row([(skip[M], 1.0), (z1[M], -1.0)], -INF, 0)
        for o2 in ORD2:
            cap2 = {M: [(mu[M], 1.0), (g6[M], -1.0)] + ([(skip[M], -1.0)] if M in PAIR else []) for M in HEAVY}
            z2 = greedy(m, cap2, d, o2, th2)
            g7, y7, rho7 = gset(7)
            for M in HEAVY:
                if M in PAIR:
                    r1, r2 = m.var(), m.var()
                    m.row([(r1, 1.0), (z1[M], -1.0), (skip[M], 1.0)], -INF, 0)
                    m.row([(r1, 1.0), (rho6[M], -d)], -INF, 0)
                    m.row([(r2, 1.0), (z2[M], -1.0)], -INF, 0)
                    m.row([(r2, 1.0), (rho5[M], -d)], -INF, 0)
                    m.row([(skip[M], 1.0), (rho7[M], -d)], -INF, 0)
                    m.row([(g7[M], 1.0), (z1[M], -1.0), (z2[M], -1.0), (r1, 1.0), (r2, 1.0)], 0, INF)
                else:
                    m.row([(g7[M], 1.0), (z1[M], -1.0), (z2[M], -1.0)], 0, INF)
            ys = [y5, y6, y7]; gs = [g5, g6, g7]
            load = [[], [], []]
            for a in P4:
                xs = {P: m.var() for P in PATS}
                m.row([(xs[P], 1.0) for P in PATS], d, d)
                for j in range(3):
                    m.row([(xs[frozenset([j])], 1.0), (ys[j][a], -d)], -INF, 0)
                for P, v in xs.items():
                    for j in P: load[j].append((v, 1.0))
            m.row(load[0] + [(ell5, -1.0)], 0, 0)
            m.row(load[1] + [(ell6, -1.0)], 0, 0)
            for j in range(3):
                m.row([(gs[j][M], 1.0) for M in TYPES] + load[j] + [(L, -1.0)], -INF, 0)
    m.h.changeColCost(L, 1.0)
    m.h.setOptionValue("time_limit", tlim)
    m.h.setOptionValue("mip_rel_gap", 1e-6)
    t0 = time.time(); m.h.run()
    st = m.h.modelStatusToString(m.h.getModelStatus())
    info = m.h.getInfo()
    sol = m.h.getSolution().col_value
    raw = dict(mu={M: sol[mu[M]] for M in TYPES}, g5={M: sol[g5[M]] for M in TYPES}, y5={a: round(sol[y5[a]]) for a in P4},
               rho5={M: round(sol[rho5[M]]) for M in PAIR}, ell5=sol[ell5])
    plan = dict(mu={tuple(sorted(M)): round(sol[mu[M]], 5) for M in TYPES if sol[mu[M]] > 1e-7},
                g5={tuple(sorted(M)): round(sol[g5[M]], 5) for M in TYPES if sol[g5[M]] > 1e-7},
                y5=[a for a in P4 if sol[y5[a]] > .5], rho5=[tuple(sorted(M)) for M in PAIR if sol[rho5[M]] > .5])
    if fix is not None or ord1 is not None:
        return st, info.objective_function_value, info.mip_dual_bound, time.time() - t0, m.n, plan, raw
    return st, info.objective_function_value, info.mip_dual_bound, time.time() - t0, m.n, plan


def ccg(t, d, big="first", tlim=600.0, rounds=4):
    """column-and-constraint generation over stage-1 adversary orders: solve against the current order set O, then
    check the stage-1 plan against every order of the big family (each o1 is an independent subproblem once stage 1 is
    fixed, with the big family at stage 2 too); add violating orders and repeat."""
    BIG = orders(big)
    O = orders("two")
    for it in range(rounds):
        st, val, bnd, sec, nv, plan, raw = solve(t, d, tlim=tlim, ord1=O, ord2=O)
        print("  ccg round %d: |O|=%d %s value=%.5f bound=%.5f (%.0fs)" % (it, len(O), st, val, bnd, sec), flush=True)
        if bnd > t + 1e-7:
            return "adversary wins", bnd, O
        worst = []
        for o1 in BIG:
            r = solve(t, d, tlim=tlim, fix=raw, ord1=[o1], ord2=BIG)
            worst.append((r[2], o1))
        worst.sort(key=lambda z: -z[0])
        print("  plan vs big family: worst bound %.5f (budget %.3f)" % (worst[0][0], t), flush=True)
        if worst[0][0] <= t + 1e-7:
            return "plan survives big family", val, O
        new = [o for v, o in worst if v > t + 1e-7 and o not in O][:3]
        O = O + new
        O2 = O
    return "undecided", val, O


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "ccg":
    t = float(sys.argv[2]); eps = float(sys.argv[3]); d = 1 - t - eps
    print("ccg t=%.3f delta=%.5f" % (t, d), flush=True)
    print(ccg(t, d)[:2], flush=True)
    sys.exit(0)

if __name__ == "__main__":
    t = float(sys.argv[1]); eps = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-4
    kind = sys.argv[3] if len(sys.argv) > 3 else "first"
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    capmode = (sys.argv[5] != "nocap") if len(sys.argv) > 5 else True
    if len(sys.argv) > 6: FLOOR = float(sys.argv[6])
    d = 1 - t - eps
    st, val, bnd, sec, nv, plan = solve(t, d, kind, tl, capmode)
    print("t=%.3f delta=%.5f (1-t-%.0e) orders=%s | %s value=%.5f dual_bound=%.5f budget=%.3f | %.0fs vars=%d" % (
        t, d, eps, kind, st, val, bnd, t, sec, nv), flush=True)
    print("  plan:", plan, flush=True)
