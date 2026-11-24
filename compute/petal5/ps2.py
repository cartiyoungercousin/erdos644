"""PETAL §27: strategy PS2 (designed windows + triple-cell sealing) on pooled arena families; exact replay.
Usage: py ps2.py [games]

Petals (class X, forced by tau_Y points of R_Y):
  request i (i = 0,1,2): F_i in R_Y of size max(tau_Y, |R_Y-parts of earlier petals|) containing those parts, plus a block
      W_i of R_X (pairwise disjoint blocks, |W_i| = min(T - |F_i|, tau_X - 1));
  request 3: F_3 likewise, W_3 = R_X minus (W_0 u W_1 u W_2), plus the common pool/other points of petals 0..2.
  => R_X-parts of petals are R_X - W_i, R_Y-parts of different petals are disjoint, empty common intersection.
Centres (class Y, forced by G_j in R_X, |G_j| >= tau_X):
  T_a = points of U in every petal but a.  S-petals: s1 in {0,1,2} sealed in request 0 with T_s1, s2 = 3 sealed in request 1
  with T_3.  Every other point of B = U - R_X is put in two of the three requests; points of type [4]-{s1} must use request 0,
  type [4]-{s2} request 1 (integer design, HiGHS MIP).  G_j contains R_X-traces of earlier centres and T_a cap R_X of its
  S-petal.
"""
import sys, os, itertools
import numpy as np, highspy
sys.path.insert(0, os.path.dirname(__file__))
from pool_strip import Fam, tau_profile, search, two_cover
from bload_lp import allowed, PATS


def design(counts, s1, s2):
    """integer pattern assignment minimising the max load.  counts: dict type->number of points."""
    h = highspy.Highs(); h.setOptionValue("output_flag", False)
    h.addVar(0, highspy.kHighsInf); n = 1
    loads = [[] for _ in range(3)]
    vars_ = {}
    for J, c in counts.items():
        pats = allowed(J, s1, s2)
        if not pats: return None
        ids = []
        for P in pats:
            h.addVar(0, c); h.changeColIntegrality(n, highspy.HighsVarType.kInteger)
            vars_[(J, P)] = n; ids.append(n)
            for j in P: loads[j].append(n)
            n += 1
        h.addRow(c, c, len(ids), np.array(ids, dtype=np.int32), np.ones(len(ids)))
    for j in range(3):
        ids = loads[j] + [0]
        h.addRow(-highspy.kHighsInf, 0, len(ids), np.array(ids, dtype=np.int32), np.array([1.0] * len(loads[j]) + [-1.0]))
    h.changeColCost(0, 1.0); h.run()
    sol = h.getSolution().col_value
    return {key: int(round(sol[i])) for key, i in vars_.items()}, h.getInfo().objective_function_value


def ps2_strategy(F, T, ask, X):
    Y = 1 - X
    k = F.k
    tX, tY = F.tau_c(X), F.tau_c(Y)
    reqs, reps, flags = [], [], []
    RX, RY = sorted(F.R[X]), sorted(F.R[Y])
    petals = []
    used = 0
    W = []
    for i in range(4):
        prevY = set().union(*[P & F.R[Y] for P in petals]) if petals else set()
        Fi = set(prevY)
        for x in RY:
            if len(Fi) >= tY: break
            Fi.add(x)
        if i < 3:
            w = min(T - len(Fi), tX - 1)
            Wi = set(RX[used:used + w]); used += w
        else:
            Wi = set(RX[used:])
            if len(Wi) > tX - 1: flags.append("W_3 too big")
            I = set.intersection(*petals)
            Wi |= I - F.R[Y] - F.R[X]
        W.append(Wi)
        S = Fi | Wi
        reqs.append(S)
        E = ask(S)
        if E is None: flags.append("no reply"); return dict(reqs=reqs, reps=reps, flags=flags)
        if F.classes(E) != [X]: flags.append("petal class")
        petals.append(E); reps.append(E)
    if set.intersection(*petals): flags.append("petals meet")
    U = set().union(*petals)
    typ = {x: frozenset(a for a in range(4) if x in petals[a]) for x in U}
    B = [x for x in U if x not in F.R[X]]
    Tset = {a: {x for x in U if typ[x] == frozenset(range(4)) - {a}} for a in range(4)}
    counts = {}
    for x in B:
        counts[typ[x]] = counts.get(typ[x], 0) + 1
    # choose S-petals by predicted worst request
    best = None
    for s1 in (None, 0, 1, 2):
        for s2 in (None, 3):
            r = design(counts, s1, s2)
            if r is None: continue
            asg, _ = r
            load = [0, 0, 0]
            for (J, P), c in asg.items():
                for j in P: load[j] += c
            g = [tX, tX, tX]
            if s1 is not None: g[0] = max(tX, len(Tset[s1] & F.R[X]))
            if s2 is not None: g[1] = max(tX, len(Tset[s2] & F.R[X]) + F.d[Y])
            g[2] = max(tX, 2 * F.d[Y])
            pred = max(g[j] + load[j] for j in range(3))
            if best is None or pred < best[0]: best = (pred, s1, s2, asg)
    pred, s1, s2, asg = best
    # realise the pattern assignment on points
    pat = {}
    pool_by_type = {}
    for x in sorted(B): pool_by_type.setdefault(typ[x], []).append(x)
    for (J, P), c in sorted(asg.items(), key=lambda z: (sorted(z[0][0]), sorted(z[0][1]))):
        for _ in range(c): pat[pool_by_type[J].pop()] = P
    Z = []
    for j in range(3):
        G = set().union(*[C & F.R[X] & U for C in Z]) if Z else set()
        if j == 0 and s1 is not None: G |= Tset[s1] & F.R[X]
        if j == 1 and s2 is not None: G |= Tset[s2] & F.R[X]
        for x in RX:
            if len(G) >= tX: break
            G.add(x)
        S = G | {x for x in B if j in pat[x]}
        # S-petal T-points outside R_X are in B and carry the right pattern by the design constraints
        reqs.append(S)
        E = ask(S)
        if E is None: flags.append("no reply"); return dict(reqs=reqs, reps=reps, flags=flags, pred=pred)
        if F.classes(E) != [Y]: flags.append("centre class")
        Z.append(E); reps.append(E)
    return dict(reqs=reqs, reps=reps, flags=flags, pred=pred)


def inst(k, T, tA, tF, dA, dF, m, po=False):
    return (k, T, tA - 1 + k - dA, tF - 1 + k - dF, dA, dF, m, po)


INST = [
    # small k (family-test sizes): k = 12, d = 2 and k = 16, d = 3 at t = 3/4
    inst(12, 9, 5, 5, 2, 2, 6), inst(12, 9, 5, 5, 2, 2, 12, True), inst(16, 12, 6, 7, 3, 3, 8), inst(16, 12, 6, 7, 3, 3, 16, True),
    inst(20, 15, 8, 8, 4, 4, 10),  # control: k = 20, d = 4 is beyond t/4
    # t = 3/4: open range for pooled A was [3t/16, 1-t) = [5.6, 10) points at k = 40; PS2 predicts d <= 7
    inst(40, 30, 15, 16, 6, 6, 0), inst(40, 30, 15, 16, 6, 6, 40), inst(40, 30, 15, 16, 7, 7, 0), inst(40, 30, 15, 16, 7, 7, 40),
    inst(40, 30, 15, 16, 7, 7, 40, True),
    inst(80, 60, 30, 31, 12, 12, 60), inst(80, 60, 30, 31, 14, 14, 60), inst(80, 60, 30, 31, 15, 15, 0), inst(80, 60, 30, 31, 15, 15, 80),
    inst(80, 60, 30, 31, 15, 15, 80, True),
    # t = 0.78 (range [14.6, 22) at k = 100; PS2 predicts d <= 19)
    inst(100, 78, 39, 40, 16, 16, 80), inst(100, 78, 39, 40, 19, 19, 0), inst(100, 78, 39, 40, 19, 19, 100),
    # t = 0.8: range [7.5, 10) at k = 50, PS2 covers all (t/4 = 1 - t)
    inst(50, 40, 20, 21, 8, 8, 40), inst(50, 40, 20, 21, 9, 9, 40), inst(50, 40, 20, 21, 9, 9, 40, True),
    # asymmetric leaks
    inst(80, 60, 30, 31, 15, 12, 60), inst(80, 60, 30, 31, 12, 15, 60),
    # controls above t/4
    inst(40, 30, 15, 16, 8, 8, 40), inst(80, 60, 30, 31, 16, 16, 80), inst(80, 60, 30, 31, 18, 18, 80),
]

if __name__ == "__main__":
    games = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    print("k T | nA nF dA dF m pool_only | t d/k t/4 | tau | games covers over-T maxreq centre_max maxcov flags")
    for (k, T, nA, nF, dA, dF, m, po) in INST:
        F = Fam(k, nA, nF, dA, dF, m, pool_only=po)
        tau = tau_profile(F)
        st = search(F, T, 0, games, seed=7 * k + dA + 13 * m, strat=ps2_strategy)
        print("%d %d | %d %d %d %d %d %d | %.3f %.3f %.3f | %d | %d %d %d %d %d %d %s" % (
            k, T, nA, nF, dA, dF, m, int(po), T / k, max(dA, dF) / k, T / (4 * k), tau,
            st["games"], st["covers"], st["viol"], st["maxreq"], st["cmax"], st["maxcov"], sorted(st["flags"])), flush=True)
