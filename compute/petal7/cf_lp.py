"""PETAL §46: centres-first (CF) with petal slack, against the leak-on-triple-centre adversary V. Mass-level MIP.

Model (k = 1).  Centres 1-3 first, forced class F (|G_j| >= t/2 in R_A); then four class-A petals, each forced by an
R_F part Y_a of mass t/2 + s_a, window W_a in R_A of mass t/2 - s_a (s_a = slack moved from window to R_F sealing).
Adversary V: centre traces in R_A, mass delta each (pairwise disjoint after sealing, so |G_3| >= 2 delta > t/2 on the
strip and the centre R_F blocks total <= 2t - 2 delta); every centre misses exactly t/2 of R_F, extra misses on points
already missed; petal leaks on R_F points outside Y_a lying in the most centres.
R_F splits into Tri (in all three centres, mass tau3), kappa_j (missed by centre j only: in the two others), low points.
Necessary conditions for a CF win (each a kill otherwise, PETAL 46.1):
  (N1) tau3 >= n - (2t - 2 delta),  n = 1 + t/2 - delta;  kappa_j + lambda_j = t/2;  sum kappa + lam + tau3 = n;
       2 lam <= sum lambda_j <= 3 lam.
  (N2) if T_a (R_A points in W_a only) is nonempty, Y_a contains Tri;
  (N3) if type kappa_j is not contained in Y_a, T_a avoids z_j;
  Leak structure (V chooses the types): pair (a, b), a < b, is linkable at j if kappa_j (mass >= delta) is available to
  both and Y_b does not seal L_a cap kappa_j (sig_abj).  Adversary V*: each petal leak is spread over its available
  types with at least min(kappa_j, delta/3) on each, so that seal costs at least that; V* puts L_b on unsealed points of
  L_a.  One common point links, so linkable needs only kappa_j > ETA.  Sealing is decided per pair and type after L_a is
  seen, which is all the adaptivity she has.
  (N5'') a pairwise linkable triple at j is a kill if the fourth petal has another available type;
  (N6'') a linkable pair at j forces the pair cell D_ab to avoid z_j;
  (N7'') complementary linkable pairs at different types are a kill.
  (N4) windows: cell masses mu[M, j] (M = set of windows holding the point, j = trace label 0..3) cover R_A, window
       masses t/2 - s_a, trace masses delta.
Relaxations in her favour: she chooses the kappa/lambda split and the windows' cells; pair and triple leaks, the
adversary's own-part choice on the window slack, pool traces are all ignored.  So value > 0 (extra budget needed) is a
real loss of every CF plan against V.  Objective: least Delta with  [e_a] tau3 + sum_{j excluded} kappa_j <= t/2 + s_a + Delta.
Usage: py cf_lp.py   (ETA env: least kappa mass carrying a link; default 1e-3)
History of the leak block (PETAL 46.2): logs/cf_lp_eta.log = concentrated-leak accounting (seal cost delta, obsolete
code path); logs/cf_lp_vstar.log = current code (spread leaks, seal cost >= min(kappa_j, delta/3)).
"""
import itertools, sys
import numpy as np, highspy

ETA = float(__import__('os').environ.get('ETA', '1e-3'))   # least kappa mass that can carry a linked leak point
LEAKS = True   # include the leak-structure kills N5-N7 (PETAL 46.1)
SUBS = [frozenset(M) for r in range(1, 5) for M in itertools.combinations(range(4), r)]


def solve(t, dl, tlim=60):
    n = 1 + t / 2 - dl
    h = highspy.Highs(); h.setOptionValue("output_flag", False); h.setOptionValue("time_limit", float(tlim))
    inf = highspy.kHighsInf
    nv = [0]

    def var(lo=0.0, hi=inf, integ=False, cost=0.0):
        h.addVar(lo, hi); i = nv[0]; nv[0] += 1
        if integ: h.changeColIntegrality(i, highspy.HighsVarType.kInteger)
        if cost: h.changeColCost(i, cost)
        return i

    def row(lo, hi, coefs):
        idx = np.array([c[0] for c in coefs], dtype=np.int32); val = np.array([c[1] for c in coefs], dtype=float)
        h.addRow(lo, hi, len(idx), idx, val)

    D = var(-inf, inf, cost=1.0)
    kap = [var(0, t / 2) for _ in range(3)]; lj = [var(0, t / 2) for _ in range(3)]
    lam = var(); tau3 = var(max(0.0, n - (2 * t - 2 * dl)), n)
    for j in range(3): row(t / 2, t / 2, [(kap[j], 1), (lj[j], 1)])
    row(n, n, [(kap[0], 1), (kap[1], 1), (kap[2], 1), (lam, 1), (tau3, 1)])
    row(0, inf, [(lj[0], 1), (lj[1], 1), (lj[2], 1), (lam, -2)])
    row(-inf, 0, [(lj[0], 1), (lj[1], 1), (lj[2], 1), (lam, -3)])
    s = [var(0, t / 2) for _ in range(4)]
    x = [[var(0, 1, True) for _ in range(3)] for _ in range(4)]   # x[a][j] = 1: Y_a contains kappa_j
    e = [var(0, 1, True) for _ in range(4)]                       # e[a] = 1: T_a may be nonempty
    BIG = 2.0
    BUD = []; SEALCOST = {}
    for a in range(4):
        y = [var() for _ in range(3)]; ye = var()
        for j in range(3): row(-BIG, inf, [(y[j], 1), (kap[j], -1), (x[a][j], -BIG)]); row(-inf, 0, [(y[j], 1), (kap[j], -1)])
        row(-BIG, inf, [(ye, 1), (tau3, -1), (e[a], -BIG)])
        BUD.append([(ye, 1)] + [(y[j], 1) for j in range(3)] + [(s[a], -1), (D, -1)])
    mu = {(M, j): var() for M in SUBS for j in range(4)}
    row(n, n, [(v, 1) for v in mu.values()])
    for a in range(4):
        row(t / 2, t / 2, [(mu[(M, j)], 1) for M in SUBS if a in M for j in range(4)] + [(s[a], 1)])
    for j in range(1, 4):
        row(dl, dl, [(mu[(M, j)], 1) for M in SUBS])
    for a in range(4):
        Ta = frozenset([a])
        row(-inf, 0, [(mu[(Ta, j)], 1) for j in range(4)] + [(e[a], -t / 2)])
        for j in range(1, 4):   # trace z_j in T_a only if Y_a contains kappa_j
            row(-inf, 0, [(mu[(Ta, j)], 1), (x[a][j - 1], -t / 2)])
    if LEAKS:
        # avail[a][j] = 1 - x[a][j]; V picks the leak types (robust).  big[j] = 1 iff kappa_j >= delta (room for a leak).
        big = [var(0, 1, True) for _ in range(3)]
        for j in range(3): row(-inf, ETA, [(kap[j], 1), (big[j], -BIG)])   # kappa_j > ETA forces big_j = 1 (one common point links)
        # V*: leak a spread over its available types, at least min(kappa_j, delta/3) on each; sealing L_a cap kappa_j in Y_b
        # (sig[a,b,j]) costs at least that.  m_j >= min(kappa_j, delta/3) via binary q_j.
        m = [var() for _ in range(3)]; q = [var(0, 1, True) for _ in range(3)]
        for j in range(3):
            row(0, inf, [(m[j], 1), (kap[j], -1), (q[j], BIG)]); row(dl / 3 - BIG, inf, [(m[j], 1), (q[j], -BIG)])
        sig, lk = {}, {}
        for a, b in itertools.combinations(range(4), 2):
            for j in range(3):
                sig[(a, b, j)] = var(0, 1, True)
                lk[(a, b, j)] = var(0, 1)
                row(0, inf, [(lk[(a, b, j)], 1), (x[a][j], 1), (x[b][j], 1), (sig[(a, b, j)], 1), (big[j], -1)])
                row(-inf, t / 2, [(mu[(frozenset([a, b]), j + 1)], 1), (lk[(a, b, j)], t / 2)])      # N6''
                cv = var()
                row(-BIG, inf, [(cv, 1), (m[j], -1), (sig[(a, b, j)], -BIG), (x[a][j], BIG)])
                SEALCOST.setdefault(b, []).append((cv, 1))
        for (a, b, c) in itertools.combinations(range(4), 3):                                          # N5''
            d = ({0, 1, 2, 3} - {a, b, c}).pop()
            for j in range(3):
                for i in range(3):
                    if i != j:   # d has another available type i: its leak lies in centre j
                        row(-inf, 2, [(lk[(a, b, j)], 1), (lk[(a, c, j)], 1), (lk[(b, c, j)], 1), (x[d][i], -1)])
        for P, Q in (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))):                             # N7''
            for i in range(3):
                for j in range(3):
                    if i != j:
                        row(-inf, 1, [(lk[(P[0], P[1], i)], 1), (lk[(Q[0], Q[1], j)], 1)])
    for a in range(4): row(-inf, t / 2, BUD[a] + SEALCOST.get(a, []))
    h.run()
    st = h.modelStatusToString(h.getModelStatus())
    if st not in ("Optimal",): return st, None, None
    sol = h.getSolution().col_value
    info = dict(kappa=[round(sol[i], 4) for i in kap], tau3=round(sol[tau3], 4), s=[round(sol[i], 4) for i in s],
                x=[[int(round(sol[i])) for i in xa] for xa in x], e=[int(round(sol[i])) for i in e])
    return st, sol[D], info


if __name__ == "__main__":
    print("control (outside strip): t=0.75 delta=0.10, 0.15, 0.20 ;  then strip scan", flush=True)
    pts = [(0.75, 0.10), (0.75, 0.15), (0.75, 0.20)]
    for t in (0.7501, 0.76, 0.77, 0.7777):
        lo, hi = t / 2 - 1 / 6, 1 - t
        pts += [(t, lo + (hi - lo) * f) for f in (0.0, 0.25, 0.5, 0.75, 0.999)]
    for (t, dl) in pts:
        st, D, info = solve(t, dl)
        print("t=%.4f delta=%.4f (t/2-1/6=%.4f, 1-t=%.4f): %s  Delta=%s  %s" % (
            t, dl, t / 2 - 1 / 6, 1 - t, st, None if D is None else "%.5f" % D, info), flush=True)
