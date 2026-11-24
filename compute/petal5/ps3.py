"""PETAL §28: strategy PS3 = the optimal window plan of window_lp.py, played on point sets; exact replay.
Usage: py ps3.py [games]

Petals (class X, forced by tau_Y points of R_Y):
  W_1, W_2 = disjoint blocks of R_X of size wmax = min(tau_X - 1, T - tau_Y)  (private windows);
  W_3 = rest R0 of R_X outside W_1, W_2, W_3' ... concretely: W_3 = p private points + a shared block Sh (|W_3| = wmax);
  W_4 = the remaining uncovered points of R_X (p' points) + as much of Sh as the budget allows.
  Request 4 also contains the common points of petals 1-3 outside R_X (in its R_Y part, or extra for pool points).
Centres: S-assignment (petal -> centre request or D) and the B-pattern design are chosen by MIP on the actual B points,
  minimising the predicted worst request max(tau_X, z_j + |T_a cap R_X|) + load_j with z_j = (j-1) d_Y.
"""
import sys, os, itertools
import numpy as np, highspy
sys.path.insert(0, os.path.dirname(__file__))
from pool_strip import Fam, tau_profile, search

PATS = [frozenset(P) for r in (1, 2, 3) for P in itertools.combinations(range(3), r)]
ASSIGNS = list(itertools.product([None, 0, 1, 2], repeat=4))


def allowed(J, assign):
    out = []
    for P in PATS:
        ok = len(P) >= 2
        if len(J) == 1:
            a = next(iter(J))
            if assign[a] is not None and assign[a] in P: ok = True
        if len(J) == 3:
            a = next(iter(frozenset(range(4)) - J))
            if assign[a] is not None and assign[a] not in P: ok = False
        if ok: out.append(P)
    return out


def design(counts, assign, base):
    """integer pattern design minimising max_j (base_j + load_j)."""
    h = highspy.Highs(); h.setOptionValue("output_flag", False)
    h.addVar(0, highspy.kHighsInf); n = 1
    loads = [[] for _ in range(3)]; vars_ = {}
    for J, c in counts.items():
        pats = allowed(J, assign)
        ids = []
        for P in pats:
            h.addVar(0, c); h.changeColIntegrality(n, highspy.HighsVarType.kInteger)
            vars_[(J, P)] = n; ids.append(n)
            for j in P: loads[j].append(n)
            n += 1
        h.addRow(c, c, len(ids), np.array(ids, dtype=np.int32), np.ones(len(ids)))
    for j in range(3):
        ids = loads[j] + [0]
        h.addRow(-highspy.kHighsInf, -base[j], len(ids), np.array(ids, dtype=np.int32), np.array([1.0] * len(loads[j]) + [-1.0]))
    h.changeColCost(0, 1.0); h.run()
    if h.modelStatusToString(h.getModelStatus()) != "Optimal": return None
    sol = h.getSolution().col_value
    return {key: int(round(sol[i])) for key, i in vars_.items()}, h.getInfo().objective_function_value


def ps3_strategy(F, T, ask, X):
    Y = 1 - X
    tX, tY = F.tau_c(X), F.tau_c(Y)
    reqs, reps, flags = [], [], []
    RX, RY = sorted(F.R[X]), sorted(F.R[Y])
    wmax = min(tX - 1, T - tY)
    nX = len(RX)
    W1, W2 = set(RX[:wmax]), set(RX[wmax:2 * wmax])
    rest = RX[2 * wmax:]                       # must be covered by W3 u W4
    p = max(0, len(rest) - wmax)               # points only in W4 ... computed below
    # split rest: W3 = rest[:wmax]; W4 must contain rest[wmax:] (private of W4) and as much of W3 as possible
    W3 = set(rest[:wmax])
    priv4 = set(rest[wmax:])
    petals = []
    for i in range(4):
        Fi = set()
        if i == 3:
            I = set.intersection(*petals)
            Fi |= I & F.R[Y]
            extra = I - F.R[X] - F.R[Y]
        for x in RY:
            if len(Fi) >= tY: break
            Fi.add(x)
        if i < 3:
            Wi = [W1, W2, W3][i]
            S = Fi | Wi
        else:
            room = T - len(Fi) - len(extra)
            if room < len(priv4): flags.append("W4 budget")
            # shared part: take from the end of W3 so that W3's private part is the front
            sh = sorted(W3)[::-1][:max(0, min(wmax, room) - len(priv4))]
            Wi = priv4 | set(sh)
            S = Fi | Wi | extra
        reqs.append(S)
        E = ask(S)
        if E is None: flags.append("no reply"); return dict(reqs=reqs, reps=reps, flags=flags)
        if F.classes(E) != [X]: flags.append("petal class")
        petals.append(E); reps.append(E)
    if set.intersection(*petals): flags.append("petals meet")
    U = set().union(*petals)
    typ = {x: frozenset(a for a in range(4) if x in petals[a]) for x in U}
    B = [x for x in U if x not in F.R[X]]
    Tx = {a: {x for x in U & F.R[X] if typ[x] == frozenset(range(4)) - {a}} for a in range(4)}
    counts = {}
    for x in B: counts[typ[x]] = counts.get(typ[x], 0) + 1
    best = None
    for A in ASSIGNS:
        if any(A.count(j) > 1 for j in range(3)): continue
        base = []
        for j in range(3):
            g = j * F.d[Y] + sum(len(Tx[a]) for a in range(4) if A[a] == j)
            base.append(max(tX, g))
        r = design(counts, A, base)
        if r is None: continue
        if best is None or r[1] < best[0]: best = (r[1], A, r[0])
    pred, A, asg = best
    pat, byt = {}, {}
    for x in sorted(B): byt.setdefault(typ[x], []).append(x)
    for (J, P), c in sorted(asg.items(), key=lambda z: (sorted(z[0][0]), sorted(z[0][1]))):
        for _ in range(c): pat[byt[J].pop()] = P
    Z = []
    for j in range(3):
        G = set().union(*[C & F.R[X] & U for C in Z]) if Z else set()
        for a in range(4):
            if A[a] == j: G |= Tx[a]
        for x in RX:
            if len(G) >= tX: break
            G.add(x)
        S = G | {x for x in B if j in pat[x]}
        reqs.append(S)
        E = ask(S)
        if E is None: flags.append("no reply"); return dict(reqs=reqs, reps=reps, flags=flags, pred=pred)
        if F.classes(E) != [Y]: flags.append("centre class")
        Z.append(E); reps.append(E)
    return dict(reqs=reqs, reps=reps, flags=flags, pred=pred)


def inst(k, T, tA, tF, d, m, po=False):
    return (k, T, tA - 1 + k - d, tF - 1 + k - d, d, d, m, po)


INST = [
    # t = 3/4: PS2 reached d/k < 3/16 + ... = t/4 (d <= 7 at k = 40); PS3 limit t/2 - 1/6 = 5/24 (d <= 8.33 at k = 40)
    inst(40, 30, 15, 16, 8, 0), inst(40, 30, 15, 16, 8, 40), inst(40, 30, 15, 16, 8, 40, True),
    inst(80, 60, 30, 31, 16, 80), inst(80, 60, 30, 31, 16, 0),
    inst(120, 90, 45, 46, 24, 100), inst(120, 90, 45, 46, 24, 100, True),
    # t = 0.775 (limit = 1 - t essentially: t/2 - 1/6 = 0.2208 > 1 - t = 0.225? no: 0.2208 < 0.225)
    inst(80, 62, 31, 32, 17, 80),
    # t = 0.78 > 7/9: whole range closed; d < (1 - t) k = 22 at k = 100
    inst(100, 78, 39, 40, 21, 80), inst(100, 78, 39, 40, 21, 100, True),
    # controls above the limit
    inst(40, 30, 15, 16, 9, 40), inst(80, 60, 30, 31, 17, 80), inst(20, 15, 8, 8, 4, 10),
]

if __name__ == "__main__":
    games = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    print("k T | nA nF d m pool_only | t d/k (t/2-1/6) | tau | games covers over-T maxreq centre_max maxcov flags")
    for (k, T, nA, nF, dA, dF, m, po) in INST:
        F = Fam(k, nA, nF, dA, dF, m, pool_only=po)
        best = None
        for X in (0, 1):
            st = search(F, T, X, games, seed=11 * k + dA + m, strat=ps3_strategy)
            if best is None or (st["viol"], st["covers"], st["maxreq"]) < (best[1]["viol"], best[1]["covers"], best[1]["maxreq"]): best = (X, st)
        X, st = best
        print("%d %d | %d %d %d %d %d | %.3f %.3f %.4f | %d | X=%s %d %d %d %d %d %d %s" % (
            k, T, nA, nF, dA, m, int(po), T / k, dA / k, T / k / 2 - 1 / 6, tau_profile(F), "AF"[X],
            st["games"], st["covers"], st["viol"], st["maxreq"], st["cmax"], st["maxcov"], sorted(st["flags"])), flush=True)
