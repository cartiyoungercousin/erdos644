"""PETAL 47: centres-first (CF) as a scenario-tree min-max, mass level, against the adaptive leak adversary V_ad.

Same relaxations in her favour as cf_lp.py (pair/triple leaks, Tri leaks, own-part choice on the slack, pool traces
ignored).  What changes: her petal decisions are NON-ANTICIPATIVE and the adversary's leak is chosen AFTER seeing the
request.

Stage 1 (before any petal, no scenario): kappa_j, lambda_j, tau3, as cf_lp (N1).
Tree: node h = (o_0..o_{a-1}), o_a' = index into OPTS = the type set Theta of petal a''s leak.  The leak is delta
 spread equally over kappa_j, j in Theta (OPTS=1: singletons + the full set; OPTS=2: all 7 nonempty subsets).
 At node h (petal a) she picks: slack s_h, exclusions x[h][j] (Y_a contains kappa_j), e_h (Tri in Y_a), and sealing bits
 sl[h][a'][j] (Y_a contains the type-j part of L_a', mass delta/|Theta_a'|, j in Theta_a').
 Window cell masses mu_l[M, trace] per leaf l, NON-ANTICIPATIVE (cell masses aggregated by M & {0..a} equal across
 leaves sharing o_{<a}); NONANT=0 drops this (clairvoyant windows: a further relaxation in her favour).
V_ad: leak of petal a' needs x[h_a'][j]=0 for j in Theta; petal b > a' puts one leak point on the type-j part of L_a'
 (a link at j) unless Y_b contains that part (sl) or kappa_j (x):  lk(a',b,j) >= 1 - sl - x.
 Cost of sealing parts of type j in Y_b: min(kappa_j, sum of the sealed parts) (adversary keeps leaks disjoint up to
 capacity kappa_j); parts of excluded types are free.
Kills per leaf (as PETAL 46.1):
 N7 disjoint linked pairs, links at different types i != j; N5 pairwise linked triple at j with Theta_d not in {j};
 N6 link (a',b,j) => mu[{a',b}, trace j] = 0; N2/N3 as cf_lp.
 Leaf valid iff x[h_a][j]=0 and kappa_j > ETA for all j in Theta_a.
Objective: least Delta, Y_a mass <= Yb + s_h + Delta (Yb = t/2; INT mode: exact integer counts, `py cf_tree.py int k T d`).  Delta > 0: every CF plan loses to V_ad (obstruction for CF
within this model); Delta <= 0: necessary conditions only, a plan needs a point replay.
Usage: py cf_tree.py t delta [timelimit]     env ETA, NONANT, OPTS
"""
import itertools, os, sys
import numpy as np, highspy

ETA = float(os.environ.get('ETA', '1e-3'))
NONANT = os.environ.get('NONANT', '1') == '1'
OPTMODE = os.environ.get('OPTS', '1')
OPTS = [(0,), (1,), (2,), (0, 1, 2)] if OPTMODE == '1' else [c for r in (1, 2, 3) for c in itertools.combinations(range(3), r)]
SUBS = [frozenset(M) for r in range(1, 5) for M in itertools.combinations(range(4), r)]


def params_cont(t, dl):
    n = 1 + t / 2 - dl
    return dict(nA=n, nF=n, miss=t / 2, Wb=t / 2, Yb=t / 2, d=dl, tri_lo=max(0.0, n - (2 * t - 2 * dl)), integer=False)


def params_int(k, T, d):
    """exact integer instance, counts in points (unit = 1 point); H(k; nA, nF, d, d, m)"""
    S = 2 * k - 2 * d + T - 1; nA, nF = (S + 1) // 2, S // 2
    tA, tF = nA - k + d + 1, nF - k + d + 1
    assert tA + tF == T + 1
    blocks = sum(T - max(tA, j * d) for j in range(3))
    return dict(nA=nA, nF=nF, miss=nF - (k - d), Wb=tA - 1, Yb=tF, d=d, tri_lo=max(0, nF - blocks), integer=True)


def solve(P, tlim=600, verbose=False):
    nA, nF, miss, Wb, Yb, dl = P['nA'], P['nF'], P['miss'], P['Wb'], P['Yb'], P['d']; INT = P['integer']
    h = highspy.Highs(); h.setOptionValue("output_flag", verbose); h.setOptionValue("time_limit", float(tlim))
    h.setOptionValue("threads", 4)
    inf = highspy.kHighsInf; nv = [0]; BIG = 3.0 * max(1.0, Wb)
    NO = len(OPTS)

    def var(lo=0.0, hi=inf, integ=False, cost=0.0, cont=False):
        integ = integ or (INT and not cont)
        h.addVar(lo, hi); i = nv[0]; nv[0] += 1
        if integ: h.changeColIntegrality(i, highspy.HighsVarType.kInteger)
        if cost: h.changeColCost(i, cost)
        return i

    def row(lo, hi, coefs):
        idx = np.array([c[0] for c in coefs], dtype=np.int32); val = np.array([c[1] for c in coefs], dtype=float)
        h.addRow(lo, hi, len(idx), idx, val)

    D = var(-inf, inf, cost=1.0, cont=True)
    kap = [var(0, miss) for _ in range(3)]; lj = [var(0, miss) for _ in range(3)]
    lam = var(); tau3 = var(P['tri_lo'], nF)
    for j in range(3): row(miss, miss, [(kap[j], 1), (lj[j], 1)])
    row(nF, nF, [(kap[0], 1), (kap[1], 1), (kap[2], 1), (lam, 1), (tau3, 1)])
    row(0, inf, [(lj[0], 1), (lj[1], 1), (lj[2], 1), (lam, -2)])
    row(-inf, 0, [(lj[0], 1), (lj[1], 1), (lj[2], 1), (lam, -3)])
    big = [var(0, 1, True) for _ in range(3)]  # binary
    for j in range(3): row(-inf, ETA, [(kap[j], 1), (big[j], -BIG)])
    # ---- tree nodes
    nodes = {}
    for a in range(4):
        for hist in itertools.product(range(NO), repeat=a):
            N = dict(a=a, s=var(0, Wb), x=[var(0, 1, True) for _ in range(3)], e=var(0, 1, True), sl={})
            for ap in range(a):
                for j in OPTS[hist[ap]]: N['sl'][(ap, j)] = var(0, 1, True)
            ye = var(); y = [var() for _ in range(3)]
            row(-BIG, inf, [(ye, 1), (tau3, -1), (N['e'], -BIG)])
            for j in range(3):
                row(-BIG, inf, [(y[j], 1), (kap[j], -1), (N['x'][j], -BIG)]); row(-inf, 0, [(y[j], 1), (kap[j], -1)])
            cost = []
            for j in range(3):
                parts = [(N['sl'][(ap, j)], (dl // len(OPTS[hist[ap]])) if INT else dl / len(OPTS[hist[ap]])) for ap in range(a) if j in OPTS[hist[ap]]]
                w = var(); q = var(0, 1, True)
                if parts:   # w >= min(kappa_j, sum parts) unless x_j = 1
                    row(0, inf, [(w, 1)] + [(c, -m) for c, m in parts] + [(q, BIG), (N['x'][j], BIG)])
                    row(-BIG, inf, [(w, 1), (kap[j], -1), (q, -BIG), (N['x'][j], BIG)])
                cost.append((w, 1))
            row(-inf, Yb, [(ye, 1)] + [(v, 1) for v in y] + cost + [(N['s'], -1), (D, -1)])
            nodes[hist] = N
    # ---- leaves
    leaves = list(itertools.product(range(NO), repeat=4)); MU = {}
    for l in leaves:
        th = [OPTS[o] for o in l]
        mu = {(M, j): var() for M in SUBS for j in range(4)}; MU[l] = mu
        row(nA, nA, [(v, 1) for v in mu.values()])
        Nh = [nodes[l[:a]] for a in range(4)]
        for a in range(4):
            row(Wb, Wb, [(mu[(M, j)], 1) for M in SUBS if a in M for j in range(4)] + [(Nh[a]['s'], 1)])
        for j in range(1, 4): row(dl, dl, [(mu[(M, j)], 1) for M in SUBS])
        for a in range(4):
            Ta = frozenset([a])
            row(-inf, 0, [(mu[(Ta, j)], 1) for j in range(4)] + [(Nh[a]['e'], -Wb)])
            for j in range(1, 4): row(-inf, 0, [(mu[(Ta, j)], 1), (Nh[a]['x'][j - 1], -Wb)])
        V = [(Nh[a]['x'][j], 1) for a in range(4) for j in th[a]] + [(big[j], -1) for a in range(4) for j in th[a]]
        nV = sum(len(x) for x in th)

        def relax(coefs, rhs, k=1.0):    # sum coefs <= rhs + k*(number of violated validity conditions)
            row(-inf, rhs + k * nV, coefs + [(v, -k * c) for v, c in V])
        lk = {}
        for a, b in itertools.combinations(range(4), 2):
            for j in th[a]:
                lk[(a, b, j)] = var()
                row(1, inf, [(lk[(a, b, j)], 1), (Nh[b]['sl'][(a, j)], 1), (Nh[b]['x'][j], 1)])
                relax([(mu[(frozenset([a, b]), j + 1)], 1), (lk[(a, b, j)], Wb)], Wb, Wb)
        for P, Q in (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))):
            for i in th[P[0]]:
                for j in th[Q[0]]:
                    if i != j: relax([(lk[P + (i,)], 1), (lk[Q + (j,)], 1)], 1, BIG)
        for (a, b, c) in itertools.combinations(range(4), 3):
            d = ({0, 1, 2, 3} - {a, b, c}).pop()
            for j in th[a]:
                if j in th[b] and not set(th[d]) <= {j}:
                    relax([(lk[(a, b, j)], 1), (lk[(a, c, j)], 1), (lk[(b, c, j)], 1)], 2, BIG)
    if NONANT:
        for a in range(4):
            groups = {}
            for l in leaves: groups.setdefault(l[:a], []).append(l)
            for pre, ls in groups.items():
                base = ls[0]
                for l in ls[1:]:
                    for Mp in {frozenset(M & set(range(a + 1))) for M in SUBS}:
                        for j in range(4):
                            co = [(MU[base][(M, j)], 1) for M in SUBS if frozenset(M & set(range(a + 1))) == Mp] + \
                                 [(MU[l][(M, j)], -1) for M in SUBS if frozenset(M & set(range(a + 1))) == Mp]
                            row(0, 0, co)
    h.run()
    st = h.modelStatusToString(h.getModelStatus())
    if st != "Optimal":
        return st, None, None
    sol = h.getSolution().col_value
    info = dict(kappa=[round(sol[i], 4) for i in kap], tau3=round(sol[tau3], 4),
                nodes={hist: dict(s=round(sol[N['s']], 4), x=[int(round(sol[i])) for i in N['x']], e=int(round(sol[N['e']])),
                                  sl=[k for k, i in N['sl'].items() if sol[i] > .5]) for hist, N in nodes.items()})
    info['mu'] = {''.join(map(str, l)): {'%s|%d' % (''.join(map(str, sorted(M))), j): round(sol[v], 4) for (M, j), v in MU[l].items() if sol[v] > 1e-9} for l in leaves}
    info['nodes'] = {''.join(map(str, hh)): v for hh, v in info['nodes'].items()}
    for v in info['nodes'].values(): v['sl'] = [list(q) for q in v['sl']]
    return st, sol[D], info


if __name__ == "__main__":
    if sys.argv[1] == 'int':        # py cf_tree.py int k T d [timelimit]
        k, T, d = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); tl = float(sys.argv[5]) if len(sys.argv) > 5 else 600
        P = params_int(k, T, d); tag = "INT k=%d T=%d d=%d %s" % (k, T, d, {x: P[x] for x in ('nA', 'nF', 'miss', 'Wb', 'Yb', 'tri_lo')})
    else:                            # py cf_tree.py t delta [timelimit]
        t, dl = float(sys.argv[1]), float(sys.argv[2]); tl = float(sys.argv[3]) if len(sys.argv) > 3 else 600
        P = params_cont(t, dl); tag = "t=%.5f delta=%.5f" % (t, dl)
    st, Dv, info = solve(P, tl)
    print("%s NONANT=%s OPTS=%s: %s Delta=%s" % (tag, NONANT, OPTMODE, st, None if Dv is None else "%.5f" % Dv), flush=True)
    if info:
        print("kappa", info['kappa'], "tau3", info['tau3'])
        for hist, v in sorted(info['nodes'].items(), key=lambda kv: (len(kv[0]), kv[0])): print(hist, v)
        if len(sys.argv) > 1 and os.environ.get('DUMP'):
            import json; json.dump(dict(P={k_: v for k_, v in P.items()}, OPTS=OPTS, **info), open(os.environ['DUMP'], 'w'))
