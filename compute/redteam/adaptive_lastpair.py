"""§15: the last bit is revealed after her last request, so leaves q+U and q+O (q = first R-1 bits) must be played with
the SAME full line.  For every q: joint plan-restricted MILP of the pair (all requests shared, root free unless a tree
file fixes the first k rounds), plans tried in turn; exact replay of both leaves at T.
Usage: py adaptive_lastpair.py T N R tag [plans=0,1,2,3,5] [tl] [treefile k]"""
import sys, json, itertools, pulp, tilt, adaptive_m as M
T, N, R, tag = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
ps = [int(x) for x in (sys.argv[5] if len(sys.argv) > 5 else "0,1,2,3,5").split(",")]
tl = float(sys.argv[6]) if len(sys.argv) > 6 else 60
tree = {kk: {int(J): v for J, v in r.items()} for kk, r in json.load(open(sys.argv[7])).items()} if len(sys.argv) > 7 else {}
k = int(sys.argv[8]) if len(sys.argv) > 8 else 0
plans = tilt.load_plans(); out = open(f"logs/adaptive_lastpair_{tag}.log", "a")
val = lambda v: v if isinstance(v, (int, float)) else pulp.value(v)
summ = {}
for q in ("".join(x) for x in itertools.product("UO", repeat=R - 1)):
    best = None
    for pi in ps:
        prob = pulp.LpProblem("lp", pulp.LpMinimize); cnt = [0]

        def V(lo=0, hi=None, cat="Continuous"):
            cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
        z = prob.add_variable("z", -3, 4); prob += z
        fixed = [tree[q[:i]] for i in range(k)]
        hs = [M.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(q + c), fixed, plans[pi][1], plans[pi][0], R) for c in "UO"]
        for e in range(k, R):
            for J in hs[0][e]: prob += hs[0][e][J] - hs[1][e][J] == 0
        res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
        zv = pulp.value(z) if res.has_solution else None
        ex = None
        if zv is not None and zv < 0:
            reqs = [{J: val(v) for J, v in s.items() if val(v) > 1e-9} for s in hs[0]]
            try: ex = [float(-M.replay(T, N, q + c, reqs, R)[0]) for c in "UO"]
            except AssertionError: ex = None
        d = dict(q=q, plan=pi, status=res.status_str, z=zv, exact_margins_at_T=ex)
        out.write(json.dumps(d) + "\n"); out.flush()
        if ex and min(ex) > 0:
            best = (min(ex), pi); break
        if zv is not None and (best is None or (best[1] is None and -zv > best[0])): best = (-zv, None)
    summ[q] = best
    print(json.dumps(dict(q=q, best=best)), flush=True)
won = [q for q, b in summ.items() if b and b[1] is not None]
out.write(json.dumps(dict(SUMMARY=True, T=T, N=N, R=R, pairs=len(summ), won_exact=len(won),
                          smallest=min((summ[q][0], q) for q in won) if won else None,
                          not_won={q: summ[q] for q in summ if q not in won})) + "\n")
