"""§14 diagnostic, R requested rounds (m = R+2): leaves share requests of rounds k..e only (0-based), each leaf its own
plan (index into tilt.load_plans, rounds beyond the plan free; 'f' = free) and discard.  Exact replay of each leaf at T.
Usage: py adaptive_pairR.py R T N treefile k e tl drop leaf:plan [...]"""
import sys, json, pulp, tilt, adaptive_m as M
R = int(sys.argv[1]); T, N = float(sys.argv[2]), float(sys.argv[3])
tree = {kk: {int(J): v for J, v in r.items()} for kk, r in json.load(open(sys.argv[4])).items()}
k, e, tl, drop0 = int(sys.argv[5]), int(sys.argv[6]), float(sys.argv[7]), int(sys.argv[8]); specs = [a.split(":") for a in sys.argv[9:]]
plans = tilt.load_plans(); prob = pulp.LpProblem("p", pulp.LpMinimize); cnt = [0]
def V(lo=0, hi=None, cat="Continuous"):
    cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
z = prob.add_variable("z", -3, 4); prob += z; hs = []
for b, p in specs:
    ref = None if p == "f" else plans[int(p)][0]
    hs.append(M.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(b), [tree[b[:i]] for i in range(k)], drop0, ref, R))
for h in hs[1:]:
    for i in range(k, e + 1):
        for J in hs[0][i]: prob += hs[0][i][J] - h[i][J] == 0
res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
out = dict(R=R, k=k, e=e, drop=drop0, specs=sys.argv[9:], status=res.status_str, z=pulp.value(z) if res.has_solution else None)
if res.has_solution:
    val = lambda v: v if isinstance(v, (int, float)) else pulp.value(v)
    ex = []
    for (b, p), h in zip(specs, hs):
        reqs = [{J: val(v) for J, v in s.items() if val(v) > 1e-9} for s in h]
        try: ex.append(float(M.replay(T, N, b, reqs, R)[0]))
        except AssertionError: ex.append("err")
    out["exact_each_leaf_at_T"] = ex
print(json.dumps(out), flush=True)
