"""§14 diagnostic: leaves sharing ONLY the request of round e (the node's request), each leaf with its own plan
(index or 'f' = free).  Usage: py adaptive_pair.py T N treefile k e tl leaf:plan [leaf:plan ...]"""
import sys, json, pulp, tilt
T, N = float(sys.argv[1]), float(sys.argv[2]); tree = {kk: {int(J): v for J, v in r.items()} for kk, r in json.load(open(sys.argv[3])).items()}
k, e, tl = int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6]); specs = [a.split(":") for a in sys.argv[7:]]
plans = tilt.load_plans(); prob = pulp.LpProblem("p", pulp.LpMinimize); cnt = [0]
def V(lo=0, hi=None, cat="Continuous"):
    cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
z = prob.add_variable("z", -3, 4); prob += z; hs = []
for b, p in specs:
    ref, drop = (None, 5) if p == "f" else plans[int(p)][:2]
    hs.append(tilt.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(b), [tree[b[:i]] for i in range(k)], drop, ref))
for h in hs[1:]:
    for i in range(k, e + 1):
        for J in hs[0][i]: prob += hs[0][i][J] - h[i][J] == 0
res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
print(json.dumps(dict(specs=sys.argv[7:], status=res.status_str, z=pulp.value(z) if res.has_solution else None,
      req=None if not res.has_solution else {J: round(pulp.value(v), 5) for J, v in hs[0][e].items() if pulp.value(v) > 1e-9})), flush=True)
