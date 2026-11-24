"""§14: non-anticipative MILP on a chosen SET of leaves (full non-anticipativity: the round-e request is shared by all
listed leaves agreeing on bits[:e]); rounds < k fixed from treefile ('-' = none).  Each leaf own plan ('f' = free).
Writes the node requests to logs/adaptive_multi_<tag>.json.  Usage: py adaptive_multi.py T N treefile k tl tag leaf:plan ..."""
import sys, json, pulp, tilt, adaptive_replay as A
T, N = float(sys.argv[1]), float(sys.argv[2]); tf = sys.argv[3]
tree = {} if tf == "-" else {kk: {int(J): v for J, v in r.items()} for kk, r in json.load(open(tf)).items()}
k, tl, tag = int(sys.argv[4]), float(sys.argv[5]), sys.argv[6]; specs = [a.split(":") for a in sys.argv[7:]]
plans = tilt.load_plans(); prob = pulp.LpProblem("m", pulp.LpMinimize); cnt = [0]
def V(lo=0, hi=None, cat="Continuous"):
    cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
z = prob.add_variable("z", -3, 4); prob += z; hs = {}
for b, p in specs:
    ref, drop = (None, 5) if p == "f" else plans[int(p)][:2]
    hs[b] = tilt.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(b), [tree[b[:i]] for i in range(k)], drop, ref)
first = {}
for b, _ in specs:
    for e in range(k, 6):
        if b[:e] in first:
            a = first[b[:e]]
            for J in hs[a][e]: prob += hs[a][e][J] - hs[b][e][J] == 0
        else: first[b[:e]] = b
res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
out = dict(tag=tag, k=k, specs=sys.argv[7:], status=res.status_str, z=pulp.value(z) if res.has_solution else None)
if res.has_solution:
    nodes = dict(tree)
    for kk, b in first.items(): nodes[kk] = {J: pulp.value(v) for J, v in hs[b][len(kk)].items() if pulp.value(v) > 1e-9}
    json.dump({kk: {str(J): v for J, v in r.items()} for kk, r in nodes.items()}, open(f"logs/adaptive_multi_{tag}.json", "w"))
    out["exact_at_T"] = {b: float(A.replay(T, N, b, [nodes[b[:e]] for e in range(6)])[0]) for b, _ in specs}
    out["root"] = {J: round(v, 5) for J, v in nodes[""].items()} if "" in nodes else None
print(json.dumps(out), flush=True)
