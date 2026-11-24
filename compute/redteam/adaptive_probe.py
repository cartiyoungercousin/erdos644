"""§14 probe: non-adaptive lines for schedules with a given prefix, with the first k requests FIXED (from a tree file).
Usage: py adaptive_probe.py T N treefile k prefix [maxplans]"""
import sys, json, itertools, pulp, time, tilt
import adaptive_replay as A
T = float(sys.argv[1]); N = float(sys.argv[2]); tf = sys.argv[3]; k = int(sys.argv[4]); pre = sys.argv[5]
mp = int(sys.argv[6]) if len(sys.argv) > 6 else 27
tree = {kk: {int(J): v for J, v in r.items()} for kk, r in json.load(open(tf)).items()} if tf != "-" else {}
plans = tilt.load_plans()
def leaf_solve(bits, fixed, ref, drop, tl=20):
    prob = pulp.LpProblem("leaf", pulp.LpMinimize); cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    h = tilt.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(bits), fixed, drop, ref)
    res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
    if not res.has_solution: return None, None
    return pulp.value(z), [{J: pulp.value(v) for J, v in s.items() if pulp.value(v) > 1e-9} if isinstance(s[next(iter(s))], pulp.LpVariable) or True else s for s in h]
for rest in itertools.product("UO", repeat=6 - len(pre)):
    bits = tuple(pre) + rest; fixed = [tree["".join(bits[:e])] for e in range(k)]
    best = None
    for idx in range(min(mp, len(plans))):
        ref, drop, tag = plans[idx]
        zv, reqs = leaf_solve(bits, fixed, ref, drop)
        if zv is None: continue
        reqs = [{J: float(pulp.value(v)) if not isinstance(v, (int, float)) else v for J, v in s.items()} for s in reqs]
        ze = float(A.replay(T + tilt.MARGIN, N, bits, reqs)[0]) if zv < -0.0012 else None
        if best is None or zv < best[0]: best = (zv, ze, idx)
        if ze is not None and ze < 0: break
    print(json.dumps(dict(bits="".join(bits), k=k, z=best and best[0], exact=best and best[1], plan=best and best[2])), flush=True)
