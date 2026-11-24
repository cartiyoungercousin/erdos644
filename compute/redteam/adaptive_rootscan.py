"""§15 diagnostic: two leaves (one per value of the first bit) that share ONLY the root request; scan pairs of plans.
z < 0 means a common root exists for these two leaves under these plans (each leaf otherwise free to adapt).
Usage: py adaptive_rootscan.py T N R leafU leafO tl plan,plan,... [maxpairs]"""
import sys, json, itertools, pulp, tilt, adaptive_m as M
T, N, R = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]); bu, bo = sys.argv[4], sys.argv[5]; tl = float(sys.argv[6])
ps = [int(x) for x in sys.argv[7].split(",")]; plans = tilt.load_plans()
out = open(f"logs/adaptive_rootscan_N{N}_m{R + 2}.log", "a")
for pu, po in itertools.product(ps, ps):
    prob = pulp.LpProblem("r", pulp.LpMinimize); cnt = [0]

    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    hu = M.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(bu), [], plans[pu][1], plans[pu][0], R)
    ho = M.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(bo), [], plans[po][1], plans[po][0], R)
    for J in hu[0]: prob += hu[0][J] - ho[0][J] == 0
    res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
    zv = pulp.value(z) if res.has_solution else None
    d = dict(N=N, m=R + 2, leaves=[bu, bo], plans=[pu, po], status=res.status_str, z=zv,
             root=None if zv is None else {J: round(pulp.value(v), 6) for J, v in hu[0].items()})
    out.write(json.dumps(d) + "\n"); out.flush(); print(json.dumps(d), flush=True)
