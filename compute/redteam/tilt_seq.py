"""§13 diagnostic: NON-ADAPTIVE tilt schedules.  For every one of the 64 bit sequences (known to her in advance) find
a requester line by plan-restricted MILP (all logged plans, first success), verify exactly at T.  A sequence with no
line found is a candidate hard schedule.  Usage: py tilt_seq.py T N"""
import sys, json, itertools, pulp, time, tilt
T = float(sys.argv[1]); N = float(sys.argv[2]); plans = tilt.load_plans(); out = open(f"tiltseq_T{T}_N{N}.log", "a")
def leaf_solve(bits, ref, drop, tl=10):
    prob = pulp.LpProblem("leaf", pulp.LpMinimize); cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    h = tilt.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(bits), [], drop, ref)
    res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
    if not res.has_solution: return None, None
    return pulp.value(z), [{J: pulp.value(v) for J, v in s.items() if pulp.value(v) > 1e-9} for s in h]
res = {}
for bits in itertools.product("UO", repeat=6):
    best = None; t0 = time.time()
    for idx in range(len(plans)):
        ref, drop, tag = plans[idx]
        zv, reqs = leaf_solve(bits, ref, drop)
        if zv is None: continue
        ze = None
        if zv < -0.0015:
            try: ze = float(tilt.exact_leaf(T, N, bits, reqs)[0])
            except AssertionError: ze = None
        if best is None or zv < best[0]: best = (zv, ze, tag, idx)
        if ze is not None and ze < 0:
            plans.insert(0, plans.pop(idx)); break
    rec = dict(T=T, N=N, bits="".join(bits), z=None if best is None else best[0], exact=None if best is None else best[1], plan=None if best is None else best[2], secs=round(time.time() - t0))
    out.write(json.dumps(rec) + "\n"); out.flush()
    res["".join(bits)] = rec
won = [b for b, r in res.items() if r["exact"] is not None and r["exact"] < 0]
print(json.dumps(dict(SUMMARY=True, T=T, N=N, sequences_won_exact=len(won), not_won={b: (None if r["z"] is None else round(r["z"], 4)) for b, r in res.items() if b not in won},
                      smallest_margin=max(res[b]["exact"] for b in won) if won else None)), flush=True)
