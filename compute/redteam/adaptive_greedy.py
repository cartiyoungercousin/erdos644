"""§14: depth-first construction of a requester subtree against the adaptive tilted spread, candidates from lines.
At node p (request for round e = len(p)), every leaf below p is solved NON-adaptively with the requests on the path to
p fixed (plan-restricted MILP, budget T - 0.001).  Candidates for the node's request are the round-e requests of those
lines, hardest leaf first.  A candidate is accepted when every leaf below p is still winnable with it fixed (MILP z <
-0.0015 and exact replay at T < 0); then recurse.  At the last node (e = 5) the two leaves are solved jointly.
Every leaf of the finished subtree is replayed EXACTLY at T (margin 0) with adaptive_replay.replay.
Usage: py adaptive_greedy.py T N treefile k prefix tag [maxcand] [tl]"""
import sys, json, itertools, pulp, time, tilt
import adaptive_replay as A
T = float(sys.argv[1]); N = float(sys.argv[2]); tf = sys.argv[3]; k = int(sys.argv[4]); pre = sys.argv[5]; tag = sys.argv[6]
MC = int(sys.argv[7]) if len(sys.argv) > 7 else 4; TL = float(sys.argv[8]) if len(sys.argv) > 8 else 20
tree = {kk: {int(J): v for J, v in r.items()} for kk, r in json.load(open(tf)).items()}
tree = {kk: r for kk, r in tree.items() if len(kk) < k and kk == pre[:len(kk)]}
plans = tilt.load_plans(); order = list(range(len(plans)))
log = open(f"logs/adaptive_{tag}.log", "a")
def W(d): log.write(json.dumps(d) + "\n"); log.flush()
def solve(leafbits, fixed, ref, drop, tl):
    prob = pulp.LpProblem("g", pulp.LpMinimize); cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    hs = [tilt.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(b), fixed, drop, ref) for b in leafbits]
    e = len(fixed)
    for h in hs[1:]:
        for J in hs[0][e]: prob += hs[0][e][J] - h[e][J] == 0
    res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
    if not res.has_solution: return None, None
    val = lambda v: v if isinstance(v, (int, float)) else pulp.value(v)
    return pulp.value(z), [[{J: val(v) for J, v in s.items() if val(v) > 1e-9} for s in h] for h in hs]
def line(b, fixed):
    """best exact-won non-adaptive line for leaf b with fixed prefix requests: (exact margin, reqs) or None"""
    for i in list(order):
        ref, drop, tg = plans[i]
        zv, L = solve([b], fixed, ref, drop, TL)
        if zv is None or zv > -0.0015: continue
        zq = float(A.replay(T, N, b, L[0])[0])
        if zq < 0:
            order.remove(i); order.insert(0, i); return zq, L[0]
    return None
nsolves = [0]
def rec(p):
    e = len(p); fixed = [tree[p[:i]] for i in range(e)]
    if e == 5:
        for i in list(order)[:12]:
            ref, drop, tg = plans[i]
            zv, L = solve([p + "U", p + "O"], fixed, ref, drop, TL * 2)
            if zv is None or zv > -0.0015: continue
            zs = [float(A.replay(T, N, p + c, L[j])[0]) for j, c in enumerate("UO")]
            if max(zs) < 0:
                tree[p] = L[0][5]; W(dict(node=p, ok=True, exact=zs, plan=tg)); return True
        W(dict(node=p, ok=False)); return False
    below = ["".join(tuple(p) + r) for r in itertools.product("UO", repeat=6 - e)]
    lines = {}
    for b in below:
        r = line(b, fixed)
        if r is None: W(dict(node=p, ok=False, dead_leaf=b)); return False
        lines[b] = r
    cands = []
    for b in sorted(below, key=lambda b: -lines[b][0]):
        c = lines[b][1][e]
        if all(max(abs(c.get(J, 0) - d.get(J, 0)) for J in set(c) | set(d)) > 1e-6 for d in cands): cands.append(c)
    for ci, c in enumerate(cands[:MC]):
        tree[p] = c; fixed2 = fixed + [c]; good = True
        for b in sorted(below, key=lambda b: -lines[b][0]):
            if line(b, fixed2) is None: good = False; W(dict(node=p, cand=ci, rejected_by=b)); break
        if not good: continue
        W(dict(node=p, cand=ci, accepted=True, req={str(J): v for J, v in c.items()}))
        if rec(p + "U") and rec(p + "O"): return True
        for kk in [kk for kk in tree if len(kk) > e and kk.startswith(p)]: del tree[kk]
    del tree[p]; W(dict(node=p, ok=False, cands=len(cands))); return False
t0 = time.time(); W(dict(start=True, T=T, N=N, prefix=pre, k=k, MC=MC, TL=TL))
ok = rec(pre)
out = dict(SUMMARY=True, T=T, N=N, prefix=pre, constructed=ok, secs=round(time.time() - t0))
if ok:
    det = []
    for r in itertools.product("UO", repeat=6 - len(pre)):
        b = pre + "".join(r); reqs = [tree[b[:e]] for e in range(6)]
        zq, d, un = A.replay(T, N, b, reqs); det.append((b, float(zq), d))
    out.update(leaves_won_exact_at_T=sum(x[1] < 0 for x in det), leaves=len(det), worst=max(det, key=lambda x: x[1]), detail=det)
    json.dump({kk: {str(J): v for J, v in r.items()} for kk, r in tree.items()}, open(f"logs/adaptive_tree_{tag}.json", "w"))
W(out); print(json.dumps({kk: v for kk, v in out.items() if kk != "detail"}), flush=True)
