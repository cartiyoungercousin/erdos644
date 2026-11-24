"""§14: full NON-ANTICIPATIVE MILP for a subtree of the requester's strategy tree against the adaptive tilted spread.
Leaves = all bit strings (replies 2..7) extending PREFIX; requests for rounds < len(FIXEDK) taken from a tree file;
for every later round e the request is shared by all leaves agreeing on bits[:e] (optionally ignoring bit indices in
IGN, approach (1)).  Each leaf gets its own plan (types forced complete) from a probe log (or plan index / 'free').
Discards: per leaf the plan's discard, or with ALLD=1 any of the 7 (binary choice).  Objective: max over leaves of
mass(D) - budget.  The resulting tree is replayed EXACTLY on every leaf at the true T (adaptive_replay.replay, margin 0).
Usage: py adaptive_tree.py T N treefile k prefix planspec tl tag [ign] [alld] [m]
  planspec: probe log path | integer plan index | 'free'"""
import sys, json, itertools, pulp, time, tilt
import adaptive_replay as A
T = float(sys.argv[1]); N = float(sys.argv[2]); tf = sys.argv[3]; k = int(sys.argv[4]); pre = sys.argv[5]
ps = sys.argv[6]; tl = float(sys.argv[7]); tag = sys.argv[8]
ign = set(int(c) for c in sys.argv[9]) if len(sys.argv) > 9 and sys.argv[9] != "-" else set()
alld = len(sys.argv) > 10 and sys.argv[10] == "1"
tree0 = {kk: {int(J): v for J, v in r.items()} for kk, r in json.load(open(tf)).items()}
plans = tilt.load_plans()
leaves = ["".join(tuple(pre) + r) for r in itertools.product("UO", repeat=6 - len(pre))]
if ps == "free": lp = {b: (None, 5) for b in leaves}
elif ps.lstrip("-").isdigit(): lp = {b: (plans[int(ps)][0], plans[int(ps)][1]) for b in leaves}
else:
    pr = {d["bits"]: d["plan"] for d in map(json.loads, open(ps))}
    lp = {b: (plans[pr[b]][0], plans[pr[b]][1]) for b in leaves}
log = open(f"logs/adaptive_{tag}.log", "a")
def key(bits, e): return "".join(c if i not in ign else "*" for i, c in enumerate(bits[:e]))
prob = pulp.LpProblem("adapt", pulp.LpMinimize); cnt = [0]
def V(lo=0, hi=None, cat="Continuous"):
    cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
z = prob.add_variable("z", -3, 4); prob += z
Tm = T - tilt.MARGIN; hs = {}
for b in leaves:
    fixed = [tree0[b[:e]] for e in range(k)]
    ref, drop = lp[b]
    if not alld:
        hs[b] = tilt.add_leaf(prob, V, z, Tm, N, list(b), fixed, drop, ref)
    else:
        # any discard: z_b = min over drops; z >= z_b.  Implemented with selector binaries and big-M on the final row.
        zb = [V(-3, 4) for _ in range(7)]; y = [V(cat="Binary") for _ in range(7)]
        prob += pulp.lpSum(y) == 1
        # first drop builds the leaf; others reuse its final masses via a second copy of the delta block
        hs[b] = tilt.add_leaf(prob, V, zb[0], Tm, N, list(b), fixed, 1, ref)
        raise SystemExit("alld not implemented in this build")
first = {}
for b in leaves:
    for e in range(k, 6):
        kk = key(b, e)
        if kk in first:
            a = first[kk]
            for J in hs[a][e]: prob += hs[a][e][J] - hs[b][e][J] == 0
        else: first[kk] = b
t0 = time.time()
log.write(json.dumps(dict(start=True, T=T, N=N, prefix=pre, k=k, plans=ps, tl=tl, ign=sorted(ign), leaves=len(leaves), vars=cnt[0])) + "\n"); log.flush()
res = prob.solve(pulp.HiGHS(msg=True, timeLimit=tl, threads=1, log_file=f"logs/adaptive_{tag}.highs"))
zv = pulp.value(z) if res.has_solution else None
out = dict(T=T, N=N, prefix=pre, status=res.status_str, milp_z=zv, secs=round(time.time() - t0))
if zv is not None:
    tree = dict(tree0)
    for kk, b in first.items():
        e = len(kk); tree[kk] = {J: pulp.value(v) for J, v in hs[b][e].items() if pulp.value(v) > 1e-9}
    json.dump({kk: {str(J): v for J, v in r.items()} for kk, r in tree.items()}, open(f"logs/adaptive_tree_{tag}.json", "w"))
    det = []
    for b in leaves:
        reqs = [tree0[b[:e]] if e < k else tree[key(b, e)] for e in range(6)]
        try: zq, d, un = A.replay(T, N, b, reqs); det.append((b, float(zq), d))
        except AssertionError as ex: det.append((b, "error " + str(ex), None))
    ok = [x for x in det if isinstance(x[1], float)]
    out.update(leaves_won_exact_at_T=sum(x[1] < 0 for x in ok), leaves=len(leaves), worst_exact_at_T=max(ok, key=lambda x: x[1]) if ok else None, detail=det)
log.write(json.dumps(out) + "\n"); log.flush()
print(json.dumps({kk: v for kk, v in out.items() if kk != "detail"}), flush=True)
