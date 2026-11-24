"""Resume a lookahead tree (tilt_la.py) at its failed nodes with more plans / time; re-verify all 64 leaves exactly.
Usage: py tilt_fix.py T N L tl maxplans"""
import sys, json, time, tilt, tilt_la
T = float(sys.argv[1]); N = float(sys.argv[2]); L = int(sys.argv[3]); tl = float(sys.argv[4]); mp = int(sys.argv[5])
fn = f"tiltla_tree_T{T}_N{N}_L{L}.json"
tree = {k: {int(J): v for J, v in r.items()} for k, r in json.load(open(fn)).items()}
plans = tilt.load_plans(); log = open(f"tiltla_T{T}_N{N}_L{L}.log", "a"); failed = []
def rec(prefix):
    e = len(prefix)
    if e == 6: return
    key = "".join(prefix)
    if key not in tree:
        fixed = [tree["".join(prefix[:i])] for i in range(e)]; best = None
        for idx in range(min(mp, len(plans))):
            ref, drop, tag = plans[idx]
            zv, req = tilt_la.node_solve(T - tilt.MARGIN, N, prefix, fixed, tl, drop, ref, L)
            if zv is not None and (best is None or zv < best[0]): best = (zv, req, tag, idx)
            if zv is not None and zv < -0.003: break
        log.write(json.dumps(dict(T=T, N=N, L=L, node=key, z=None if best is None else best[0], plan=None if best is None else best[2], resumed=True)) + "\n"); log.flush()
        if best is None or best[0] > -1e-4: failed.append((key, None if best is None else round(best[0], 4))); return
        plans.insert(0, plans.pop(best[3])); tree[key] = best[1]
    for bit in "UO": rec(prefix + [bit])
t0 = time.time(); rec([])
won, missing, worst, detail = tilt.verify(T, N, tree)
summ = dict(SUMMARY=True, resumed=True, T=T, N=N, L=L, failed_nodes=failed, leaves_won_exact=won, leaves_missing=missing,
            worst_exact=None if worst is None else [float(worst[0]), worst[1], worst[2]], secs=round(time.time() - t0), detail=detail)
log.write(json.dumps(summ) + "\n")
json.dump({k: {str(J): v for J, v in r.items()} for k, r in tree.items()}, open(fn, "w"))
print(json.dumps({k: v for k, v in summ.items() if k != "detail"}), flush=True)
