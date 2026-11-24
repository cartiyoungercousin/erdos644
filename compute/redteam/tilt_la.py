r"""§13, second construction of the requester's strategy tree against the tilted-spread adversary: LOOKAHEAD nodes.
At the node deciding the request of round e the MILP contains all 2^L continuations of the next L bits (then the last
bit repeated), with the non-anticipativity constraints "requests of round e+i agree for leaves agreeing on the first
i bits".  One plan (sets of types requested completely) is imposed on all leaves of a node; plans are tried in turn.
Only the round-e request is kept; children are solved afresh.  Exact verification of all 64 leaves as in tilt.py.
Usage: py tilt_la.py T N L [tl]"""
import pulp, sys, time, json, itertools, tilt

def node_solve(T, N, prefix, fixed, tl, drop, ref, L):
    e = len(fixed); L = min(L, 6 - e)
    prob = pulp.LpProblem("tiltla", pulp.LpMinimize); cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    leaves = list(itertools.product("UO", repeat=L)); hs = []
    for cont in leaves:
        bits = list(prefix) + list(cont); bits += [bits[-1]] * (6 - len(bits))
        hs.append(tilt.add_leaf(prob, V, z, T, N, bits, fixed, drop, ref))
    for a in range(len(leaves)):
        for b in range(a + 1, len(leaves)):
            for i in range(L):
                if leaves[a][:i] == leaves[b][:i]:
                    # tie b to the first leaf with the same i-prefix only (avoid redundant constraints)
                    first = min(c for c in range(len(leaves)) if leaves[c][:i] == leaves[b][:i])
                    if a == first:
                        for J in hs[a][e + i]: prob += hs[a][e + i][J] - hs[b][e + i][J] == 0
    res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
    if not res.has_solution: return None, None
    return pulp.value(z), {J: pulp.value(v) for J, v in hs[0][e].items() if pulp.value(v) > 1e-9}

def build(T, N, L, log, tl=20, maxplans=3):
    tree = {}; plans = tilt.load_plans(); stats = dict(nodes=0, failed=[], zs={})
    def rec(prefix, fixed):
        e = len(fixed)
        if e == 6: return
        key = "".join(prefix); best = None
        for idx in range(min(maxplans, len(plans))):
            ref, drop, tag = plans[idx]
            zv, req = node_solve(T - tilt.MARGIN, N, prefix, fixed, tl, drop, ref, L)
            if zv is not None and (best is None or zv < best[0]): best = (zv, req, tag, idx)
            if zv is not None and zv < -0.003: break
        stats["nodes"] += 1; stats["zs"][key] = None if best is None else round(best[0], 5)
        log.write(json.dumps(dict(T=T, N=N, L=L, node=key, z=None if best is None else best[0], plan=None if best is None else best[2])) + "\n"); log.flush()
        if best is None or best[0] > -1e-4:
            stats["failed"].append(key); return
        plans.insert(0, plans.pop(best[3])); tree[key] = best[1]
        for bit in ("U", "O"): rec(prefix + [bit], fixed + [best[1]])
    rec([], [])
    return tree, stats

if __name__ == "__main__":
    T = float(sys.argv[1]); N = float(sys.argv[2]); L = int(sys.argv[3]); tl = float(sys.argv[4]) if len(sys.argv) > 4 else 20
    log = open(f"tiltla_T{T}_N{N}_L{L}.log", "a"); t0 = time.time()
    tree, stats = build(T, N, L, log, tl)
    won, missing, worst, detail = tilt.verify(T, N, tree)
    summ = dict(SUMMARY=True, T=T, N=N, L=L, nodes=stats["nodes"], failed_nodes=stats["failed"], leaves_won_exact=won, leaves_missing=missing,
                worst_exact=None if worst is None else [float(worst[0]), worst[1], worst[2]], root_z=stats["zs"].get(""), secs=round(time.time() - t0), detail=detail)
    log.write(json.dumps(summ) + "\n"); log.flush()
    json.dump({k: {str(J): v for J, v in r.items()} for k, r in tree.items()}, open(f"tiltla_tree_T{T}_N{N}_L{L}.json", "w"))
    print(json.dumps({k: v for k, v in summ.items() if k != "detail"}), flush=True)
