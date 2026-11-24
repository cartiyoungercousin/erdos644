"""§15 (v2: the unit is a LAST-BIT PAIR q+U, q+O, which must share every request, since the last bit is revealed
after her last request).  Automatic construction of a requester strategy tree against the adaptive tilted spread (m = R + 2).
Node p (request for round e = len(p)): every leaf below p gets a NON-adaptive line with the path requests fixed
(plan-restricted MILP at T - 0.001, exact replay at T).  Candidates for the node's request: (0) a seed request (root
only, optional), (a) a non-anticipative MILP on the H hardest leaves below each child (each with the plan its line
used), (b) the round-e requests of the lines, hardest leaf first.  A candidate is accepted if every leaf below p stays
winnable; then recurse (depth-first, with backtracking).  At e = R-1 the two leaves are solved jointly.
Finally ALL leaves are replayed exactly at T and the tree is checked for non-anticipativity (adaptive_check).
All restrictions (plans, candidate sets, time limits) are on HER side: a failure is "not found", not an adversary win.
Usage: py adaptive_driver.py T N R tag [seedtree|-] [H] [MC] [TL] [MTL]"""
import sys, json, itertools, pulp, time, tilt, adaptive_m as M

T = float(sys.argv[1]); N = float(sys.argv[2]); R = int(sys.argv[3]); tag = sys.argv[4]
seed = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != "-" else None
H = int(sys.argv[6]) if len(sys.argv) > 6 else 2
MC = int(sys.argv[7]) if len(sys.argv) > 7 else 3
TL = float(sys.argv[8]) if len(sys.argv) > 8 else 20
MTL = float(sys.argv[9]) if len(sys.argv) > 9 else 600
plans = tilt.load_plans(); order = list(range(len(plans))); tree = {}
log = open(f"logs/adaptive_{tag}.log", "a")


def W(d):
    log.write(json.dumps(d) + "\n"); log.flush()


def val(v):
    return v if isinstance(v, (int, float)) else pulp.value(v)


def milp(specs, fixed, share_from, tl):
    """specs: list of (bits, plan index).  Round-e requests (e >= share_from) shared by leaves with equal bits[:e]."""
    prob = pulp.LpProblem("d", pulp.LpMinimize); cnt = [0]

    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z; hs = []
    for b, pi in specs:
        ref, drop = plans[pi][:2]
        hs.append(M.add_leaf(prob, V, z, T - tilt.MARGIN, N, list(b), fixed, drop, ref, R))
    first = {}
    for i, (b, _) in enumerate(specs):
        for e in range(share_from, R):
            if b[:e] in first:
                h0 = hs[first[b[:e]]]
                for J in h0[e]: prob += h0[e][J] - hs[i][e][J] == 0
            else:
                first[b[:e]] = i
    res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
    if not res.has_solution: return None, None
    return pulp.value(z), [[{J: val(v) for J, v in s.items() if val(v) > 1e-9} for s in h] for h in hs]


def line(q, fixed, maxp=None):
    """best exact-won line for the last-bit pair q (R-1 bits): both leaves share all requests"""
    for i in list(order)[:maxp]:
        zv, L = milp([(q + "U", i), (q + "O", i)], fixed, len(fixed), TL)
        if zv is None or zv >= 0: continue
        try: zq = max(float(M.replay(T, N, q + c, L[0], R)[0]) for c in "UO")
        except AssertionError: continue
        if zq < 0:
            order.remove(i); order.insert(0, i); return zq, L[0], i
    return None


def same(c, d):
    return max([abs(c.get(J, 0) - d.get(J, 0)) for J in set(c) | set(d)] + [0]) < 1e-6


def rec(p):
    e = len(p); fixed = [tree[p[:i]] for i in range(e)]
    if e == R - 1:
        r = line(p, fixed)
        if r is None: W(dict(node=p, ok=False)); return False
        tree[p] = r[1][e]; W(dict(node=p, ok=True, margin=-r[0])); return True
    below = ["".join(tuple(p) + r) for r in itertools.product("UO", repeat=R - 1 - e)]
    lines = {}
    for b in below:
        r = line(b, fixed)
        if r is None:
            W(dict(node=p, ok=False, dead_leaf=b)); return False
        lines[b] = r
    hardest = {c: sorted([b for b in below if b[e] == c], key=lambda b: -lines[b][0]) for c in "UO"}
    used = sorted({lines[b][2] for b in below} | {0, 1, 2, 3})

    def gen():
        """candidates, lazily: seed, line requests, multi on hard leaves (line plans), then plan-pair scan"""
        if p in seeds: yield "seed", seeds[p]
        for b in sorted(below, key=lambda b: -lines[b][0])[:MC]:
            yield "line:" + b, lines[b][1][e]
        bu, bo = hardest["U"][0], hardest["O"][0]
        scan = []
        for pu in used:
            for po in used:
                zv, L = milp([(bu + 'U', pu), (bu + 'O', pu), (bo + 'U', po), (bo + 'O', po)], fixed, e, 120); W(dict(node=p, pair=[bu, bo], plans=[pu, po], z=zv))
                if zv is not None and zv < 0: scan.append((zv, pu, po, L[0][e]))
        scan.sort(key=lambda x: x[0])
        # cutting loop: start from the best plan pair, add the first leaf that has no line under the candidate
        for zv0, pu, po, c0 in scan[:2]:
            S = [(bu + c2, pu) for c2 in 'UO'] + [(bo + c2, po) for c2 in 'UO']; c = c0
            for it in range(10):
                fx = fixed + [c]; bad = None
                for b in sorted(below, key=lambda b: -lines[b][0]):
                    if b + 'U' in [x for x, _ in S]: continue
                    if line(b, fx, 10) is None: bad = b; break
                if bad is None:
                    yield f"cut:{S}", c; break
                got = None
                for pi in [lines[bad][2]] + [q for q in used if q != lines[bad][2]]:
                    zv, L = milp(S + [(bad + 'U', pi), (bad + 'O', pi)], fixed, e, MTL)
                    W(dict(node=p, cut_iter=it, add=bad, plan=pi, z=zv))
                    if zv is not None and zv < 0: got = (pi, L[0][e]); break
                if got is None: W(dict(node=p, cut_failed=[x for x, _ in S] + [bad])); break
                S += [(bad + 'U', got[0]), (bad + 'O', got[0])]; c = got[1]
        for zv, pu, po, c in scan[:4]:
            yield f"pair:{pu},{po}", c
    tried = []
    for src, c in gen():
        if any(same(c, d) for d in tried): continue
        tried.append(c)
        tree[p] = c; fixed2 = fixed + [c]; bad = None
        for b in sorted(below, key=lambda b: -lines[b][0]):
            if line(b, fixed2) is None:
                bad = b; break
        if bad:
            W(dict(node=p, cand=src, rejected_by=bad)); continue
        W(dict(node=p, cand=src, accepted=True, secs=round(time.time() - t0)))
        if rec(p + "U") and rec(p + "O"): return True
        for kk in [kk for kk in tree if len(kk) > e and kk.startswith(p)]: del tree[kk]
    tree.pop(p, None); W(dict(node=p, ok=False, cands=len(tried))); return False


seeds = {}
if seed:
    s = json.load(open(seed)); seeds = {"": {int(J): v for J, v in s[""].items()}}
t0 = time.time(); W(dict(start=True, T=T, N=N, R=R, H=H, MC=MC, TL=TL, MTL=MTL, seed=seed))
ok = rec("")
out = dict(SUMMARY=True, T=T, N=N, m=R + 2, constructed=ok, secs=round(time.time() - t0))
if ok:
    import adaptive_check
    json.dump({kk: {str(J): v for J, v in r.items()} for kk, r in tree.items()}, open(f"logs/adaptive_tree_{tag}.json", "w"))
    out.update(adaptive_check.check(T, N, R, f"logs/adaptive_tree_{tag}.json", f"logs/adaptive_verify_{tag}.log"))
W(out); print(json.dumps(out), flush=True)
