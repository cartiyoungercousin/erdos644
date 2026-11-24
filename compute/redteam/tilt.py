r"""RED TEAM §13: the TILTED SPREAD adversary (CORE.md §15) against the free requester, as a game tree.

Adversary on N points: at every reply the dump (omission, mass omega = N - T - 1) is
      half proportional (same fraction of every unrequested class)  +  half concentrated,
and the concentrated half goes, AT HIS CHOICE AFTER SEEING THE REQUEST, either
      mode U: onto unused points first, then lowest reply-degree  (into the points lying in many co-edges), or
      mode O: onto highest reply-degree first                     (out of them, onto old points).
So he has one free bit per reply: 2^6 reply sequences for the first seven replies (m = 8).
Requester: completely free, adaptive.  A requester strategy is a tree: the request for reply j depends on the bits of
replies < j.  It is built top-down: at each node a joint MILP over the two children (shared request at this node,
both bits, default continuation = the same bit repeated) fixes the node's request; then recurse.  This is a greedy
construction (a restriction on HER only).  The finished tree is verified leaf by leaf in exact rational arithmetic at
T (MILP budget T - margin), the adversary's rule applied with the true unrequested masses.
Result line per job: number of leaves won exactly, worst exact margin mass(D) - T over the 64 leaves.
Usage: py tilt.py worker  (jobs split by parity)   |   py tilt.py one T N
"""
import pulp, sys, time, json
from fractions import Fraction as Fr
def popc(x): return bin(x).count("1")
ORD = {"U": lambda ty: sorted(ty, key=lambda J: (popc(J), J)), "O": lambda ty: sorted(ty, key=lambda J: (-popc(J), J))}
AL = 0.5
PAIRK = 6
MARGIN = 0.001

def add_leaf(prob, V, z, T, N, bits, fixed, drop, ref=None):
    """bits: list of 6 modes for replies 2..7; fixed: list of request dicts for the first len(fixed) rounds."""
    E = 7; m = {0: N - 1.0, 1: 1.0}; rho = {1: 1}; hist = []
    slack = N - T - 1.0; lam = 1.0 / (N - T)
    for e in range(1, E):
        b = 1 << e; types = sorted(m); ub = {J: (1.0 if J else N) for J in types}
        if e - 1 < len(fixed):
            s = {J: float(fixed[e - 1].get(J, 0.0)) for J in types}
        else:
            s = {J: V(0, ub[J]) for J in types}
            for J in types: prob += s[J] <= m[J]
            prob += pulp.lpSum(s.values()) == T
            if ref is not None:
                for J in ref[e - 1]:
                    if J in s: prob += s[J] - m[J] == 0
        a = {J: m[J] - s[J] for J in types}
        ov = {J: V(0, ub[J]) for J in types}
        for J in types: prob += ov[J] <= a[J]
        prob += pulp.lpSum(ov.values()) == slack
        pre = []
        for J in ORD[bits[e - 1]](types):
            pre.append(J); g = V(cat="Binary")
            prob += a[J] - ov[J] <= ub[J] * g
            prob += slack - pulp.lpSum(ov[K] for K in pre) <= slack * (1 - g)
        m2, rho2 = {}, dict(rho)
        for J in types:
            o = AL * (1 - lam) * a[J] + (1 - AL) * ov[J]
            m2[J] = s[J] + o; m2[J | b] = a[J] - o
            r = V(cat="Binary"); prob += a[J] <= ub[J] * r + 1e-7; rho2[J | b] = r
        hist.append(s); m, rho = m2, rho2
    full = 127; I = full & ~(1 << (drop - 1)); delta = {}
    for P in range(full + 1):
        if P & ~I: continue
        comp = I & ~P
        if comp == 0: delta[P] = 1; continue
        dv = V(cat="Binary"); delta[P] = dv
        for K, rk in rho.items():
            if K and (K & comp) == comp:
                if isinstance(rk, int):
                    if rk: prob += dv >= 1
                else: prob += dv >= rk
    tot = []
    for J, mj in m.items():
        dl = delta[J & I]
        if isinstance(dl, int): tot.append(mj)
        else:
            d = V(0, N); prob += d >= mj - (N if J == 0 else 1.0) * (1 - dl); tot.append(d)
    prob += pulp.lpSum(tot) <= T + z
    return hist

def node_solve(T, N, prefix, fixed, tl, drop=5, ref=None, ref2=None, drop2=None):
    # ref / drop: plan of the U-child; ref2 / drop2: plan of the O-child (default: the same plan)
    """Joint MILP for the node whose request is for round len(fixed)+1; children: bit U and bit O at that round."""
    e = len(fixed)                      # 0-based index of the round to decide
    prob = pulp.LpProblem("tilt", pulp.LpMinimize); cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    hs = []
    for bit in ("U", "O"):
        bits = list(prefix) + [bit] * (6 - len(prefix))
        if bit == "U" or ref2 is None: hs.append(add_leaf(prob, V, z, T, N, bits, fixed, drop, ref))
        else: hs.append(add_leaf(prob, V, z, T, N, bits, fixed, drop2 or drop, ref2))
    for J in hs[0][e]: prob += hs[0][e][J] - hs[1][e][J] == 0
    res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
    if not res.has_solution: return res.status_str, None, None
    req = {J: pulp.value(v) for J, v in hs[0][e].items() if pulp.value(v) > 1e-9}
    return res.status_str, pulp.value(z), req

def exact_leaf(T, N, bits, reqs, margin=MARGIN):
    """Exact replay of one leaf: reqs = the six requests along this branch.  Returns (min over discards of D - T, drop)."""
    Tq = Fr(T).limit_denominator(10**4) + Fr(margin).limit_denominator(10**6); Nq = Fr(N).limit_denominator(10**4)
    m = {0: Nq - 1, 1: Fr(1)}; real = {1}; half = Fr(1, 2)
    for e in range(1, 7):
        b = 1 << e; sf = reqs[e - 1]; s = {}
        for J, mj in m.items():
            x = float(sf.get(J, 0.0))
            s[J] = mj if x >= float(mj) - 3e-5 else (Fr(0) if x < 3e-5 else Fr(x).limit_denominator(10**6))
        tot = sum(s.values()); assert tot <= Tq, f"over budget at reply {e+1}: {float(tot)}"
        a = {J: m[J] - s[J] for J in m}; slack = Nq - tot - 1; lam = 1 / (Nq - tot)
        ov = {J: Fr(0) for J in m}; left = slack
        for J in ORD[bits[e - 1]](sorted(m)):
            x = min(left, a[J]); ov[J] = x; left -= x
        assert left == 0
        m2 = {}
        for J in m:
            o = half * (1 - lam) * a[J] + half * ov[J]
            m2[J] = s[J] + o
            if a[J] > 0:
                real.add(J | b)
                if a[J] - o > 0: m2[J | b] = a[J] - o
        m = m2
        assert sum(v for J, v in m.items() if J & b) == 1
    best = None
    for drop in range(7):
        I = 127 & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        if best is None or D - Tq < best[0]: best = (D - Tq, drop + 1)
    return best

def load_plans(prefer=("cert_N2", "nb_0.log:N1.9", "swap_0.log:N1.8:w4", "nb_0.log:N2.0:[1.0, 1.0, 1.0, 1.0, 0", "nb_1.log:N2.0:[1.0, 0.0", "swap_1.log:N1.9:w5")):
    """Plans = (sets of types requested completely at each round, discard) read off every logged winning line."""
    import glob, fano_read, swap
    plans = []
    def add(hist, drop, tag):
        ref = [frozenset(J for J in mm if mm[J] > 2e-6 and mm[J] - ss.get(J, 0.0) < 2e-6) for mm, ss in hist]
        key = (tuple(ref), drop)
        if key not in [(tuple(p[0]), p[1]) for p in plans]: plans.append((ref, drop, tag))
    for f in ["cert_N2_T076.json"] + sorted(glob.glob("nb_[01].log")) + ["plan.log"]:
        for l in open(f):
            if not l.startswith("{"): continue
            d = json.loads(l)
            if d.get("sol") and d.get("z") is not None and d["z"] < -0.002:
                add(fano_read.simulate(d)[2], d["drop"][0], f"{f}:N{d['Ns'][0]}:{d.get('alphas')}")
    for f in sorted(glob.glob("swap_[01].log")):
        for l in open(f):
            d = json.loads(l)
            if d.get("sol") and d.get("exact_z_float") is not None and d["exact_z_float"] < 0:
                add(swap.simulate(d)[2], d["drop"][0], f"{f}:N{d['N']}:w{d['w']}")
    front = [p for pre in prefer for p in plans if p[2].startswith(pre)][:len(prefer)]
    return front + [p for p in plans if p not in front]

def build(T, N, log, tl=12):
    tree = {}; plans = load_plans()
    stats = dict(nodes=0, failed=[], zs={}, plans_used={})
    def rec(prefix, fixed):
        e = len(fixed)
        if e == 6: return
        key = "".join(prefix); best = None
        for idx in range(len(plans)):
            ref, drop, tag = plans[idx]
            st, zv, req = node_solve(T - MARGIN, N, prefix, fixed, tl, drop, ref)
            if zv is not None and (best is None or zv < best[0]): best = (zv, req, tag, idx)
            if zv is not None and zv < -0.004: break
        if best is None or best[0] > -1e-4:             # second chance: different plans for the two children
            top = plans[:PAIRK]
            for i, (r1, d1, t1) in enumerate(top):
                for j, (r2, d2, t2) in enumerate(top):
                    if i == j: continue
                    st, zv, req = node_solve(T - MARGIN, N, prefix, fixed, tl, d1, r1, r2, d2)
                    if zv is not None and (best is None or zv < best[0]): best = (zv, req, t1 + " | " + t2, i)
                    if zv is not None and zv < -0.004: break
                if best is not None and best[0] < -0.004: break
        stats["nodes"] += 1
        stats["zs"][key] = None if best is None else round(best[0], 5)
        log.write(json.dumps(dict(T=T, N=N, node=key, z=None if best is None else best[0], plan=None if best is None else best[2])) + chr(10)); log.flush()
        if best is None or best[0] > -1e-4:
            stats["failed"].append(key); return
        plans.insert(0, plans.pop(best[3]))            # move-to-front
        stats["plans_used"][best[2]] = stats["plans_used"].get(best[2], 0) + 1
        tree[key] = best[1]
        for bit in ("U", "O"): rec(prefix + [bit], fixed + [best[1]])
    rec([], [])
    return tree, stats

def verify(T, N, tree):
    import itertools
    won = 0; worst = None; missing = 0; detail = []
    for bits in itertools.product("UO", repeat=6):
        reqs = []
        for e in range(6):
            key = "".join(bits[:e])
            if key not in tree: reqs = None; break
            reqs.append(tree[key])
        if reqs is None: missing += 1; continue
        try:
            zq, drop = exact_leaf(T, N, bits, reqs)
        except AssertionError as ex:
            detail.append(("".join(bits), "error " + str(ex))); continue
        won += zq < 0
        if worst is None or zq > worst[0]: worst = (zq, "".join(bits), drop)
        detail.append(("".join(bits), float(zq), drop))
    return won, missing, worst, detail

def job(T, N):
    log = open(f"tilt_T{T}_N{N}.log", "a"); t0 = time.time()
    tree, stats = build(T, N, log)
    won, missing, worst, detail = verify(T, N, tree)
    summ = dict(SUMMARY=True, T=T, N=N, nodes=stats["nodes"], failed_nodes=stats["failed"], leaves_won_exact=won, leaves_missing=missing,
                worst_exact=None if worst is None else [float(worst[0]), worst[1], worst[2]], root_z=stats["zs"].get(""), plans_used=stats["plans_used"], secs=round(time.time() - t0), detail=detail)
    log.write(json.dumps(summ) + "\n"); log.flush()
    json.dump({k: {str(J): v for J, v in r.items()} for k, r in tree.items()}, open(f"tilt_tree_T{T}_N{N}.json", "w"))
    print(json.dumps({k: v for k, v in summ.items() if k != "detail"}), flush=True)

if __name__ == "__main__":
    if sys.argv[1] == "one":
        job(float(sys.argv[2]), float(sys.argv[3]))
    else:
        wk = int(sys.argv[1])
        jobs = [(0.76, 1.85), (0.76, 1.8), (0.76, 1.9), (0.76, 1.78), (0.751, 1.85), (0.751, 1.8), (0.751, 1.9), (0.751, 1.78)]
        for i, (T, N) in enumerate(jobs):
            if i % 2 == wk: job(T, N)
