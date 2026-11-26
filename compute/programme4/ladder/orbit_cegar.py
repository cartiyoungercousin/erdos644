r"""Rung 2 (and Rung 0 existence probes): G-invariant (7,2)-families with tau >= T+1, by CEGAR over orbits.
Co-edge form on V = [n]: co-edges are c-sets (c = n - k); the family has tau >= T+1 iff every T-set lies in a co-edge
(T-covering).  Good seven = at most 7 co-edges covering every pair of V (= at most 7 members with no 2-point
transversal).
Outer: SAT over orbit variables (one per G-orbit of c-sets), one covering clause per G-orbit of T-sets.  Each model is
shrunk greedily to a minimal covering union of orbits.  Inner: search the explicit family for a good seven, with the
first co-edge fixed to an orbit representative (valid: the family is G-invariant).  A good seven found is re-checked
by plain code and cut: "not all of these (<= 7) orbits".  UNSAT = no G-invariant T-covering family without a good
seven (cuts are valid by monotonicity: any invariant family containing those orbits contains the seven).
Usage: py orbit_cegar.py GROUP n c T [maxiter] [inner=dfs|cpsat] [seed]
  GROUP in: agl1_19, psl3_4, agl2_5, psl2_25, psl2_31, cyc15, ... (see groups_by_name)
Writes logs/oc_GROUP_n_c_T.log and, on a seven-free covering model, logs/oc_GROUP_n_c_T_family.txt.
"""
import sys, itertools, time, random, math, json, os
import numpy as np
from pysat.solvers import Solver
import groups as GR

HERE = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(HERE, "logs"), exist_ok=True)
G_ARR = [None]
NODE_LIMIT = int(os.environ.get("NODE_LIMIT", "2000000000"))


def groups_by_name(name):
    if name == "agl1_19": return GR.agl1(19)
    if name == "psl3_4": g, G, _, _ = GR.psl3_4(); return g, G
    if name == "agl2_5": return GR.agl2(5)
    if name == "psl2_25": return GR.psl2(5, 2, 2)
    if name == "psl2_31": return GR.psl2(31)
    if name.startswith("cyc"): return GR.cyclic(int(name[3:]))
    if name.startswith("agl1_"): return GR.agl1(int(name[5:]))
    raise ValueError(name)


def masks_of_size(n, s):
    N = math.comb(n, s)
    return np.sort(np.fromiter((sum(1 << x for x in cmb) for cmb in itertools.combinations(range(n), s)), dtype=np.int64, count=N))


def image(arr, g):
    out = np.zeros_like(arr)
    for x, gx in enumerate(g):
        out |= ((arr >> x) & 1) << gx
    return out


def orbits(arr, gens):
    """arr sorted int64 masks closed under the group; returns orbit label (0..O-1) per element and reps (min mask)."""
    N = len(arr); lab = np.arange(N, dtype=np.int64)
    idxs = []
    for g in gens:
        inv = [0] * len(g)
        for x, gx in enumerate(g): inv[gx] = x
        idxs.append(np.searchsorted(arr, image(arr, g))); idxs.append(np.searchsorted(arr, image(arr, inv)))
    while True:
        old = lab.copy()
        for ix in idxs:
            lab = np.minimum(lab, lab[ix])
        lab = lab[lab]
        if np.array_equal(lab, old): break
    uniq, oid = np.unique(lab, return_inverse=True)
    for ix in idxs: assert np.array_equal(oid[ix], oid)  # orbit labels are invariant under every generator
    return oid, arr[uniq]  # reps = smallest index = smallest mask in orbit (arr sorted)


def bits(m):
    return [x for x in range(m.bit_length()) if m >> x & 1]


def check_seven(blocks, n):
    cov = set()
    for B in blocks:
        bb = bits(B)
        for a, b in itertools.combinations(bb, 2): cov.add((a, b))
    return len(cov) == n * (n - 1) // 2


# ---------------- inner search: good seven in an explicit family (list of masks), first block among reps
def inner_dfs(fam, reps, n, maxm=7, node_limit=5 * 10 ** 6, rng=None, fam_oid=None, rep_oid=None):
    """Exact DFS (complete if node_limit not hit): choose blocks covering all pairs, <= maxm blocks.
    Block 1 ranges over reps; then repeatedly take the uncovered pair with fewest family members containing it and
    branch on those members.  Bound: uncovered pairs <= (remaining blocks) * C(c,2) and per-point:
    a point x with u_x uncovered partners needs ceil(u_x/(c-1)) more blocks through it."""
    c = bin(int(fam[0])).count("1"); cp = c * (c - 1) // 2
    P = [(a, b) for a in range(n) for b in range(a + 1, n)]; pid = {p: i for i, p in enumerate(P)}
    famL = [int(f) for f in fam]
    pairs_of = []
    for f in famL:
        bb = bits(f); pairs_of.append([pid[(a, b)] for a, b in itertools.combinations(bb, 2)])
    by_pair = [[] for _ in P]
    for j, ps in enumerate(pairs_of):
        for p in ps: by_pair[p].append(j)
    fidx = {f: j for j, f in enumerate(famL)}
    cnt = [0] * len(P); nodes = [0]; sol = []
    dead = set()  # orbits already shown to lie in no good seven (all reps tried before)
    foid = list(fam_oid) if fam_oid is not None else [0] * len(famL)
    unc = [len(P)]
    def add(j, d):
        for p in pairs_of[j]:
            if d > 0:
                if cnt[p] == 0: unc[0] -= 1
                cnt[p] += 1
            else:
                cnt[p] -= 1
                if cnt[p] == 0: unc[0] += 1
    def rec(left):
        nodes[0] += 1
        if nodes[0] > node_limit: raise TimeoutError
        if unc[0] == 0: return True
        if left == 0 or unc[0] > left * cp: return False
        # per point bound
        need = 0
        best = None; bestn = 10 ** 9
        ux = [0] * n
        for i, p in enumerate(P):
            if cnt[i] == 0:
                ux[p[0]] += 1; ux[p[1]] += 1
        for x in range(n):
            if -(-ux[x] // (c - 1)) > left: return False
        for i in range(len(P)):
            if cnt[i] == 0:
                l = len(by_pair[i])
                if l < bestn: bestn = l; best = i
        if bestn == 0: return False
        cands = [j for j in by_pair[best] if foid[j] not in dead]
        # order: most new pairs first
        sc = sorted(cands, key=lambda j: -sum(1 for p in pairs_of[j] if cnt[p] == 0))
        for j in sc:
            add(j, 1); sol.append(famL[j])
            if rec(left - 1): return True
            add(j, -1); sol.pop()
        return False
    for r in reps:
        j = fidx[int(r)]
        add(j, 1); sol.append(famL[j])
        try:
            if rec(maxm - 1): return list(sol), nodes[0]
        except TimeoutError:
            return None, -1
        add(j, -1); sol.pop()
        if rep_oid is not None: dead.add(rep_oid[reps.index(r)])
    return None, nodes[0]


def inner_heur(C, oidC, chs, repC, G_arr, n, rng, tries=200, sample=4000, maxm=7):
    """Randomised greedy search for a good seven in the G-invariant family = union of orbits chs (NOT exhaustive).
    Block 1 = an orbit representative; each next block = the best of `sample` random members (random orbit
    representative moved by a random group element) by number of newly covered pairs."""
    chs_arr = np.array(chs); reps = repC[chs_arr].astype(np.int64)
    rep_bits = np.array([[(int(r) >> x) & 1 for x in range(n)] for r in reps], dtype=np.int64)
    nr = np.random.default_rng(rng.randrange(1 << 30))
    full = (1 << n) - 1
    for t in range(tries):
        b0 = int(reps[t % len(reps)]); blocks = [b0]
        U = [full & ~(1 << x) for x in range(n)]  # uncovered partners
        def cover(B):
            for x in range(n):
                if B >> x & 1: U[x] &= ~B
        cover(b0)
        while len(blocks) < maxm and any(U):
            ri = nr.integers(0, len(reps), sample); gi = nr.integers(0, len(G_arr), sample)
            g = G_arr[gi]                      # sample x n images
            bitsm = rep_bits[ri]               # sample x n
            imgs = np.zeros(sample, dtype=np.int64)
            for x in range(n):
                imgs |= bitsm[:, x] << g[:, x]
            Ua = np.array(U, dtype=np.int64)
            score = np.zeros(sample, dtype=np.int64)
            for x in range(n):
                inx = (imgs >> x) & 1
                if Ua[x]:
                    score += inx * np.bitwise_count(imgs & Ua[x]).astype(np.int64)
            j = int(np.argmax(score))
            if score[j] == 0: break
            blocks.append(int(imgs[j])); cover(int(imgs[j]))
        if not any(U):
            return blocks, t + 1
    return None, tries


def inner_cpsat(fam, reps, n, m=7, workers=2, tl=None):
    from ortools.sat.python import cp_model
    c = bin(int(fam[0])).count("1"); rmin = -(-(n - 1) // (c - 1))
    md = cp_model.CpModel()
    y = [[md.NewBoolVar("") for i in range(m)] for x in range(n)]
    tup = [[(int(f) >> x) & 1 for x in range(n)] for f in fam]
    tupr = [[(int(f) >> x) & 1 for x in range(n)] for f in reps]
    for i in range(m):
        md.AddAllowedAssignments([y[x][i] for x in range(n)], tupr if i == 0 else tup)
    for x, z in itertools.combinations(range(n), 2):
        ps = []
        for i in range(m):
            p = md.NewBoolVar(""); ps.append(p); md.AddImplication(p, y[x][i]); md.AddImplication(p, y[z][i])
        md.AddBoolOr(ps)
    if m * c == rmin * n + (m * c - rmin * n):
        for x in range(n): md.Add(sum(y[x]) >= rmin)
    v = [sum((1 << (n - 1 - x)) * y[x][i] for x in range(n)) for i in range(m)]
    for i in range(1, m - 1): md.Add(v[i] >= v[i + 1] + 1)
    s = cp_model.CpSolver(); s.parameters.num_workers = workers
    if tl: s.parameters.max_time_in_seconds = tl
    st = s.Solve(md)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return [sum(1 << x for x in range(n) if s.Value(y[x][i])) for i in range(m)], s.StatusName(st)
    return None, s.StatusName(st)


def main():
    a = sys.argv[1:]
    gname, n, c, T = a[0], int(a[1]), int(a[2]), int(a[3])
    maxiter = int(a[4]) if len(a) > 4 else 10 ** 6
    inner = a[5] if len(a) > 5 else "dfs"
    seed = int(a[6]) if len(a) > 6 else 0
    rng = random.Random(seed)
    tag = f"oc_{gname}_{n}_{c}_{T}" + (f"_s{seed}" if seed else "")
    logf = open(os.path.join(HERE, "logs", tag + ".log"), "w")
    def log(*s):
        msg = " ".join(str(x) for x in s); print(msg, flush=True); logf.write(msg + "\n"); logf.flush()
    t0 = time.time()
    gens, G = groups_by_name(gname)
    G_ARR[0] = np.array(G, dtype=np.int64)
    log(f"group {gname}: order {len(G)} on {n} points; c={c} (k={n-c}), T={T} (tau target {T+1}), r={n-(n-c)-(T+1)+1}")
    assert len(gens[0]) == n
    C = masks_of_size(n, c); oidC, repC = orbits(C, gens); O = len(repC)
    sizes = np.bincount(oidC)
    log(f"c-set orbits: {O} (sizes min {sizes.min()} max {sizes.max()}), {time.time()-t0:.1f}s")
    Tm = masks_of_size(n, T); oidT, repT = orbits(Tm, gens)
    log(f"T-set orbits: {len(repT)}, {time.time()-t0:.1f}s")
    clauses = []
    for X in repT:
        X = int(X); comp = [x for x in range(n) if not X >> x & 1]
        sup = np.array([X | sum(1 << y for y in Y) for Y in itertools.combinations(comp, c - T)], dtype=np.int64)
        ids = sorted(set(oidC[np.searchsorted(C, sup)].tolist()))
        clauses.append(ids)
    log(f"covering clauses built: {len(clauses)}, mean length {np.mean([len(x) for x in clauses]):.1f}, {time.time()-t0:.1f}s")
    s = Solver(name="g4", with_proof=True)
    for cl in clauses: s.add_clause([o + 1 for o in cl])
    cuts = []; it = 0
    members_of = None
    while it < maxiter:
        it += 1
        if not s.solve():
            log(f"UNSAT after {it-1} cuts: no {gname}-invariant T-covering family without a good seven. {time.time()-t0:.1f}s")
            proof = s.get_proof()
            with open(os.path.join(HERE, "logs", tag + "_cert.json"), "w") as f:
                json.dump({"group": gname, "n": n, "c": c, "T": T, "gens": gens, "clauses": clauses, "cuts": cuts}, f)
            with open(os.path.join(HERE, "logs", tag + "_proof.drup"), "w") as f:
                f.write("\n".join(proof) + "\n")
            break
        model = s.get_model(); chosen = [o for o in range(O) if model[o] > 0]
        # shrink to a minimal covering union (random order)
        chs = set(chosen); cover_cnt = [sum(1 for o in cl if o in chs) for cl in clauses]
        occ = {}
        for ci, cl in enumerate(clauses):
            for o in cl:
                if o in chs: occ.setdefault(o, []).append(ci)
        order = list(chs); rng.shuffle(order)
        order.sort(key=lambda o: -sizes[o])  # try to drop big orbits first
        for o in order:
            if all(cover_cnt[ci] > 1 for ci in occ.get(o, [])):
                chs.discard(o)
                for ci in occ.get(o, []): cover_cnt[ci] -= 1
        chs = sorted(chs)
        fam = C[np.isin(oidC, chs)]
        reps = [int(repC[o]) for o in chs]
        t1 = time.time()
        if inner == "heur":
            sev, ntries = inner_heur(C, oidC, chs, repC, G_ARR[0], n, rng)
            status = "found" if sev else "heur-fail"
        elif inner == "js":
            fam_oid = oidC[np.isin(oidC, chs)].tolist(); famL = [int(f) for f in fam]
            pos = {f: i for i, f in enumerate(famL)}
            tmp = os.path.join(HERE, "logs", tag + "_inner.json")
            json.dump({"n": n, "m": 7, "fam": famL, "oid": fam_oid, "reps": [pos[r] for r in reps], "nodeLimit": NODE_LIMIT}, open(tmp, "w"))
            import subprocess
            for attempt in range(6):
                lim = NODE_LIMIT if attempt == 0 else NODE_LIMIT // 4
                json.dump({"n": n, "m": 7, "fam": famL, "oid": fam_oid, "reps": [pos[r] for r in reps], "nodeLimit": lim, "seed": attempt * 7919}, open(tmp, "w"))
                out = subprocess.run(["node", "--max-old-space-size=8000", os.path.join(HERE, "inner.js"), tmp], capture_output=True, text=True)
                res = json.loads(out.stdout.strip().splitlines()[-1])
                sev = res["seven"]; status = res["status"]; nodes = res["nodes"]
                if status != "limit": break
                log(f"  inner attempt {attempt}: node limit {lim} hit; retrying with shuffled order")
        elif inner == "dfs":
            fam_oid = oidC[np.isin(oidC, chs)]
            sev, nodes = inner_dfs(fam, reps, n, fam_oid=fam_oid.tolist(), rep_oid=chs)
            status = "found" if sev else ("limit" if nodes < 0 else "none")
        else:
            sev, status = inner_cpsat(fam, reps, n)
        if sev is None:
            log(f"iter {it}: minimal covering family of {len(chs)} orbits ({len(fam)} co-edges): inner {inner} -> {status} ({time.time()-t1:.1f}s)")
            if status in ("none", "INFEASIBLE"):
                if inner == "js": log(f"  exhaustive DFS: {nodes} nodes")
                fn = os.path.join(HERE, "logs", tag + "_family.txt")
                with open(fn, "w") as f:
                    for F in fam: f.write(" ".join(map(str, bits(int(F)))) + "\n")
                log(f"CANDIDATE seven-free covering family written to {fn}: VERIFY INDEPENDENTLY")
                break
            else:
                log("inner search inconclusive; stopping (obstacle)"); break
        famset = set(map(int, fam)) if inner != "heur" else None
        assert check_seven(sev, n) and (famset is None or all(int(B) in famset for B in sev))
        if inner == "heur": assert all(int(oidC[np.searchsorted(C, B)]) in set(chs) and int(C[np.searchsorted(C, B)]) == B for B in sev)
        os_ = sorted(set(int(oidC[np.searchsorted(C, B)]) for B in sev))
        cuts.append(os_); s.add_clause([-(o + 1) for o in os_])
        if True:
            log(f"iter {it}: family {len(chs)} orbits ({len(fam)} co-edges), seven over {len(os_)} orbits, inner {time.time()-t1:.1f}s, total {time.time()-t0:.0f}s")
    logf.close()


if __name__ == "__main__":
    main()
