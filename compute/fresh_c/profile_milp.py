"""
Scale-free block-symmetric ("profile") families for Erdos #644.

Ground set V = V_1 u ... u V_m, |V_j| = n_j * k  (n_j real, k -> infinity).
Family H(P) = all k-sets A whose profile a = (|A n V_j|/k)_j lies in P,
P = union of boxes {lo_r <= a <= hi_r, sum a = 1}.

bad7(n, boxes): MILP deciding whether 7 edges with profiles in P can be placed with
  M-family (M(x) = {i : x not in A_i}) pairwise intersecting (=> NOT 2-coverable).
  Variables: z_S (S nonempty subset of [7]) = membership in a maximal intersecting family
  (monotone, z_S + z_{S^c} = 1), w[j][S] = measure of points of block j with M(x) = S.
tau(n, boxes): MILP for min sum t such that no box has a profile a <= n - t  (closed limit).
"""
import pulp, itertools, sys, time

FULL = 127
SUBS = list(range(1, 128))

def solver(tl=120, msg=False):
    return pulp.HiGHS(msg=msg, timeLimit=tl)

def bad7(n, boxes, enlarge=0.0, tl=120, forced_types=None, msg=False, want_witness=True):
    m = len(n)
    prob = pulp.LpProblem("bad7", pulp.LpMinimize)
    z = {}
    for S in SUBS:
        if S == FULL:
            continue
        c = FULL ^ S
        if S < c:
            z[S] = prob.add_variable(f"z{S}", cat="Binary")
    def Z(S):
        if S == FULL: return 1
        c = FULL ^ S
        return z[S] if S < c else 1 - z[c]
    # monotone
    for S in SUBS:
        if S == FULL: continue
        for i in range(7):
            if not (S >> i) & 1:
                T = S | (1 << i)
                if T != FULL:
                    prob += Z(S) <= Z(T)
    w = {(j, S): prob.add_variable(f"w{j}_{S}", lowBound=0, upBound=n[j]) for j in range(m) for S in SUBS}
    for j in range(m):
        prob += pulp.lpSum(w[j, S] for S in SUBS) == n[j]
        for S in SUBS:
            if S != FULL:
                prob += w[j, S] <= n[j] * Z(S)
    a = {}
    for i in range(7):
        for j in range(m):
            a[i, j] = n[j] - pulp.lpSum(w[j, S] for S in SUBS if (S >> i) & 1)
        prob += pulp.lpSum(a[i, j] for j in range(m)) == 1
    R = len(boxes)
    u = {(i, r): prob.add_variable(f"u{i}_{r}", cat="Binary") for i in range(7) for r in range(R)}
    BIG = max(n) + 1
    for i in range(7):
        prob += pulp.lpSum(u[i, r] for r in range(R)) == 1
        for r, (lo, hi) in enumerate(boxes):
            for j in range(m):
                prob += a[i, j] >= lo[j] - enlarge - BIG * (1 - u[i, r])
                prob += a[i, j] <= hi[j] + enlarge + BIG * (1 - u[i, r])
    if forced_types is not None:
        for i, r in enumerate(forced_types):
            prob += u[i, r] == 1
    else:
        for i in range(6):
            prob += pulp.lpSum(r * u[i, r] for r in range(R)) <= pulp.lpSum(r * u[i + 1, r] for r in range(R))
        res = prob.solve(solver(tl, msg))
    st = res.status_str
    if res.has_solution and st != "Optimal":
        st = "Optimal"
    if st == "Optimal" and want_witness:
        prof = [[pulp.value(a[i, j]) for j in range(m)] for i in range(7)]
        types = [max(range(R), key=lambda r: pulp.value(u[i, r])) for i in range(7)]
        supp = {j: {S: round(pulp.value(w[j, S]), 5) for S in SUBS if pulp.value(w[j, S]) > 1e-7} for j in range(m)}
        return True, dict(profiles=prof, types=types, supp=supp)
    if st == "Infeasible":
        return False, None
    return None, st

def tau(n, boxes, tl=60):
    """min sum t s.t. every box is killed: exists j with t_j >= n_j - lo_rj, or sum_j min(hi_rj, n_j - t_j) <= 1,
    (closed versions; also box must be nonempty to matter)."""
    m = len(n)
    prob = pulp.LpProblem("tau", pulp.LpMinimize)
    t = [prob.add_variable(f"t{j}", lowBound=0, upBound=n[j]) for j in range(m)]
    prob += pulp.lpSum(t)
    BIG = sum(n) + 2
    for r, (lo, hi) in enumerate(boxes):
        if sum(lo) > 1 + 1e-12 or sum(min(hi[j], n[j]) for j in range(m)) < 1 - 1e-12:
            continue
        modes = [prob.add_variable(f"k{r}_{j}", cat="Binary") for j in range(m + 1)]
        prob += pulp.lpSum(modes) >= 1
        for j in range(m):
            prob += t[j] >= (n[j] - lo[j]) + 1e-4 - BIG * (1 - modes[j])
        v = [prob.add_variable(f"v{r}_{j}", lowBound=0) for j in range(m)]
        b = [prob.add_variable(f"b{r}_{j}", cat="Binary") for j in range(m)]
        for j in range(m):
            prob += v[j] >= min(hi[j], n[j]) - BIG * b[j]
            prob += v[j] >= n[j] - t[j] - BIG * (1 - b[j])
        prob += pulp.lpSum(v) <= 1 - 1e-4 + BIG * (1 - modes[m])
    prob.solve(solver(tl))
    return pulp.value(prob.objective), [pulp.value(x) for x in t]

def show(S):
    return "".join(str(i + 1) for i in range(7) if (S >> i) & 1)

def report(n, boxes, enlarge=0.0, tl=120):
    tv, tt = tau(n, boxes)
    t0 = time.time()
    bad, wit = bad7(n, boxes, enlarge=enlarge, tl=tl)
    print(f"n={n} boxes={boxes} tau={tv:.4f} t*={[round(x,3) for x in tt]} bad={bad} ({time.time()-t0:.1f}s)")
    if bad:
        print("  types", wit["types"], "profiles", [[round(x, 3) for x in p] for p in wit["profiles"]])
        for j, d in wit["supp"].items():
            print("  block", j, {show(S): v for S, v in d.items()})
    elif bad is None:
        print("  status", wit)
    sys.stdout.flush()
    return tv, bad

if __name__ == "__main__":
    report([1.74], [([1.0], [1.0])])
    # two symmetric blocks, two pure types
    for h, al in [(1.0, 0.6), (1.0, 0.68), (1.05, 0.71), (1.08, 0.73), (1.15, 0.77), (1.2, 0.81)]:
        be = min(1.0, h)
        report([h, h], [([al, 0], [be, 1 - al]), ([0, al], [1 - al, be])])
