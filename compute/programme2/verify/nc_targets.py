"""Targeted checks for notes/PROGRAMME2_NC.md on Sym(X)xSym(Y)-invariant k-uniform families.

Family F(nx, ny, k, J) = all k-subsets A of X u Y (|X|=nx, |Y|=ny) with |A n X| in J.
 - tau, (W,d)-completeness: exact, by type enumeration.
 - NC1 hypothesis: min |W n (G1uG2uG3)| over triples with empty intersection, ILP over
   (part x containment-pattern) counts (HiGHS); cross-checked against the hand bound
   |U| >= 3k/2, |W n U| >= |U| - (n - w).
 - good seven: co-type ILP (all 127 co-types, pairwise-intersecting support); a feasible
   solution is rebuilt as 7 explicit sets and brute-force pair-checked.
"""
import itertools, sys, json, math
import pulp

def J_of(kind, nx, k):
    r = range(0, min(nx, k) + 1)
    if kind == "complete": return set(r)
    if kind == "odd": return {j for j in r if j % 2 == 1}
    if kind == "even": return {j for j in r if j % 2 == 0}
    raise ValueError

def contains_member(cx, cy, k, J):
    return any(j <= cx and k - j <= cy for j in J)

def tau(nx, ny, k, J):
    best = None
    for mx in range(nx + 1):
        for my in range(ny + 1):
            if not contains_member(nx - mx, ny - my, k, J):
                if best is None or mx + my < best: best = mx + my
    return best

def dmin(wx, wy, k, J):
    w = wx + wy
    for d in range(0, w - k + 1):
        ok = all(contains_member(ux, k + d - ux, k, J)
                 for ux in range(max(0, k + d - wy), min(wx, k + d) + 1))
        if ok: return d
    return None

PATS = [p for p in itertools.product((0, 1), repeat=3) if sum(p) < 3]

def nc1_min_union(nx, ny, wx, wy, k, J):
    parts = {"XW": wx, "XO": nx - wx, "YW": wy, "YO": ny - wy}
    pr = pulp.LpProblem("nc1", pulp.LpMinimize)
    n = {(q, p): pr.add_variable(f"n_{q}_{''.join(map(str,p))}", 0, parts[q], cat="Integer")
         for q in parts for p in PATS}
    for q in parts: pr += pulp.lpSum(n[q, p] for p in PATS) == parts[q]
    allJ = set(range(0, min(nx, k) + 1))
    for s in range(3):
        pr += pulp.lpSum(n[q, p] for q in parts for p in PATS if p[s]) == k
        if J != allJ:
            js = sorted(J)
            sel = [pr.add_variable(f"sel_{s}_{j}", cat="Binary") for j in js]
            pr += pulp.lpSum(sel) == 1
            pr += pulp.lpSum(n[q, p] for q in ("XW", "XO") for p in PATS if p[s]) == \
                  pulp.lpSum(j * v for j, v in zip(js, sel))
    pr += pulp.lpSum(n[q, p] for q in ("XW", "YW") for p in PATS if sum(p) > 0)
    st = pr.solve(pulp.HiGHS(msg=False))
    if st.status.name != "Optimal": return None
    return round(pulp.value(pr.objective))

def nc_status(nx, ny, k, J):
    """scan all W types; report whether Theorem NC / NC1 / NC0(a) hypotheses hold anywhere"""
    t = tau(nx, ny, k, J); thm = nc1 = nc0 = False; best = None
    for wx in range(nx + 1):
        for wy in range(ny + 1):
            w = wx + wy; d = dmin(wx, wy, k, J)
            if d is None or w < k + d + 2: continue
            a = max(0, 2 * k + 2 * d + 3 - w)
            if t > (k + 1) / 2 + a: thm = True
            if 4 * w >= 7 * (k + d) + 18: nc0 = True
            mu = nc1_min_union(nx, ny, wx, wy, k, J)
            hand = max(math.ceil(3 * k / 2) - (nx + ny - w), 0)
            assert mu is None or mu >= hand, ("ILP below hand bound", mu, hand)
            bound = 2 * (w - k - d) - 3
            slack = (bound - mu) if mu is not None else None
            if best is None or (slack is not None and slack > best[0]): best = (slack, wx, wy, d, mu, bound)
            if mu is not None and mu <= bound: nc1 = True
    return dict(tau=t, thmNC=thm, NC1=nc1, NC0a=nc0, best_slack=best)

def good_seven(nx, ny, k, J, timelimit=600):
    """co-type ILP; returns explicit seven (list of frozensets) or None (infeasible)"""
    cot = [I for r in range(1, 8) for I in itertools.combinations(range(7), r)]
    pr = pulp.LpProblem("g7", pulp.LpMinimize)
    x = {I: pr.add_variable("x_" + "".join(map(str, I)), 0, nx, cat="Integer") for I in cot}
    y = {I: pr.add_variable("y_" + "".join(map(str, I)), 0, ny, cat="Integer") for I in cot}
    s = {I: pr.add_variable("s_" + "".join(map(str, I)), cat="Binary") for I in cot}
    pr += pulp.lpSum([])
    pr += pulp.lpSum(x.values()) == nx
    pr += pulp.lpSum(y.values()) == ny
    for I in cot:
        pr += x[I] <= nx * s[I]; pr += y[I] <= ny * s[I]
    for I, K in itertools.combinations(cot, 2):
        if not set(I) & set(K): pr += s[I] + s[K] <= 1
    allJ = set(range(0, min(nx, k) + 1))
    for i in range(7):
        # slot i contains the points whose co-type avoids i
        pr += pulp.lpSum(x[I] + y[I] for I in cot if i not in I) == k
        if J != allJ:
            js = sorted(J); sel = [pr.add_variable(f"sl_{i}_{j}", cat="Binary") for j in js]
            pr += pulp.lpSum(sel) == 1
            pr += pulp.lpSum(x[I] for I in cot if i not in I) == pulp.lpSum(j * v for j, v in zip(js, sel))
    st = pr.solve(pulp.HiGHS(msg=False, timeLimit=timelimit))
    status = st.status.name
    if status != "Optimal": return status, None
    pts = []; vid = 0
    for I in cot:
        for _ in range(round(x[I].value())): pts.append(("X", vid, I)); vid += 1
    for I in cot:
        for _ in range(round(y[I].value())): pts.append(("Y", vid, I)); vid += 1
    seven = [frozenset(v for (_, v, I) in pts if i not in I) for i in range(7)]
    Xs = {v for (p, v, _) in pts if p == "X"}
    for B in seven: assert len(B) == k and len(B & Xs) in J
    allp = [v for (_, v, _) in pts]
    for u, v in itertools.combinations_with_replacement(allp, 2):
        assert any(u not in B and v not in B for B in seven), "pair check failed"
    return status, seven

if __name__ == "__main__":
    cases = json.loads(sys.argv[1]); do7 = len(sys.argv) < 3 or sys.argv[2] != "no7"
    for name, nx, ny, k, kind in cases:
        J = J_of(kind, nx, k); r = nc_status(nx, ny, k, J)
        line = dict(name=name, nx=nx, ny=ny, n=nx + ny, k=k, kind=kind, **r)
        if do7:
            st, sv = good_seven(nx, ny, k, J); line["good7"] = st if sv is None else "FOUND+checked"
        print(json.dumps(line), flush=True)
