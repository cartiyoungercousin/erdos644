"""§11 side check C: block-type 'core + pool' families, continuum model (k = 1).
Blocks W0 (size w), P (size p). Edge types: 'core' = k-set inside W0; 'pool' = c points in W0 and
1-c in P.  H(w,p,c) = all edges of both types.
tau = (w-1) + min(1-c, max(0, p-(1-c)))          (kill the core, then the cheaper way to kill pool edges)
(7,2) fails iff for some j there is a bad 7-tuple with j pool edges (MILP as in overlap_family.py).
Floating MILP: a bad tuple is a witness; 'none found' is numerical."""
import sys, pulp
FULL = 127
PAIRS = [(K, L) for K in range(1, 128) for L in range(K, 128) if K | L == FULL]
def has_bad(w, p, c, j):
    pool = (1 << j) - 1                                   # edges 0..j-1 are pool edges
    pr = pulp.LpProblem("bad", pulp.LpMinimize)
    y = {K: pr.add_variable(f"y{K}", cat="Binary") for K in range(1, 128)}
    mW = {K: pr.add_variable(f"w{K}", 0, 2) for K in range(1, 128)}
    mP = {K: pr.add_variable(f"p{K}", 0, 2) for K in range(1, 128) if not (K & ~pool)}
    for K in mW: pr += mW[K] <= 2 * y[K]
    for K in mP: pr += mP[K] <= 2 * y[K]
    pr += pulp.lpSum(mW.values()) <= w; pr += pulp.lpSum(mP.values()) <= p
    for K, L in PAIRS: pr += (y[K] <= 0) if K == L else (y[K] + y[L] <= 1)
    for i in range(7):
        inW = pulp.lpSum(v for K, v in mW.items() if K >> i & 1)
        if i < j:
            pr += inW == c; pr += pulp.lpSum(v for K, v in mP.items() if K >> i & 1) == 1 - c
        else:
            pr += inW == 1
    pr += pulp.lpSum(y.values())
    st = pr.solve(pulp.HiGHS(msg=False, threads=1, timeLimit=60))
    if st.status.name == "Infeasible": return False
    if not st.has_solution: raise RuntimeError(st.status.name)
    return True
def tau(w, p, c):
    core = max(0.0, w - 1) if w >= 1 else 0.0
    if p < 1 - c or w < c: return core                    # no pool edges
    if w < 1: return min(w - c, p - (1 - c))              # no core edges
    return core + min(1 - c, p - (1 - c))
if __name__ == "__main__":
    best = (0, None); rows = 0
    for c in (0.25, 0.4, 0.5, 0.6, 0.75):
        for w10 in range(8, 18):
            for p10 in range(2, 16):
                w, p = w10 / 10, p10 / 10
                tv = tau(w, p, c)
                if tv <= max(best[0], 0.5) + 1e-9: continue
                rows += 1
                if not any(has_bad(w, p, c, j) for j in (0, 1, 2, 3, 4, 5, 6, 7)):
                    best = (tv, (w, p, c)); print("new best (7,2):", best, flush=True)
    print("candidates tested:", rows, "| best (7,2) core+pool family with tau/k > 0.5:", best)
