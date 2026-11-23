"""Path 4 / soundness: overlapped two-cluster families H2(alpha,o,beta), continuum model (k = 1).
Blocks A (|A|=alpha), O (|O|=o), B (|B|=beta); edges = all k-sets inside A∪O or inside O∪B.
tau/k = min_c  c + (alpha+o-c-1)^+ + (beta+o-c-1)^+ ,  0 <= c <= o.
(7,2) fails iff for some i there is a bad 7-tuple with i edges in A∪O and 7-i in O∪B:
  masses m[block, K] (K = membership set), y[K] = 1 if K is used anywhere,
  y[K]+y[K'] <= 1 when K ∪ K' = [7]; every edge has mass 1; block capacities.
Floating MILP (HiGHS): 'bad tuple found' is a witness; 'none' is numerical evidence only.
"""
import sys, itertools, pulp
FULL = 127
PAIRS = [(K, L) for K in range(1, 128) for L in range(K, 128) if K | L == FULL]
def has_bad(alpha, o, beta, i):
    T1 = (1 << i) - 1; T2 = FULL ^ T1
    p = pulp.LpProblem("bad", pulp.LpMinimize)
    y = {K: p.add_variable(f"y{K}", cat="Binary") for K in range(1, 128)}
    m = {}
    for blk, allowed, cap in (("A", T1, alpha), ("O", FULL, o), ("B", T2, beta)):
        vs = []
        for K in range(1, 128):
            if K & ~allowed: continue
            v = p.add_variable(f"m{blk}{K}", 0, 1); m[blk, K] = v; vs.append(v)
            p += v <= y[K]
        p += pulp.lpSum(vs) <= cap
    for K, L in PAIRS:
        p += (y[K] <= 0) if K == L else (y[K] + y[L] <= 1)
    for j in range(7):
        p += pulp.lpSum(v for (blk, K), v in m.items() if K >> j & 1) == 1
    p += pulp.lpSum(y.values())
    st = p.solve(pulp.HiGHS(msg=False, threads=1, timeLimit=60))
    if st.status.name == "Infeasible": return False
    if not st.has_solution: raise RuntimeError(st.status.name)
    return True
def tau(alpha, o, beta):
    cands = {0.0, o, min(o, max(0.0, alpha + o - 1)), min(o, max(0.0, beta + o - 1))}
    return min(c + max(0, alpha + o - c - 1) + max(0, beta + o - c - 1) for c in cands)
def is72(alpha, o, beta):
    if alpha + o >= 1.75 or beta + o >= 1.75: return False          # contains a complete family with a Fano tuple
    if (beta >= 1.2 and alpha >= 1) or (alpha >= 1.2 and beta >= 1): return False   # 6 + 1 on disjoint parts
    return not any(has_bad(alpha, o, beta, i) for i in (1, 6, 2, 5, 3, 4, 0, 7))
if __name__ == "__main__":
    step = float(sys.argv[1]) if len(sys.argv) > 1 else 0.1
    n = round(2 / step); best = (0, None); rows = []
    for ia in range(0, n + 1):
        for ib in range(ia, n + 1):
            for io in range(0, n + 1):
                a, b, o = ia * step, ib * step, io * step
                if b + o < 1: continue
                tv = tau(a, o, b)
                if tv <= best[0] + 1e-9 or tv <= 0.6: continue      # only look for improvements
                if is72(a, o, b):
                    best = (tv, (a, o, b)); print("new best (7,2):", round(tv, 4), (round(a,3), round(o,3), round(b,3)), flush=True)
    print("max tau/k over (7,2) overlapped two-cluster families on this grid (only values > 0.6 searched):", best)
