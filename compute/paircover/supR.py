r"""CORE 116: R(n,c,T) = sup over T-covering families of c-sets on [n] of rho*(family)   [computed exact by MILP; float LP inside]
1/R = theta* = min over prob. mu on pairs of  max_S min_{K>=S, |K|=c} mu(K)   (S a T-set, mu(K) = sum of mu over pairs in K).
MILP: z >= mu(K_{S,E}) - (1 - b_{S,E}), sum_E b_{S,E} = 1.  Also: ascent heuristic (best-response families) for larger n.
Usage: py -3.14 supR.py n c T [mip|ascent] [seed]"""
import sys, itertools, random, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds, linprog
from scipy.sparse import lil_matrix, csr_matrix
n, c, T = map(int, sys.argv[1:4]); mode = sys.argv[4] if len(sys.argv) > 4 else "mip"
pairs = list(itertools.combinations(range(n), 2)); pid = {p: i for i, p in enumerate(pairs)}; P = len(pairs)
Ts = list(itertools.combinations(range(n), T))
def pk(K): return [pid[p] for p in itertools.combinations(sorted(K), 2)]
pool = (n - c + T) * (n - c + T - 1) / (T * (T - 1)); rnd = n * (n - 1) / (T * (T - 1)); low = n * (n - 1) / (c * (c - 1))
print(f"n={n} c={c} T={T}: lower C(n,2)/C(c,2) = {low:.4f}; pool (k+T)(k+T-1)/(T(T-1)) = {pool:.4f}; random-T bound = {rnd:.4f}")
def rhostar(fam):
    fam = list(fam); A = lil_matrix((P, len(fam)))
    for j, K in enumerate(fam):
        for i in pk(K): A[i, j] = 1
    r = linprog(np.ones(len(fam)), A_ub=-csr_matrix(A), b_ub=-np.ones(P), bounds=(0, None), method="highs")
    return r.fun, -r.ineqlin.marginals
if mode == "mip":
    ext = [[tuple(sorted(S + E)) for E in itertools.combinations([x for x in range(n) if x not in S], c - T)] for S in Ts]
    nb = sum(len(e) for e in ext); nv = P + 1 + nb   # mu, z, b
    rows = []; lo = []; hi = []
    A = lil_matrix((1 + len(Ts) + nb, nv)); r = 0
    for i in range(P): A[r, i] = 1
    lo.append(1); hi.append(1); r += 1
    bj = P + 1
    for s, e in enumerate(ext):
        for K in e: A[r, bj] = 1; bj += 1
        lo.append(1); hi.append(1); r += 1
    bj = P + 1
    for s, e in enumerate(ext):
        for K in e:   # z - mu(K) - b >= -1
            A[r, P] = 1
            for i in pk(K): A[r, i] -= 1
            A[r, bj] = -1; lo.append(-1); hi.append(np.inf); r += 1; bj += 1
    cost = np.zeros(nv); cost[P] = 1
    integ = np.zeros(nv); integ[P + 1:] = 1
    res = milp(cost, constraints=LinearConstraint(csr_matrix(A), lo, hi), integrality=integ,
               bounds=Bounds(np.zeros(nv), np.ones(nv)), options={"time_limit": float(sys.argv[5]) if len(sys.argv) > 5 else 3000, "disp": False})
    print("MILP status:", res.status, res.message, " theta* =", res.fun, " R = 1/theta* =", 1 / res.fun if res.fun else None,
          " dual bound theta >=", getattr(res, "mip_dual_bound", None))
    mu = res.x[:P]; fam = set(); bj = P + 1
    for e in ext:
        for K in e:
            if res.x[bj] > .5: fam.add(K)
            bj += 1
    val, y = rhostar(fam); print(f"check: best-response family has {len(fam)} members, rho* = {val:.6f}")
    sup = sorted([(mu[i], pairs[i]) for i in range(P) if mu[i] > 1e-7], reverse=True)
    print("mu support:", len(sup), " values:", sorted(set(round(v, 5) for v, _ in sup)))
    print("mu-heavy pairs:", sup[:12])
    deg = np.zeros(n)
    for v, (a, b) in sup: deg[a] += v; deg[b] += v
    print("mu-degrees:", np.round(deg, 4))
else:   # ascent: alternate best-response family and optimal dual mu, random restarts
    rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 0); best = 0
    for rep in range(int(sys.argv[6]) if len(sys.argv) > 6 else 5):
        mu = np.array([rng.random() ** 3 for _ in range(P)]); mu /= mu.sum()
        last = -1
        for it in range(40):
            fam = set()
            for S in Ts:
                outs = [x for x in range(n) if x not in S]; bv = 9; bK = None
                for E in itertools.combinations(outs, c - T):
                    K = tuple(sorted(S + E)); v = mu[pk(K)].sum() + 1e-9 * rng.random()
                    if v < bv: bv, bK = v, K
                fam.add(bK)
            val, y = rhostar(fam)
            if val <= last + 1e-9: break
            last = val; mu = np.maximum(y, 0); mu /= mu.sum()
        best = max(best, last); print(f"restart {rep}: rho* reached {last:.6f} ({len(fam)} members)  best so far {best:.6f}", flush=True)
