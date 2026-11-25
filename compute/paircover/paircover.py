r"""CORE 117: fractional pair-cover rho* (exact rational bracket) and integral pair-cover rho (SAT, exact) of a co-edge family.
rho*  = min sum w_K  s.t. sum_{K >= {x,y}} w_K >= 1 for all pairs.  HiGHS float solve, then rational primal w and dual y
        (pair packing, sum over pairs inside each K <= 1) are rounded and repaired by scaling, and checked in Fractions:
        lo = sum y <= rho* <= sum w = hi; 'exact' when lo == hi.
rho   = least number of members covering all pairs: SAT (Cadical 1.9.5, seqcounter) for bound b = ceil(lo), ceil(lo)+1, ...
        with the implied constraints  r_x >= 3 when 2(c-1) < n-1  (a point in <= 2 members needs their union = V).
Usage: py -3.14 paircover.py famfile T [n] [sat_seconds]"""
import sys, itertools, time, math, threading
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
f = sys.argv[1]; T = int(sys.argv[2])
fam = [tuple(sorted(map(int, l.split()))) for l in open(f) if l.strip()]
fam = sorted(set(fam)); m = len(fam)
n = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != "-" else max(max(K) for K in fam) + 1
satsec = float(sys.argv[4]) if len(sys.argv) > 4 else 600
c = len(fam[0]); assert all(len(K) == c for K in fam); k = n - c
pairs = list(itertools.combinations(range(n), 2)); pid = {p: i for i, p in enumerate(pairs)}; P = len(pairs)
inK = [[pid[p] for p in itertools.combinations(K, 2)] for K in fam]
# T-covering check
cov = set()
for K in fam: cov.update(itertools.combinations(K, T))
unc = math.comb(n, T) - len(cov)
print(f"{f}: m={m} members of size c={c}, n={n}, k={k}, T={T}; uncovered T-sets: {unc}")
low = F(n * (n - 1), c * (c - 1)); rnd = F(n * (n - 1), T * (T - 1)); poolv = F((k + T) * (k + T - 1), T * (T - 1))
print(f"  bounds: C(n,2)/C(c,2) = {float(low):.4f}   random-T n(n-1)/(T(T-1)) = {float(rnd):.4f}   pool value (k+T)(k+T-1)/(T(T-1)) = {float(poolv):.4f}")
A = lil_matrix((P, m))
for j, ps in enumerate(inK):
    for i in ps: A[i, j] = 1
A = csr_matrix(A)
r = linprog(np.ones(m), A_ub=-A, b_ub=-np.ones(P), bounds=(0, None), method="highs")
w = r.x; y = -r.ineqlin.marginals
def rat(v, D): return [F(max(x, 0)).limit_denominator(D) for x in v]
def exact_basic(A_rows, cols, rhs):
    """solve the square-or-tall system A_rows[:, cols] w = rhs exactly (Fractions, Gauss-Jordan); None if singular/inconsistent"""
    M = [[F(1) if j in r else F(0) for j in cols] + [F(rhs)] for r in A_rows]; nc = len(cols); piv = []; row = 0
    for col in range(nc):
        p = next((i for i in range(row, len(M)) if M[i][col] != 0), None)
        if p is None: continue
        M[row], M[p] = M[p], M[row]; pv = M[row][col]; M[row] = [x / pv for x in M[row]]
        for i in range(len(M)):
            if i != row and M[i][col] != 0:
                f_ = M[i][col]; M[i] = [a - f_ * b for a, b in zip(M[i], M[row])]
        piv.append(col); row += 1
        if row == len(M): break
    if any(all(x == 0 for x in M[i][:nc]) and M[i][nc] != 0 for i in range(len(M))): return None
    sol = [F(0)] * nc
    for i, col in enumerate(piv): sol[col] = M[i][nc]
    return sol
def certify(xv, inK, P, m, tol=1e-9):
    """exact primal cover from the float optimum: support columns, rows tight in float; returns exact total or None"""
    supp = [j for j in range(m) if xv[j] > tol]
    cvf = np.zeros(P)
    for j in supp:
        for i in inK[j]: cvf[i] += xv[j]
    tight = [i for i in range(P) if cvf[i] < 1 + 1e-7]
    sets = [set(jj for jj, j in enumerate(supp) if i in inKs[j]) for i in tight]
    sol = exact_basic(sets, list(range(len(supp))), 1)
    if sol is None or min(sol) < 0: return None
    cv = [F(0)] * P
    for jj, j in enumerate(supp):
        for i in inK[j]: cv[i] += sol[jj]
    return sum(sol) if min(cv) >= 1 else None
inKs = [set(ps) for ps in inK]
best = None
for D in (60, 840, 5040, 10 ** 5, 10 ** 7):
    W = rat(w, D); Y = rat(y, D)
    cv = [F(0)] * P
    for j, ps in enumerate(inK):
        if W[j]:
            for i in ps: cv[i] += W[j]
    mc = min(cv); hi = sum(W) / mc
    ld = max(sum((Y[i] for i in ps), F(0)) for ps in inK); lo = sum(Y) / ld
    if best is None or hi - lo < best[1] - best[0]: best = (lo, hi, D)
    if lo == hi: break
lo, hi, D = best
if lo != hi:
    ex = certify(w, inK, P, m)
    if ex is not None and ex < hi: hi = ex
fs_ = lambda q: str(q) if q.denominator < 10 ** 6 else "%.9f" % float(q)
supp = sum(1 for x in w if x > 1e-9)
print(f"  rho*: float {r.fun:.6f};  exact bracket [{fs_(lo)}, {fs_(hi)}] = [{float(lo):.6f}, {float(hi):.6f}] {'EXACT' if lo == hi else ''} (denominators <= {D}); primal support {supp}")
pt = [sum(w[j] for j, K in enumerate(fam) if x in K) for x in range(n)]
print(f"  optimal w: point loads r_x in [{min(pt):.4f}, {max(pt):.4f}] (sum {sum(pt):.4f} = c*rho*); integral cover needs >= 3 each when 2(c-1) < n-1")
# degree cut: in an integral cover a point in <= 2 members needs their union = V, impossible when 2c < n + 1 [proved]
need3 = 2 * (c - 1) < n - 1
if need3:
    Dg = lil_matrix((n, m))
    for j, K in enumerate(fam):
        for x in K: Dg[x, j] = 1
    from scipy.sparse import vstack
    r3 = linprog(np.ones(m), A_ub=-vstack([A, csr_matrix(Dg)]), b_ub=-np.concatenate([np.ones(P), 3 * np.ones(n)]), bounds=(0, None), method="highs")
    print(f"  rho*_3 (pair cover + every point in weight >= 3): float {r3.fun:.6f}; trivial floor 3n/c = {3*n/c:.4f}")
else: print("  degree cut not valid here (2c >= n + 1)")
# integral rho by SAT
pc = [[j + 1 for j in range(m) if x in fam[j] and z in fam[j]] for x, z in pairs]
pts = [[j + 1 for j in range(m) if x in fam[j]] for x in range(n)]
b = max(math.ceil(lo), math.ceil(F(3 * n, c)) if need3 else 1, 1); rho = None
if len(sys.argv) > 5 and sys.argv[5].isdigit(): b = int(sys.argv[5])
if len(sys.argv) > 5 and sys.argv[5] == 'lp': b = 99
while rho is None and b <= 20:
    top = m; cl = []
    cnf = CardEnc.atmost(lits=list(range(1, m + 1)), bound=b, top_id=top, encoding=EncType.seqcounter); cl += cnf.clauses; top = max(top, cnf.nv)
    if need3:
        for L in pts:
            e = CardEnc.atleast(lits=L, bound=3, top_id=top, encoding=EncType.seqcounter); cl += e.clauses; top = max(top, e.nv)
    s = Cadical195(bootstrap_with=cl)
    for L in pc: s.add_clause(L)
    t0 = time.time(); tm = threading.Timer(satsec, s.interrupt); tm.start()
    ok = s.solve_limited(expect_interrupt=True); tm.cancel(); dt = time.time() - t0
    if ok is None: print(f"  SAT b={b}: TIMEOUT after {dt:.0f}s"); break
    if ok:
        ch = [fam[v - 1] for v in s.get_model() if 0 < v <= m]
        assert len(ch) <= b and all(any(x in K and z in K for K in ch) for x, z in pairs)
        rho = len(ch); print(f"  SAT b={b}: cover of size {rho} found, checked ({dt:.1f}s):", " ".join("{" + ",".join(map(str, K)) + "}" for K in ch))
    else: print(f"  SAT b={b}: UNSAT ({dt:.1f}s)"); b += 1
    s.delete()
if rho: print(f"  RESULT rho = {rho}, rho* = {float(lo):.6f}{'' if lo == hi else '..%.6f' % float(hi)}, gap rho/rho* = {rho / float(hi):.4f}{'' if lo == hi else '..%.4f' % (rho / float(lo))}, good seven: {'YES' if rho <= 7 else 'NO'}")
else: print(f"  RESULT rho undecided (>= {b}), rho* = [{float(lo):.6f}, {float(hi):.6f}]")
