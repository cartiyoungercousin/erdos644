r"""SATURATION Task 1(c): can a near-pool family be saturated at a pool point?  [solver-only: HiGHS MILP; witnesses
re-checked by plain code]
Instance (k, T, n), c = n - k, pool Y with |Y| = w (default omega = n - k - T), near-pool space
M_{Y,eta} = {c-sets K : |Y - K| <= eta}.  A saturation witness at a pool incidence (y, B), B = V - K, y in Y - K, is
K' = K + {y} together with K_1..K_6 in M_{Y,eta} covering every pair of V (Lemma 4 / Cor. 5 of MINIMAL_FRAME), with
the necessary side conditions of a counterexample H containing K, K_1..K_6:
  (i)  K in M_{Y,eta}:  |Y - K'| <= eta - 1;
  (ii) y in U := U(K_1..K_6)  (else K, K_1..K_6 would already be good);
  (iii)|U| >= T + 1         (else T-covering gives K'' in H containing U and K_1..K_6, K'' is good in H).
Model: co-type counts a_I (points of V - Y) and b_I (points of Y), I a nonempty subset of {0..6}, member 0 = K'.
A configuration of counts with pairwise-intersecting support is exactly a good seven up to relabelling (FABLE_C 2.1-2.3).
Usage: py -3.14 nearpool_sat_milp.py k T n eta [w] [obj]   obj = min|max: optimise the number of K_1..K_6 missing y; minmiss: minimise the total pool misses of K_1..K_6
(= the number of the six edges B_1..B_6 through y)"""
import sys, itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
k, T, n, eta = map(int, sys.argv[1:5]); w = int(sys.argv[5]) if len(sys.argv) > 5 and int(sys.argv[5]) > 0 else n - k - T
obj = sys.argv[6] if len(sys.argv) > 6 else None
c = n - k; sizes = [c + 1] + [c] * 6
types = [I for I in range(1, 128)]
nt = len(types); idx = {}
def var(name):
    idx[name] = len(idx); return idx[name]
for I in types:
    for p in 'absuzd': var((p, I))
nv = len(idx); A = []; lo = []; hi = []
def row(coefs, l, h):
    r = np.zeros(nv)
    for key, v in coefs: r[idx[key]] += v
    A.append(r); lo.append(l); hi.append(h)
INF = np.inf
for I in types:
    row([(('a', I), 1), (('b', I), 1), (('s', I), -n)], -INF, 0)
    row([(('a', I), 1), (('b', I), 1), (('s', I), -1)], 0, INF)
    row([(('u', I), 1), (('s', I), -1)], -INF, 0)
    row([(('u', I), 1)] + [(('s', J), -1) for J in types if (I & J) & ~1 == 0], -INF, 0)
    row([(('z', I), 1), (('a', I), -1), (('b', I), -1)], -INF, 0)
    row([(('z', I), 1), (('u', I), -n)], -INF, 0)
    if I & 1:
        row([(('d', I), 1), (('b', I), -1)], -INF, 0)
        row([(('d', I), 1), (('u', I), -1)], -INF, 0)
    else:
        row([(('d', I), 1)], 0, 0)
for I, J in itertools.combinations(types, 2):
    if I & J == 0: row([(('s', I), 1), (('s', J), 1)], -INF, 1)
row([(('a', I), 1) for I in types], n - w, n - w)
row([(('b', I), 1) for I in types], w, w)
row([(('z', I), 1) for I in types], T + 1, INF)
row([(('d', I), 1) for I in types], 1, 1)
for i in range(7):
    row([(('a', I), 1) for I in types if I >> i & 1] + [(('b', I), 1) for I in types if I >> i & 1], sizes[i], sizes[i])
    row([(('b', I), 1) for I in types if I >> i & 1], w - eta + (1 if i == 0 else 0), INF)
lb = np.zeros(nv); ub = np.zeros(nv); integ = np.zeros(nv)
for (p, I), j in idx.items():
    ub[j] = {'a': n, 'b': w, 's': 1, 'u': 1, 'z': n, 'd': 1}[p]; integ[j] = 0 if p == 'z' else 1
cvec = np.zeros(nv)
if obj == 'minmiss':  # minimise total pool misses of K_1..K_6, i.e. maximise sum_i |Y & K_i| over i >= 1
    for I in types:
        cvec[idx[('b', I)]] = -sum(1 for i in range(1, 7) if I >> i & 1)
elif obj:
    for I in types:
        if I & 1: cvec[idx[('d', I)]] = (7 - bin(I).count('1')) * (1 if obj == 'min' else -1)
res = milp(c=cvec, constraints=LinearConstraint(np.array(A), lo, hi), integrality=integ, bounds=Bounds(lb, ub),
           options={'time_limit': 1800, 'disp': False})
print(f"(k,T,n)=({k},{T},{n}) c={c} |Y|={w} eta={eta} obj={obj}: status {res.status} {res.message}")
if res.x is None:
    print("RESULT: NO saturation witness at a pool point" + (" [solver-only, HiGHS proved infeasible]" if res.status == 2 else " (undecided)"))
    sys.exit()
x = np.round(res.x).astype(int)
pts = []  # (type, inY)
for I in types:
    pts += [(I, False)] * x[idx[('a', I)]] + [(I, True)] * x[idx[('b', I)]]
Ks = [{p for p, (I, _) in enumerate(pts) if I >> i & 1} for i in range(7)]
Y = {p for p, (I, iny) in enumerate(pts) if iny}
ok = len(pts) == n and all(len(Ks[i]) == sizes[i] for i in range(7))
ok &= all(any(u in K and v in K for K in Ks) for u in range(n) for v in range(u, n))
ok &= all(len(Y - Ks[i]) <= eta for i in range(1, 7)) and len(Y - Ks[0]) <= eta - 1
U = {u for u in range(n) if any(not any(u in K and v in K for K in Ks[1:]) for v in range(n))}
ys = [p for p in Y & Ks[0] if p in U]
ok &= len(U) >= T + 1 and len(ys) > 0
print("re-check by plain code:", ok, f"| |U(K_1..K_6)| = {len(U)}, pool points of K' in U: {len(ys)}")
for I in types:
    if x[idx[('a', I)]] or x[idx[('b', I)]]:
        print(f"  type {''.join(str(i) for i in range(7) if I >> i & 1):>8}: V' {x[idx[('a', I)]]:2d}  Y {x[idx[('b', I)]]:2d}  inU {x[idx[('u', I)]]}")
dI = [I for I in types if x[idx[('d', I)]]]
if dI:
    cand_y = [p for p in ys if pts[p][0] == dI[0]]
    assert cand_y, 'designated type not realised'
    ys = cand_y
print(f"  MILP objective {res.fun}; designated co-type {[i for i in range(7) if dI[0] >> i & 1]}")
y = ys[0]
print(f"  designated y has co-type {sorted(i for i in range(7) if y in Ks[i])}; members missing y among K_1..K_6: "
      f"{[i for i in range(1, 7) if y not in Ks[i]]}; Y-misses per member {[len(Y - K) for K in Ks]}")
print("RESULT: saturation witness EXISTS (local conditions (i)-(iii))" if ok else "RESULT: witness FAILED re-check")
