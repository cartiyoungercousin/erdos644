"""§16(b): general best response vs the FIXED §14 tree along one label path.  Requests fixed per node (key = label prefix);
reply mass r_J (taken from type J, sum r = 1, r_J <= m_J - s_J) is FREE every round; discard = her best of 7 (adversary maximises the min).
usage: py mip_br.py LABELPATH tl [alpha_floor]   -> prints MILP value of mass(D)-T and exact replay of the extracted reply sequence."""
import sys, json, time, pulp
from fractions import Fraction as Fr
path = sys.argv[1]; tl = float(sys.argv[2]); T = 0.76; N = 1.8; EPS = 1e-4; ALPHA = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0; TLOW = T - 0.02; LAMLO = 1 / (N - TLOW)
tree = json.load(open("logs/adaptive_tree_full_T0.76_N1.8.json"))
prob = pulp.LpProblem("br", pulp.LpMaximize); cnt = [0]
def V(lo=0, hi=None, cat="Continuous"):
    cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
w = prob.add_variable("w", -1, 3); prob += w
m = {0: N - 1.0, 1: 1.0}; rho = {1: 1}; R = []; S = []
for e in range(1, 7):
    b = 1 << e; rq = {int(k): v for k, v in tree[path[:e - 1]].items()}; s = {}; r = {}
    for J, mj in m.items():
        x = rq.get(J, 0.0); ub = N if J == 0 else 1.0
        if x < 3e-5: s[J] = 0.0
        else:
            sj = V(0, min(ub, x)); c = V(cat="Binary"); s[J] = sj
            prob += sj <= mj; prob += sj >= mj - ub * (1 - c); prob += sj >= x - x * c
    if ALPHA > 0: prob += pulp.lpSum(s[J] for J in m) >= TLOW
    for J, mj in m.items():
        ub = N if J == 0 else 1.0; r[J] = V(0, 1.0); prob += r[J] <= mj - s[J]
        if ALPHA > 0: prob += r[J] <= (1 - ALPHA * (1 - LAMLO)) * (mj - s[J])
    prob += pulp.lpSum(r.values()) == 1
    m2, rho2 = {}, dict(rho)
    for J, mj in m.items():
        m2[J] = mj - r[J]; m2[J | b] = r[J]
        rr = V(cat="Binary"); prob += EPS * rr <= mj - s[J]; rho2[J | b] = rr
    R.append(r); S.append(s); m, rho = m2, rho2
for d in range(7):
    I = 127 & ~(1 << d); dvs = {}
    for P in range(128):
        if P & ~I: continue
        comp = I & ~P
        if comp == 0: dvs[P] = 1; continue
        dv = V(cat="Binary"); dvs[P] = dv
        prob += dv <= pulp.lpSum(rho[K] for K in rho if K and (K & comp) == comp)
    tot = []
    for J, mj in m.items():
        dl = dvs[J & I]
        if isinstance(dl, int): tot.append(mj)
        else:
            g = V(0, N); prob += g <= mj; prob += g <= (N if J == 0 else 1.0) * dl; tot.append(g)
    prob += w <= pulp.lpSum(tot)
t0 = time.time()
res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl, threads=1))
print(path, "status", res.status_str, "vars", cnt[0], "secs", round(time.time() - t0), flush=True)
if not res.has_solution: sys.exit()
print("MILP mass(D) - T =", pulp.value(w) - T, flush=True)
# exact replay with extracted replies (rounded to 1e-7)
Tq = Fr(76, 100); Nq = Fr(18, 10); mm = {0: Nq - 1, 1: Fr(1)}; real = {1}
for e in range(1, 7):
    b = 1 << e; rq = {int(k): v for k, v in tree[path[:e - 1]].items()}; s = {}
    for J, mj in mm.items():
        x = rq.get(J, 0.0)
        s[J] = mj if x >= float(mj) - 3e-5 else (Fr(0) if x < 3e-5 else Fr(x).limit_denominator(10**6))
    assert sum(s.values()) <= Tq
    a = {J: mm[J] - s[J] for J in mm}
    lamq = 1 / (Nq - sum(s.values())); capf = (1 - Fr(ALPHA) * (1 - lamq)) if ALPHA > 0 else Fr(1)
    rv = {J: min(a[J] * capf, Fr(round(pulp.value(R[e - 1][J]) * 10**7), 10**7)) for J in mm}
    deficit = 1 - sum(rv.values())
    for J in sorted(mm, key=lambda J: -(a[J] * capf - rv[J])):
        x = min(deficit, a[J] * capf - rv[J]); rv[J] += x; deficit -= x
        if deficit == 0: break
    assert deficit == 0
    if ALPHA > 0:
        lamq = 1 / (Nq - sum(s.values())); bad = [J for J in mm if a[J] - rv[J] < Fr(ALPHA) * (1 - lamq) * a[J]]
        print('  floor check (true lam) violations:', len(bad))
        assert not bad
    m2 = {}
    for J in mm:
        m2[J] = mm[J] - rv[J]
        if a[J] > 0: real.add(J | b)
        if rv[J] > 0: m2[J | b] = rv[J]
    mm = m2
    print("reply", e + 1, {J: round(float(v), 4) for J, v in rv.items() if v > 0})
best = None
for drop in range(7):
    I = 127 & ~(1 << drop)
    D = sum(mj for J, mj in mm.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
    if best is None or D - Tq < best[0]: best = (D - Tq, drop + 1)
print("EXACT replay: mass(D)-T = %.6f (best discard %d)" % (float(best[0]), best[1]), "ADVERSARY BEATS FIXED TREE" if best[0] > 0 else "requester wins")
