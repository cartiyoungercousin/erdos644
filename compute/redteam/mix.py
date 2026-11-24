r"""RED TEAM: neighbourhood of the proportional adversary.  Reply at round e =
     alpha_e * (proportional reply)  +  (1 - alpha_e) * (vertex reply: omit the slack greedily in a fixed order),
i.e. omission  o_J = alpha_e (1-lam_e) a_J + (1-alpha_e) o^vertex_J.  alpha = 1: prop.py; alpha = 0: C's scripts.
Orders: LOW (omit lowest degree first, pool first), HIGH (highest degree first), GIFT (pool last, then low degree).
Requester exactly optimal (MILP), full budget; terminal as in prop.py; `drops` restricts her discard
(a restriction on her, so a negative value is still a requester win).
"""
import pulp, sys, time, json
def popc(x): return bin(x).count("1")
ORD = {"LOW": lambda ty: sorted(ty, key=lambda J: (popc(J), J)),
       "HIGH": lambda ty: sorted(ty, key=lambda J: (-popc(J), J)),
       "GIFT": lambda ty: sorted(ty, key=lambda J: (J == 0, popc(J), J))}
def solve(T, Ns, alphas, order="LOW", tl=300, drops=None, msg=False):
    E = len(Ns); NM = max(Ns)
    prob = pulp.LpProblem("mix", pulp.LpMinimize); cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    m = {0: Ns[0] - 1.0, 1: 1.0}; rho = {1: 1}; hist = []
    for e in range(1, E):
        b = 1 << e; m[0] = m[0] + (Ns[e] - Ns[e - 1]); lam = 1.0 / (Ns[e] - T); al = alphas[e - 1]
        slack = Ns[e] - T - 1.0
        types = sorted(m); ub = {J: (1.0 if J else NM) for J in types}
        s = {J: V(0, ub[J]) for J in types}
        for J in types: prob += s[J] <= m[J]
        prob += pulp.lpSum(s.values()) == T
        a = {J: m[J] - s[J] for J in types}
        ov = {J: 0 for J in types}
        if al < 1 and slack > 1e-9:
            ov = {J: V(0, ub[J]) for J in types}
            for J in types: prob += ov[J] <= a[J]
            prob += pulp.lpSum(ov.values()) == slack
            pre = []
            for J in ORD[order](types):
                pre.append(J); g = V(cat="Binary")
                prob += a[J] - ov[J] <= ub[J] * g
                prob += slack - pulp.lpSum(ov[K] for K in pre) <= slack * (1 - g)
        m2, rho2 = {}, dict(rho)
        for J in types:
            o = al * (1 - lam) * a[J] + (1 - al) * ov[J]
            m2[J] = s[J] + o; m2[J | b] = a[J] - o
            r = V(cat="Binary"); prob += a[J] <= ub[J] * r; rho2[J | b] = r
        hist.append(s); m, rho = m2, rho2
    full = (1 << E) - 1; picks = []
    for drop in range(E):
        if drops is not None and drop + 1 not in drops: continue
        I = full & ~(1 << drop); pick = V(cat="Binary"); picks.append((drop, pick)); delta = {}
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
                d = V(0, NM); prob += d >= mj - (NM if J == 0 else 1.0) * (1 - dl); tot.append(d)
        prob += pulp.lpSum(tot) <= T + z + (NM + 4) * (1 - pick)
    prob += pulp.lpSum(p for _, p in picks) == 1
    res = prob.solve(pulp.HiGHS(msg=msg, timeLimit=tl, threads=1))
    if not res.has_solution: return res.status_str, None, None, res.best_bound, None
    drop = [d + 1 for d, p in picks if pulp.value(p) > 0.5]
    sol = [{str(J): round(pulp.value(v), 9) for J, v in s.items() if pulp.value(v) > 1e-9} for s in hist]
    return res.status_str, pulp.value(z), drop, res.best_bound, sol
if __name__ == "__main__":
    T = float(sys.argv[1]); N = [float(x) for x in sys.argv[2].split(",")]; al = [float(x) for x in sys.argv[3].split(",")]
    order = sys.argv[4]; tl = float(sys.argv[5]); drops = [int(x) for x in sys.argv[6].split(",")] if len(sys.argv) > 6 else None
    if len(N) == 1: N = N * 7
    if len(al) == 1: al = al * 6
    t0 = time.time()
    st, zv, drop, bd, sol = solve(T, N, al, order, tl, drops)
    print(json.dumps(dict(T=T, Ns=N, alphas=al, order=order, drops=drops, status=st, z=zv, bound=bd, drop=drop, secs=round(time.time() - t0), sol=sol)), flush=True)
