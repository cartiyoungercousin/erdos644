r"""RED TEAM: mixed-reply ("proportional") adversaries, requester exactly optimal (one MILP).

Scale-free model (masses in units of k), same conventions as compute/fresh_c/pivot.py:
 type = bitmask of replies containing the point, type 0 = active pool; a type J|new is REALISED iff some
 point of J is unrequested.  Adversary rule (deterministic, NOT a vertex reply):
     reply e takes the same fraction lam_e = 1/(N_e - T) of EVERY unrequested active type (pool included),
 where N_e is the mass of the active ground set at round e (schedule Ns; growing schedule = fresh territory
 opened round by round; requests on not-yet-active pool are useless since he activates unrequested points).
 N_e = 1+T is the forced complete family (control).  The requester must spend exactly T (restriction on her).
Terminal (E replies, then one more request): she picks 6 of the E replies and needs mass(D) <= T.
 z* = min over requesters of mass(D) - T.  z* <= 0: requester beats this adversary with E+1 requests.
"""
import pulp, sys, time, itertools, json
def popc(x): return bin(x).count("1")
def solve(T, Ns, keep=6, tl=300, msg=False, only_drop=None, alpha=None):
    E = len(Ns)
    prob = pulp.LpProblem("prop", pulp.LpMinimize)
    cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1
        return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    NM = max(Ns)
    m = {0: Ns[0] - 1.0, 1: 1.0}; rho = {1: 1}
    hist = []
    for e in range(1, E):
        b = 1 << e
        m[0] = m[0] + (Ns[e] - Ns[e - 1])
        lam = 1.0 / (Ns[e] - T)
        assert lam <= 1 + 1e-12
        types = sorted(m)
        ub = {J: (1.0 if J else NM) for J in types}
        s = {J: V(0, ub[J]) for J in types}
        for J in types: prob += s[J] <= m[J]
        prob += pulp.lpSum(s.values()) == T
        m2, rho2 = {}, dict(rho)
        for J in types:
            a = m[J] - s[J]
            m2[J] = m[J] - lam * a
            m2[J | b] = lam * a
            r = V(cat="Binary"); prob += a <= ub[J] * r
            rho2[J | b] = r
        hist.append(s); m, rho = m2, rho2
    full = (1 << E) - 1
    picks = []
    for drop in itertools.combinations(range(E), E - keep):
        if only_drop is not None and tuple(drop) not in only_drop: continue
        I = full
        for d in drop: I &= ~(1 << d)
        pick = V(cat="Binary"); picks.append((drop, pick))
        delta = {}
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
    drop = [d for d, p in picks if pulp.value(p) > 0.5][0]
    sol = [{J: pulp.value(v) for J, v in s.items() if pulp.value(v) > 1e-9} for s in hist]
    return res.status_str, pulp.value(z), [d + 1 for d in drop], res.best_bound, sol

def replay(T, Ns, sol, eps=1e-7):
    """Independent float re-simulation of a requester line; returns min over 6-subsets of mass(D) - T."""
    E = len(Ns)
    m = {0: Ns[0] - 1.0, 1: 1.0}; real = {1}
    for e in range(1, E):
        b = 1 << e; m[0] += Ns[e] - Ns[e - 1]; lam = 1.0 / (Ns[e] - T)
        s = sol[e - 1]; assert sum(s.values()) <= T + 1e-6
        m2 = {}
        for J, mj in m.items():
            sj = min(mj, s.get(J, 0.0)); a = mj - sj
            m2[J] = mj - lam * a
            if a > eps: m2[J | b] = lam * a; real.add(J | b)
        m = m2
    full = (1 << E) - 1; best = 9
    for drop in range(E):
        I = full & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        best = min(best, D - T)
    return best

if __name__ == "__main__":
    T = float(sys.argv[1]); Ns = [float(eval(x)) for x in sys.argv[2].split(",")]; tl = float(sys.argv[3])
    if len(Ns) == 1: Ns = Ns * 7
    t0 = time.time()
    st, zv, drop, bd, sol = solve(T, Ns, tl=tl)
    rp = replay(T, Ns, sol) if sol else None
    print(json.dumps(dict(T=T, Ns=[round(x, 4) for x in Ns], status=st, z=zv, bound=bd, drop=drop, replay=rp, secs=round(time.time() - t0), sol=[{str(J): round(v, 6) for J, v in s.items()} for s in sol] if sol else None)), flush=True)
