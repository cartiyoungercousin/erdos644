r"""m-request discard game against SCRIPTED PIVOT adversaries on the 2k-point ground set (N = 2, slack r = 1-T).

Adversary class (deterministic scripts; the requester is completely free and knows the script):
 every reply lies in a ground set V of mass N; in a round of kind
   ('greedy', order, freeze): he omits the slack (current active mass - T - 1) greedily in the given order of
       types (pool = type 0 = points in no reply yet); if freeze, the omitted points are frozen: they are
       never used again, so from then on the active ground set has zero slack;
   ('forced',): zero slack, reply = all unrequested active points.
 Orders:  POOLFIRST = omit pool first, then low degree  (never use fresh points: 'forced-region' play, keeps Z unused)
          WASTE     = omit highest degree first, pool last (reply as disjoint / as fresh as possible)
          GIFT      = pool last, omit lowest positive degree first ('useless gifts': pivot onto the unused Z)
 Realisation: type J+{new} is realised whenever some point of J is unrequested (adversary keeps one point).
Terminal: requester picks `keep` of the E replies (keep = 6: discards allowed; keep = E: no discard) and needs
mass(D) <= T.   z* = min over requesters of that mass(D) - T   (one MILP; exact for the stated script).
"""
import pulp, sys, time, itertools
def popc(x): return bin(x).count("1")
def tstr(J): return "".join(str(i + 1) for i in range(9) if (J >> i) & 1) or "pool"
POOLFIRST = lambda types: sorted(types, key=lambda J: (popc(J), J))
WASTE = lambda types: sorted(types, key=lambda J: (-popc(J), J))
GIFT = lambda types: sorted(types, key=lambda J: (J == 0, popc(J), J))

def solve(T, E, script, N=2.0, keep=6, tl=1100, msg=False, start2=True, only_drop=None):
    prob = pulp.LpProblem("pivot", pulp.LpMinimize)
    cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1
        return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    if start2:   # replies 1 and 2 are disjoint k-sets (reply 2 fresh) sharing O(1) points; V = their union
        m = {1: 1.0, 2: 1.0, 3: 0.0}; rho = {1: 1, 2: 1, 3: 1}; e_first = 2
    else:
        m = {0: N - 1.0, 1: 1.0}; rho = {1: 1}; e_first = 1
    frozen = []                      # (type, mass expression)
    active = N
    hist = []
    for e in range(e_first, E):
        b = 1 << e
        kind = script[e - e_first]
        types = sorted(m)
        ub = {J: (1.0 if J else N - 1.0) for J in types}
        s = {J: V(0, ub[J]) for J in types}
        for J in types: prob += s[J] <= m[J]
        prob += pulp.lpSum(s.values()) == T
        a = {J: m[J] - s[J] for J in types}
        slack = active - T - 1.0
        o = {J: 0 for J in types}
        if kind[0] == "greedy" and slack > 1e-9:
            o = {J: V(0, ub[J]) for J in types}
            for J in types: prob += o[J] <= a[J]
            prob += pulp.lpSum(o.values()) == slack
            pre = []
            for J in kind[1](types):
                pre.append(J)
                g = V(cat="Binary")
                prob += a[J] - o[J] <= ub[J] * g
                prob += slack - pulp.lpSum(o[K] for K in pre) <= slack * (1 - g)
            if kind[2]:
                for J in types: frozen.append((J, o[J]))
                active = active - slack
        m2, rho2 = {}, dict(rho)
        for J in types:
            keepmass = s[J] if (kind[0] == "greedy" and kind[2]) or kind[0] == "forced" or slack <= 1e-9 else s[J] + o[J]
            m2[J] = keepmass
            m2[J | b] = a[J] - o[J]
            r = V(cat="Binary"); prob += r >= a[J] * (1.0 / ub[J])
            rho2[J | b] = r
        hist.append((s, o)); m, rho = m2, rho2
    full = (1 << E) - 1
    picks = []
    for drop in itertools.combinations(range(E), E - keep):
        if only_drop is not None and tuple(drop) != tuple(only_drop): continue
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
        for J, mj in list(m.items()) + frozen:
            dl = delta[J & I]
            if isinstance(dl, int): tot.append(mj)
            else:
                d = V(0, N); prob += d >= mj - (N if J == 0 else 1.0) * (1 - dl); tot.append(d)
        prob += pulp.lpSum(tot) <= T + z + 6 * (1 - pick)
    prob += pulp.lpSum(p for _, p in picks) == 1
    res = prob.solve(pulp.HiGHS(msg=msg, timeLimit=tl))
    if not res.has_solution: return res.status_str, None, None, res.best_bound
    drop = [d for d, p in picks if pulp.value(p) > 0.5][0]
    return res.status_str, pulp.value(z), [d + 1 for d in drop], res.best_bound

F = ("forced",)
LOW = lambda types: sorted(types, key=lambda J: (popc(J), J))          # omit lowest degree first ('useless gifts')
HIGH = lambda types: sorted(types, key=lambda J: (-popc(J), J))        # omit highest degree first
ONE = lambda types: sorted(types, key=lambda J: (J != 1, popc(J), J))  # omit points lying only in reply 1 first
SCRIPTS = {      # rules for replies 3, 4, ...  (replies 1, 2 disjoint; ground set V = A_1 u A_2, slack r)
 "T8: freeze Z in A_1 at reply 3, then forced (Theorem 8)": [("greedy", ONE, True)] + [F] * 7,
 "L: omit lowest degree every round (never frozen)": [("greedy", LOW, False)] * 8,
 "H: omit highest degree every round (never frozen)": [("greedy", HIGH, False)] * 8,
 "LH: alternate lowest / highest": [("greedy", LOW, False), ("greedy", HIGH, False)] * 4,
 "HL: alternate highest / lowest": [("greedy", HIGH, False), ("greedy", LOW, False)] * 4,
 "L4: lowest at reply 3, freeze lowest at reply 4, then forced": [("greedy", LOW, False), ("greedy", LOW, True)] + [F] * 6,
 "H4: highest at reply 3, freeze lowest at reply 4, then forced": [("greedy", HIGH, False), ("greedy", LOW, True)] + [F] * 6,
 "L5: lowest at replies 3-4, freeze lowest at reply 5, then forced": [("greedy", LOW, False)] * 2 + [("greedy", LOW, True)] + [F] * 5,
}
if __name__ == "__main__":
    E = int(sys.argv[1]); keep = int(sys.argv[2]); T = float(sys.argv[3]); sel = sys.argv[4].split(",") if len(sys.argv) > 4 and sys.argv[4] != "all" else None
    tl = float(sys.argv[5]) if len(sys.argv) > 5 else 1100
    for name, sc in SCRIPTS.items():
        if sel and name.split(":")[0] not in sel: continue
        t0 = time.time()
        st, zv, drop, bd = solve(T, E, sc, keep=keep, tl=tl)
        if zv is None: print(f"m={E+1} keep={keep} T={T} [{name}]: {st} bound {bd}", flush=True); continue
        verdict = "ADVERSARY wins" if (st == "Optimal" and zv > 1e-6) or bd > 1e-6 else ("requester wins" if zv <= 1e-6 else "undecided")
        print(f"m={E+1} keep={keep} T={T} [{name}]: {st} min mass(D)-T = {zv:+.4f} (bound {bd:+.4f}) discard {drop} -> {verdict} [{time.time()-t0:.0f}s]", flush=True)
