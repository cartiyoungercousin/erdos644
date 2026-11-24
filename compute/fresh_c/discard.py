r"""Discard game against 'free start, then forced' (waste-type) adversaries: exact MILP, requester free.

m requests, m-1 = E replies followed by a final request; the requester wins iff for SOME 6 of the E replies
(his choice, i.e. he may discard E-6 replies) the set D of points lying in a covering pair of those six has
mass <= T (the final request then contains D).
Adversary: the first replies are preset ("free start"), after which every reply is the forced complement of
the request inside a fixed ground set V' of mass 1+T (zero slack).  Points outside V' ("frozen") keep their type.
Types: bitmask over replies 1..E.  One MILP: z* = min over requesters of (min over 6-subsets of mass(D)) - T.
"""
import pulp, sys, time, itertools
def popc(x): return bin(x).count("1")
def tstr(J): return "".join(str(i + 1) for i in range(9) if (J >> i) & 1) or "0"

def solve(T, E, init, frozen, e0, tl=1100, msg=False, keep=6, only_drop=None):
    prob = pulp.LpProblem("discard", pulp.LpMinimize)
    cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1
        return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -2, 4); prob += z
    m = dict(init); rho = {J: (1 if (J and init[J] > 0) else 0) for J in init}
    for J in frozen:
        if J: rho[J] = 1
    reqs = []
    for e in range(e0, E):
        b = 1 << e
        s = {J: V(0, 1) for J in m}
        for J in m: prob += s[J] <= m[J]
        prob += pulp.lpSum(s.values()) == T
        m2, rho2 = {}, dict(rho)
        for J in m:
            m2[J] = s[J]
            m2[J | b] = m[J] - s[J]
            r = V(cat="Binary"); prob += r >= m[J] - s[J]
            rho2[J | b] = r
            rho2.setdefault(J, rho.get(J, 0))
        reqs.append(s); m, rho = m2, rho2
    full = (1 << E) - 1
    picks = []
    for drop in itertools.combinations(range(E), E - keep):
        if only_drop is not None and tuple(drop) != tuple(only_drop): continue
        I = full
        for d in drop: I &= ~(1 << d)
        pick = V(cat="Binary"); picks.append((drop, pick, I))
        delta = {}
        subs = [P for P in range(full + 1) if (P & ~I) == 0]
        for P in subs:
            comp = I & ~P
            if comp == 0:
                delta[P] = 1; continue
            dv = V(cat="Binary"); delta[P] = dv
            for K, rk in rho.items():
                if K and (K & I & comp) == comp:
                    if isinstance(rk, int):
                        if rk: prob += dv >= 1
                    else:
                        prob += dv >= rk
        tot = []
        for J, mj in m.items():
            if J == 0: continue
            dl = delta[J & I]
            if isinstance(dl, int): tot.append(mj)
            else:
                d = V(0, 1); prob += d >= mj - (1 - dl); tot.append(d)
        for J, fz in frozen.items():
            dl = delta[J & I]
            tot.append(fz * dl if not isinstance(dl, int) else fz)
        prob += pulp.lpSum(tot) <= T + z + 4 * (1 - pick)
    prob += pulp.lpSum(p for _, p, _ in picks) == 1
    res = prob.solve(pulp.HiGHS(msg=msg, timeLimit=tl))
    if not res.has_solution: return res.status_str, None, None, None
    zv = pulp.value(z)
    drop = [d for d, p, _ in picks if pulp.value(p) > 0.5][0]
    val = lambda e: e if isinstance(e, (int, float)) else pulp.value(e)
    final = {tstr(J): round(val(mj), 4) for J, mj in m.items() if val(mj) > 1e-6}
    return res.status_str, zv, [d + 1 for d in drop], dict(final=final, bound=res.best_bound,
            reqs=[{tstr(J): round(pulp.value(v), 4) for J, v in s.items() if pulp.value(v) > 1e-6} for s in reqs])

def scripts(T):
    r = 1 - T
    return {
      "control: complete family on V' (no waste), start after reply 1": (dict(init={0: T, 1: 1.0}, frozen={}, e0=1)),
      "A: Theorem-8 adversary (A_1 = X+Z, A_2 = Y disjoint)": dict(init={1: T, 2: 1.0, 3: 0.0}, frozen={1: r}, e0=2),
      "B: balanced waste (Z split between A_1 and A_2)": dict(init={1: 1 - r / 2, 2: 1 - r / 2, 3: 0.0}, frozen={1: r / 2, 2: r / 2}, e0=2),
      "C: A_1 and A_2 overlap in r, V' = A_1 u A_2": dict(init={1: T, 2: T, 3: r}, frozen={}, e0=2),
    }

if __name__ == "__main__":
    E = int(sys.argv[1]); keep = int(sys.argv[2])
    for T in [float(x) for x in sys.argv[3:]]:
        for name, sc in scripts(T).items():
            t0 = time.time()
            st, zv, drop, info = solve(T, E, keep=keep, **sc)
            if zv is None: print(f"m={E+1} T={T} [{name}]: {st}", flush=True); continue
            print(f"m={E+1} keep={keep} T={T} [{name}]: {st} min mass(D)-T = {zv:+.4f} (bound {info['bound']:+.4f}) discard replies {drop}"
                  f" -> {'ADVERSARY wins' if zv > 1e-6 and st == 'Optimal' else ('requester wins' if zv <= 1e-6 else 'undecided')} [{time.time()-t0:.0f}s]", flush=True)
            if "A:" in name:
                print("    final types:", info["final"])
