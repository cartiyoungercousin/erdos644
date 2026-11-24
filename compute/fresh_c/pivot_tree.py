r"""m = 8 discard game on the 2k-point pivot ground set with ADAPTIVE SWITCHING between adversary rules.

Replies 1, 2: disjoint k-sets (reply 2 fresh, the 'waste'); V = A_1 u A_2 (mass 2, slack r = 1-T).
Reply e >= 3: the adversary chooses, after seeing the request, one rule from a menu (tree branching):
   L  : omit the slack from lowest-degree points first      ('useless gifts', near-disjoint replies)
   H  : omit the slack from highest-degree points first
   Z1 : omit points lying only in A_1 first and FREEZE them (Theorem-8 forced-region play; zero slack afterwards)
   ZL : omit lowest-degree points first and FREEZE them      (pivot, then forced region)
 after a freeze every later reply is forced.  The requester is free at every node and, at each leaf, chooses
 which reply to discard.  One MILP: z* = min over requester trees of max over leaves of (mass(D) - T).
Exact for THIS menu class only (rule choice adaptive; within a rule the reply is determined by the request)."""
import pulp, sys, time, itertools
from pivot import popc, tstr, LOW, HIGH, ONE
RULES = {"L": (LOW, False), "H": (HIGH, False), "Z1": (ONE, True), "ZL": (LOW, True)}

class PT:
    def __init__(self, T, E, menu, keep=6, tl=1100, N=2.0):
        self.T, self.E, self.menu, self.keep, self.N = T, E, menu, keep, N
        self.prob = pulp.LpProblem("pt", pulp.LpMinimize); self.cnt = 0
        self.z = self.prob.add_variable("z", -3, 4); self.prob += self.z
        self.leaves = []
        self.build((), 2, {1: 1.0, 2: 1.0, 3: 0.0}, {1: 1, 2: 1, 3: 1}, [], N)
        self.res = self.prob.solve(pulp.HiGHS(msg=False, timeLimit=tl))
    def V(self, lo=0, hi=None, cat="Continuous"):
        self.cnt += 1; return self.prob.add_variable(f"v{self.cnt}", lo, hi, cat)
    def build(self, path, e, m, rho, frozen, active):
        prob, T, N = self.prob, self.T, self.N
        if e == self.E: self.leaf(path, m, rho, frozen); return
        b = 1 << e
        types = sorted(m)
        s = {J: self.V(0, 1) for J in types}
        for J in types: prob += s[J] <= m[J]
        prob += pulp.lpSum(s.values()) == T
        a = {J: m[J] - s[J] for J in types}
        slack = active - T - 1.0
        options = self.menu(path, e) if slack > 1e-9 else ["F"]
        for name in options:
            fz = list(frozen); act = active
            if name == "F":
                o = {J: 0 for J in types}; freeze = True
            else:
                order, freeze = RULES[name]
                o = {J: self.V(0, 1) for J in types}
                for J in types: prob += o[J] <= a[J]
                prob += pulp.lpSum(o.values()) == slack
                pre = []
                for J in order(types):
                    pre.append(J); g = self.V(cat="Binary")
                    prob += a[J] - o[J] <= g
                    prob += slack - pulp.lpSum(o[K] for K in pre) <= slack * (1 - g)
                if freeze:
                    fz += [(J, o[J]) for J in types]; act = active - slack
            m2, rho2 = {}, dict(rho)
            for J in types:
                m2[J] = s[J] if freeze else s[J] + o[J]
                m2[J | b] = a[J] - o[J]
                r = self.V(cat="Binary"); prob += r >= a[J]
                rho2[J | b] = r
            self.build(path + (name,), e + 1, m2, rho2, fz, act)
    def leaf(self, path, m, rho, frozen):
        prob, T, E = self.prob, self.T, self.E
        full = (1 << E) - 1; picks = []
        for drop in itertools.combinations(range(E), E - self.keep):
            I = full
            for d in drop: I &= ~(1 << d)
            pick = self.V(cat="Binary"); picks.append((drop, pick)); delta = {}
            for P in range(full + 1):
                if P & ~I: continue
                comp = I & ~P
                if comp == 0: delta[P] = 1; continue
                dv = self.V(cat="Binary"); delta[P] = dv
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
                    d = self.V(0, 1); prob += d >= mj - (1 - dl); tot.append(d)
            prob += pulp.lpSum(tot) <= T + self.z + 6 * (1 - pick)
        prob += pulp.lpSum(p for _, p in picks) == 1
        self.leaves.append((path, picks))

def menu_small(path, e):      # adaptive switching, 7 leaves
    if e == 2: return ["Z1", "L", "H"]
    if e == 3: return ["ZL", "L", "H"]
    return ["L"]
def menu_two(path, e):        # L/H switching at replies 3,4,5 then L
    return ["L", "H"] if e <= 4 else ["L"]
if __name__ == "__main__":
    T = float(sys.argv[1]); which = sys.argv[2]; tl = float(sys.argv[3])
    t0 = time.time()
    pt = PT(T, 7, menu_small if which == "small" else menu_two, tl=tl)
    r = pt.res
    zv = pulp.value(pt.z) if r.has_solution else None
    print(f"m=8 one discard, T={T}, menu={which}: leaves={len(pt.leaves)} vars={pt.cnt} status={r.status_str} z*={zv} bound={r.best_bound} [{time.time()-t0:.0f}s]")
    if zv is not None:
        for path, picks in pt.leaves:
            print("   leaf", path, "discard", [d + 1 for d, p in picks if pulp.value(p) > 0.5])
        print("   verdict:", "ADVERSARY (menu) wins" if r.best_bound > 1e-6 else ("requester beats this menu class" if zv <= 1e-6 else "undecided"))
