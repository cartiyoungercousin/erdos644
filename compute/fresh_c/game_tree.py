r"""
Genuine (one-sided exact) solver for the six-edge endgame on a bounded ground set.

Adversary = "complete family on a ground set of mass N" (so sigma = N - T - 1 is his slack): after each
request of mass T he must take mass 1 out of the unrequested mass 1 + sigma, i.e. he chooses which sigma to OMIT.
His strategy is restricted to a finite MENU of omission rules per round (greedy omission in a given order of
types).  Round 6 is NOT restricted: the adversary's last response is exact (closed form), and realization
flags are exact (a type J+{i+1} is realized iff some point of type J is unrequested).
The requester is completely free and adaptive: he chooses a separate request at every node of the menu tree.
One MILP:  z* = min over requester trees of max over leaves of (mass(D) - T).
   z* > 0  ==> this menu adversary beats EVERY requester (rigorous up to MILP tolerance): game value > T.
   z* <= 0 ==> the requester beats this menu (says nothing about better adversaries).
Types: bitmask J over edges 1..5 (0 = pool of untouched points).
"""
import pulp, sys, time, itertools

def popc(x): return bin(x).count("1")
def tstr(J): return "".join(str(i + 1) for i in range(6) if (J >> i) & 1) or "pool"

class Tree:
    def __init__(self, T, N, menu, tl=600, msg=False, start=None):
        self.T, self.N, self.sig, self.menu = T, N, N - T - 1, menu
        self.prob = pulp.LpProblem("tree", pulp.LpMinimize)
        self.cnt = 0
        self.z = self.prob.add_variable("z", -2, 3)
        self.prob += self.z
        self.leaves = []
        self.nodes = []
        self.fixed_s = None
        if start is None:
            m = {0: N - 1.0, 1: 1.0}
            rho = {1: 1}
            self.build((), 1, m, rho)
        else:                                   # numeric state after i edges, requester's request there fixed
            i0, m, rho, self.fixed_s = start
            self.build((), i0, m, rho)
        self.res = self.prob.solve(pulp.HiGHS(msg=msg, timeLimit=tl))

    def V(self, lo=0, hi=None, cat="Continuous"):
        self.cnt += 1
        return self.prob.add_variable(f"v{self.cnt}", lo, hi, cat)

    def build(self, path, i, m, rho):
        prob, T, N, sig = self.prob, self.T, self.N, self.sig
        types = sorted(m.keys())
        s = {J: self.V(0, N) for J in types}
        for J in types: prob += s[J] <= m[J]
        prob += pulp.lpSum(s.values()) == T
        if self.fixed_s is not None and not path:
            for J in types: prob += s[J] == self.fixed_s.get(J, 0.0)
        a = {J: m[J] - s[J] for J in types}
        if i == 5:
            self.leaf(path, m, rho, s, a); return
        b = 1 << i
        self.nodes.append((path, i, m, s, rho))
        for name, order in self.menu(i, types):
            o = {J: self.V(0, N) for J in types}
            for J in types: prob += o[J] <= a[J]
            prob += pulp.lpSum(o.values()) == sig
            pre = []
            for J in order:
                pre.append(J)
                g = self.V(cat="Binary")
                ub = 1.0 if J else N - 1.0
                prob += a[J] - o[J] <= ub * g
                prob += sig - pulp.lpSum(o[K] for K in pre) <= sig * (1 - g)
            m2, rho2 = {}, {}
            for J in types:
                m2[J] = s[J] + o[J]
                m2[J | b] = a[J] - o[J]
                if J: rho2[J] = rho[J]
                r = self.V(cat="Binary")
                prob += r >= a[J] * (1.0 if J else 1.0 / (N - 1.0))
                rho2[J | b] = r
            self.build(path + (name,), i + 1, m2, rho2)

    def leaf(self, path, m, rho, s, a):
        prob, T, N = self.prob, self.T, self.N
        types = sorted(m.keys())
        q = {}
        for J in types:
            if J:
                q[J] = self.V(cat="Binary"); prob += q[J] >= a[J]
        tot = []
        dl, d6 = {}, {}
        for J in types:
            comp = 31 ^ J
            sup = [K for K in range(1, 32) if (K & comp) == comp]
            if comp == 0:
                dl[J] = 1; d6[J] = 1
            else:
                dl[J] = self.V(cat="Binary"); d6[J] = self.V(cat="Binary")
                for K in sup:
                    prob += dl[J] >= q[K]
                    prob += d6[J] >= rho[K]
            P = self.V(0, N); E = self.V(0, N)
            ub = 1.0 if J else N - 1.0
            prob += P >= m[J] - ub * (1 - dl[J])
            prob += E >= a[J] - ub * (1 - d6[J]) - ub * dl[J]
            tot += [P, E]
        prob += pulp.lpSum(tot) <= T + self.z
        self.leaves.append((path, m, s, a, tot, rho, q))

def val(e):
    return e if isinstance(e, (int, float)) else pulp.value(e)

def order_first(first, types, base):
    rest = [J for J in base(types) if J not in first]
    return list(first) + rest
asc = lambda types: sorted(types, key=lambda J: (popc(J), J))        # omit pool / low degree first  (= take high degree)
desc = lambda types: sorted(types, key=lambda J: (-popc(J), J))      # omit high degree first        (= take low degree)

def menu_basic(i, types):
    return [("lo", asc(types)), ("hi", desc(types))]

def menu_single(limit):
    """all 'omit type J first' items (then ascending), at most limit[i] items in round i+1 (by descending degree)"""
    def menu(i, types):
        items = [("lo", asc(types)), ("hi", desc(types))]
        cand = sorted(types, key=lambda J: (-popc(J), -J))
        for J in cand:
            if len(items) >= limit.get(i, 2): break
            items.append((tstr(J), order_first([J], types, asc)))
        return items[: limit.get(i, 2)]
    return menu

if __name__ == "__main__":
    T = float(sys.argv[1]); N = float(sys.argv[2])
    lim = {i + 1: int(x) for i, x in enumerate(sys.argv[3].split(","))} if len(sys.argv) > 3 else {1: 2, 2: 2, 3: 2, 4: 2}
    t0 = time.time()
    tr = Tree(T, N, menu_single(lim), tl=float(sys.argv[4]) if len(sys.argv) > 4 else 600)
    r = tr.res
    zv = pulp.value(tr.z) if r.has_solution else None
    print(f"T={T} N={N} menu sizes={lim}: leaves={len(tr.leaves)} vars={tr.cnt} status={r.status_str} z*={zv} bound={r.best_bound} [{time.time()-t0:.0f}s]")
    if zv is not None:
        print("  verdict:", "ADVERSARY (menu) beats every requester" if r.status_str == "Optimal" and zv > 1e-5 else ("requester beats this menu" if zv <= 1e-5 else "undecided (time limit)"))
