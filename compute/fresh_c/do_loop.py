r"""Counterexample-guided loop for the m = 8, one-discard game on the 2k-point ground set (adversary confined
to V = A_1 u A_2, slack r = 1-T per reply, replies 1 and 2 disjoint).

Adversary pool: at every node (history) of the game tree a list of reply RULES; a rule = "omit the slack from
these types first, in this order, then from the remaining types by lowest (L) or highest (H) degree".  These
are vertices of the reply polytope of the adversary, chosen adaptively (after seeing the request).
Step 1 (requester vs pool): one MILP, requester free at every node, discard chosen per leaf:
        v_pool = min over requester trees of max over leaves of (mass(D) - T).   CERTIFIED LOWER BOUND on the
        value of the unrestricted game (the adversary may restrict himself to the pool).
Step 2 (adversary oracle): at every node, with the request made there fixed, every single-type-first rule is
        tried as a deviation; its value is the best continuation of the requester against the default rule
        below (exact MILP).  The best deviations with value > v_pool are added to the menu of that node.
The loop closes only if no deviation improves; then v_pool is the value against all single-type-first
vertex replies (one deviation deep), not a proof for arbitrary replies."""
import pulp, sys, time, itertools
from concurrent.futures import ProcessPoolExecutor


def popc(x): return bin(x).count("1")
def tstr(J): return "".join(str(i + 1) for i in range(9) if (J >> i) & 1) or "0"


E = 7


def order_of(rule, types):
    first = [J for J in rule[:-1] if J in types]
    key = (lambda J: (popc(J), J)) if rule[-1] == "L" else (lambda J: (-popc(J), J))
    return first + sorted([J for J in types if J not in first], key=key)


class Tree2:
    def __init__(self, T, menus, default=("L",), discards=(0, 1), start=None, fixed=None, tl=900):
        self.T, self.menus, self.default, self.discards = T, menus, default, discards
        self.prob = pulp.LpProblem("t2", pulp.LpMinimize)
        self.cnt = 0
        self.z = self.prob.add_variable("z", -3, 4)
        self.prob += self.z
        self.nodes, self.leaves = [], []
        self.fixed = fixed
        if start is None:
            start = ((), 2, {1: 1.0, 2: 1.0, 3: 0.0}, {1: 1, 2: 1, 3: 1})
        self.root = start[0]
        self.build(*start)
        self.res = self.prob.solve(pulp.HiGHS(msg=False, timeLimit=tl))

    def V(self, lo=0, hi=None, cat="Continuous"):
        self.cnt += 1
        return self.prob.add_variable(f"v{self.cnt}", lo, hi, cat)

    def build(self, path, e, m, rho):
        prob, T = self.prob, self.T
        if e == E:
            self.leaf(path, m, rho)
            return
        b = 1 << e
        types = sorted(m)
        r = 1.0 - T
        s = {J: self.V(0, 1) for J in types}
        for J in types:
            prob += s[J] <= m[J]
        prob += pulp.lpSum(s.values()) == T
        if self.fixed is not None and path == self.root:
            for J in types:
                prob += s[J] == self.fixed.get(J, 0.0)
        a = {J: m[J] - s[J] for J in types}
        self.nodes.append((path, e, m, rho, s))
        for rule in self.menus.get(path, [self.default]):
            o = {J: self.V(0, 1) for J in types}
            for J in types:
                prob += o[J] <= a[J]
            prob += pulp.lpSum(o.values()) == r
            pre = []
            for J in order_of(rule, types):
                pre.append(J)
                g = self.V(cat="Binary")
                prob += a[J] - o[J] <= g
                prob += r - pulp.lpSum(o[K] for K in pre) <= r * (1 - g)
            m2, rho2 = {}, dict(rho)
            for J in types:
                m2[J] = s[J] + o[J]
                m2[J | b] = a[J] - o[J]
                rv = self.V(cat="Binary")
                prob += rv >= a[J]
                rho2[J | b] = rv
            self.build(path + (rule,), e + 1, m2, rho2)

    def leaf(self, path, m, rho):
        prob, T = self.prob, self.T
        full = (1 << E) - 1
        picks = []
        for d in self.discards:
            I = full & ~(1 << d)
            pick = self.V(cat="Binary")
            picks.append((d, pick))
            delta = {}
            for P in range(full + 1):
                if P & ~I:
                    continue
                comp = I & ~P
                if comp == 0:
                    delta[P] = 1
                    continue
                dv = self.V(cat="Binary")
                delta[P] = dv
                for K, rk in rho.items():
                    if K and (K & comp) == comp:
                        if isinstance(rk, int):
                            if rk:
                                prob += dv >= 1
                        else:
                            prob += dv >= rk
            tot = []
            for J, mj in m.items():
                dl = delta[J & I]
                if isinstance(dl, int):
                    tot.append(mj)
                else:
                    dd = self.V(0, 1)
                    prob += dd >= mj - (1 - dl)
                    tot.append(dd)
            prob += pulp.lpSum(tot) <= T + self.z + 6 * (1 - pick)
        prob += pulp.lpSum(p for _, p in picks) == 1
        self.leaves.append((path, picks))


def val(e):
    return e if isinstance(e, (int, float)) else pulp.value(e)


def eval_candidate(args):
    T, path, e, mnum, rnum, snum, rule, discards = args
    t = Tree2(T, {path: [rule]}, discards=discards, start=(path, e, mnum, rnum), fixed=snum, tl=240)
    if not t.res.has_solution:
        return (None, path, rule)
    return (t.res.best_bound, path, rule)      # certified lower bound on the best continuation of the requester


def pstr(path):
    return " > ".join("omit " + ",".join(tstr(J) for J in rule[:-1]) + "|" + rule[-1] for rule in path) or "(root)"


if __name__ == "__main__":
    T = float(sys.argv[1]); iters = int(sys.argv[2]); tl = float(sys.argv[3]); workers = int(sys.argv[4])
    discards = tuple(range(7)) if (len(sys.argv) > 5 and sys.argv[5] == "all") else (0, 1)
    log = open(f"do_loop_T{T}.log", "a")

    def out(*a):
        s = " ".join(str(x) for x in a)
        print(s, flush=True)
        log.write(s + "\n")
        log.flush()

    menus = {}
    out(f"=== T={T} discards allowed={[d + 1 for d in discards]} start {time.strftime('%H:%M:%S')}")
    for it in range(iters):
        t0 = time.time()
        tr = Tree2(T, menus, discards=discards, tl=tl)
        r = tr.res
        if not r.has_solution:
            out(f"iter {it}: tree MILP no solution ({r.status_str})")
            break
        zv = pulp.value(tr.z)
        out(f"iter {it}: leaves={len(tr.leaves)} requester-vs-pool value: incumbent {zv:+.4f}, certified lower bound {r.best_bound:+.4f} ({r.status_str}) [{time.time() - t0:.0f}s]")
        if r.best_bound > 1e-6:
            out("  ADVERSARY POOL WINS (certified for the modelled discards). Pool:")
            for p, ms in menus.items():
                out("    at", pstr(p), ":", [pstr((x,)) for x in ms])
            break
        cands = []
        for path, e, m, rho, s in tr.nodes:
            mnum = {J: max(0.0, val(m[J])) for J in m}
            rnum = {J: (1 if val(rho[J]) > 0.5 else 0) for J in rho}
            snum = {J: min(mnum[J], max(0.0, val(s[J]))) for J in s}
            have = set(menus.get(path, [("L",)]))
            for J in mnum:
                if mnum[J] - snum[J] < 0.01:
                    continue
                for tail in ("L", "H"):
                    rule = (J, tail)
                    if rule in have:
                        continue
                    cands.append((T, path, e, mnum, rnum, snum, rule, discards))
        t1 = time.time()
        with ProcessPoolExecutor(max_workers=workers) as ex:
            results = list(ex.map(eval_candidate, cands, chunksize=1))
        results = [x for x in results if x[0] is not None]
        results.sort(key=lambda x: -x[0])
        if not results:
            out("  no candidates")
            break
        best = results[0]
        out(f"  adversary oracle: {len(cands)} single-type-first deviations evaluated [{time.time() - t1:.0f}s]; best value {best[0]:+.4f} at node [{pstr(best[1])}] rule {pstr((best[2],))};"
            f" gap (best deviation - pool value) = {best[0] - zv:+.4f}")
        if best[0] <= zv + 1e-5:
            out("  LOOP CLOSED at one-deviation depth: no single-type-first deviation improves on the pool value.")
            break
        added = 0
        for v, path, rule in results[:3]:
            if v > zv + 1e-5:
                menus.setdefault(path, [("L",)])
                if rule not in menus[path]:
                    menus[path].append(rule)
                    added += 1
                    out(f"    + at node [{pstr(path)}] add rule {pstr((rule,))} (deviation value {v:+.4f})")
        out(f"  added {added} rules; pool now has {sum(len(v) for v in menus.values())} rules at {len(menus)} nodes")
    out(f"=== end {time.strftime('%H:%M:%S')}")
