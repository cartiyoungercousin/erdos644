"""R2-core part 2: Fano-template game for every order of the six requests, against the
"drop a non-reducing point whenever one is on offer" adversary.  Floating MILP (HiGHS): evidence.

Point type = (isE, status of the point at each of the six lines: 0 present, 1 requested, 2 dropped).
cost(A, fut) = least number of future absences needed to cover a point with absence set A.
A point on offer at step r is NON-REDUCING if being absent from L_r does not lower its cost.
Adversary: step 1: all drops on E or all outside E, chosen after seeing the request (2 scenarios);
step r >= 2: no reducing point is dropped while an undropped non-reducing point is on offer
(binary z per step and scenario).  Everything the adversary leaves open is decided in the
requester's favour, so "max c/g = 3" means the adversary wins above 3.

The MILP maximises c for fixed g: the result is the largest ratio at which the requester can
still win against this adversary (an upper bound for the true threshold of that order).

usage: py orders_milp.py [first=all|n] [--commit]   (--commit: first response not adaptive, scenario E only / N only)
"""
import sys, itertools
import pulp

LINES = [frozenset(s) for s in ({1, 2}, {3, 4}, {1, 3}, {2, 4}, {1, 4}, {2, 3})]
ASTARS = [frozenset(i for i in range(6) if p in LINES[i]) for p in (1, 2, 3, 4)]
BPAIRS = [frozenset({2 * j, 2 * j + 1}) for j in range(3)]
NAMES = ["1A", "1B", "2A", "2B", "3A", "3B"]
import os
G = float(os.environ.get("R2G", "0.01")); CAP = float(os.environ.get("R2CAP", "6"))


def ok(isE, a):
    return any(s <= a for s in ASTARS) or (not isE and any(p <= a for p in BPAIRS))


def cost(isE, a, fut):
    best = 99
    for n in range(len(fut) + 1):
        for F in itertools.combinations(fut, n):
            if ok(isE, a | set(F)): return n
    return best


def solve(order, scenarios=("E", "N"), g=G):
    prob = pulp.LpProblem("orders", pulp.LpMaximize)
    c = prob.add_variable("c", -1, CAP * g)
    prob += c
    T = 0.75 + g
    first = {}
    for sc in scenarios:
        types = []
        for isE in (True, False):
            for st in itertools.product((0, 1, 2), repeat=6):          # st[i] = status at step i of the order
                if st[0] == 2 and isE != (sc == "E"): continue
                absent = frozenset(order[i] for i in range(6) if st[i])
                if not ok(isE, absent): continue
                types.append((isE, st))
        x = [prob.add_variable(f"x_{sc}_{i}", 0, 2) for i in range(len(types))]
        y = [prob.add_variable(f"y_{sc}_{r}", 0, 1) for r in range(6)]
        prob += pulp.lpSum(v for v, t in zip(x, types) if t[0]) == 1
        prob += pulp.lpSum(v for v, t in zip(x, types) if not t[0]) == 0.75 + c
        for r in range(6):
            prob += pulp.lpSum(v for v, t in zip(x, types) if t[1][r] == 1) + y[r] == T
            prob += pulp.lpSum(v for v, t in zip(x, types) if t[1][r] == 2) - y[r] == c - g
        for r in range(1, 6):
            fut = [order[i] for i in range(r + 1, 6)]
            red = []
            for isE, st in types:
                a = frozenset(order[i] for i in range(r) if st[i])
                red.append(cost(isE, a | {order[r]}, fut) < cost(isE, a, fut))
            z = prob.add_variable(f"z_{sc}_{r}", cat="Binary")
            # z = 1: some non-reducing point stays on offer undropped, so no reducing point is dropped
            prob += pulp.lpSum(v for v, t, rd in zip(x, types, red) if t[1][r] == 0 and not rd) <= 2 * z
            prob += pulp.lpSum(v for v, t, rd in zip(x, types, red) if t[1][r] == 2 and rd) <= 2 * (1 - z)
        first[sc] = (pulp.lpSum(v for v, t in zip(x, types) if t[0] and t[1][0] == 1),
                     pulp.lpSum(v for v, t in zip(x, types) if not t[0] and t[1][0] == 1), y[0])
    if len(scenarios) == 2:
        for a, b in zip(first["E"], first["N"]): prob += a - b == 0
    st = prob.solve(pulp.HiGHS(msg=False, threads=1, timeLimit=600))
    if not st.has_solution: return None, st.status.name
    return c.value() / g, st.status.name


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if "--commit" in sys.argv:
        for order in [(0, 1, 2, 3, 4, 5), (0, 2, 4, 1, 3, 5), (0, 2, 1, 3, 4, 5), (0, 2, 3, 1, 4, 5)]:
            print(" ".join(NAMES[i] for i in order), "E only:", solve(order, ("E",)), "N only:", solve(order, ("N",)), flush=True)
        sys.exit()
    orders = [(0,) + p for p in itertools.permutations(range(1, 6))]
    if args: orders = orders[:int(args[0])]
    worst = 0
    for order in orders:
        val, status = solve(order)
        worst = max(worst, val or 0)
        print(" ".join(NAMES[i] for i in order), "max c/g =", None if val is None else round(val, 6), status, flush=True)
    print("largest ratio over", len(orders), "orders:", round(worst, 6))
