"""R2-core part 2: scenario tree with history-class modes (floating MILP, evidence).

Adversary: at step j < D he picks, after seeing the request, one history class
(isE, status at the earlier steps) and drops points of that class as long as any is on offer;
whatever else he drops is decided in the requester's favour.  At steps >= D: non-reducing points
first (as in orders_milp.py).  Optional restriction of the modes per step by KEEP.
Output: max c/g (capped) at which the requester wins at every leaf with non-anticipative requests.

usage: py orders_modes.py D order(comma-separated line indices) [...]
"""
import sys, itertools
import pulp
from orders_milp import ok, cost, NAMES, G, CAP


def solve(order, D, g=G, tl=1800, keep=None, want=False):
    prob = pulp.LpProblem("modes", pulp.LpMaximize)
    c = prob.add_variable("c", -1, CAP * g)
    prob += c
    T = 0.75 + g
    modes = []
    for j in range(D):
        ms = [(isE, h) for isE in (True, False) for h in itertools.product((0, 1, 2), repeat=j)]
        if keep and j in keep: ms = [m for m in ms if m in keep[j]]
        modes.append(ms)
    leaves = list(itertools.product(*modes))
    types = [(isE, st) for isE in (True, False) for st in itertools.product((0, 1, 2), repeat=6)
             if ok(isE, frozenset(order[i] for i in range(6) if st[i]))]
    red = {}
    for r in range(D, 6):
        fut = [order[i] for i in range(r + 1, 6)]
        for isE, st in types:
            key = (r, isE, st[:r])
            if key not in red:
                a = frozenset(order[i] for i in range(r) if st[i])
                red[key] = cost(isE, a | {order[r]}, fut) < cost(isE, a, fut)
    X = {}
    for li, lf in enumerate(leaves):
        x = [prob.add_variable(f"x_{li}_{i}", 0, 2) for i in range(len(types))]
        y = [prob.add_variable(f"y_{li}_{r}", 0, 1) for r in range(6)]
        X[lf] = x
        prob += pulp.lpSum(v for v, t in zip(x, types) if t[0]) == 1
        prob += pulp.lpSum(v for v, t in zip(x, types) if not t[0]) == 0.75 + c
        for r in range(6):
            prob += pulp.lpSum(v for v, t in zip(x, types) if t[1][r] == 1) + y[r] == T
            prob += pulp.lpSum(v for v, t in zip(x, types) if t[1][r] == 2) - y[r] == c - g
            if r < D: top = [(t[0], t[1][:r]) == lf[r] for t in types]
            else: top = [not red[(r, t[0], t[1][:r])] for t in types]
            hi = [v for v, t, k in zip(x, types, top) if k and t[1][r] == 0]
            lo = [v for v, t, k in zip(x, types, top) if not k and t[1][r] == 2]
            if hi and lo:
                z = prob.add_variable(f"z_{li}_{r}", cat="Binary")
                prob += pulp.lpSum(hi) <= 2 * z
                prob += pulp.lpSum(lo) <= 2 * (1 - z)
    for j in range(D):
        groups = {}
        for lf in leaves: groups.setdefault(lf[:j], []).append(lf)
        for grp in groups.values():
            for l1, l2 in zip(grp, grp[1:]):
                agg = {}
                for i, (isE, st) in enumerate(types):
                    agg.setdefault((isE, st[:j], st[j] == 1), []).append(i)
                for idx in agg.values():
                    prob += pulp.lpSum(X[l1][i] for i in idx) - pulp.lpSum(X[l2][i] for i in idx) == 0
    st = prob.solve(pulp.HiGHS(msg=False, threads=1, timeLimit=tl))
    if not st.has_solution: return None, st.status.name
    return round(c.value() / g, 5), st.status.name, len(leaves)


if __name__ == "__main__":
    D = int(sys.argv[1])
    for a in sys.argv[2:]:
        order = tuple(int(ch) for ch in a.split(","))
        print(" ".join(NAMES[i] for i in order), "D =", D, solve(order, D), flush=True)
