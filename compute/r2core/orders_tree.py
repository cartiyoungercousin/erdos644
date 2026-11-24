"""R2-core part 2: scenario-tree version of orders_milp.py (floating MILP, evidence).

Adversary: at each of the first D responses he picks a mode after seeing the request:
  mode E: priority  non-reducing > reducing E-points > reducing non-E points
  mode N: priority  non-reducing > reducing non-E points > reducing E-points
(a lower class is dropped only when the higher classes on offer are exhausted); after step D:
non-reducing first, the rest in the requester's favour.  The requester must win at all 2^D leaves
with non-anticipative requests.  Output: max c/g at which he still can (upper bound for the
threshold of that order; the true adversary is at least this strong).

usage: py orders_tree.py D [second-line-index ...]
"""
import sys, itertools
import pulp
from orders_milp import ok, cost, NAMES, G, CAP


def solve(order, D, g=G, tl=900):
    prob = pulp.LpProblem("tree", pulp.LpMaximize)
    c = prob.add_variable("c", -1, CAP * g)
    prob += c
    T = 0.75 + g
    leaves = list(itertools.product("EN", repeat=D))
    types = [(isE, st) for isE in (True, False) for st in itertools.product((0, 1, 2), repeat=6)
             if ok(isE, frozenset(order[i] for i in range(6) if st[i]))]
    red = {}
    for r in range(6):
        fut = [order[i] for i in range(r + 1, 6)]
        for isE, st in types:
            key = (r, isE, st[:r])
            if key not in red:
                a = frozenset(order[i] for i in range(r) if st[i])
                red[key] = cost(isE, a | {order[r]}, fut) < cost(isE, a, fut)
    X = {}
    for lf in leaves:
        nm = "".join(lf)
        x = [prob.add_variable(f"x_{nm}_{i}", 0, 2) for i in range(len(types))]
        y = [prob.add_variable(f"y_{nm}_{r}", 0, 1) for r in range(6)]
        X[lf] = x
        prob += pulp.lpSum(v for v, t in zip(x, types) if t[0]) == 1
        prob += pulp.lpSum(v for v, t in zip(x, types) if not t[0]) == 0.75 + c
        for r in range(6):
            prob += pulp.lpSum(v for v, t in zip(x, types) if t[1][r] == 1) + y[r] == T
            prob += pulp.lpSum(v for v, t in zip(x, types) if t[1][r] == 2) - y[r] == c - g
            cls = []                                   # priority classes at step r
            for isE, st in types:
                if not red[(r, isE, st[:r])]: cls.append(0)
                elif r < D: cls.append(1 if isE == (lf[r] == "E") else 2)
                else: cls.append(1)
            for lev in (0, 1):
                hi = [v for v, t, k in zip(x, types, cls) if k == lev and t[1][r] == 0]
                lo = [v for v, t, k in zip(x, types, cls) if k > lev and t[1][r] == 2]
                if not hi or not lo: continue
                z = prob.add_variable(f"z_{nm}_{r}_{lev}", cat="Binary")
                prob += pulp.lpSum(hi) <= 2 * z
                prob += pulp.lpSum(lo) <= 2 * (1 - z)
    # non-anticipativity: leaves sharing the first j modes agree on the state after j steps and on request j+1
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
    return round(c.value() / g, 5), st.status.name


if __name__ == "__main__":
    D = int(sys.argv[1]); seconds = [int(a) for a in sys.argv[2:]] or [2]
    for sec in seconds:
        rest = [i for i in range(1, 6) if i != sec]
        for p in itertools.permutations(rest):
            order = (0, sec) + p
            print(" ".join(NAMES[i] for i in order), "D =", D, solve(order, D), flush=True)
