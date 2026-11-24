"""R2-core part 2: a REQUESTER strategy that is static after the second response.

Order of lines: order[0], order[1] adaptive, the remaining four requests are fixed in advance
once the second response is seen (so later responses cannot hurt: an absence never hurts).
Step 1: request E1 of E and N1 = T - E1 outside E.  Response: a points of E, s - a outside.
By the Minkowski argument (R2CORE_RESULTS section 9) only a = 0 and a = s need a plan.
Step 2: request rho_cl from each history class cl = (isE, status at step 1), every class with
status R or '.' keeps at least s points on offer; then the adversary's drop vectors form a polytope
whose vertices are: a subset S of the two small classes (dropped at step 1) dropped entirely, the
rest of the s drops in one big class X.  16 leaves per a; each leaf needs a static cover.
Floating LP (HiGHS) maximising c for fixed g; the solution is then checked in exact arithmetic
by verify_two_stage.py.

usage: py two_stage.py [order=0,2,4,1,3,5] [g=0.01]
"""
import sys, itertools, json
import pulp
from orders_milp import ok, NAMES

def build(order, g, cfix=None):
    prob = pulp.LpProblem("two_stage", pulp.LpMaximize)
    c = prob.add_variable("c", 0, 0.2)
    prob += c
    if cfix is not None: prob += c == cfix
    s = c - g; T = 0.75 + g
    E1 = prob.add_variable("E1", 0, 1); N1 = prob.add_variable("N1", 0, 1)
    prob += E1 + N1 == T
    types = [(isE, st) for isE in (True, False) for st in itertools.product((0, 1, 2), (0, 1, 2), (0, 1), (0, 1), (0, 1), (0, 1))
             if ok(isE, frozenset(order[i] for i in range(6) if st[i]))]
    classes = [(isE, h) for isE in (True, False) for h in (1, 2, 0)]
    big = [cl for cl in classes if cl[1] != 2]; small = [cl for cl in classes if cl[1] == 2]
    V = {"c": c, "E1": E1, "N1": N1}
    for th in (0, 1):
        mass = {(True, 1): E1, (True, 2): th * s, (True, 0): 1 - E1 - th * s,
                (False, 1): N1, (False, 2): (1 - th) * s, (False, 0): 0.75 + c - N1 - (1 - th) * s}
        rho = {cl: prob.add_variable(f"rho_{th}_{int(cl[0])}{cl[1]}", 0, 1) for cl in classes}
        V.update({f"rho_{th}_{int(cl[0])}{cl[1]}": rho[cl] for cl in classes})
        prob += pulp.lpSum(rho.values()) == T
        off = {cl: mass[cl] - rho[cl] for cl in classes}
        for cl in classes: prob += off[cl] >= (s if cl in big else 0)
        for S in ((), (small[0],), (small[1],), tuple(small)):
            for Xc in big:
                d = {cl: 0 for cl in classes}
                for cl in S: d[cl] = off[cl]
                d[Xc] = s - pulp.lpSum(off[cl] for cl in S)
                nm = f"{th}_{''.join(str(int(cl[0])) for cl in S)}_{int(Xc[0])}{Xc[1]}"
                x = [prob.add_variable(f"x_{nm}_{i}", 0, 2) for i in range(len(types))]
                V.update({f"x_{nm}_{i}": v for i, v in enumerate(x)})
                for cl in classes:
                    for st1, rhs in ((1, rho[cl]), (2, d[cl]), (0, off[cl] - d[cl])):
                        prob += pulp.lpSum(v for v, t in zip(x, types) if (t[0], t[1][0]) == cl and t[1][1] == st1) - rhs == 0
                for r in range(2, 6):
                    prob += pulp.lpSum(v for v, t in zip(x, types) if t[1][r] == 1) <= T
    return prob, V, types

if __name__ == "__main__":
    order = tuple(int(a) for a in (sys.argv[1] if len(sys.argv) > 1 else "0,2,4,1,3,5").split(","))
    g = float(sys.argv[2]) if len(sys.argv) > 2 else 0.01
    prob, V, types = build(order, g)
    st = prob.solve(pulp.HiGHS(msg=False, threads=1))
    print(" ".join(NAMES[i] for i in order), st.status.name, "max c/g =", round(V["c"].value() / g, 6))
    for k, v in V.items():
        if not k.startswith("x_"): print("  ", k, round(v.value(), 6))
