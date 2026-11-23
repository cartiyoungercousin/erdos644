"""Cross-check of the pattern tables (tables.py) against an independent MILP formulation of the
static closure (labels on the 13 regions, candidate pairs from the membership-union criterion,
binary support variables).  Random profiles, requests and responses, including boundary cases."""
import itertools, random, sys
import pulp
from game import *

def milp_close(A, r, rm, P):
    for c in P:
        if REG_MEM[c] & A == A: return None
    adj = [(c, d) for c, d in itertools.combinations(sorted(P), 2) if (REG_MEM[c] | REG_MEM[d]) & A == A]
    act = sorted({c for pr in adj for c in pr})
    LAB = list(range(1, 1 << r))
    prob = pulp.LpProblem("close", pulp.LpMinimize)
    tau = prob.add_variable("tau", 0, 4)
    m = {(c, L): prob.add_variable(f"m_{c}_{L}", 0, 1) for c in act for L in LAB}
    u = {(c, L): prob.add_variable(f"u_{c}_{L}", cat="Binary") for c in act for L in LAB}
    prob += tau
    for c in act:
        prob += pulp.lpSum(m[c, L] for L in LAB) == max(rm[c], 0.0)
        prob += pulp.lpSum(u[c, L] for L in LAB) >= 1
        for L in LAB: prob += m[c, L] <= u[c, L]
    for (c, d) in adj:
        for L in LAB:
            for L2 in LAB:
                if L & L2 == 0: prob += u[c, L] + u[d, L2] <= 1
    for j in range(r):
        prob += pulp.lpSum(m[c, L] for c in act for L in LAB if (L >> j) & 1) <= tau
    st = prob.solve(solver())
    assert st.status.name == "Optimal"
    return tau.value()

if __name__ == "__main__":
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    worst = 0
    for it in range(n):
        g = 20
        while True:
            x, y, z = sorted((random.randint(0, 10) / g for _ in range(3)), reverse=True)
            if random.random() < .25: z = 0.0
            if random.random() < .1: y = z = 0.0
            if x + y <= 1 and x > 0: break
        mass = cell_mass(x, y, z); t = random.choice([.8, .85])
        M = menu(mass, t); d, tag = random.choice(M)
        # random admissible response (no looseness needed for this check)
        cap = [max(mass[c] - d[c], 0) for c in range(6)]
        kv = [random.random() * cap[c] * random.choice([0, 1, 1]) for c in range(6)]
        s = sum(kv)
        if s > 1: kv = [v / s for v in kv]; s = 1.0
        kv.append(1 - s)
        P = present_regions(mass, d); rm = region_mass(mass, kv)
        for C in closures(mass, d):
            v, i = C.value(rm, full=True)
            if C.name == "Q": A, r = E_ | F_ | G_ | K_, 3
            else:
                a1, a2 = TRIPLE_EDGES[CELL_NAMES.index(C.name[1:])]; A, r = a1 | a2 | K_, 4
            w = milp_close(A, r, rm, P)
            worst = max(worst, abs(v - w))
            flag = "" if abs(v - w) < 1e-6 else "   <-- MISMATCH"
            print(f"{it:3d} ({x},{y},{z}) {tag:28s} {C.name:3s} table={v:.6f} milp={w:.6f}{flag}", flush=True)
    print("max |table - milp| =", worst)
