"""phi(x,y,z): least budget T/k at which a good triple with pair cells x,y,z (k = 1) closes by FOUR
STATIC requests (optimal over all label allocations; the manuscript's Hall and symmetric
allocations are two special cases).  MILP over label supports.
Also phi5: same with 5 static requests after a PAIR (not used here)."""
import itertools, sys
import pulp

R = 4
LABELS = list(range(1, 1 << R))
CELLS = ["X", "Y", "Z", "PE", "PF", "PG"]
ADJ = [("X","Y"),("X","Z"),("Y","Z"),("X","PG"),("Y","PF"),("Z","PE")]

def phi(x, y, z, want_support=False):
    mass = {"X": x, "Y": y, "Z": z, "PE": 1-x-y, "PF": 1-x-z, "PG": 1-y-z}
    if min(mass.values()) < -1e-12: return None
    prob = pulp.LpProblem("phi", pulp.LpMinimize)
    tau = prob.add_variable("tau", 0, 3)
    m = {(c, L): prob.add_variable(f"m_{c}_{L}", 0, 1) for c in CELLS for L in LABELS}
    u = {(c, L): prob.add_variable(f"u_{c}_{L}", cat="Binary") for c in CELLS for L in LABELS}
    prob += tau
    for c in CELLS:
        prob += pulp.lpSum(m[c, L] for L in LABELS) == max(mass[c], 0.0)
        for L in LABELS: prob += m[c, L] <= u[c, L]
    for (c, d) in ADJ:
        for L in LABELS:
            for L2 in LABELS:
                if L & L2 == 0: prob += u[c, L] + u[d, L2] <= 1
    for j in range(R):
        prob += pulp.lpSum(m[c, L] for c in CELLS for L in LABELS if (L >> j) & 1) <= tau
    st = prob.solve(pulp.HiGHS(msg=False))
    if st.status.name != "Optimal": return None
    if want_support:
        return tau.value(), {(c, bin(L)): round(m[c, L].value(), 4) for c in CELLS for L in LABELS if m[c, L].value() > 1e-7}
    return tau.value()

if __name__ == "__main__":
    print("Fano point (1/2,1/2,1/2):", phi(.5,.5,.5, True))
    print("symmetric line x=y=z=a:")
    for a in [0, .1, .2, .25, .3, 1/3, .35, .4, 3/7, .45, .5]:
        print(f"  a={a:.4f}  phi={phi(a,a,a):.4f}")
    print("x = 1/2, y = z = b:")
    for b in [0, .05, .1, .15, .2, .25, .3, .35, .375, .4, .45, .5]:
        print(f"  b={b:.3f}  phi={phi(.5,b,b):.4f}")
    print("x = 1/2, z = 0, y = b:")
    for b in [0, .1, .2, .25, .3, .375, .5]:
        print(f"  b={b:.3f}  phi={phi(.5,b,0):.4f}")
    # worst case over a grid, and the set where phi <= 0.76
    N = 20; worst = (0, None); good = []
    for i in range(N+1):
        for j in range(i+1):
            for l in range(j+1):
                x, y, z = i/N, j/N, l/N
                if x + y > 1 + 1e-9: continue
                v = phi(x, y, z)
                if v is None: continue
                if v > worst[0]: worst = (v, (x, y, z))
                if v <= 0.7501: good.append((x, y, z))
    print("worst static phi on grid (cells <= 1):", worst)
    print("grid points with phi <= 3/4:", good)
