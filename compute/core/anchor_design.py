# CORE Part IV: static design value of an anchor triple (three co-edges covering V), any pattern.
# Shape (p12,p13,p23) = masses of B_a∩B_b (points in exactly one co-edge); q_c = 1 - p_ac - p_bc.
# Four non-adaptive requests; value D = least possible maximal load.   py anchor_design.py [K]
import itertools, sys, pulp
R = range(4)
TYPES = [frozenset(s) for r in range(0, 5) for s in itertools.combinations(R, r)]
CELLS = ["P12", "P13", "P23", "Q1", "Q2", "Q3"]
GRIDS = [("P12", "P13"), ("P12", "P23"), ("P13", "P23"), ("P12", "Q3"), ("P13", "Q2"), ("P23", "Q1")]
def design(p12, p13, p23):
    mass = {"P12": p12, "P13": p13, "P23": p23, "Q1": 1 - p12 - p13, "Q2": 1 - p12 - p23, "Q3": 1 - p13 - p23}
    pr = pulp.LpProblem("d", pulp.LpMinimize)
    L = pr.add_variable("L", 0, 4)
    x = {(c, J): pr.add_variable("x_%s_%d" % (c, i), 0, 2) for c in CELLS for i, J in enumerate(TYPES)}
    u = {(c, J): pr.add_variable("u_%s_%d" % (c, i), cat="Binary") for c in CELLS for i, J in enumerate(TYPES)}
    pr += L
    for c in CELLS:
        pr += pulp.lpSum(x[c, J] for J in TYPES) == mass[c]
        for J in TYPES: pr += x[c, J] <= 2 * u[c, J]
    for c1, c2 in GRIDS:
        for J in TYPES:
            for J2 in TYPES:
                if not (J & J2): pr += u[c1, J] + u[c2, J2] <= 1
    for r in R: pr += pulp.lpSum(x[c, J] for c in CELLS for J in TYPES if r in J) <= L
    st = pr.solve(pulp.HiGHS(msg=False))
    sol = {(c, "".join(str(r + 4) for r in sorted(J))): round(x[c, J].value(), 4) for c in CELLS for J in TYPES if x[c, J].value() > 1e-7}
    return L.value(), sol
if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    rows = []
    for a in range(0, K + 1):
        for b in range(0, a + 1):
            for c in range(0, b + 1):
                if a + b > K: continue
                v, sol = design(a / K, b / K, c / K)
                rows.append((a, b, c, v))
    print("grid 1/%d: shapes (p12 >= p13 >= p23), value D; window shapes are those with p > 3/4" % K)
    for thr in (0.7501, 0.76, 0.78, 0.80):
        good = [(a, b, c) for a, b, c, v in rows if v <= thr and a + b + c > 0.75 * K]
        print("  D <= %.4f and p > 3/4: %d shapes: %s" % (thr, len(good), good))
    good0 = [(a, b, c) for a, b, c, v in rows if v <= 0.7501 and a + b + c <= 0.75 * K]
    print("  D <= 3/4 and p <= 3/4 (spread side): %d shapes; max p12 among them: %s" % (len(good0), max(a for a, b, c in good0)))
    import json; json.dump(rows, open("anchor_design_%d.json" % K, "w"))
