"""Shapes of bad 7-tuples (normalized k = 1), via the miss-pattern MILP.

Variables: mass n_P >= 0 for each miss-pattern P (nonempty subset of [7]); binary z_P = "P used".
Bad tuple <=> used patterns pairwise intersect.  Edge i has mass sum_{P not containing i} n_P = 1.
Q1: min union size (expect 7/4, Fano).
Q2: min union size when the used 3-sets do not contain all 7 lines of any Fano plane (expect 9/5).
Q3: in a universe of size 1+t, range of a pair intersection |A1 n A2| over bad tuples.
"""
import itertools, sys
import pulp

P7 = 7
FULL = (1 << P7) - 1
PATS = [s for s in range(1, FULL + 1)]          # miss patterns (FULL = point in no set)

def fano_planes():
    base = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
    seen = set()
    for perm in itertools.permutations(range(7)):
        lines = frozenset(frozenset(perm[x] for x in L) for L in base)
        seen.add(lines)
    return [sorted(sum(1 << x for x in L) for L in pl) for pl in seen]

def model(name, sense=pulp.LpMinimize):
    prob = pulp.LpProblem(name, sense)
    n = {P: prob.add_variable(f"n_{P}", 0, 7) for P in PATS}
    z = {P: prob.add_variable(f"z_{P}", cat="Binary") for P in PATS}
    for P in PATS:
        prob += n[P] <= 7 * z[P]
    for P in PATS:
        for Q in PATS:
            if P < Q and (P & Q) == 0:
                prob += z[P] + z[Q] <= 1
    for i in range(P7):
        prob += pulp.lpSum(n[P] for P in PATS if not (P >> i) & 1) == 1
    return prob, n, z

def solve(prob):
    st = prob.solve(pulp.HiGHS(msg=False))
    return st.status.name

def union(n):  # points in at least one set
    return pulp.lpSum(n[P] for P in PATS if P != FULL)

if __name__ == "__main__":
    prob, n, z = model("minunion"); prob += union(n)
    print("Q1 min union:", solve(prob), pulp.value(prob.objective))
    print("   support:", {bin(P): round(n[P].value(), 4) for P in PATS if n[P].value() > 1e-7})

    planes = fano_planes(); print("number of Fano planes on [7]:", len(planes))
    prob, n, z = model("nofano"); prob += union(n)
    for pl in planes:
        prob += pulp.lpSum(z[L] for L in pl) <= 6
    print("Q2 min union, no full Fano among used 3-sets:", solve(prob), pulp.value(prob.objective))
    print("   support:", {bin(P): round(n[P].value(), 4) for P in PATS if n[P].value() > 1e-7})

    for t in [0.75, 0.76, 0.78, 0.79, 0.80, 0.82, 6/7, 0.9, 1.0]:
        res = []
        for sense in (pulp.LpMinimize, pulp.LpMaximize):
            prob, n, z = model("pair", sense)
            prob += pulp.lpSum(n[P] for P in PATS if not (P & 0b11))      # |A1 n A2|
            prob += union(n) <= 1 + t
            st = solve(prob); res.append(round(pulp.value(prob.objective), 4) if st == "Optimal" else st)
        print(f"Q3 t={t:.4f}: pair intersection range in bad tuples within universe 1+t: {res}")
