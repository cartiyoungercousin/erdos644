"""
fresh_b/shape_lp.py  --  non-adaptive 4-request completion of a good triple,
optimised over ALL obstruction shapes (intersecting label families on [7]).

Setting (k normalised to 1).  E1,E2,E3 with empty triple intersection,
a_i = |E_j ∩ E_l| (pairwise intersection opposite i), u_i = 1 - a_j - a_l (private part of E_i).
Atoms of W = E1 ∪ E2 ∪ E3:  A_i (label {i} ∪ J)  and  U_i (label {j,l} ∪ J),  J ⊆ {4,5,6,7}
= set of later requests X_4..X_7 that contain the point.
7 edges have no 2-cover  <=>  all labels pairwise intersect  <=>
   J(x) ∩ J(y) != ∅  for x in A_i, y in A_j (i != j)  and for x in A_i, y in U_i.
Request size  |X_j| = total mass of points whose J contains j.   Minimise L = max_j |X_j|.
If L*(a) <= T/k then tau > T forces a (7,2)-violation from this triple.
"""
import itertools, sys
import numpy as np
import highspy

SUBS = [frozenset(s) for r in range(1, 5) for s in itertools.combinations(range(4), r)]

def solve(a, msg=False):
    a1, a2, a3 = a
    u = [1 - a2 - a3, 1 - a1 - a3, 1 - a1 - a2]
    if min(u) < -1e-12:
        return None
    size = {('A', 0): a1, ('A', 1): a2, ('A', 2): a3, ('U', 0): u[0], ('U', 1): u[1], ('U', 2): u[2]}
    classes = [c for c in size if size[c] > 1e-12]
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    inf = highspy.kHighsInf
    nv = 0
    def var(lb, ub, cost=0.0, integer=False):
        nonlocal nv
        h.addVar(lb, ub)
        if cost:
            h.changeColCost(nv, cost)
        if integer:
            h.changeColIntegrality(nv, highspy.HighsVarType.kInteger)
        nv += 1
        return nv - 1
    def row(lb, ub, terms):
        idx = np.array([t[0] for t in terms], dtype=np.int32)
        val = np.array([t[1] for t in terms], dtype=np.float64)
        h.addRow(lb, ub, len(terms), idx, val)
    L = var(0, inf, 1.0)
    y = {(c, J): var(0, 1, integer=True) for c in classes for J in SUBS}
    m = {(c, J): var(0, inf) for c in classes for J in SUBS}
    for c in classes:
        row(size[c], size[c], [(m[c, J], 1.0) for J in SUBS])
        for J in SUBS:
            row(-inf, 0.0, [(m[c, J], 1.0), (y[c, J], -size[c])])
    for j in range(4):
        row(-inf, 0.0, [(m[c, J], 1.0) for c in classes for J in SUBS if j in J] + [(L, -1.0)])
    conflicts = []
    for i in range(3):
        for j in range(i + 1, 3):
            conflicts.append((('A', i), ('A', j)))
        conflicts.append((('A', i), ('U', i)))
    for c, d in conflicts:
        if c in classes and d in classes:
            for J in SUBS:
                for K in SUBS:
                    if not (J & K):
                        row(-inf, 1.0, [(y[c, J], 1.0), (y[d, K], 1.0)])
    h.run()
    cv = h.getSolution().col_value
    sol = {(c, J): cv[m[c, J]] for c in classes for J in SUBS if cv[m[c, J]] > 1e-9}
    return cv[L], sol

def show(sol):
    out = []
    for (c, J), v in sorted(sol.items(), key=lambda t: (t[0][0][0], t[0][0][1], sorted(t[0][1]))):
        out.append(f"{c[0]}{c[1]+1}:{{{','.join(str(x+4) for x in sorted(J))}}}={v:.4f}")
    return "  ".join(out)

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "sym"
    if mode == "sym":
        print("symmetric triples a_i = S/3:   S, L*, min(S, (3-S)/2 , ...) closed forms: G=max(S,3/4), Fano=(3-S)/2")
        for t in range(0, 37):
            S = t / 24
            L, sol = solve((S / 3, S / 3, S / 3))
            print(f"S={S:.4f}  L*={L:.4f}  G={max(S,0.75):.4f}  Fano={(3-S)/2:.4f}   {show(sol)}")
    elif mode == "grid":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 8
        worst = (0, None)
        for i in range(N + 1):
            for j in range(i, N + 1):
                for l in range(j, N + 1):
                    a = (i / N, j / N, l / N)
                    r = solve(a)
                    if r is None:
                        continue
                    L, sol = r
                    S = sum(a)
                    print(f"a={a[0]:.3f},{a[1]:.3f},{a[2]:.3f}  S={S:.3f}  L*={L:.4f}  Fano={(3-S)/2:.4f}")
                    if L > worst[0]:
                        worst = (L, a)
        print("WORST", worst)
    elif mode == "one":
        a = tuple(float(x) for x in sys.argv[2:5])
        L, sol = solve(a)
        print(L, show(sol))
