"""§9: exact LP for the outside overlap of two Theorem-8.1 responses through a_1 at the
balanced anchor (u*,u*,u*), k = 1.  R = response to B_1∪a_1∪a_2 (a_1∪a_2 ⊇ X = E∩F: sealing),
R' = response to B_2∪a_1∪a_3.  Cells of W: E-cells X1,X2,Y3,Y4,PE1..PE4; (Z,PF,PG) x (B1,B2,B3).
Variables: r[c], r2[c] (masses of R, R' in cell c), both[c] (R∩R' in c), o (R∩R' outside W),
n, n2 (private outside parts).  Objective: max o.  Exact decisions by the rational simplex of
compute/r1/exact_infeasible.py."""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r1"))
from exact_infeasible import feasible
def model(t, branch, extra=()):
    us = (2 - t) / 3; pe = (1 - 2*us) / 4; rho = t - Fr(3, 4)
    beta = [(t + 2*rho) / 3, (t + 2*rho) / 3, (t - 4*rho) / 3]
    size = {"X1": us/2, "X2": us/2, "Y3": us/2, "Y4": us/2, "PE1": pe, "PE2": pe, "PE3": pe, "PE4": pe}
    for nm, s in (("Z", us), ("PF", 1 - 2*us), ("PG", 1 - 2*us)):
        for j in range(3): size[f"{nm}{j+1}"] = s * beta[j] / t
    cls = lambda c: ("a" + c[-1]) if c[0] in "XY" or c.startswith("PE") else ("B" + c[-1])
    okR  = [c for c in size if cls(c) not in ("B1", "a1", "a2")]
    okR2 = [c for c in size if cls(c) not in ("B2", "a1", "a3")]
    names = [("r", c) for c in okR] + [("s", c) for c in okR2] + [("b", c) for c in okR if c in okR2] + ["o", "n", "n2"]
    rows = []
    for c in size:
        co = {}
        if c in okR: co[("r", c)] = 1
        if c in okR2: co[("s", c)] = 1
        if c in okR and c in okR2:
            co[("b", c)] = -1
            rows.append(({("b", c): 1, ("r", c): -1}, "<=", 0, "both<=r")); rows.append(({("b", c): 1, ("s", c): -1}, "<=", 0, "both<=r'"))
        if co: rows.append((co, "<=", size[c], f"capacity {c}"))
    trR = {("r", c): 1 for c in okR}; trR2 = {("s", c): 1 for c in okR2}
    rows.append(({**trR, "o": 1, "n": 1}, "==", 1, "|R| = 1")); rows.append(({**trR2, "o": 1, "n2": 1}, "==", 1, "|R'| = 1"))
    rows.append((trR, ">=", t - Fr(1, 2), "Lemma B for R")); rows.append((trR2, ">=", t - Fr(1, 2), "Lemma B for R'"))
    a = {("r", c): 1 for c in okR if cls(c)[0] == "a"}; b = {("r", c): 1 for c in okR if c[0] == "Z" or c.startswith("PF")}
    rows.append((a if branch == "E" else b, ">=", us, f"minimality on (E,F,R): |R∩{branch}| >= u*"))
    rows.append(({**a, **b}, "<=", 3 - 2*t - us, "tight-triple on (E,F,R)"))
    # Lemma B for R' against the good triple (E,F,R):  |R'∩(E∪F∪R)| >= (3t - |E∪F∪R|)/2
    tr = {("s", c): 1 for c in okR2 if not c.startswith("PG")}
    for c in okR2:
        if c.startswith("PG") and c in okR: tr[("b", c)] = 1
    tr["o"] = 1
    co = dict(tr)
    for key in list(a) + list(b): co[key] = co.get(key, 0) - Fr(1, 2)          # |W1| = 3 - us - a - b
    rows.append((co, ">=", (3*t - 3 + us) / 2, "Lemma B for R' on E∪F∪R"))
    for e in extra: rows.append(e)
    return names, rows, us
def decide(names, rows, target):
    idx = {n: i for i, n in enumerate(names)}; A = []; bb = []
    def add(co, rhs, sg):
        r = [Fr(0)] * len(names)
        for n, v in co.items(): r[idx[n]] = sg * Fr(v)
        A.append(r); bb.append(sg * Fr(rhs))
    for co, s, rhs, _ in rows:
        if s in ("<=", "=="): add(co, rhs, 1)
        if s in (">=", "=="): add(co, rhs, -1)
    add({"o": 1}, target, -1)
    return feasible(A, bb)
if __name__ == "__main__":
    for t in (Fr(19, 25), Fr(39, 50)):
        eps = t - Fr(3, 4)
        for br in ("E", "F"):
            names, rows, us = model(t, br)
            guess = min(1 - us, Fr(3, 2) - t)
            ok = decide(names, rows, guess) and not decide(names, rows, guess + Fr(1, 10**6))
            print(f"t={float(t)} branch |R∩{br}|>=u*: max outside overlap = {guess} = {float(guess):.4f}"
                  f" [exact: {ok}]  needed <= eps = {float(eps)}  ratio = {float(guess/eps):.1f}")
