"""§7 of NEW_PATHS.md: exact LP for the escape of Theorem 6.4.
Continuum model (k = 1). Edges E,F,P3,P4 (bits 0..3) and the far edge G.
u = 1 - t/2 - delta (lex-min cell), far pairs meet in <= 2*delta (closed: adversary-favourable).
Variables: m[c] = mass of Venn cell c (c = non-empty proper subset mask of the 4 petals; the
4-wise cell is sealed), g[c] = mass of G inside cell c (only cells G can reach).
Adversary maximises |U| + beta = sum m + sum g ; the requester's 5+2 closure needs it <= 2t.
Variant A: D4 seals G∩P3 (then (G,P3,P4) is good and P3,P4 are close).
Variant B: D4 does not (P3,P4 far or close: two branches; G may meet P3∩P4).
Float LP (HiGHS) proposes the optimum v; the exact rational simplex of r1/exact_infeasible.py
certifies  feasible(obj >= v - eps)  and  infeasible(obj >= v + eps).
"""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r1"))
from exact_infeasible import feasible
import pulp
CELLS = list(range(1, 15))
def build(t, delta, variant, branch):
    """returns (names, rows) ; rows = (coef dict, sense, rhs) with sense in '<=', '>=', '=='"""
    u = 1 - t/2 - delta; far = 2*delta; b3 = t - 1 + u
    gcells = [1, 2, 3, 4, 8] + ([12] if variant == "B" else [])
    names = [("m", c) for c in CELLS] + [("g", c) for c in gcells]
    rows = []
    for i in range(4):                                             # |edge| = 1
        rows.append(({("m", c): 1 for c in CELLS if c >> i & 1}, "==", Fr(1)))
    def pair(i, j): return {("m", c): 1 for c in CELLS if c >> i & 1 and c >> j & 1}
    rows.append((pair(0, 1), "==", u))                             # |E∩F| = u (choice of E,F)
    for (i, j) in ((0, 2), (1, 2), (0, 3), (1, 3)):                # minimality via (E|F, G, P3|P4)
        rows.append((pair(i, j), ">=", u))
    if variant == "A" or branch == "close":
        rows.append((pair(2, 3), ">=", u))                         # minimality via (G,P3,P4) / gap
    else:
        rows.append((pair(2, 3), "<=", far))                       # gap, far branch
    rows.append(({("m", 7): 1}, "<=", u - b3))                     # D3 cuts b3 of E∩F
    if variant == "A":                                             # D4: seal G∩P3, E∩F∩P3, rest on E∩F
        rows.append(({("m", 11): 1, ("g", 4): -1}, "<=", u - b3))  # |E∩F∩P4| <= u - (b3 - g3)
        rows.append(({("m", 7): 1, ("g", 4): 1}, "<=", b3))        # sealing must be affordable
    else:
        rows.append(({("m", 11): 1}, "<=", u - b3))
    for c in gcells: rows.append(({("g", c): 1, ("m", c): -1}, "<=", Fr(0)))
    rows.append(({("g", 1): 1, ("g", 3): 1}, "<=", far))           # G far from E
    rows.append(({("g", 2): 1, ("g", 3): 1}, "<=", far))           # G far from F
    rows.append(({("g", c): 1 for c in gcells if c & 4}, "<=", far))   # G far from P3
    rows.append(({("g", c): 1 for c in gcells if c & 8}, "<=", far))   # G far from P4
    obj = {n: 1 for n in names}
    return names, rows, obj
def float_max(names, rows, obj):
    p = pulp.LpProblem("u", pulp.LpMaximize)
    x = {n: p.add_variable(f"{n[0]}{n[1]}", 0, 2) for n in names}
    p += pulp.lpSum(float(a) * x[n] for n, a in obj.items())
    for coef, s, rhs in rows:
        e = pulp.lpSum(float(a) * x[n] for n, a in coef.items())
        p += (e <= float(rhs)) if s == "<=" else (e >= float(rhs)) if s == ">=" else (e == float(rhs))
    st = p.solve(pulp.HiGHS(msg=False))
    if st.status.name == "Infeasible": return None
    return sum(float(a) * x[n].value() for n, a in obj.items())
def exact_feasible(names, rows, obj, target):
    idx = {n: i for i, n in enumerate(names)}; A = []; b = []
    def add(coef, rhs, sign):
        r = [Fr(0)] * len(names)
        for n, a in coef.items(): r[idx[n]] = sign * Fr(a)
        A.append(r); b.append(sign * Fr(rhs))
    for coef, s, rhs in rows:
        if s in ("<=", "=="): add(coef, rhs, 1)
        if s in (">=", "=="): add(coef, rhs, -1)
    if target is not None: add(obj, target, -1)
    return feasible(A, b)
def certified_max(t, delta, variant, branch="close", eps=Fr(1, 10**5)):
    names, rows, obj = build(t, delta, variant, branch)
    v = float_max(names, rows, obj)
    if v is None:
        assert not exact_feasible(names, rows, obj, None); return None
    vq = Fr(round(v * 10**6), 10**6)
    lo = exact_feasible(names, rows, obj, vq - eps); hi = exact_feasible(names, rows, obj, vq + eps)
    assert lo and not hi, (v, lo, hi)
    return vq
def verdict(t, delta, variant):
    """exact decision: can the adversary reach |U| + beta > 2t (by margin 1e-5)?"""
    out = {}
    for br in (("close",) if variant == "A" else ("close", "far")):
        names, rows, obj = build(t, delta, variant, br)
        out[br] = exact_feasible(names, rows, obj, 2*t + Fr(1, 10**5))
    return out
if __name__ == "__main__":
    for t in (Fr(33, 40), Fr(423, 500)):
        print(f"t = {float(t)}  (u_max = 1 - t/2 = {float(1 - t/2):.4f})")
        for variant in ("A", "B"):
            # largest delta on a 1/4000 grid for which every branch is infeasible for the adversary
            best = None
            for j in range(0, 600):
                d = Fr(j, 4000)
                if 1 - t/2 - d < Fr(1, 2): break
                if any(verdict(t, d, variant).values()): break
                best = d
            print(f"  variant {variant}: closes for delta <= {best} = {float(best) if best is not None else None}"
                  f"  i.e. u >= {float(1 - t/2 - best) if best is not None else None}")
        for u0 in (Fr(1, 2), Fr(11, 20)):
            d = 1 - t/2 - u0
            for variant in ("A", "B"):
                for br in (("close",) if variant == "A" else ("close", "far")):
                    print(f"    u = {float(u0)} (delta = {float(d):.4f}) variant {variant}/{br}: "
                          f"max |U|+beta = {certified_max(t, d, variant, br)}  vs 2t = {float(2*t)}")
