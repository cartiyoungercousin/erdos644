"""Referee check (independent code): static certificates by exact co-type MILP.

A static certificate with q members used in full: seven subsets of an n-point ground,
sets 0..q-1 of size exactly c = n - k (members), sets q..6 of size <= T (lines),
such that every pair of points (x = y included) lies in a common set.
Equivalently: every point has a nonempty co-type J in [7] and the co-types that occur
are pairwise intersecting. We count points by co-type (127 integer variables) and forbid
two disjoint co-types from both occurring. Exact for the given (k, T, n, q).

Usage:  py -3.14 static_cert.py q2 | q3 | pool | sat
"""
import sys
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

TYPES = list(range(1, 128))
POP = [bin(J).count("1") for J in TYPES]
DISJ = [(a, b) for a in range(127) for b in range(a + 1, 127) if TYPES[a] & TYPES[b] == 0]


def solve(k, T, n, q, objective=None, common_min=0, forbid_small=False):
    """Return (feasible, max objective, dict cotype -> count)."""
    c = n - k
    nv = 254  # n_J (0..126), y_J (127..253)
    rows, lo, hi = [], [], []

    def add(coefs, l, h):
        rows.append(coefs); lo.append(l); hi.append(h)

    add({a: 1 for a in range(127)}, n, n)
    for i in range(7):
        coefs = {a: 1 for a in range(127) if TYPES[a] >> i & 1}
        if i < q:
            add(coefs, c, c)
        else:
            add(coefs, 0, T)
    for a in range(127):
        add({a: 1, 127 + a: -n}, -np.inf, 0)      # n_J <= n*y_J
        add({a: 1, 127 + a: -1}, 0, np.inf)       # y_J <= n_J
    for a, b in DISJ:
        add({127 + a: 1, 127 + b: 1}, -np.inf, 1)
    if common_min:
        add({126: 1}, common_min, np.inf)
    A = lil_matrix((len(rows), nv))
    for r, coefs in enumerate(rows):
        for j, v in coefs.items():
            A[r, j] = v
    ub = np.array([n] * 127 + [1] * 127, dtype=float)
    if forbid_small:
        for a in range(127):
            if POP[a] <= 2:
                ub[a] = 0
    cost = np.zeros(nv)
    if objective is not None:
        for a in range(127):
            cost[a] = -objective(TYPES[a], POP[a])
    res = milp(c=cost, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=np.ones(nv),
               bounds=Bounds(np.zeros(nv), ub), options={"mip_rel_gap": 0.0})
    if res.status == 2:
        return False, None, None
    assert res.status == 0, res.message
    x = np.rint(res.x[:127]).astype(int)
    return True, int(round(-float(cost @ res.x))), {TYPES[a]: int(x[a]) for a in range(127) if x[a]}


def Sq(k, T, n, q):
    return q * (n - k) + (7 - q) * T - 3 * n     # = k * S_q(N, t)


def run_q2():
    print("q = 2 static certificates. Claim (102.1): exist only if n <= 5T - 2k, and then 4|S| <= 5T - 2k - n.")
    print("Rows: k T n | kS_2 = 5T-2k-n | feasible | max|S| | verdict")
    bad = 0
    for k in (4, 8, 12, 16, 20):
        for T in range((3 * k + 3) // 4, k):
            for n in range(k + T, 3 * k - T + 3):
                s2 = Sq(k, T, n, 2)
                feas, val, sol = solve(k, T, n, 2, objective=lambda J, p: 1 if J == 127 else 0)
                ok = (not feas) or (s2 >= 0 and 4 * val <= s2)
                bad += (not ok)
                print(k, T, n, "|", s2, "|", feas, "|", val, "|", "ok" if ok else "VIOLATION",
                      "(n>=2k)" if n >= 2 * k else "",
                      "(no cert though budget>=0)" if (s2 >= 0 and not feas) else "")
    print("violations of the claim:", bad)


def run_q3():
    print("q >= 3: max over certificates of W+ + 4|S| (W+ = waste on points outside S with |J|>=3),")
    print("against kS_q. 'hyp' = same with co-types of size <= 2 forbidden (the hypothesis of 102.1).")
    print("Rows: k T n q | kS_q | max free | max hyp | size<=2 co-type mass at the free max")
    obj = lambda J, p: 4 if J == 127 else max(p - 3, 0)
    viol = 0
    for k in (8, 12, 16):
        T = (3 * k) // 4 + (0 if k == 8 else 1)
        for n in range(2 * k - 1, 3 * k - T):
            for q in (3, 4, 5, 7):
                f1, v1, s1 = solve(k, T, n, q, objective=obj)
                f2, v2, _ = solve(k, T, n, q, objective=obj, forbid_small=True)
                m2 = sum(v for J, v in (s1 or {}).items() if bin(J).count("1") <= 2)
                flag = ""
                if f1 and v1 > Sq(k, T, n, q):
                    flag = "EXCEEDS S_q (hypothesis fails)"; viol += 1
                if f2 and v2 > Sq(k, T, n, q):
                    flag += " THEOREM VIOLATED"
                print(k, T, n, q, "|", Sq(k, T, n, q), "|", v1 if f1 else "infeasible", "|",
                      v2 if f2 else "infeasible", "|", m2, flag)
                sys.stdout.flush()
    print("instances where the budget is exceeded without the hypothesis:", viol)


def run_pool():
    print("Pool family P_Y in a link at S disjoint from Y (|Y| = c - T, |S| = s): is there a good seven?")
    print("= seven (c-s)-sets on n-s points, common part >= c-T, covering all pairs. Claim 100.3: none once s > T - 3k/4.")
    bad = 0
    for k in (8, 12, 16, 20):
        for T in range((3 * k + 3) // 4, min(k, (3 * k) // 4 + 4)):
            for n in sorted({5 * T - 2 * k + 1, (4 * T + k) // 2, 2 * k, 3 * k - T - 1}):
                if not (k + T <= n < 3 * k - T):
                    continue
                for s in range(0, T - (3 * k) // 4 + 3):
                    feas, _, _ = solve(k, T - s, n - s, 7, common_min=(n - k) - T)
                    m4 = 4 * s - (4 * T - 3 * k)
                    ok = not (feas and m4 > 0)
                    bad += (not ok)
                    print(k, T, n, s, "| 4(s - eps k) =", m4, "| good seven:", feas, "" if ok else "VIOLATION",
                          "(none although s <= eps k: rounding)" if (not feas and m4 <= 0) else "")
    print("violations:", bad)
    print()
    print("Link INSIDE the core (S subset of Y, s = a): 100.1(c) read literally says no good seven for s > eps k.")
    for (k, T, n) in ((8, 6, 16), (12, 9, 23), (16, 13, 31)):
        y = (n - k) - T
        for a in range(0, y + 1):
            feas, _, _ = solve(k, T - a, n - a, 7, common_min=y - a)
            print(k, T, n, "s = a =", a, "| 4(s - eps k) =", 4 * a - (4 * T - 3 * k), "| good seven:", feas)


def run_sat():
    """Cross-check of the MILP by a point-level SAT model on small cases."""
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool

    def sat(k, T, n, q):
        c = n - k
        pool = IDPool()
        cls = []
        a = [[pool.id(("a", i, x)) for x in range(n)] for i in range(7)]
        for i in range(7):
            cls += CardEnc.atmost(lits=a[i], bound=(c if i < q else T), vpool=pool,
                                  encoding=EncType.seqcounter).clauses
        for x in range(n):
            for y in range(x, n):
                zs = []
                for i in range(7):
                    z = pool.id(("z", i, x, y))
                    zs.append(z)
                    cls += [[-z, a[i][x]], [-z, a[i][y]]]
                cls.append(zs)
        for x in range(c if q else T):
            cls.append([a[0][x]])
        with Cadical153(bootstrap_with=cls) as S:
            return S.solve()

    print("SAT cross-check (k T n q | SAT | MILP)")
    # satisfiable cases plus small unsatisfiable ones (counting-type UNSAT is slow for CDCL at k = 8)
    for (k, T, n, q) in ((4, 3, 7, 2), (4, 3, 8, 2), (8, 6, 14, 2), (8, 7, 19, 2), (4, 3, 8, 3),
                         (8, 6, 15, 3), (8, 6, 17, 3), (8, 6, 14, 7), (5, 4, 9, 7), (5, 4, 10, 3)):
        r1 = sat(k, T, n, q)
        r2 = solve(k, T, n, q)[0]
        print(k, T, n, q, "|", r1, "|", r2, "" if r1 == r2 else "MISMATCH")
        sys.stdout.flush()


if __name__ == "__main__":
    {"q2": run_q2, "q3": run_q3, "pool": run_pool, "sat": run_sat}[sys.argv[1]]()
