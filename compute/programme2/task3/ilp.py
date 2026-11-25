r"""Ground truth by integer programming on CELL COUNTS (exact reduction, notes section 2):
H = (a+C) cap (V choose k) has a Fano-type good seven  <=>  there are integers z_{g,J} >= 0
(g = class, J = admissible pattern) with
   sum_J z_{g,J} = N_g,   sum_{g, J ni l} z_{g,J} = k  (all l),
   sum_{g,J ni l} (z_{g,J} mod 2) g = alpha  (all l, in Q = F2^r),
   and the seven sets distinct.
A feasible point is turned into explicit sets and checked EXACTLY by core.verify_seven.
Also: minimum W = |O1|+|O2|+|O3| over pairwise disjoint O_i in a + C (with O_i of parity k when wanted).
"""
import pulp
from core import PATTERNS, LSET, popc

def solver(): return pulp.HiGHS(msg=False, timeLimit=600)

def good_seven_counts(cells, alpha, r, k):
    """cells: dict class -> N_g.  Returns dict (g, J) -> z or None (infeasible)."""
    P = pulp.LpProblem('g7', pulp.LpMinimize)
    z, b, t = {}, {}, {}
    for g, N in cells.items():
        for j, J in enumerate(PATTERNS):
            z[g, j] = P.add_variable(f'z_{g}_{j}', 0, N, cat='Integer')
            b[g, j] = P.add_variable(f'b_{g}_{j}', cat='Binary')
            t[g, j] = P.add_variable(f't_{g}_{j}', 0, N, cat='Integer')
            P += z[g, j] == 2 * t[g, j] + b[g, j]
    for g, N in cells.items():
        P += pulp.lpSum(z[g, j] for j in range(len(PATTERNS))) == N
    for l in range(7):
        P += pulp.lpSum(z[g, j] for g in cells for j, J in enumerate(PATTERNS) if l in J) == k
        for i in range(r):
            sv = P.add_variable(f's_{l}_{i}', 0, None, cat='Integer')
            P += pulp.lpSum(b[g, j] for g in cells if g >> i & 1 for j, J in enumerate(PATTERNS) if l in J) == 2 * sv + (alpha >> i & 1)
    for l in range(7):
        for l2 in range(7):
            if l != l2:
                P += pulp.lpSum(z[g, j] for g in cells for j, J in enumerate(PATTERNS) if l in J and l2 not in J) >= 1
    res = P.solve(solver())
    status = res.status.name
    if res.status != pulp.LpSolveStatus.Optimal: return None, status
    return {(g, PATTERNS[j]): int(round(z[g, j].value())) for g in cells for j in range(len(PATTERNS)) if round(z[g, j].value())}, status

def sets_from_counts(cs, zc):
    cells = {g: list(v) for g, v in cs.cells().items()}
    B = [0] * 7
    for (g, J), c in zc.items():
        for _ in range(c):
            x = cells[g].pop()
            for l in J: B[l] |= 1 << x
    return B

def min_triple(cs, k=None, bound=None):
    """min sum |O_i| over pairwise disjoint O_1,O_2,O_3 in a+C (if k given: each |O_i| = k mod 2).
    Returns (W, [O1,O2,O3]) or (None, None)."""
    cells = cs.cells(); r = cs.r
    P = pulp.LpProblem('tri', pulp.LpMinimize)
    o, bb, tt = {}, {}, {}
    for i in range(3):
        for g, pts in cells.items():
            o[i, g] = P.add_variable(f'o_{i}_{g}', 0, len(pts), cat='Integer')
            bb[i, g] = P.add_variable(f'ob_{i}_{g}', cat='Binary')
            tt[i, g] = P.add_variable(f'ot_{i}_{g}', 0, len(pts), cat='Integer')
            P += o[i, g] == 2 * tt[i, g] + bb[i, g]
        for j in range(r):
            sv = P.add_variable(f'os_{i}_{j}', 0, None, cat='Integer')
            P += pulp.lpSum(bb[i, g] for g in cells if g >> j & 1) == 2 * sv + (cs.alpha >> j & 1)
        if k is not None:
            sv = P.add_variable(f'op_{i}', 0, None, cat='Integer')
            P += pulp.lpSum(o[i, g] for g in cells) == 2 * sv + (k & 1)
    for g, pts in cells.items():
        P += pulp.lpSum(o[i, g] for i in range(3)) <= len(pts)
    P += pulp.lpSum(o.values())
    res = P.solve(solver())
    if res.status != pulp.LpSolveStatus.Optimal: return None, None
    pools = {g: list(v) for g, v in cells.items()}
    Os = []
    for i in range(3):
        O = 0
        for g in cells:
            for _ in range(int(round(o[i, g].value()))): O |= 1 << pools[g].pop()
        Os.append(O)
    for O in Os: assert cs.syn(O) == cs.alpha
    return sum(popc(O) for O in Os), Os
