r"""Structured construction with the Y-step done by ILP (instead of the cell-parity rule of (C1)).
Same skeleton as construct.py: Omega_i on triangles T_i (odd cover), fixer pair on T* if f = 1,
u unused points, every other point of V' on an anti-pencil (colour class Y_p, |Y_p| = m_p).
The ILP only chooses WHICH points are unused / in the fixer / in which Y_p, subject to
[R_l cap Y] = 0 for all l.  Output verified exactly by the caller."""
import itertools, pulp
from core import LSET, popc
from construct import ODD_TRIPLES, BRIEF_TRIPLES, BRIEF_FIX, TRIANGLES, m_vector

def construct_ilp(cs, k, Omegas, brief=False):
    n = cs.n
    w = [popc(O) for O in Omegas]; W = sum(w); s = 4 * n - 7 * k - W
    if s < 0 or any((x - k) % 2 for x in w): return None, 'H0/H1'
    f = ((k - W) % 4) // 2; u = (s - 2 * f) // 4
    Vp = ((1 << n) - 1) & ~(Omegas[0] | Omegas[1] | Omegas[2])
    cells = cs.cells(Vp)
    cands = []
    for tri in (BRIEF_TRIPLES if brief else ODD_TRIPLES):
        for perm in itertools.permutations(range(3)):
            for Ts in ((BRIEF_FIX if brief else TRIANGLES) if f else [frozenset()]):
                e = [0] * 7
                for i in range(3):
                    for l in tri[perm[i]]: e[l] += w[i]
                for l in Ts: e[l] += 2 * f
                m = m_vector(k, e)
                if m is not None and min(m) >= 0: cands.append((tuple(m), tri, perm, Ts))
    if not cands: return None, 'H2: no nonnegative m'
    seen = {}
    for c in cands: seen.setdefault(c[0], c)
    for m, tri, perm, Ts in sorted(seen.values(), key=lambda c: -min(c[0]))[:6]:
        for fg in ([g for g in cells if len(cells[g]) >= 2] if f else [None]):
            P = pulp.LpProblem('y', pulp.LpMinimize)
            y = {(g, p): P.add_variable(f'y_{g}_{p}', 0, len(cells[g]), cat='Integer') for g in cells for p in range(7)}
            b = {(g, p): P.add_variable(f'b_{g}_{p}', cat='Binary') for g in cells for p in range(7)}
            hh = {(g, p): P.add_variable(f'h_{g}_{p}', 0, len(cells[g]), cat='Integer') for g in cells for p in range(7)}
            uu = {g: P.add_variable(f'u_{g}', 0, len(cells[g]), cat='Integer') for g in cells}
            for g in cells:
                for p in range(7): P += y[g, p] == 2 * hh[g, p] + b[g, p]
                P += pulp.lpSum(y[g, p] for p in range(7)) + uu[g] == len(cells[g]) - (2 if g == fg else 0)
            P += pulp.lpSum(uu.values()) == u
            for p in range(7): P += pulp.lpSum(y[g, p] for g in cells) == m[p]
            for l in range(7):
                for i in range(cs.r):
                    sv = P.add_variable(f's_{l}_{i}', 0, None, cat='Integer')
                    P += pulp.lpSum(b[g, p] for g in cells if g >> i & 1 for p in range(7) if p not in LSET[l]) == 2 * sv
            res = P.solve(pulp.HiGHS(msg=False, timeLimit=120))
            if res.status != pulp.LpSolveStatus.Optimal: continue
            pools = {g: list(v) for g, v in cells.items()}
            F = 0
            if fg is not None: F = (1 << pools[fg].pop()) | (1 << pools[fg].pop())
            Y = [0] * 7
            for g in cells:
                for p in range(7):
                    for _ in range(int(round(y[g, p].value()))): Y[p] |= 1 << pools[g].pop()
            B = [0] * 7
            for l in range(7):
                for p in range(7):
                    if p not in LSET[l]: B[l] |= Y[p]
            for i in range(3):
                for l in tri[perm[i]]: B[l] |= Omegas[i]
            for l in Ts: B[l] |= F
            return B, dict(m=list(m), f=f, u=u)
    return None, 'Y-step infeasible'
