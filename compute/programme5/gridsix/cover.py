"""First-order static cover of an alive cell-pair graph.  [exact MILP, SCIP]
A point of cell c is described by its membership vector v in {0,1}^r (which of the r requests contain it); points of
one cell with the same v are interchangeable, so a cover is a mass distribution n[c,v] with sum_v n[c,v] = |c|.
Alive pair (c,d) is killed iff every pair of used vectors (v on c, w on d) shares a request (v.w >= 1).
Request i has size sum_{c, v_i = 1} n[c,v].  min_t returns the least max request size (exact for the model).
Cells of mass 0 are dropped; a cell of mass 0+ should be given a tiny mass by the caller."""
import itertools
from ortools.linear_solver import pywraplp

SUPPORT = set()   # (cell, vector) pairs with binary s = 1 in the last min_t solution


def min_t(sizes, alive, r, fixed=None, tl=60, budgets=None):
    """sizes: {cell: mass}; alive: iterable of (c, d) (c == d allowed); r: number of requests.
    budgets: optional list of r per-request caps (then minimise the common excess over them).
    fixed: optional {(i, c): amount} lower bounds on request i's amount in cell c.
    Returns (t, plan) with plan = {(c, v): mass} or (None, status)."""
    cells = [c for c in sizes if sizes[c] > 0]
    al = [(c, d) for c, d in alive if c in cells and d in cells]
    used = set(c for p in al for c in p)
    V = [v for v in itertools.product((0, 1), repeat=r) if any(v)]
    sv = pywraplp.Solver.CreateSolver('SCIP'); inf = sv.infinity()
    n, s = {}, {}
    for c in used:
        for v in V:
            n[c, v] = sv.NumVar(0, sizes[c], ''); s[c, v] = sv.BoolVar('')
            sv.Add(n[c, v] <= sizes[c] * s[c, v])
        sv.Add(sum(n[c, v] for v in V) == sizes[c])
    for c, d in al:
        for v in V:
            for w in V:
                if not any(a and b for a, b in zip(v, w)):
                    if c == d and v == w: sv.Add(s[c, v] == 0)
                    elif c == d and v > w: continue
                    else: sv.Add(s[c, v] + s[d, w] <= 1)
    t = sv.NumVar(0, inf, 't')
    for i in range(r):
        load = sum(n[c, v] for c in used for v in V if v[i])
        if budgets: sv.Add(load <= budgets[i] + t)
        else: sv.Add(load <= t)
        if fixed:
            for (j, c), amt in fixed.items():
                if j == i: sv.Add(sum(n[c, v] for v in V if v[i]) >= amt)
    sv.Minimize(t); sv.SetTimeLimit(int(tl * 1000))
    st = sv.Solve()
    if st != pywraplp.Solver.OPTIMAL: return None, st
    plan = {(c, v): n[c, v].solution_value() for c in used for v in V if n[c, v].solution_value() > 1e-9}
    SUPPORT.clear(); SUPPORT.update({(c, v) for c in used for v in V if s[c, v].solution_value() > 0.5})
    return t.solution_value(), plan


def requests(plan, r):
    out = [dict() for _ in range(r)]
    for (c, v), m in plan.items():
        for i in range(r):
            if v[i]: out[i][c] = out[i].get(c, 0) + m
    return out


def check(plan, alive, r):
    """independent re-check of a plan: every alive pair of used vectors intersects; returns max request load"""
    for c, d in alive:
        for (c1, v), m1 in plan.items():
            if c1 != c: continue
            for (d1, w), m2 in plan.items():
                if d1 != d: continue
                if not any(a and b for a, b in zip(v, w)): return None
    return max(sum(m for (c, v), m in plan.items() if v[i]) for i in range(r))


if __name__ == '__main__':
    # grid frame vs passive play after Theorem P's K (units k/14): rows X, B; columns A, Y; alive (X u B) x A u B x Y
    S = {'X': 6, 'B': 7, 'A': 7, 'Y': 5}
    al = [('X', 'A'), ('B', 'A'), ('B', 'Y')]
    for r in (3, 4, 5):
        tt, pl = min_t(S, al, r)
        print(r, tt, check(pl, al, r), requests(pl, r))
