"""Coarse (asymptotic) version of block-type families.

Normalize by r. A coarse family: block masses beta_b > 0 (ground set size n = r * sum beta),
and a finite set S of allowed normalized types c (c_b >= 0, sum c = 1, c_b <= beta_b).
It models, for huge r, the family of all r-sets whose block profile is within o(r) of a type in S.

  tau/r -> min sum t_b  s.t. for every c in S there is b with t_b >= beta_b - c_b.
  bad 7-tuple exists (robustly) iff the MILP below is feasible: continuous signature masses
  m[b][s] >= 0 summing to beta_b, presence binaries z[s] forbidding complementary-covering
  pairs, and each edge's profile equal to some c in S.

Closed (non-strict) inequalities are used throughout, so a coarse family declared GOOD avoids bad
configurations even on the boundary: it is a robust candidate. Exact-boundary tricks (like FKW's
parity, which lives exactly at n = 7k+1) only contribute +O(1) and are invisible here.
"""
from __future__ import annotations

import itertools
from fractions import Fraction

import pulp


def coarse_tau(beta, S):
    """LP-free exact tau for coarse families: try all 'blocking' assignments.

    For each type c we must pick a block b(c) with t_b >= beta_b - c_b. Given the choice,
    t_b = max over c assigned to b of (beta_b - c_b). Minimize over choices; small instances only.
    We do it smarter: t is determined by thresholds; enumerate candidate t_b values from the set
    {0} ∪ {beta_b - c_b : c in S}.
    """
    m = len(beta)
    cands = [sorted({0} | {beta[b] - c[b] for c in S if beta[b] - c[b] > 0}) for b in range(m)]
    best = None
    for t in itertools.product(*cands):
        if all(any(t[b] >= beta[b] - c[b] for b in range(m)) for c in S):
            v = sum(t)
            if best is None or v < best[0]:
                best = (v, t)
    return best


def coarse_bad(beta, S, p=7, msg=False):
    m = len(beta)
    full = (1 << p) - 1
    sigs = range(1 << p)
    prob = pulp.LpProblem("coarse_bad", pulp.LpMinimize)
    mv = {(b, s): prob.add_variable(f"m_{b}_{s}", 0, float(beta[b])) for b in range(m) for s in sigs}
    z = {s: prob.add_variable(f"z_{s}", cat="Binary") for s in sigs}
    for b in range(m):
        prob += pulp.lpSum(mv[b, s] for s in sigs) == float(beta[b])
        for s in sigs:
            prob += mv[b, s] <= float(beta[b]) * z[s]
    prob += z[full] == 0
    for s in sigs:
        for s2 in sigs:
            if s < s2 and (s | s2) == full:
                prob += z[s] + z[s2] <= 1
    S = list(S)
    y = {(i, j): prob.add_variable(f"y_{i}_{j}", cat="Binary") for i in range(p) for j in range(len(S))}
    for i in range(p):
        prob += pulp.lpSum(y[i, j] for j in range(len(S))) == 1
        for b in range(m):
            prob += (pulp.lpSum(mv[b, s] for s in sigs if s >> i & 1)
                     == pulp.lpSum(float(S[j][b]) * y[i, j] for j in range(len(S))))
    idx = [pulp.lpSum(j * y[i, j] for j in range(len(S))) for i in range(p)]
    for i in range(p - 1):
        prob += idx[i] <= idx[i + 1]
    stats = prob.solve(pulp.HiGHS(msg=msg))
    st = stats.status.name
    if st == "Infeasible":
        return None
    if st != "Optimal":
        raise RuntimeError(st)
    used = sorted({S[j] for i in range(p) for j in range(len(S)) if round(y[i, j].value()) == 1})
    return used


def grid_types(beta, q):
    """All types with coordinates in (1/q)Z, sum 1, c_b <= beta_b."""
    m = len(beta)
    out = []
    for c in itertools.product(range(q + 1), repeat=m):
        if sum(c) == q:
            cc = tuple(Fraction(x, q) for x in c)
            if all(cc[b] <= beta[b] for b in range(m)):
                out.append(cc)
    return out


def best_good_subfamily(beta, S, time_budget=300):
    """Branch and bound: maximize coarse tau over subsets of S without robust bad 7-tuples."""
    import time
    t0 = time.time()
    conflicts = []
    best = {"tau": Fraction(0), "S": None}
    seen = set()

    def rec(T: frozenset, banned: frozenset):
        if time.time() - t0 > time_budget or T in seen or not T:
            return
        seen.add(T)
        tv = coarse_tau(beta, T)[0]
        if tv <= best["tau"]:
            return
        C = next((c for c in conflicts if c <= T), None)
        if C is None:
            used = coarse_bad(beta, T)
            if used is None:
                best["tau"], best["S"] = tv, T
                return
            C = frozenset(used)
            conflicts.append(C)
        for typ in sorted(C - banned):
            rec(T - {typ}, banned)
            banned = banned | {typ}

    rec(frozenset(S), frozenset())
    return best, len(conflicts), time.time() - t0


if __name__ == "__main__":
    import sys
    # sanity: complete coarse family nu = beta (one block). Good iff nu < 7/4 (boundary is bad
    # in the closed model), tau = nu - 1.
    for nu in (Fraction(3, 2), Fraction(7, 4), Fraction(9, 5)):
        S = [(Fraction(1),)]
        print("complete nu =", nu, "tau =", coarse_tau([nu], S)[0], "bad:", coarse_bad([nu], S) is not None)
    q = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    # two blocks: beta in grid of quarters, total mass in (7/4, 2]
    found = []
    for a4 in range(1, 8):
        for b4 in range(1, 8):
            beta = (Fraction(a4, 4), Fraction(b4, 4))
            if not (Fraction(7, 4) <= sum(beta) <= 2) or a4 > b4 + 3:
                continue
            S = grid_types(beta, q)
            best, nc, dt = best_good_subfamily(beta, S, budget)
            print(f"beta={tuple(map(str, beta))}: best robust tau/r = {best['tau']} ({float(best['tau']):.3f})"
                  f"  conflicts={nc} ({dt:.0f}s)", flush=True)
            if best["tau"] > Fraction(3, 4):
                found.append((best["tau"], beta, sorted(best["S"])))
    print("beats 3/4:", found)
