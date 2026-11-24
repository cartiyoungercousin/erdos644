"""CORE Part IX: structured positions for the multi-pair triangle exhaustion.
n = 2q replies in q disjoint pairs, each pair balanced (|Ki & Kj| = o); request S triangle-type for every pair
(nothing of Ki & Kj, a of each private part); minimise f = unrequested mass lying inside ALL unions Ki u Kj.
Any dump then has >= (omega - f)/q outside some pair's union.  The LP designs (position, request); the engine checks
(i) the least need among the existing readings, (ii) his menu / random dumps.
Usage: py spoil_struct.py t N q seed [a_slack]"""
import sys, json, random, itertools
import pulp
import spoil as SP, spoil_hunt as H

def design(t, N, q, rng, extra=None, a=None, o=None):
    n = 2 * q; c = N - 1; om = N - 1 - t; eps = t - 0.75
    a = N / 2 - 0.625 if a is None else a; o = a + eps / 2 if o is None else o
    pairs = [(2 * i, 2 * i + 1) for i in range(q)]
    cells = range(1 << n)
    pr = pulp.LpProblem("d", pulp.LpMinimize)
    m = {J: pr.add_variable(f"m{J}", 0.0, None, "Continuous") for J in cells}; s = {J: pr.add_variable(f"s{J}", 0.0, None, "Continuous") for J in cells}
    f = pulp.lpSum(m[J] - s[J] for J in cells if all(J >> i & 1 or J >> j & 1 for i, j in pairs))
    pr += f + 1e-3 * pulp.lpSum(rng.random() * m[J] for J in cells) + 1e-3 * pulp.lpSum(rng.random() * s[J] for J in cells)
    pr += pulp.lpSum(m.values()) == N; pr += pulp.lpSum(s.values()) == t
    for J in cells: pr += s[J] <= m[J]
    for i in range(n): pr += pulp.lpSum(m[J] for J in cells if J >> i & 1) == c
    for i, j in pairs:
        pr += pulp.lpSum(m[J] for J in cells if J >> i & 1 and J >> j & 1) == o
        for J in cells:
            if J >> i & 1 and J >> j & 1: pr += s[J] == 0
        pr += pulp.lpSum(s[J] for J in cells if J >> i & 1 and not J >> j & 1) == a
        pr += pulp.lpSum(s[J] for J in cells if J >> j & 1 and not J >> i & 1) == a
    if extra: extra(pr, m, s, cells, pairs)
    res = pr.solve(pulp.HiGHS(msg=False))
    if res.status_str != "Optimal": return None
    M = {J: pulp.value(m[J]) for J in cells if pulp.value(m[J]) > 1e-9}
    S = {J: min(pulp.value(s[J]), M[J]) for J in cells if J in M and pulp.value(s[J]) > 1e-9}
    return M, S, pulp.value(f)

if __name__ == "__main__":
    t, N, q, seed = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed); E = SP.Engine(t, N); n = 2 * q
    for trial in range(int(sys.argv[5]) if len(sys.argv) > 5 else 5):
        r = design(t, N, q, rng)
        if r is None: print("infeasible"); break
        M, S, f = r
        vold, arg = E.min_need(M, n, want_arg=True)
        target = min(vold, E.base)
        best = -9; bd = None
        for d in E.menu(M, S, 1) + H.random_fills(E, M, S, rng, 300):
            v = E.min_need(E.step(M, S, d, 1 << n), n + 1, new=n, stop_below=best)
            if v > best: best, bd = v, d
        print(json.dumps(dict(trial=trial, ncells=len(M), f=f, omega=E.om, base=E.base, vold=vold, vold_arg=str(arg), his_best=best, his_dump=SP.fmt(bd),
                              pos=SP.fmt(M), s=SP.fmt(S)))[:1500], flush=True)
