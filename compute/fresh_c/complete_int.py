"""Integer version of 'is the complete k-uniform family on N points (7,2)?'.
It fails (7,2) iff there are 7 k-subsets whose M-family is intersecting, i.e. iff there are non-negative
INTEGERS n_S (S a non-empty subset of [7], supported on an intersecting family) with sum n_S = N and
sum_{S containing i} n_S = N - k for every i.  Small exact ILP (pulp/HiGHS)."""
import pulp, sys
SUBS = list(range(1, 128))
def fails(k, N):
    prob = pulp.LpProblem("c", pulp.LpMinimize)
    z = {}
    for S in SUBS:
        if S == 127: continue
        c = 127 ^ S
        if S < c: z[S] = prob.add_variable(f"z{S}", cat="Binary")
    def Z(S):
        if S == 127: return 1
        c = 127 ^ S
        return z[S] if S < c else 1 - z[c]
    for S in SUBS:
        if S == 127: continue
        for i in range(7):
            if not (S >> i) & 1 and (S | (1 << i)) != 127:
                prob += Z(S) <= Z(S | (1 << i))
    n = {S: prob.add_variable(f"n{S}", 0, N, "Integer") for S in SUBS}
    for S in SUBS:
        if S != 127: prob += n[S] <= N * Z(S)
    prob += pulp.lpSum(n.values()) == N
    for i in range(7):
        prob += pulp.lpSum(n[S] for S in SUBS if (S >> i) & 1) == N - k
    res = prob.solve(pulp.HiGHS(msg=False, timeLimit=120))
    return res.status_str
for k in range(4, 17):
    row = []
    best = None
    for N in range(-(-7 * k // 4) - 2, 2 * k + 1):
        st = fails(k, N)
        row.append(f"N={N}:{'bad7' if st == 'Optimal' else ('(7,2)' if st == 'Infeasible' else st)}")
        if st == "Infeasible": best = N
        if st == "Optimal" and N > 7 * k / 4 + 1: break
    print(f"k={k}: 7k/4={7*k/4:.2f}  largest N with complete family (7,2): {best}  => tau = {best - k + 1} (ceil(3k/4) = {-(-3*k//4)})   [{' '.join(row)}]", flush=True)
