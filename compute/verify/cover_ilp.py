"""Independent exact ILP for C(v,k,2): one binary per k-subset, one covering row per pair (HiGHS via pulp)."""
import itertools, sys, time, pulp
def solve(v, k, tl=1500):
    blocks = list(itertools.combinations(range(v), k))
    P = pulp.LpProblem("cov", pulp.LpMinimize)
    x = [P.add_variable(f"x{i}", cat="Binary") for i in range(len(blocks))]
    P += pulp.lpSum(x)
    for p, q in itertools.combinations(range(v), 2):
        P += pulp.lpSum(x[i] for i, B in enumerate(blocks) if p in B and q in B) >= 1
    P += x[0] == 1   # symmetry: block {0..k-1} may be assumed present (transitivity of S_v on k-sets)
    st = P.solve(pulp.HiGHS(msg=False, timeLimit=tl))
    chosen = [blocks[i] for i in range(len(blocks)) if x[i].value() > 0.5]
    ok = all(any(p in B and q in B for B in chosen) for p, q in itertools.combinations(range(v), 2))
    return st.status_str, len(chosen), ok, chosen
if __name__ == "__main__":
    for v, k in [(9,4),(10,5),(10,4),(11,5),(12,5),(13,6)]:
        t = time.time(); s, n, ok, ch = solve(v, k)
        print(f"C({v},{k},2): status={s} value={n} witness_ok={ok} ({time.time()-t:.1f}s)", flush=True)
        print("  ", ch, flush=True)
