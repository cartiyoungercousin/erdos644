"""m = 8, one discard, ground set of mass N (pool of untouched points), scripted adversaries, requester free.
Exact value per (T, N, script) = min over discarded reply in {1, 2} of one MILP each (the requester is
restricted to discarding reply 1 or 2: a negative value is a rigorous requester win against that script)."""
import sys, time
from concurrent.futures import ProcessPoolExecutor
import pivot
from pivot import POOLFIRST, WASTE, GIFT, LOW, HIGH, ONE
F = ("forced",)
SC = {
 "W,T8  (reply 2 disjoint, freeze Z in A_1, then forced)": [("greedy", WASTE, False), ("greedy", ONE, True)] + [F] * 5,
 "W,L   (reply 2 disjoint, then omit lowest degree incl. pool)": [("greedy", WASTE, False)] + [("greedy", LOW, False)] * 6,
 "W,H   (reply 2 disjoint, then omit highest degree)": [("greedy", WASTE, False)] + [("greedy", HIGH, False)] * 6,
 "W,G   (reply 2 disjoint, then fresh points first, omit lowest positive degree)": [("greedy", WASTE, False)] + [("greedy", GIFT, False)] * 6,
 "PF    (never a fresh point: omit pool first every round)": [("greedy", POOLFIRST, False)] * 7,
}
def job(a):
    T, N, name, d, tl = a
    t0 = time.time()
    st, zv, drop, bd = pivot.solve(T, 7, SC[name], N=N, keep=6, tl=tl, start2=False, only_drop=(d,))
    return (T, N, name, d, st, zv, bd, time.time() - t0)
if __name__ == "__main__":
    tl = float(sys.argv[1])
    jobs = [(T, N, name, d, tl) for T in (0.76, 0.80) for N in (2.0, 2.15, 7 / 3) for name in SC for d in (0, 1)]
    out = open("ntable.log", "a")
    res = {}
    with ProcessPoolExecutor(max_workers=7) as ex:
        for T, N, name, d, st, zv, bd, tt in ex.map(job, jobs, chunksize=1):
            line = f"T={T} N={N:.3f} [{name}] discard {d+1}: {st} value {zv if zv is None else round(zv,4)} bound {round(bd,4)} [{tt:.0f}s]"
            print(line, flush=True); out.write(line + "\n"); out.flush()
            res.setdefault((T, N, name), []).append((zv, bd, st))
    for (T, N, name), v in res.items():
        vals = [x[0] for x in v if x[0] is not None]; bds = [x[1] for x in v]
        line = f"SUMMARY T={T} N={N:.3f} [{name}]: value (discards 1,2) incumbent {min(vals):+.4f} lower bound {min(bds):+.4f} all optimal {all(x[2]=='Optimal' for x in v)}"
        print(line, flush=True); out.write(line + "\n")
