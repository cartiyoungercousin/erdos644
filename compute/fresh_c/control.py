"""m = 8, one discard, T as given: per-discard decomposition (one small MILP per discarded reply; the value
of the game against a deterministic adversary is the min over the discarded reply)."""
import sys, time
import discard, pivot
T = float(sys.argv[1]); which = sys.argv[2]; tl = float(sys.argv[3]) if len(sys.argv) > 3 else 150
E = 7
def run(name, fn):
    t0 = time.time(); vals = {}
    for j in range(E):
        st, zv, drop, extra = fn((j,))
        bd = extra["bound"] if isinstance(extra, dict) else extra
        vals[j + 1] = (zv, bd, st)
    best = min(v[0] for v in vals.values() if v[0] is not None)
    lb = min(v[1] for v in vals.values())
    allopt = all(v[2] == "Optimal" for v in vals.values())
    verdict = "ADVERSARY wins" if lb > 1e-6 else ("requester wins" if best <= 1e-6 else "undecided")
    print(f"m=8 one discard T={T} [{name}]: min over discards of (mass(D)-T) = {best:+.4f} (lower bound {lb:+.4f}, all optimal: {allopt}) -> {verdict}"
          f"   per discarded reply: " + " ".join(f"{j}:{v[0]:+.3f}" for j, v in vals.items()) + f"  [{time.time()-t0:.0f}s]", flush=True)
if which in ("forced", "all"):
    for name, sc in discard.scripts(T).items():
        run(name, lambda d, sc=sc: discard.solve(T, E, keep=6, only_drop=d, tl=tl, **sc))
if which in ("pivot", "all"):
    for name, sc in pivot.SCRIPTS.items():
        run(name, lambda d, sc=sc: pivot.solve(T, E, sc, keep=6, only_drop=d, tl=tl))
