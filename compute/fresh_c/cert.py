r"""Certified requester-vs-pool value by decomposition over the requester's discard pattern.

For a pool (menus on the game tree) the requester's problem is
      v_pool = min over discard patterns p (one discard per leaf) of  v(p),
      v(p)   = min over request trees of max over leaves of (mass(D_{p(leaf)}) - T)      [one MILP, no pick variables].
Each v(p) is solved separately (in parallel).  v_pool > 0 for all patterns  ==> the pool adversary beats every
requester (for the discards modelled).  Monotonicity used for pruning: dropping leaves can only lower v."""
import sys, time, itertools, pulp
from concurrent.futures import ProcessPoolExecutor
from do_loop import Tree2, pstr, tstr, val, E

def leaves_of(menus, default=("L",)):
    out = []
    def rec(path, e):
        if e == E: out.append(path); return
        for rule in menus.get(path, [default]): rec(path + (rule,), e + 1)
    rec((), 2)
    return out

def solve_pattern(args):
    T, menus, pattern, tl = args
    t0 = time.time()
    t = Tree2(T, menus, leafdisc={p: (d,) for p, d in pattern.items()}, tl=tl)
    r = t.res
    zv = pulp.value(t.z) if r.has_solution else None
    return (pattern, r.status_str, zv, r.best_bound, time.time() - t0)

def pool_value(T, menus, discards=(0, 1), tl=600, workers=7, log=print):
    leaves = leaves_of(menus)
    pats = [dict(zip(leaves, ds)) for ds in itertools.product(discards, repeat=len(leaves))]
    with ProcessPoolExecutor(max_workers=workers) as ex:
        res = list(ex.map(solve_pattern, [(T, menus, p, tl) for p in pats], chunksize=1))
    inc = min((x[2] for x in res if x[2] is not None), default=None)
    lb = min(x[3] for x in res)
    nopt = sum(1 for x in res if x[1] == "Optimal")
    return inc, lb, nopt, len(res), res

if __name__ == "__main__":
    T = float(sys.argv[1]); tl = float(sys.argv[2])
    L = ("L",)
    menus = {(L, L): [L, (6, "H"), (10, "L"), (10, "H")]}     # the four-rule fork at reply 5 from do_loop iteration 0
    t0 = time.time()
    inc, lb, nopt, n, res = pool_value(T, menus, tl=tl)
    print(f"T={T} 4-rule fork: {n} discard patterns, {nopt} optimal; v_pool incumbent {inc:+.4f}, certified lower bound {lb:+.4f} [{time.time()-t0:.0f}s]")
    for pat, st, zv, bd, tt in sorted(res, key=lambda x: (x[2] if x[2] is not None else 9)):
        print("   pattern", [d + 1 for d in pat.values()], st, None if zv is None else round(zv, 4), round(bd, 4), f"{tt:.0f}s")
