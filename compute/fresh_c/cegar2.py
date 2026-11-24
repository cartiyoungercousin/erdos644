"""Exact (within the model) search over ALL two-block profile families with profiles on a grid.
For block sizes (n1,n2) and target T: find a set P of grid profiles a1 (edge has a1*k points in V1, (1-a1)*k in V2)
with tau(P) > T  [tau = min(n1-p_min, p_max+n2-1, n-1-maxgap)]  and no bad 7-multiset (MILP adversary).
CEGAR: every MILP witness yields a forbidden support set; DFS enumerates P avoiding all forbidden supports."""
import sys, time
from profile_milp import bad7

def run(n1, n2, T, g, budget=240, verbose=False):
    n = n1 + n2
    s = n - 1 - T
    N = round(1 / g)
    pts = [i for i in range(N + 1) if i * g <= n1 + 1e-9 and 1 - i * g <= n2 + 1e-9]
    if s <= g + 1e-9 or not pts:
        return "trivially-none", 0
    forb = []  # bitmasks over grid index
    t0 = time.time(); nmilp = 0
    maxgap = int((s - 1e-9) / g)       # gap (in grid units) must be < s  -> <= maxgap, strict if s multiple
    if abs(maxgap * g - s) < 1e-9: maxgap -= 1
    lo_ok = lambda i: i * g < n1 - T - 1e-9          # smallest point must be < n1 - T
    hi_ok = lambda i: i * g > T + 1 - n2 + 1e-9      # largest point must be > T+1-n2
    sys.setrecursionlimit(10000)
    while True:
        # DFS for a P avoiding forbidden supports
        found = None
        def dfs(cur, mask):
            nonlocal found
            if found is not None: return
            last = cur[-1]
            if hi_ok(last):
                found = list(cur); return
            # extend: prefer largest gap
            for d in range(maxgap, 0, -1):
                nx = last + d
                if nx not in ptset: continue
                nm = mask | (1 << nx)
                if any((f & nm) == f for f in forb): continue
                dfs(cur + [nx], nm)
                if found is not None: return
        ptset = set(pts)
        for st in pts:
            if not lo_ok(st): break
            m0 = 1 << st
            if any((f & m0) == f for f in forb): continue
            dfs([st], m0)
            if found is not None: break
        if found is None:
            return "none", nmilp
        P = [i * g for i in found]
        boxes = [([a, 1 - a], [a, 1 - a]) for a in P]
        bad, wit = bad7([n1, n2], boxes, enlarge=0.0, tl=60)
        nmilp += 1
        if bad is True:
            used = set(wit["types"])
            f = 0
            for r in used: f |= 1 << found[r]
            forb.append(f)
            if verbose: print("   bad", [round(P[r], 3) for r in sorted(used)], flush=True)
        else:
            return ("UNBROKEN" if bad is False else "timeout"), (P, nmilp)
        if time.time() - t0 > budget:
            return "budget", nmilp

if __name__ == "__main__":
    T = float(sys.argv[1]); g = float(sys.argv[2])
    cases = [(1.0, 1.0), (0.9, 1.1), (0.95, 0.95), (1.1, 1.1), (0.8, 1.2), (1.0, 1.2), (0.9, 0.9), (1.2, 1.2), (0.7, 1.3), (1.05, 0.9)]
    for n1, n2 in cases:
        t0 = time.time()
        res = run(n1, n2, T, g)
        print(f"n=({n1},{n2}) T={T} grid={g}: {res}  [{time.time()-t0:.0f}s]", flush=True)
