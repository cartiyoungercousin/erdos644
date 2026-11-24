"""PETAL section 21: certified exclusion cost of a class.
State: atoms {frozenset(member indices): mass}.  A set S excludes the class (given only "same-class overlaps > c") iff no E of
mass 1 outside S has |E n X_i| > c for all members i.  By LP duality  e = min over weights w (simplex) of cost(w),
cost(w) = least mass to delete, taken from the highest weighted depth downwards, so that the heaviest unit of mass left has
weighted depth <= c.  Every w gives a request that really excludes (upper bound on e is rigorous); the grid over w makes the
minimum approximate.   usage: py exclusion.py
"""
import itertools

def cost(atoms, w, c):
    lev = sorted(((sum(w[i] for i in A), m) for A, m in atoms.items() if m > 0), reverse=True)
    def top(rem):                      # weighted depth of the heaviest unit of mass in rem (list of (depth, mass))
        tot = 0.0; left = 1.0
        for d, m in rem:
            t = min(m, left); tot += d * t; left -= t
            if left <= 0: break
        return tot
    if top(lev) <= c + 1e-12: return 0.0
    lo, hi = 0.0, sum(m for _, m in lev)
    for _ in range(50):
        mid = (lo + hi) / 2; rem = []; d = mid
        for dep, m in lev:
            t = min(m, d); d -= t
            if m - t > 0: rem.append((dep, m - t))
        if top(rem) <= c: hi = mid
        else: lo = mid
    return hi

def excl(atoms, n, c, step=20):
    best = (9, None)
    for comp in itertools.product(range(step + 1), repeat=n - 1):
        if sum(comp) > step: continue
        w = [x / step for x in comp] + [(step - sum(comp)) / step]
        v = cost(atoms, w, c)
        if v < best[0] - 1e-9: best = (v, w)
    return best

def Q(c):                              # 17.1: four blocks of c/2, privates rho
    rho = 1 - 1.5 * c; at = {}
    for i in range(4):
        at[frozenset(j for j in range(4) if j != i)] = c / 2
        at[frozenset([i])] = rho
    return at

def Yclass(m, z, q, hit_types, c):
    """m members: arena part = region minus own block of mass q (blocks disjoint), common part 1 - z - (m-1)q >= 0;
    hits of mass z, member j has hit type j % hit_types (members of a type share their hits)."""
    at = {}
    common = 1 - z - (m - 1) * q
    assert common >= -1e-9
    at[frozenset(range(m))] = common
    for i in range(m): at[frozenset(j for j in range(m) if j != i)] = q
    for h in range(hit_types): at[frozenset(j for j in range(m) if j % hit_types == h)] = at.get(frozenset(j for j in range(m) if j % hit_types == h), 0) + z
    return at

if __name__ == "__main__":
    t = 0.75
    for c in [0.52, 0.54, 0.56]:
        eX, w = excl(Q(c), 4, c)
        rho = 1 - 1.5 * c; mu = rho / 2
        print("Q(c=%.2f): rho=%.3f mu=%.3f  e_X=%.4f (1-c=%.2f)  J'' cost 1-c+4mu=%.3f" % (c, rho, mu, eX, 1 - c, 1 - c + 4 * mu))
        for z in [3 * mu]:
            for m, ht in [(2, 2), (3, 2), (4, 2), (3, 3), (4, 4)]:
                rows = []
                qmax = (1 - z - c) if m == 2 else min((1 - z - c), (1 - z) / (m - 1))
                for q in [0.0, qmax / 2, qmax]:
                    if 1 - z - q < c - 1e-9: continue
                    eY, wy = excl(Yclass(m, z, q, ht, c), m, c, step=10 if m >= 4 else 20)
                    rows.append("q=%.3f e_Y=%.3f sum=%.3f%s" % (q, eY, eX + eY, " EXCLUDED" if eX + eY <= t else ""))
                print("   Y: m=%d hit-types=%d z=%.3f | " % (m, ht, z) + " ; ".join(rows))
