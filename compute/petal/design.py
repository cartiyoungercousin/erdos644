"""Triple-free four petals: exact 3-round design value and the fourth-petal minimax (PETAL.md part II).

Cells: grid r = A_r x A'_r, masses (a_r, b_r), r = 1,2,3   (a = (p12,p13,p23), b = (c34,c24,c14)).
design(a, b): min over kill-type assignments (types = nonempty subsets of {0,1,2}; on each grid the types
  used on the two sides must pairwise intersect) of the maximum round load.  MILP (HiGHS), masses real.
fourth(a, T, K): she chooses r (requests inside the singles, sum T - p), he chooses b_i <= q_i - r_i,
  sum b = K (grid units); returns (win?, r, worst b, value).
Usage: py design.py table K T      (shapes a1>=a2>=a3 with T-K/3 < p <= T, units of K)
"""
import sys, itertools, functools
import highspy, math

TYPES = [1, 2, 3, 4, 5, 6, 7]
EPS = 1e-4
DISJ = [(F, G) for F in TYPES for G in TYPES if F & G == 0]

@functools.lru_cache(maxsize=None)
def _design(cells):
    h = highspy.Highs(); h.setOptionValue("output_flag", False); h.setOptionValue("log_to_console", False)
    inf = highspy.kHighsInf
    nv = 0
    def var(lo, hi, integer=False):
        nonlocal nv
        h.addVar(lo, hi)
        if integer: h.changeColIntegrality(nv, highspy.HighsVarType.kInteger)
        nv += 1; return nv - 1
    L = var(0, inf)
    h.changeColCost(L, 1.0)
    load = [dict(), dict(), dict()]
    for g, (a, b) in enumerate(cells):
        # a zero cell is a sliver (O(1) points, free for the adversary): its partners still need a kill
        a = max(a, EPS); b = max(b, EPS)
        x = {F: var(0, a) for F in TYPES}; y = {G: var(0, b) for G in TYPES}
        u = {F: var(0, 1, True) for F in TYPES}; v = {G: var(0, 1, True) for G in TYPES}
        for F in TYPES:
            h.addRow(-inf, 0, 2, [x[F], u[F]], [1.0, -a])
            h.addRow(-inf, 0, 2, [y[F], v[F]], [1.0, -b])
        for F, G in DISJ:
            h.addRow(-inf, 1, 2, [u[F], v[G]], [1.0, 1.0])
        h.addRow(a, a, 7, [x[F] for F in TYPES], [1.0] * 7)
        h.addRow(b, b, 7, [y[F] for F in TYPES], [1.0] * 7)
        for i in range(3):
            for F in TYPES:
                if F >> i & 1:
                    load[i][x[F]] = 1.0; load[i][y[F]] = 1.0
    for i in range(3):
        idx = list(load[i]) + [L]; val = [1.0] * len(load[i]) + [-1.0]
        h.addRow(-inf, 0, len(idx), idx, val)
    h.run()
    return h.getInfo().objective_function_value

def design(a, b):
    cells = tuple(sorted((min(x, y), max(x, y)) for x, y in zip(a, b)))  # sides and grids are symmetric
    return _design(cells)

def comps(total, caps):
    for x in range(min(total, caps[0]) + 1):
        for y in range(min(total - x, caps[1]) + 1):
            z = total - x - y
            if 0 <= z <= caps[2]:
                yield (x, y, z)

def fourth(a, T, K):
    p = sum(a)
    q = [K - (p - a[i]) for i in range(3)]      # single part opposite to grid i: Q_3 for a1=p12, ...
    best = None
    for r in comps(T - p, q):
        caps = [q[i] - r[i] for i in range(3)]
        worst = (-1, None)
        tot = min(K, sum(caps))
        for b in comps(tot, caps):
            v = design(a, b)
            if v > worst[0] + 1e-9: worst = (v, b)
            if v > T + 1e-2: break
        if best is None or worst[0] < best[0] - 1e-9: best = (worst[0], r, worst[1])
        if worst[0] <= T + 1e-2: break
    return best

if __name__ == "__main__":
    if sys.argv[1] == "table":
        K, T = int(sys.argv[2]), int(sys.argv[3])
        lo = T - K / 3
        for p in range(0, T + 1):
            for a1 in range(p, -1, -1):
                for a2 in range(min(a1, p - a1), -1, -1):
                    a3 = p - a1 - a2
                    if a3 > a2 or a3 < 0: continue
                    if p <= lo: continue
                    v, r, b = fourth((a1, a2, a3), T, K)
                    print("a=%s p=%d  %s  value %.3f  r=%s worst b=%s" %
                          ((a1, a2, a3), p, "R" if v <= T + 1e-2 else "A", v, r, b), flush=True)
    elif sys.argv[1] == "design":
        a = tuple(float(x) for x in sys.argv[2:5]); b = tuple(float(x) for x in sys.argv[5:8])
        print(design(a, b))
