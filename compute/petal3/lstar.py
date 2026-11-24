"""L*(a,b) (TWIN 15.4), thresholds of PETAL Part III.  usage: py lstar.py"""
from fractions import Fraction as Fr
def lstar(a, b):
    c = [a + b / 3, b + a / 3, 2 * (a + b) / 3]
    if 2 * b >= a: c.append(3 * a / 4 + b / 2)
    if 2 * a >= b: c.append(3 * b / 4 + a / 2)
    return min(c)
def a0(t, d): return 1 - t / 2 - d
def beta(t, d): return (1 - d) * (2 - 3 * t / 2 - 2 * d) / (2 - t - 2 * d)
def margin(t, d): return lstar(a0(t, d), beta(t, d)) - t          # > 0: Theorem N applies
def delta_N(t):
    if margin(t, Fr(0)) <= 0: return None
    lo, hi = Fr(0), Fr(1, 4)
    for _ in range(60):
        mid = (lo + hi) / 2
        if margin(t, mid) > 0: lo = mid
        else: hi = mid
    return lo
if __name__ == "__main__":
    # check L* against the MILP design on a few single grids
    from lpw import Model
    from quadmin import add_design
    for (a, b) in [(0.5, 0.5), (1/3, 2/3), (0.6, 0.6), (0.575, 0.64), (0.5, 0.75), (0.3, 0.9), (0.625, 0.7)]:
        M = Model(); L = M.var()
        cells = {(0, 1): a, (2, 3): b, (0, 2): 0, (1, 3): 0, (0, 3): 0, (1, 2): 0}
        add_design(M, cells, L); st, v = M.minimize(L)
        print("grid (%.3f,%.3f): L* formula %.5f  MILP %.5f" % (a, b, lstar(a, b), v))
    print("t, theta=(6t-2)/5, single-serve leak bound 7/5-17t/10, delta_N(t) (uniform rule, any re-selection), t/26 (Thm J), t/8 (tailored 4+3)")
    for t in [Fr(3, 4), Fr(76, 100), Fr(77, 100), Fr(78, 100), Fr(781, 1000), Fr(79, 100), Fr(795, 1000), Fr(80, 100)]:
        dn = delta_N(t)
        print(float(t), float((6 * t - 2) / 5), float(Fr(7, 5) - 17 * t / 10), None if dn is None else round(float(dn), 5), round(float(t / 26), 5), float(t / 8),
              "margin at delta=0: %.5f" % float(margin(t, Fr(0))))
