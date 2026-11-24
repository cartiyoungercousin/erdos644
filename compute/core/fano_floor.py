# Re-check of ROADMAP 2.2: min N (k = 1) of seven co-edges covering all pairs when NOT all seven
# lines of some Fano plane occur as co-types.  Co-types F (subsets of [7]) pairwise intersecting,
# each edge has mass 1:  sum_{F not containing i} m_F = 1.   py fano_floor.py
import itertools, pulp
from fractions import Fraction
pts = range(7)
subsets = [frozenset(s) for r in range(1, 8) for s in itertools.combinations(pts, r)]
# all 30 Fano planes on [7]
base = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
planes = set()
for p in itertools.permutations(pts):
    planes.add(frozenset(frozenset(p[i] for i in L) for L in base))
assert len(planes) == 30

def solve(forbid_full_fano):
    pr = pulp.LpProblem("floor", pulp.LpMinimize)
    m = {F: pr.add_variable("m%d" % i, 0, 7) for i, F in enumerate(subsets)}
    y = {F: pr.add_variable("y%d" % i, cat="Binary") for i, F in enumerate(subsets)}
    pr += pulp.lpSum(m.values())
    for F in subsets:
        pr += m[F] <= 7 * y[F]
    for F, G in itertools.combinations(subsets, 2):
        if not (F & G): pr += y[F] + y[G] <= 1
    for i in pts:
        pr += pulp.lpSum(m[F] for F in subsets if i not in F) == 1
    if forbid_full_fano:
        for P in planes:
            pr += pulp.lpSum(y[L] for L in P) <= 6
    pr.solve(pulp.HiGHS(msg=False))
    sup = {tuple(sorted(F)): round(m[F].value(), 6) for F in subsets if m[F].value() > 1e-7}
    return pulp.value(pr.objective), sup

v0, s0 = solve(False); print("unrestricted min N =", v0, s0)
v1, s1 = solve(True);  print("no full Fano plane among the co-types: min N =", v1, s1)
# exact check of the ROADMAP example: six lines + one 4-set containing the seventh

