# CORE Part IV: for N and q, the best "no-luck" design: q co-edges used in full (mass N-1),
# 7-q co-edges only through her requests (mass <= t - s).  Maximise s.   py slackq.py
import itertools, pulp, sys
from spectrum import subsets, pts, describe
from fractions import Fraction as Fr
def best(N, q, t=0.75, forbid2=False):
    pr = pulp.LpProblem("s", pulp.LpMaximize)
    m = {F: pr.add_variable("m%d" % i, 0, 7) for i, F in enumerate(subsets)}
    y = {F: pr.add_variable("y%d" % i, cat="Binary") for i, F in enumerate(subsets)}
    s = pr.add_variable("s", -5, 5)
    pr += s
    for F in subsets: pr += m[F] <= 7 * y[F]
    for F, G in itertools.combinations(subsets, 2):
        if not (F & G): pr += y[F] + y[G] <= 1
    pr += pulp.lpSum(m.values()) == N
    for i in pts:
        load = pulp.lpSum(m[F] for F in subsets if i in F)
        if i < q: pr += load <= N - 1
        else: pr += load <= t - s
    st = pr.solve(pulp.HiGHS(msg=False))
    if not st.has_solution: return None, None
    return s.value(), {F: round(m[F].value(), 4) for F in subsets if m[F].value() > 1e-7}
if __name__ == "__main__":
    print("slack s (t = 3/4): rows N, columns q = number of co-edges used in full; count formula (q-3)(N-7/4)/(7-q)")
    for N in (1.8, 11/6, 1.9, 2.0, 2.1, 2.2, 2.25, 2.3, 2.5):
        row = []
        for q in (2, 3, 4, 5, 6):
            s, sup = best(N, q)
            row.append("q=%d: %+.4f (%+.4f)" % (q, s, (q - 3) * (N - 1.75) / (7 - q)))
        print("N = %.4f  " % N + "  ".join(row), flush=True)
    for N, q in ((2.0, 3), (2.2, 3), (2.2, 4), (2.25, 2), (2.5, 2)):
        s, sup = best(N, q); print("N = %.2f q = %d s = %+.4f:" % (N, q, s), describe(sup))
