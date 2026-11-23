"""Complete-family test for the 'good triple by response' architecture (FKW / six-sevenths).

Adversary = K_N^(k), N = (1+t)k (tau = tk+1 > T = tk).  A response to a request D of size T that
lies inside the known points is FORCED to be N \ D.  Architecture: E,F with |E n F| = m; third edge
G = response to a T-request D with (E n F) <= D <= (E u F).  Then G = N \ D contains every point
outside E u F and has E n F n G = 0.  Question: for which t does K_N contain a bad 7-tuple through
such a triple?  (If not, the architecture must discard one of E,F,G: it cannot win in 7 rounds.)
"""
import pulp
from shapes import model, solve, PATS, FULL

def min_t(m=None, lo_m=None, hi_m=None):
    prob, n, z = model("ct")
    t = prob.add_variable("t", 0, 2)
    prob += t
    prob += pulp.lpSum(n[P] for P in PATS) == 1 + t                 # universe is exactly N
    for P in PATS:
        if (P & 0b111) == 0b111: prob += n[P] == 0                   # G contains all points outside E u F
        if (P & 0b111) == 0: prob += n[P] == 0                       # good triple (P empty is excluded anyway)
    pair = pulp.lpSum(n[P] for P in PATS if not (P & 0b11))
    if m is not None: prob += pair == m
    if lo_m is not None: prob += pair >= lo_m
    if hi_m is not None: prob += pair <= hi_m
    st = solve(prob)
    if st != "Optimal": return st, None
    return round(t.value(), 5), round(pulp.value(pair), 5)

if __name__ == "__main__":
    print("m = 1/2 (the extremal pair of FKW in K_N):", min_t(m=0.5))
    for m in [0.25, 0.3, 0.35, 0.4, 3/7, 0.45, 0.5]:
        print(f"  m={m:.4f}: min t =", min_t(m=m))
    print("m free in [0, 1/2]:", min_t(lo_m=0, hi_m=0.5))
    print("m free:", min_t())
