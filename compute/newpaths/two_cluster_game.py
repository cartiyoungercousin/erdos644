"""Decisive test for Lemma G (NEW_PATHS.md, Path 1): the 4-edge "two-cluster game".
Everything in exact rationals (k = 1 normalisation).

Forced configuration (gap regime, m = |E∩K| = 0 chosen by the adversary):
  stage 1: request 1/2 of E and t-1/2 of K      -> K' far from E, b = |K∩K'| <= 3/2 - t
  stage 2: request K∩K' and t-b of E            -> K3 far from K,K', r = |E∩K3| <= 1 - t + b
  closure: 3 static requests on E,K,K',K3.
Adversary witness: the genuine family H2(N) = all k-subsets of V1 plus all k-subsets of V2,
V1,V2 disjoint, |V_i| = N = (1+t/2)k + 1 (tau = 2(N-k)+2 > T).  Its answers: m = 0,
b = 3/2 - t, r = 5/2 - 2t, every other pair cell 0.
With these cells the only candidate pair of classes is (E∩K3) x (K∩K').  A closure is a pair of
cross-intersecting label families (F_r, F_b) on [3]; by LP duality
  cost(F_r,F_b) = max_lambda  r*min_{L in F_r} lambda(L) + b*min_{L in F_b} lambda(L),
so any lambda gives a lower bound.  We enumerate ALL pairs of families and a fixed list of 10
rational lambdas: certified lower bound on the closure value.
"""
from fractions import Fraction as Fr
from itertools import combinations, product
LABELS = [frozenset(c) for n in (1,2,3) for c in combinations(range(3), n)]
FAMS = [tuple(LABELS[i] for i in range(7) if mask >> i & 1) for mask in range(1, 128)]
h, q, th = Fr(1,2), Fr(1,4), Fr(1,3)
LAM = [(1,0,0),(0,1,0),(0,0,1),(h,h,0),(h,0,h),(0,h,h),(th,th,th),(h,q,q),(q,h,q),(q,q,h)]
LAM = [tuple(Fr(x) for x in l) for l in LAM]
def lmin(F, lam): return min(sum(lam[i] for i in L) for L in F)
def closure_lower_bound(r, b):
    best = None
    for Fa, Fb in product(FAMS, FAMS):
        if any(not (L & M) for L in Fa for M in Fb): continue
        v = max(r*lmin(Fa, lam) + b*lmin(Fb, lam) for lam in LAM)
        if best is None or v < best[0]: best = (v, Fa, Fb)
    return best
def check_constraints(t, b, r):
    g = 1 - t
    cells = dict(EK=Fr(0), EKp=Fr(0), KKp=b, EK3=r, KK3=Fr(0), KpK3=Fr(0))
    ok = all(v <= g or v >= h for v in cells.values())                 # pair gap
    triples = [("EK","EKp","KKp"), ("EK","EK3","KK3"), ("KKp","KK3","KpK3"), ("EKp","EK3","KpK3")]
    for tr in triples:
        vals = [cells[c] for c in tr]
        ok &= max(vals) >= h                                           # minimality (u >= 1/2)
        ok &= sum(vals) <= 3 - 2*t                                     # tight-triple lemma
    # Lemma B: trace of the 4th edge on the union of each good triple
    trace = {("EK","EKp","KKp"): r, ("EK","EK3","KK3"): b, ("KKp","KK3","KpK3"): r, ("EKp","EK3","KpK3"): b}
    for tr in triples:
        W = 3 - sum(cells[c] for c in tr)
        ok &= trace[tr] >= (3*t - W)/2
    ok &= r <= 1 and b <= 1
    return ok
def core_game_star(t):
    """Star strategy against H2(N): block V1 with t/2 points, cut the V2-core with the rest."""
    N = 1 + t/2; core = Fr(1); steps = 1          # after the first V2 response the core is one edge
    while core > t - t/2:                          # cannot yet seal the core while blocking V1
        core -= t/2; steps += 1
    return steps + 1                               # sealing request -> one more response
if __name__ == "__main__":
    for t in (Fr(76,100), Fr(78,100), Fr(80,100)):
        b = Fr(3,2) - t; r = Fr(5,2) - 2*t
        v, Fa, Fb = closure_lower_bound(r, b)
        print(f"t={t}: witness b={b} r={r}  constraints_ok={check_constraints(t,b,r)}  "
              f"closure >= {v} ({float(v):.4f})  -> {'STUCK' if v > t else 'not certified'}")
        # weakest admissible answer of the same adversary (b = 1 - t/2, the minimum in H2(N))
        b2 = 1 - t/2; r2 = 1 - t + b2
        v2 = closure_lower_bound(r2, b2)[0]
        print(f"        (same game, adversary's b at its minimum 1-t/2={b2}, r={r2}: closure >= {v2} = {float(v2):.4f})")
        print(f"        star strategy vs H2(N): bad tuple after {core_game_star(t)} same-cluster edges + 1 centre")
