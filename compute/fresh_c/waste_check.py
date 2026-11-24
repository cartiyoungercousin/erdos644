r"""Small exact check of the 'wasted first edge' adversary (FRESH_C.md section 8).

Adversary: A_1 arbitrary; A_2 disjoint from A_1 (fresh points); fix Z inside A_1 with |Z| = 1-T and never
use Z again; all later edges inside V' = (A_1 \ Z) u A_2, which has mass 1+T, so every later reply is the
forced complement of the request inside V'.  Requester completely free (rounds 3..6 + exact D).
Model: game_tree.Tree started after two edges on ground set N = 1+T (slack 0): type '1' has mass T
(= A_1 \ Z; the points of Z have degree 1 forever and never matter), type '2' has mass 1.
Prediction (hand proof, area count): mass(D) >= 2*sqrt(T - T^2) > T for T < 4/5.
One single-threaded MILP per T."""
import sys, time, math, pulp
import game_tree
from game_tree import Tree, asc, val, tstr
_orig = pulp.HiGHS
def one_thread(**kw):
    pass
    return _orig(**kw)
game_tree.pulp.HiGHS = one_thread
for T in [float(x) for x in sys.argv[1:]]:
    N = 1 + T
    m = {0: 0.0, 1: T, 2: 1.0, 3: 0.0}
    rho = {1: 1, 2: 1, 3: 0}
    t0 = time.time()
    tr = Tree(T, N, lambda i, types: [("forced", asc(types))], tl=240, start=(2, m, rho, None))
    r = tr.res
    z = pulp.value(tr.z) if r.has_solution else None
    lb = 2 * math.sqrt(T - T * T)
    print(f"T={T}: status={r.status_str} min mass(D)-T = {z}  (MILP bound {r.best_bound}); hand lower bound on mass(D): {lb:.4f}"
          f" -> predicted margin >= {lb - T:.4f}  [{time.time()-t0:.0f}s]", flush=True)
    if z is not None:
        path, mm, s, a, tot, rho_, q = tr.leaves[0]
        print("   state after 5:", {tstr(J): round(val(mm[J]), 4) for J in sorted(mm) if val(mm[J]) > 1e-6})
