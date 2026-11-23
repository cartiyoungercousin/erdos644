"""chi(x,y,z): complete-family lower bound for ANY strategy that keeps a good triple with pair cells
(x,y,z) (k = 1).  If the family is K_N with N >= max(1+t, 3-S), a bad 7-tuple through the triple
must exist inside N points; chi = (min union of a bad 7-tuple through the triple) - 1.
A strategy keeping such a triple cannot prove tau <= t k for t < chi(x,y,z)."""
import pulp, sys
from shapes import model, solve, PATS, FULL

def chi(x, y, z):
    prob, n, zz = model("chi")
    prob += pulp.lpSum(n[P] for P in PATS if P != FULL)
    for P in PATS:
        if (P & 0b111) == 0: prob += n[P] == 0
    prob += pulp.lpSum(n[P] for P in PATS if not (P & 0b011)) == x
    prob += pulp.lpSum(n[P] for P in PATS if not (P & 0b101)) == y
    prob += pulp.lpSum(n[P] for P in PATS if not (P & 0b110)) == z
    st = solve(prob)
    return None if st != "Optimal" else max(0.0, pulp.value(prob.objective) - 1)

if __name__ == "__main__":
    print("symmetric line (a,a,a):")
    for a in [0, .1, .2, .25, .3, 1/3, .35, .4, 3/7, .45, .475, .5]:
        print(f"  a={a:.4f} chi={chi(a,a,a):.4f}  (3-S-1 = {2-3*a:.4f})", flush=True)
    print("(1/2,b,b):")
    for b in [0, .1, .2, .25, .3, .35, .375, .4, .45, .5]:
        print(f"  b={b:.3f} chi={chi(.5,b,b):.4f}", flush=True)
    print("(a,a,0) and (a,0,0):")
    for a in [.1, .25, .4, .5]:
        print(f"  a={a:.2f} chi(a,a,0)={chi(a,a,0):.4f} chi(a,0,0)={chi(a,0,0):.4f}", flush=True)
