"""PETAL section 22: best mixed (designed + observed) sealing plan against centres that hit up to nu in each private
part (mass rho = 1) of the petals, with rotation (centre j cannot hit the private part of its forcing petal a_j).
Private b (never a forcing petal): request 1 seals al1; C1 hits h1=min(nu,1-al1); request 2 seals h1+al2;
C2 hits h2=min(nu,1-h1-al2); request 3 seals h1+h2.  Private a_1 (centres 2,3): request 2 seals g, request 3 min(nu,1-g).
a_2 (centres 1,3): request 1 seals f2, request 3 min(nu,1-f2).  a_3 (centres 1,2): request 1 f3, request 2 min(nu,1-f3).
Output per nu: min over plans (grid) of the largest request surplus, in units of rho.   usage: py seal_plan.py"""
N = 40
gr = [i / N for i in range(N + 1)]
def plan(nu):
    best = (9, None)
    for al1 in gr:
        h1 = min(nu, 1 - al1)
        for al2 in [x * (1 - h1) for x in gr]:
            h2 = min(nu, 1 - h1 - al2)
            for g in gr:
                a1 = (g, min(nu, 1 - g))
                for f2 in gr:
                    a2 = (f2, min(nu, 1 - f2))
                    r3 = h1 + h2 + a1[1] + a2[1]
                    if r3 >= best[0]: continue
                    for f3 in gr:
                        a3 = (f3, min(nu, 1 - f3))
                        r1 = al1 + a2[0] + a3[0]; r2 = h1 + al2 + a1[0] + a3[1]
                        v = max(r1, r2, r3)
                        if v < best[0] - 1e-9: best = (v, dict(al1=al1, al2=round(al2, 3), g=g, f2=f2, f3=f3, r=(round(r1, 3), round(r2, 3), round(r3, 3))))
    return best
if __name__ == "__main__":
    for nu in [0.2, 0.3, 1 / 3, 0.4, 0.5, 0.6, 0.7, 0.8, 1.0]:
        v, p = plan(nu)
        print("nu/rho=%.3f  surplus=%.4f rho  (J'' would pay %.3f)  %s" % (nu, v, 4 * nu, p))
