"""PETAL section 23: the sealing-plan game solved exactly (LP per case, exhaustive over cases).
Units: single (private) part of a petal = 1 (mass rho).  A centre hits at most nu in each private part it may enter.
Three forced centres, forcing petals a_1, a_2, a_3 distinct, b the fourth petal.  Request j has a forcing mode:
  R (rotation):  forcing set = 1-c of X_{a_j} containing its private part; base surplus 0; centre j cannot enter private a_j
                 and earlier hits inside it are covered by the forcing set.
  P (private):   forcing set = 1-c-rho of the shared part of X_{a_j}; base surplus -1; valid only if the private part is
                 private in the whole family (Lemma FF); centre j may enter private a_j.
Per private part p: request 1 seals d1 (design); C1 hits h1 = min(nu, 1-d1); request 2 seals h1 + d2; C2 hits
h2 = min(nu, 1-h1-d2); request 3 seals h1 + h2.  (Hitting the maximum is dominant for him: all later costs are
nondecreasing in the hits.)  She minimises the largest request surplus.  Each min() is resolved by a case split; every
case is an LP (HiGHS); the value is the minimum over all cases and mode triples, so it is exact up to LP tolerance.
usage: py plan_lp.py
"""
import itertools
from lpw import Model, esum, toE

PRIV = ["a1", "a2", "a3", "b"]


def solve(nu, modes):
    best = (1e9, None)
    free = {(p, j): (modes[j] == "R" and p == "a%d" % (j + 1)) for p in PRIV for j in range(3)}
    for cases in itertools.product(range(4), repeat=4):
        M = Model(); v = M.var(-10, 10)
        r = [toE(-1.0 if modes[j] == "P" else 0.0) for j in range(3)]
        ok = True
        for p, cs in zip(PRIV, cases):
            c1, c2 = cs & 1, cs >> 1
            d1 = M.var(0, 1); d2 = M.var(0, 1)
            # stage 1
            if free[(p, 0)]:
                if c1: ok = False; break            # single canonical case when free
                h1 = toE(0.0)
            else:
                r[0] = r[0] + d1
                if c1 == 0: h1 = toE(nu); M.le(d1, 1 - nu)
                else: h1 = 1 - d1; M.le(1 - nu, d1)
            # stage 2
            if free[(p, 1)]:
                if c2: ok = False; break
                h2 = toE(0.0)
            else:
                r[1] = r[1] + h1 + d2
                M.le(h1 + d2, 1)
                if c2 == 0: h2 = toE(nu); M.le(h1 + d2, 1 - nu)
                else: h2 = 1 - h1 - d2; M.le(1 - nu, h1 + d2)
            # stage 3
            if not free[(p, 2)]:
                r[2] = r[2] + h1 + h2
        if not ok: continue
        for j in range(3): M.le(r[j], v)
        st, val = M.minimize(v)
        if st == "Optimal" and val < best[0] - 1e-9:
            best = (val, dict(modes="".join(modes), cases=cases, r=[round(M.val(x), 4) for x in r]))
    return best


def value(nu, allowP):
    best = (1e9, None)
    for modes in itertools.product("RP" if allowP else "R", repeat=3):
        b = solve(nu, modes)
        if b[0] < best[0] - 1e-9: best = b
    return best


if __name__ == "__main__":
    for nu in [0.2, 0.25, 0.3, 1 / 3, 0.4, 0.5, 0.6, 0.7, 0.75, 0.8, 0.9, 1.0]:
        vr = value(nu, False); vp = value(nu, True)
        print("nu/rho=%.3f  rotation only: %.4f %s | with private forcing: %.4f %s" % (nu, vr[0], vr[1]["r"], vp[0], vp[1]), flush=True)
