"""The complete-family ("complement") response at dense profiles: a certificate over ALL first
requests, not only grid requests.

Response rule:  K(D) = (E u F u G) \\ D  plus  1 - (U - t) new points,   U = 3 - S,
defined when U - t <= 1 (i.e. S >= 2 - t).  This is what the complete family K_N would answer.
The region masses are affine in D:  c+ = mass_c - d_c,  c- = d_c,  N = 1 - U + t.

For a seal pattern s (pair cells entirely in D, total mass <= t) let Face(s) be the set of
requests with d_c = mass_c on s, 0 <= d_c <= mass_c elsewhere, sum d = t.  The requester beats the
rule somewhere on Face(s) iff for some closure pattern P available under s (Q with the signature
of s, or a re-anchor closure T_c, c in s) the linear system
        d in Face(s),   W[P, lambda] . masses(d) <= t  for all lambda
is feasible.  We prove infeasibility for every pattern: first by a vectorized bound (some lambda
whose minimum over the face exceeds t: a fractional knapsack), then by an LP for the survivors.
We also check that K(D) satisfies the looseness inequalities on the whole face.

usage: py complement.py x y z t [variant=loose]
"""
import sys, itertools
from fractions import Fraction
import numpy as np
import pulp
import game, tables
from game import cell_mass, NREG, CELL_NAMES


def affine_rm(mass, t):
    """rm = A d + b for the complement response."""
    A = np.zeros((NREG, 6)); b = np.zeros(NREG)
    for c in range(6):
        A[2 * c, c] = -1.0; b[2 * c] = mass[c]        # c+
        A[2 * c + 1, c] = 1.0                          # c-
    U = 3 - (mass[0] + mass[1] + mass[2])
    b[12] = 1 - (U - t)
    return A, b, U


def face_min(G, c0, lo, hi, total):
    """min over {lo <= d <= hi, sum d = total} of c0 + G d, row-wise (fractional knapsack)."""
    order = np.argsort(G, axis=1)
    Gs = np.take_along_axis(G, order, axis=1)
    room = (hi - lo)[order]
    need = total - lo.sum()
    cum = np.cumsum(room, axis=1)
    take = np.clip(need - (cum - room), 0, room)
    return c0 + G @ lo + (Gs * take).sum(axis=1)


def check_face(mass, t, rules, sub, verbose=True):
    A, b, U = affine_rm(mass, t)
    lo = np.array([mass[c] if c in sub else 0.0 for c in range(6)]); hi = np.array(mass, float)
    if lo.sum() > t + 1e-12: return None
    d0 = [mass[c] if (c in sub or mass[c] <= game.EPS) else 0.0 for c in range(3)] + [0.0] * 3
    # looseness on the face: max of mass_c + |K & A1| + |K & A2| over the face
    worst_loose = -9
    for coef, const, bound in game.looseness_rows(mass, d0, rules):
        # kv_c = mass_c - d_c  ->  const + sum coef_c (mass_c - d_c)
        g = -np.array(coef[:6], float); c0 = const + float(np.dot(coef[:6], mass))
        mx = -face_min(-g[None, :], np.array([-c0]), lo, hi, t)[0]
        worst_loose = max(worst_loose, mx - bound)
    surv_total = 0; feas = []
    for C in game.closures(mass, d0):
        nT, nL, nc = C.W.shape
        R = C.W.reshape(nT * nL, nc) @ C.M                # region-level rows
        G = R @ A; c0 = R @ b
        mn = face_min(G, c0, lo, hi, t).reshape(nT, nL)
        surv = np.nonzero(mn.max(axis=1) <= t + 1e-9)[0]   # patterns not excluded by one row
        surv_total += len(surv)
        for i in surv:
            prob = pulp.LpProblem("f", pulp.LpMinimize)
            d = [prob.add_variable(f"d{c}", float(lo[c]), float(hi[c])) for c in range(6)]
            s = prob.add_variable("s", -5, 5)
            prob += s
            prob += pulp.lpSum(d) == t
            Gi = G[i * nL:(i + 1) * nL]; ci = c0[i * nL:(i + 1) * nL]
            for row in np.unique(np.round(np.hstack([Gi, ci[:, None]]), 12), axis=0):
                prob += pulp.lpSum(float(row[c]) * d[c] for c in range(6) if abs(row[c]) > 1e-12) + float(row[6]) <= t + s
            st = prob.solve(game.solver())
            assert st.status.name == "Optimal"
            if s.value() <= 1e-7:
                feas.append((C.name, int(i), [v.value() for v in d], s.value()))
    if verbose:
        name = "".join(CELL_NAMES[c] for c in sub) or "-"
        print(f"  seal {name:3s}: looseness slack of K(D) on the face {-worst_loose:+.4f} "
              f"({'admissible everywhere' if worst_loose <= 1e-9 else 'NOT admissible everywhere'}); "
              f"patterns needing an LP: {surv_total}; patterns beating the rule somewhere: {len(feas)}", flush=True)
        for nm, i, dd, sv in feas[:3]:
            print(f"      e.g. {nm} #{i} at D={[round(v, 4) for v in dd]} (margin {-sv:.4f})")
    return worst_loose <= 1e-9, feas


def main(x, y, z, t, variant="loose"):
    mass = cell_mass(x, y, z); rules = game.make_rules(variant, t, x, y, z)
    U = 3 - (x + y + z)
    print(f"profile ({x:.4f},{y:.4f},{z:.4f}) t={t:.4f} variant={variant}: phi={game.phi_static(x, y, z)[0]:.4f}, "
          f"S={x + y + z:.4f} (S_max rules {rules.smax}), new points of K: {1 - (U - t):.4f}")
    if U - t > 1 + 1e-12:
        print("  complement response not defined (U - t > 1)"); return None
    allok = True
    for n in range(4):
        for sub in itertools.combinations(range(3), n):
            r = check_face(mass, t, rules, sub)
            if r is None: continue
            adm, feas = r
            allok &= adm and not feas
    print("  => the complement response", "BEATS EVERY first request (all seal patterns, continuum of D)" if allok
          else "does NOT beat every request")
    return allok


if __name__ == "__main__":
    a = [float(Fraction(v)) for v in sys.argv[1:5]]
    main(*a, *(sys.argv[5:6]))
