"""Diagonal scan: at profile (a,a,a) and budget t, does the complete-family response rule
(complement.py) beat every first request?  One line per (t, a)."""
import itertools, sys
from fractions import Fraction
import game, complement

ts = [float(Fraction(v)) for v in (sys.argv[1:] or ["0.85", "0.84", "5/6", "0.82", "0.80"])]
for t in ts:
    for i in range(34, 51):
        a = i / 100
        if 3 * a > 3 - 2 * t + 1e-9 or 3 * a < 2 - t - 1e-9: continue
        phi = game.phi_static(a, a, a)[0]
        if phi <= t + 1e-9: continue
        mass = game.cell_mass(a, a, a); rules = game.make_rules("loose", t, a, a, a)
        ok = True; why = []
        for n in range(4):
            for sub in itertools.combinations(range(3), n):
                r = complement.check_face(mass, t, rules, sub, verbose=False)
                if r is None: continue
                adm, feas = r
                if not adm: ok = False; why.append(f"{n} sealed: looseness excludes the rule")
                elif feas: ok = False; why.append(f"{n} sealed: beaten by {sorted({f[0][:1] for f in feas})}")
        print(f"t={t:.4f} a={a:.2f} phi={phi:.4f} S={3*a:.2f} (S_max {3-2*t:.3f}): "
              + ("complement rule beats EVERY request" if ok else "; ".join(sorted(set(why)))), flush=True)
