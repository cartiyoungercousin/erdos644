"""Exact (integer arithmetic) re-verification of stuck profiles reported by run_grid.py.

A stuck record consists of a profile, a budget t, a rule variant and a list of responses K_i
(rationals with denominator 10^6 after rounding).  We verify, with integers only:

  (1) for EVERY request D of the grid used by outer.py (d_c = n_c/dden plus the remainder cell,
      sum = t, d_c <= mass_c) there is an i such that K_i fits outside D, satisfies the rules
      for the seal pattern of D, and
  (2) for each (K_i, seal pattern) used in (1): every pattern of every closure type available
      under that seal pattern (3-request closure of E,F,G,K; 4-request closures of the sealed
      re-anchor triples) has a request of load > t.

The pattern tables are those of tables.py (weights are rationals with denominator dividing 12
for r = 3 and 840 for r = 4); their completeness is the mathematical input (see R1_RESULTS.md),
cross-checked numerically against an independent MILP in check_tables.py.

usage: py exact_check.py out/grid_VARIANT_T_....jsonl VARIANT T [--dden N] [i j l]   (default: all stuck;
       dden defaults to 2*pden, the convention of the runs in out/)
"""
import sys, json, math, itertools
from fractions import Fraction as Fr
import numpy as np
import tables, game

LCM = {3: 12, 4: 840}
_wint = {}


def wint(r):
    if r not in _wint:
        wt = tables.weight_table(r)
        _wint[r] = {F: np.array([int(v * LCM[r]) for v in w], dtype=np.int64) for F, w in wt.items()}
        for F, w in wt.items():
            assert all((v * LCM[r]).denominator == 1 for v in w)
    return _wint[r]


_Wcache = {}


def int_table(C, key):
    if key not in _Wcache:
        wi = wint(C.r)
        _Wcache[key] = np.array([[wi[F] for F in p] for p in C.pats], dtype=np.int64).transpose(0, 2, 1)
    return _Wcache[key]


def exact_rules(variant, t, mass):
    x, y, z = mass[0], mass[1], mass[2]
    loose = 3 - 2 * t; S = x + y + z
    if variant.startswith("pot:") or variant.startswith("poth:"):
        pot = tuple(Fr(v) for v in variant.split(":")[1].split(","))
        s1, s2, s3 = sorted((x, y, z), reverse=True)
        return [loose] * 3, None, ("poth" if variant.startswith("poth:") else "pot", pot, pot[0] * s1 + pot[1] * s2 + pot[2] * s3)
    if variant == "none": return [Fr(99)] * 3, None, None
    if variant == "loose": return [loose] * 3, None, None
    if variant == "maxS": return [min(S, loose)] * 3, None, None
    if variant == "minS": return [loose] * 3, None, S
    pm = x if x < Fr(1, 2) else None
    if variant == "M": return [loose] * 3, pm, None
    if variant == "MS": return [min(S, loose) if mass[c] == x else loose for c in range(3)], pm, None
    raise ValueError(variant)


def rules_ok(mass, sub, kv, smax, pairM, smin=None):
    """exact admissibility of kv for seal pattern sub (capacities are checked elsewhere)."""
    sealed = [c for c in range(3) if c in sub or mass[c] == 0]
    if any(kv[c] != 0 for c in sealed): return False
    for c in sealed:
        a1, a2 = game.TRIPLE_EDGES[c]
        tr = sum(kv[i] for i in range(6) if game.CELL_MEM[i] & a1) + sum(kv[i] for i in range(6) if game.CELL_MEM[i] & a2)
        if mass[c] + tr > smax[c]: return False
        if isinstance(smin, tuple):          # potential rule: Phi(new triple) <= Phi(anchor)
            kind, pot, pot0 = smin
            t1 = sum(kv[i] for i in range(6) if game.CELL_MEM[i] & a1)
            t2 = sum(kv[i] for i in range(6) if game.CELL_MEM[i] & a2)
            s1, s2, s3 = sorted((mass[c], t1, t2), reverse=True)
            if kind == "poth" and s1 > Fr(1, 2): continue
            if pot[0] * s1 + pot[1] * s2 + pot[2] * s3 > pot0: return False
        elif smin is not None and mass[c] + tr < smin: return False
    if pairM is not None:
        for a in (game.E_, game.F_, game.G_):
            tr = sum(kv[i] for i in range(6) if game.CELL_MEM[i] & a)
            if pairM < tr < Fr(1, 2): return False
    return True


def exact_min_value(mass, sub, kv):
    """exact min over closure types and patterns of the max request load, for seal pattern sub."""
    massf = [float(m) for m in mass]
    d = [massf[c] if (c in sub or mass[c] == 0) else 0.0 for c in range(3)] + [0.0] * 3
    rm = []
    for i in range(6): rm += [kv[i], mass[i] - kv[i]]
    rm.append(kv[6])
    Q = 1
    for v in rm: Q = math.lcm(Q, v.denominator)
    rmi = np.array([int(v * Q) for v in rm], dtype=np.int64)
    best = None
    for C in game.closures(massf, d):
        sig = (C.name, tuple(sorted(sub)), tuple(m == 0 for m in mass[:3]), len(C.pats))
        W = int_table(C, sig)
        cm = C.M.astype(np.int64) @ rmi
        v = int((W @ cm).max(axis=1).min())
        val = Fr(v, Q * LCM[C.r])
        if best is None or val < best[0]: best = (val, C.name)
    return best


def verify_stuck(i, j, l, pden, t, variant, cuts, dden=40, verbose=True):
    x, y, z = Fr(i, pden), Fr(j, pden), Fr(l, pden)
    mass = [x, y, z, 1 - x - y, 1 - x - z, 1 - y - z]
    smax, pairM, smin = exact_rules(variant, t, mass)
    Ks = []
    for kvf, _ in cuts:
        kv = [Fr(round(v * 10**6), 10**6) for v in kvf[:6]]
        kv.append(1 - sum(kv))
        assert kv[6] >= 0
        Ks.append(kv)
    Mc = [int(m * dden) for m in mass]
    base = math.floor(t * dden); rho = t * dden - base            # remainder in units of 1/dden
    # all grid requests: n (6 ints, sum = base, n_c <= Mc) and remainder cell e (or none if rho = 0)
    grids = np.meshgrid(*[np.arange(Mc[c] + 1, dtype=np.int16) for c in range(5)], indexing="ij")
    n5 = np.stack([g.ravel() for g in grids], axis=1)
    last = base - n5.sum(axis=1)
    ok = (last >= 0) & (last <= Mc[5])
    N = np.concatenate([n5[ok], last[ok][:, None].astype(np.int16)], axis=1).astype(np.int64)
    ecells = [None] if rho == 0 else list(range(6))
    total = 0; uncovered = 0; used = set()
    # which (cut, seal pattern) pairs are admissible and winning -- computed lazily, exactly
    winmemo = {}
    def wins(ci, sub):
        if (ci, sub) not in winmemo:
            kv = Ks[ci]
            if not rules_ok(mass, sub, kv, smax, pairM, smin): winmemo[ci, sub] = False
            else: winmemo[ci, sub] = exact_min_value(mass, sub, kv)[0] > t
        return winmemo[ci, sub]
    for e in ecells:
        Nn = N if e is None else N[N[:, e] + 1 <= Mc[e]]
        if e is not None and rho > 0:
            pass
        # seal pattern of each request (cells with positive mass only)
        seal = np.zeros(len(Nn), dtype=np.int64)
        for c in range(3):
            if Mc[c] > 0: seal |= (Nn[:, c] == Mc[c]).astype(np.int64) << c
        covered = np.zeros(len(Nn), dtype=bool)
        for ci, kv in enumerate(Ks):
            # capacity: k_c <= mass_c - d_c  <=>  n_c (+rho if c == e) <= (mass_c - k_c) * dden
            fit = np.ones(len(Nn), dtype=bool)
            for c in range(6):
                lim = (mass[c] - kv[c]) * dden - (rho if c == e else 0)
                fit &= Nn[:, c] <= math.floor(lim)
            if not fit.any(): continue
            for sp in np.unique(seal[fit & ~covered]):
                sub = tuple(c for c in range(3) if (int(sp) >> c) & 1)
                if wins(ci, sub):
                    sel = fit & (seal == sp) & ~covered
                    if sel.any(): used.add((ci, sub)); covered |= sel
            if covered.all(): break
        total += len(Nn); uncovered += int((~covered).sum())
        if verbose and (~covered).any():
            bad = Nn[~covered][:3]
            print("    uncovered examples (n vectors, remainder cell", e, "):", bad.tolist())
    return total, uncovered, len(used)


if __name__ == "__main__":
    args = sys.argv[1:]
    dden = None
    if "--dden" in args:
        k = args.index("--dden"); dden = int(args[k + 1]); del args[k:k + 2]
    fn, variant, tstr = args[:3]
    t = Fr(tstr)
    only = tuple(int(a) for a in args[3:6]) if len(args) >= 6 else None
    pden = int(fn.replace("\\", "/").split("_")[-2])
    if dden is None: dden = 2 * pden if pden < 40 else pden
    nbad = 0; nok = 0
    for line in open(fn):
        r = json.loads(line)
        if r.get("win") is not None or "cuts" not in r: continue
        if only and tuple(r["p"]) != only: continue
        tot, unc, used = verify_stuck(*r["p"], pden, t, variant, r["cuts"], dden=dden)
        print(f"profile {r['p']}/{pden} t={tstr} {variant}: {tot} grid requests (step 1/{dden}), {unc} uncovered, "
              f"{used} (response, seal) pairs used, {len(r['cuts'])} responses  ->  "
              f"{'STUCK verified exactly' if unc == 0 else 'NOT verified'}", flush=True)
        nbad += unc > 0; nok += unc == 0
    print("verified:", nok, "failed:", nbad)
