"""CORE Part IX: EXACT (rational) proof that at a given position and request NO dump spoils.

Claim proved: for every legal dump D (0 <= d_J <= free_J, sum = omega) some reading R containing the new reply has
need_R <= base - margin.  Method: split the dump polytope into pieces {lo <= d <= hi, sum d = omega} (dyadic axis
splits); on a piece, one reading R and a primal feasible point of its LP at EVERY vertex of the piece with objective
<= base - margin; need_R is convex in D (LP value, masses on the right-hand side: a convex combination of feasible
points is feasible for the combined masses), so the bound holds on the whole piece.
Float (HiGHS) only proposes the reading and the points; feasibility and objective are recomputed in Fractions.
Usage: py spoil_exact.py posfile.json     ({"t":..,"N":..,"nrep":..,"pos":{cell:mass},"s":{cell:mass}} as strings of rationals)
"""
import sys, json, itertools
from fractions import Fraction as Fr
import spoil as SP

def vertices(lo, hi, tot):
    """vertices of {lo <= d <= hi, sum = tot}"""
    n = len(lo); out = set()
    for j in range(n):
        others = [i for i in range(n) if i != j]
        for bits in itertools.product((0, 1), repeat=n - 1):
            d = [None] * n; ssum = Fr(0)
            for i, b in zip(others, bits):
                d[i] = hi[i] if b else lo[i]; ssum += d[i]
            d[j] = tot - ssum
            if lo[j] <= d[j] <= hi[j]: out.add(tuple(d))
    return sorted(out)

def exact_point(P, mu, x, t, om):
    """P: Pat; mu: exact projected masses; x: float primal.  Returns exact objective of a repaired feasible point or None"""
    rd = P.rd; ncol = len(rd.cols); nF = len(rd.F)
    xs = [Fr(max(0.0, x[c])).limit_denominator(10**7) for c in range(ncol)]
    byh = {}
    for c, (hh, E) in enumerate(rd.cols): byh.setdefault(hh, []).append(c)
    for hh in range(1 << rd.r):
        cs = byh.get(hh, []); tot = sum(xs[c] for c in cs)
        if mu[hh] == 0:
            for c in cs: xs[c] = Fr(0)
            continue
        if not cs or tot == 0: return None
        f = mu[hh] / tot
        for c in cs: xs[c] *= f
    obj = Fr(0)
    for e in range(nF):
        lm = sum(xs[c] for c, (hh, E) in enumerate(rd.cols) if e in E)
        u = max(Fr(0), lm - t)
        if u > om: return None
        obj += u
    return obj

def main(fn):
    spec = json.load(open(fn)); t = Fr(spec["t"]); N = Fr(spec["N"]); nrep = spec["nrep"]
    pos = {int(J): Fr(v) for J, v in spec["pos"].items()}; s = {int(J): Fr(v) for J, v in spec["s"].items()}
    om = N - 1 - t; base = om - 4 * (t - Fr(3, 4)); c = N - 1
    assert sum(pos.values()) == N and sum(s.values()) == t and all(0 <= s[J] <= pos[J] for J in s)
    for i in range(nrep): assert sum(v for J, v in pos.items() if J >> i & 1) == c, "co-edge mass"
    E = SP.Engine(float(t), float(N)); bit = 1 << nrep
    cells = sorted(J for J in pos if pos[J] - s.get(J, 0) > 0)
    free = [pos[J] - s.get(J, Fr(0)) for J in cells]
    keys = list(E.readings(nrep + 1, new=nrep))
    def newpos(d):
        m2 = {}
        for J, v in pos.items():
            inn = s.get(J, Fr(0)) + (d[cells.index(J)] if J in cells else Fr(0))
            if inn > 0: m2[J | bit] = m2.get(J | bit, Fr(0)) + inn
            if v - inn > 0: m2[J] = m2.get(J, Fr(0)) + v - inn
        return m2
    def projx(m2, R):
        mu = [Fr(0)] * (1 << len(R))
        for J, v in m2.items():
            hh = 0
            for i, x in enumerate(R):
                if J >> x & 1: hh |= 1 << i
            mu[hh] += v
        return mu
    margin = Fr(spec.get("margin", "1/2000"))
    stats = dict(pieces=0, maxdepth=0, exact_points=0); used = {}
    cache = {}
    def vert_ok(v, key):
        """exact objective bound at vertex v for reading key, or None"""
        if (v, key) in cache: return cache[(v, key)]
        R, pi = key; P = E.pats[len(R)][pi]
        mu = projx(newpos(v), R)
        val = P.need([float(a) for a in mu]); res = None
        if val < float(base - margin) - 1e-7:
            x = list(P.rd.h.getSolution().col_value)
            res = exact_point(P, mu, x, t, om); stats["exact_points"] += 1
            if res is not None and res > base - margin: res = None
        cache[(v, key)] = res
        return res
    def rec(lo, hi, depth):
        vs = vertices(lo, hi, om)
        if not vs: return True
        stats["maxdepth"] = max(stats["maxdepth"], depth)
        order = sorted(keys, key=lambda k: -used.get(k, 0))
        for key in order:
            if all(vert_ok(v, key) is not None for v in vs):
                used[key] = used.get(key, 0) + 1; stats["pieces"] += 1; return True
        if depth >= 26: print("FAILED piece", [float(a) for a in lo], [float(a) for a in hi]); return False
        j = max(range(len(lo)), key=lambda i: min(hi[i], om) - lo[i])
        mid = (lo[j] + min(hi[j], om)) / 2
        h2 = list(hi); h2[j] = mid; l2 = list(lo); l2[j] = mid
        return rec(lo, h2, depth + 1) and rec(l2, hi, depth + 1)
    ok = rec([Fr(0)] * len(cells), [min(f, om) for f in free], 0)
    print(json.dumps(dict(file=fn, proved_no_spoiler=ok, base=str(base), margin=str(margin), bound=str(base - margin), free_cells=[SP.nm(J) for J in cells], **stats,
                          readings_used={f"{[i+1 for i in R]}#{pi}": n for (R, pi), n in used.items()})))
    return ok

if __name__ == "__main__":
    main(sys.argv[1])
