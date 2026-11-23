"""What would a second round of re-anchoring see?  (heuristic diagnostic, floating point)

For every stuck profile p of a grid file and every recorded winning response K_i, and every seal
pattern under which K_i wins: for each sealed cell c the requester could drop the opposite edge
and continue from the new good triple p' = (mass_c, |K & A1|, |K & A2|) (sorted).  We classify p'
by the status of the NEAREST grid profile in the same file: 'W' (requester wins there, static or
adaptive), 'S' (stuck), 'O' (outside the grid: a cell > xmax or S' > 3 - 2t).
Then, for each grid request D that seals at least one cell, we ask whether some recorded answering
response has all its re-anchor triples of type 'S'/'O' (then a second re-anchoring round does not
obviously help against D).  The sealed requests for which EVERY recorded answer has a re-anchor
triple near a winning profile are the candidates for a two-round win (the adversary may of course
have other answers that were never recorded, so this is an upper bound on what is plausible).

usage: py reanchor_stats.py out/grid_....jsonl VARIANT T
"""
import sys, json, math, itertools
from fractions import Fraction
import numpy as np
import game, outer

def main(fn, variant, tstr):
    t = float(Fraction(tstr)); pden = int(fn.replace("\\", "/").split("_")[-2])
    R = [json.loads(l) for l in open(fn)]
    status = {tuple(r["p"]): ("S" if r.get("win") is None else ("W" if r.get("win") in ("static", "adaptive") else "U")) for r in R}
    def classify(cells):
        q = tuple(sorted((int(round(v * pden)) for v in cells), reverse=True))
        return status.get(q, "O"), q
    dden = 2 * pden if pden < 40 else pden
    for r in sorted((r for r in R if r.get("win") is None and "cuts" in r), key=lambda r: r["p"]):
        i, j, l = r["p"]; x, y, z = i / pden, j / pden, l / pden
        mass = game.cell_mass(x, y, z); rules = game.make_rules(variant, t, x, y, z)
        entries = []          # (kv, sub, [classes of p'])
        Sdiff = []
        for kvf, losing in r["cuts"]:
            kv = list(kvf[:6]); kv.append(1 - sum(kv))
            free = [c for c in range(3) if mass[c] > 1e-9 and kv[c] <= 1e-9]
            for n in range(len(free) + 1):
                for sub in itertools.combinations(free, n):
                    if any(set(m) <= set(sub) for m in losing): continue
                    cls = []
                    for c in list(sub) + [c for c in range(3) if mass[c] <= 1e-9]:
                        a1, a2 = game.TRIPLE_EDGES[c]
                        t1 = sum(u * v for u, v in zip(game.edge_trace_coef(a1), kv))
                        t2 = sum(u * v for u, v in zip(game.edge_trace_coef(a2), kv))
                        cls.append(classify((mass[c], t1, t2))[0]); Sdiff.append(mass[c] + t1 + t2 - (x + y + z))
                    entries.append((kv, sub, cls))
        # grid requests
        Mc = [int(round(m * dden)) for m in mass]; base = math.floor(t * dden + 1e-9)
        grids = np.meshgrid(*[np.arange(Mc[c] + 1) for c in range(5)], indexing="ij")
        n5 = np.stack([g.ravel() for g in grids], axis=1); last = base - n5.sum(axis=1)
        ok = (last >= 0) & (last <= Mc[5]); N = np.concatenate([n5[ok], last[ok][:, None]], axis=1)
        seal = np.zeros(len(N), dtype=int)
        for c in range(3):
            if Mc[c] > 0: seal |= (N[:, c] == Mc[c]).astype(int) << c
        nosafe = np.zeros(len(N), bool)       # answered by a response whose re-anchor triples are all S/O
        for kv, sub, cls in entries:
            if any(cc == "W" for cc in cls): continue
            sp = sum(1 << c for c in sub)
            fit = seal == sp
            for c in range(6): fit &= N[:, c] <= math.floor((mass[c] - kv[c]) * dden + 1e-9)
            nosafe |= fit
        sealed_any = seal > 0
        open_sealed = int((sealed_any & ~nosafe).sum())
        cnt = {k: sum(1 for e in entries for cc in e[2] if cc == k) for k in "WSOU"}
        print(f"{r['p']}: requests {len(N)}, with a sealed cell {int(sealed_any.sum())}; sealed requests for which "
              f"every recorded answer has a re-anchor triple near a winning profile: {open_sealed}; "
              f"re-anchor triples near W/S/outside = {cnt['W']}/{cnt['S']}/{cnt['O']}; "
              f"S'-S in [{min(Sdiff, default=0):+.3f},{max(Sdiff, default=0):+.3f}]")

if __name__ == "__main__":
    main(*sys.argv[1:4])
