"""Test canonical first requests on the type B / B' anchors of blueprint_0.84.jsonl (floating MILP, depth 1).
Candidates (cells X,Y,Z,PE,PF,PG; r = t - sealed mass):
  c1: seal Y, Z; r into X, overflow split PE/PF
  c2: seal Y, Z; r split equally PE / PF (overflow to X)
  c3: seal Y, Z; r split equally over PE, PF, PG... (cap by mass, overflow to X)
usage: py canon.py"""
import sys, os, json
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "r1b")); sys.path.insert(0, os.path.join(here, "..", "r1"))
import multi, game, game2
T = 0.84
def fill(d, mass, order, r):
    for c in order:
        a = min(r, mass[c] - d[c]); d[c] += a; r -= a
    return d if r < 1e-9 else None
def cands(mass):
    x, y, z = mass[:3]; r = T - y - z; out = {}
    if r < -1e-9: return out
    out["c1"] = fill([0, y, z, 0, 0, 0], mass, [0, 3, 4, 5], r)
    d = [0, y, z, min(r / 2, mass[3]), min(r / 2, mass[4]), 0]; out["c2"] = fill(d, mass, [0, 5], r - d[3] - d[4])
    d = [0, y, z] + [min(r / 3, mass[c]) for c in (3, 4, 5)]; out["c3"] = fill(d, mass, [0, 3, 4, 5], r - sum(d[3:]))
    return out
R = [json.loads(l) for l in open(os.path.join(here, "blueprint_0.84.jsonl"))]
B = [r for r in R if r["kind"] == "adaptive" and not r["closures"]]
ctx = multi.Ctx("0.84", "2000,40,1", 25, 50, cls="all")
res = {}
for r in B:
    q = tuple(r["p"]); mass = game.cell_mass(*(v / 25 for v in q))
    rules = game.Rules(3 - 2 * T, pot=tuple(-v for v in ctx.pot), pot0=-ctx.phi(q) / 25, half=False)
    row = {}
    for nm, d in cands(mass).items():
        row[nm] = None if d is None else game.play(mass, d, T, rules)["result"]
    res[q] = row; print(q, r["sealed"], row, flush=True)
for nm in ("c1", "c2", "c3"): print(nm, "wins", sum(1 for v in res.values() if v.get(nm) == "R"), "of", len(res))
