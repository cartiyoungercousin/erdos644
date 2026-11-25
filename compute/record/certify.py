"""Build exact certificates for plans on profile polytopes (boxes & region R).

certify_box(box, plan_or_'static', t, C) -> certificate dict or raises search.Fail.
A certificate: {"box": [[lo,hi]x3], "kind": "static"|"plan", "plan": plan json,
                "valid": {name: y}, "roots": {branch key: tree}}  (all numbers as strings)
"""
from __future__ import annotations
import json, sys, time
from fractions import Fraction as Fr
import model, search


def Q(v):
    return Fr(v) if not isinstance(v, float) else Fr(v).limit_denominator(10 ** 6)


def certify_box(box, plan, t, C, max_nodes=4000, fast=True):
    t = Fr(t)
    box = [(Fr(a), Fr(b)) for a, b in box]
    prof = model.profile_rows(t, box)
    out = {"box": [[str(a), str(b)] for a, b in box], "t": str(t), "C": str(C)}
    absent = [c for c in range(3) if box[c] == (0, 0)]
    if plan == "static":
        so = model.static_option(absent)
        S = search.Searcher(t, [so], max_nodes=max_nodes, fast=fast and not absent)
        out["kind"] = "static"; out["absent"] = absent
        out["roots"] = {"static": S.solve_root(prof)}
        out["nodes"] = S.nodes
        return out
    if absent:
        plan = model.Plan(tuple(sorted(set(plan.sealed) | set(absent))), {c: v for c, v in plan.req.items() if c not in absent}, plan.C, plan.t, absent)
    out["kind"] = "plan"; out["plan"] = plan.to_json()
    S = search.Searcher(t, model.options_for(plan), max_nodes=max_nodes, fast=fast and not plan.absent)
    valid = {}
    rows4 = [(nm, c, r, False) for nm, c, r in prof]
    for nm, f, bound in plan.validity_rows():
        y = S.cert(rows4, f[0], bound - f[1])
        if y is None: raise search.Fail("plan invalid on box: " + nm)
        valid[nm] = y
    out["valid"] = valid
    base = prof + plan.base_rows()
    roots = {}
    for key, br in plan.branches():
        roots[json.dumps(key)] = S.solve_root(base + br)
    out["roots"] = roots
    out["nodes"] = S.nodes; out["stats"] = S.stats
    return out


def plan_from_point(p, D, C, t, adjust=None):
    """plan from a request D (6 rationals) at the profile p (3 rationals).  Constant request on
    unsealed cells (adjust=None) or an affine correction (see cover.py)."""
    mass = [p[0], p[1], p[2], 1 - p[0] - p[1], 1 - p[0] - p[2], 1 - p[1] - p[2]]
    sealed = [c for c in range(3) if D[c] == mass[c]]
    req = {c: (D[c], (0, 0, 0)) for c in range(3, 6)}
    for c in range(3):
        if c not in sealed: req[c] = (D[c], (0, 0, 0))
    return model.Plan(sealed, req, C, t)


if __name__ == "__main__":
    # test: exact certificate at one grid profile from a scan file
    fn, idx = sys.argv[1], sys.argv[2]
    t = Fr(sys.argv[3]); C = Fr(sys.argv[4]); pden = int(sys.argv[5]); dden = int(sys.argv[6])
    want = tuple(int(v) for v in idx.split(","))
    for line in open(fn):
        r = json.loads(line)
        if tuple(r["p"]) == want: break
    p = [Fr(v, pden) for v in want]
    box = [(v, v) for v in p]
    t0 = time.time()
    if r["win"] == "static":
        cert = certify_box(box, "static", t, C)
    else:
        D = [Fr(round(v * dden * 1000), dden * 1000) for v in r["D"]]
        plan = plan_from_point(p, D, C, t)
        cert = certify_box(box, plan, t, C)
    print(r["win"], "nodes", cert["nodes"], cert.get("stats"), round(time.time() - t0, 1), "s")
    if len(sys.argv) > 7: json.dump(cert, open(sys.argv[7], "w"))
