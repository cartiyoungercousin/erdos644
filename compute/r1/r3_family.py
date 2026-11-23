"""R3 realizability test for a stuck profile.

step 1 (py r3_family.py build VARIANT T i j l PDEN K):  rerun the outer loop with responses
   restricted to multiples of 1/K (so that at edge size k = K everything is integral) and write
   out/r3_<...>.json with the block sizes and the response types.
step 2 (py r3_family.py test out/r3_<...>.json [O_SIZE]):  build the block-type family
      blocks  X, Y, Z, PE, PF, PG, O (new points),
      types   E, F, G and every response type K_i (ALL k-sets with these block counts),
   compute tau exactly (MILP over block counts) and search a bad 7-tuple with typefam.py.
   Without O_SIZE: O = T + max new points (then tau > T follows from the stuck certificate),
   and the smallest O for which tau > T still holds is also reported.
(The two steps are separate processes because typefam.py and game.py configure HiGHS differently.)
"""
import sys, json, os
from fractions import Fraction

def build(variant, tstr, i, j, l, pden, k):
    import outer, game, exact_check
    t = float(Fraction(tstr)); x, y, z = i / pden, j / pden, l / pden
    rules = game.make_rules(variant, t, x, y, z)
    r = outer.solve_profile(x, y, z, t, rules, den=k, kden=k)
    assert r["win"] is None, r["win"]
    cuts = [([round(v, 9) for v in kv], [list(m) for m in losing]) for kv, losing in r["cuts"]]
    tot, unc, used = exact_check.verify_stuck(i, j, l, pden, Fraction(tstr), variant, cuts, dden=k)
    print(f"stuck with {len(cuts)} integral responses; exact check: {tot} requests, {unc} uncovered")
    mass = game.cell_mass(x, y, z)
    sizes = [round(m * k) for m in mass]
    types = sorted({tuple(round(v * k) for v in kv) for kv, _ in cuts})
    fn = f"out/r3_{variant}_{tstr.replace('/', '_')}_{i}_{j}_{l}_{pden}_k{k}.json"
    json.dump(dict(variant=variant, t=tstr, profile=[i, j, l, pden], k=k, T=int(Fraction(tstr) * k),
                   sizes=sizes, responses=types, uncovered=unc), open(fn, "w"))
    print("wrote", fn)

def tau_milp(sizes, types):
    import pulp
    prob = pulp.LpProblem("tau", pulp.LpMinimize)
    tv = [prob.add_variable(f"t_{b}", 0, s, cat="Integer") for b, s in enumerate(sizes)]
    prob += pulp.lpSum(tv)
    for i, c in enumerate(types):
        bs = []
        for b, s in enumerate(sizes):
            if c[b] == 0: continue                     # cannot hit the edge type through block b
            h = prob.add_variable(f"h_{i}_{b}", cat="Binary"); bs.append(h)
            prob += tv[b] >= (s - c[b] + 1) * h
        prob += pulp.lpSum(bs) >= 1
    st = prob.solve(pulp.HiGHS(msg=False))
    assert st.status.name == "Optimal"
    return int(round(pulp.value(prob.objective))), [int(round(v.value())) for v in tv]

def test(fn, osize=None, time_limit=900):
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    import typefam
    J = json.load(open(fn)); k, T = J["k"], J["T"]; sz = J["sizes"]
    x, y, z, pe, pf, pg = sz
    resp = [tuple(r) for r in J["responses"]]
    base = [(x, y, 0, pe, 0, 0, 0), (x, 0, z, 0, pf, 0, 0), (0, y, z, 0, 0, pg, 0)]
    maxnew = max(r[6] for r in resp)
    names = ["X", "Y", "Z", "PE", "PF", "PG", "O"]
    def fam(o):
        return [x, y, z, pe, pf, pg, o], base + [r for r in resp if r[6] <= o]
    o_full = T + maxnew
    if osize is None:
        o = o_full
        lo = None
        for cand in range(0, o_full + 1):
            s, ty = fam(cand)
            if tau_milp(s, ty)[0] > T: lo = cand; break
        print(f"k={k} T={T} cells={dict(zip(names, sz))}; {len(resp)} response types, max new points {maxnew}")
        print(f"smallest O with tau > T: {lo};  O = T + max new = {o_full}")
        todo = [o_full] + ([lo] if lo is not None and lo != o_full else [])
    else:
        todo = [osize]
    for o in todo:
        s, ty = fam(o)
        tau, tvec = tau_milp(s, ty)
        print(f"--- O = {o}: n = {sum(s)}, {len(ty)} types, tau = {tau} (T = {T}; optimal transversal block counts {dict(zip(names, tvec))})")
        F = typefam.TypeFamily(s, ty, name="r3")
        w = F.find_bad_tuple(7, time_limit=time_limit)
        if w is None:
            print("    NO bad 7-tuple: property (7,2) holds." + ("  tau > T: COUNTEREXAMPLE CANDIDATE -- verify!" if tau > T else ""))
            continue
        ok = typefam.verify_witness(F, w)
        print(f"    bad 7-tuple found (independent brute-force check: {ok}).  Edge types:")
        for c in w["edge_types"]:
            tag = {base[0]: "E", base[1]: "F", base[2]: "G"}.get(c, "K")
            print("      ", tag, dict(zip(names, c)))
        sig = {}
        for (b, sg), cnt in w["m"].items(): sig.setdefault(format(sg, "07b"), {})[names[b]] = cnt
        print("    membership classes (edge-membership bitstring, edge 7..1 -> block counts):")
        for sg in sorted(sig): print("      ", sg, sig[sg])

def prune(fn, rounds=12, time_limit=900):
    """Refinement loop on the response types: while the family has tau > T and a bad 7-tuple,
    delete the response type used most often in the tuple (ties: the one with most new points)."""
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    import typefam
    from collections import Counter
    J = json.load(open(fn)); k, T = J["k"], J["T"]; sz = J["sizes"]
    x, y, z, pe, pf, pg = sz
    resp = [tuple(r) for r in J["responses"]]
    base = [(x, y, 0, pe, 0, 0, 0), (x, 0, z, 0, pf, 0, 0), (0, y, z, 0, 0, pg, 0)]
    o = T + max(r[6] for r in resp)
    sizes = [x, y, z, pe, pf, pg, o]
    for it in range(rounds):
        types = base + resp
        tau, tvec = tau_milp(sizes, types)
        print(f"round {it}: {len(resp)} response types, tau = {tau} (T = {T})", flush=True)
        if tau <= T:
            print("   tau <= T: the remaining recorded responses no longer answer every request; stop."); return
        w = typefam.TypeFamily(sizes, types).find_bad_tuple(7, time_limit=time_limit)
        if w is None:
            print("   NO bad 7-tuple and tau > T: COUNTEREXAMPLE CANDIDATE at this k -- verify!"); return
        cnt = Counter(c for c in w["edge_types"] if c not in base)
        nb = sum(1 for c in w["edge_types"] if c in base)
        victim = max(cnt, key=lambda c: (cnt[c], c[6]))
        print(f"   bad tuple: {nb} anchor edges + response types {dict(cnt)}; deleting {victim}", flush=True)
        resp.remove(victim)


if __name__ == "__main__":
    if sys.argv[1] == "build":
        build(sys.argv[2], sys.argv[3], *(int(a) for a in sys.argv[4:9]))
    elif sys.argv[1] == "prune":
        prune(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 12)
    else:
        test(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else None)
