"""CEGAR on the adversary's round-5 menu (rounds 2-4: one fixed omission rule; round 6: exact).
Each iteration: (1) solve the requester's tree MILP against the current menu; (2) at the round-5 node, with the
requester's request fixed, evaluate every 'omit type J first' response exactly (requester's best round-6 reply
by MILP) and add the best one to the menu.  Stops when z* > 0 (menu adversary beats every requester: rigorous),
or when no candidate improves (requester's tree is then optimal against all single-type-first round-5 responses)."""
import sys, time, pulp
from game_tree import Tree, val, asc, desc, order_first, tstr, popc
T = float(sys.argv[1]); N = float(sys.argv[2]); prefix = sys.argv[3]; iters = int(sys.argv[4]); tl = float(sys.argv[5])
base = asc if prefix == "lo" else desc
items5 = [("lo", "asc", ()), ("hi", "desc", ())]
def mk(spec, types):
    name, tail, first = spec
    first = [J for J in first if J in types]
    return (name, order_first(first, types, asc if tail == "asc" else desc))
def menu(i, types):
    if i < 4: return [(prefix, base(types))]
    return [mk(sp, types) for sp in items5]
t00 = time.time()
for it in range(iters):
    t0 = time.time()
    tr = Tree(T, N, menu, tl=tl)
    r = tr.res
    if not r.has_solution:
        print(f"iter {it}: no solution ({r.status_str})", flush=True); break
    z = pulp.value(tr.z)
    print(f"iter {it}: menu5={[s[0] for s in items5]} status={r.status_str} z*={z:.5f} bound={r.best_bound:.5f} [{time.time()-t0:.0f}s]", flush=True)
    if r.status_str == "Optimal" and z > 1e-5:
        print("ADVERSARY WINS with this menu (every requester loses by at least z*)", flush=True)
        for path, m, s, a, tot, rho, q in tr.leaves:
            Dm = sum(val(x) for x in tot)
            print("  leaf", path, "mass(D)=%.4f" % Dm, "state after 5:", {tstr(J): round(val(m[J]), 4) for J in sorted(m) if val(m[J]) > 1e-6},
                  "request6:", {tstr(J): round(val(s[J]), 4) for J in sorted(s) if val(s[J]) > 1e-6})
        break
    # round-5 node
    node = [nd for nd in tr.nodes if nd[1] == 4][0]
    path, i, m, s, rho = node
    mnum = {J: max(0.0, val(m[J])) for J in m}
    rnum = {J: (1 if val(rho[J]) > 0.5 else 0) for J in rho}
    snum = {J: min(mnum[J], max(0.0, val(s[J]))) for J in s}
    tot = sum(snum.values()); 
    print("   state after 4:", {tstr(J): round(v, 4) for J, v in mnum.items() if v > 1e-6}, " request5:", {tstr(J): round(v, 4) for J, v in snum.items() if v > 1e-6}, flush=True)
    best = None
    have = {(sp[1], sp[2]) for sp in items5}
    for J in sorted(mnum):
        if mnum[J] - snum[J] < 1e-6: continue
        for tail in ("asc", "desc"):
            spec = (f"{tstr(J)}>{tail}", tail, (J,))
            if (tail, (J,)) in have: continue
            sub = Tree(T, N, lambda i_, types, spec=spec: [mk(spec, types)], tl=60, start=(4, mnum, rnum, snum))
            if not sub.res.has_solution: continue
            zz = pulp.value(sub.z)
            if best is None or zz > best[0]: best = (zz, spec)
    if best is None:
        print("   no candidates"); break
    print(f"   best single-type-first response at round 5: {best[1][0]}  value z={best[0]:.5f}", flush=True)
    if best[0] <= z + 1e-6:
        print("   no candidate improves on the current menu: requester's tree is robust to all single-type-first round-5 responses", flush=True)
        break
    items5.append(best[1])
print(f"total {time.time()-t00:.0f}s")
