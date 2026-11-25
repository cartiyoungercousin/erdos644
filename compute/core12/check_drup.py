r"""CORE 112: independent DRUP (RUP-only) checker for the UNSAT certificates written by profile_search.py.
Each added lemma must follow from the current clause set by unit propagation (forward check); deletions ('d ...')
are ignored (sound; incremental solvers delete reason/unit clauses). Accepts iff the empty clause is derived (or the final set is refuted by unit propagation alone).
It also re-derives the covering clauses from (k, T, n, cells) and checks that every other input clause is a cut
justified by a logged good seven that is re-verified here by plain code (no solver).
Usage: py -3.14 check_drup.py logs/prof_..._(base)   (reads base.cnf, base.drup, base.json)"""
import sys, json, itertools

base = sys.argv[1]
meta = json.load(open(base + '.json')); k, T, n, cells, nondeg = meta['k'], meta['T'], meta['n'], meta['cells'], meta['nondeg']
q = len(cells); c = n - k


def boxes(total):
    out = []
    def rec(j, left, cur):
        if j == q - 1:
            if left <= cells[j]: out.append(tuple(cur + [left]))
            return
        for a in range(min(left, cells[j]) + 1): rec(j + 1, left - a, cur + [a])
    rec(0, total, []); return out


P = boxes(c); idx = {p: i + 1 for i, p in enumerate(P)}
expected = set()
for s in boxes(T): expected.add(frozenset(idx[p] for p in P if all(a >= b for a, b in zip(p, s))))
if nondeg:
    for j in range(q): expected.add(frozenset(idx[p] for p in P if p[j] < cells[j]))
cuts = set()
for e in meta['sevens']:
    slots = [tuple(s) for s in e['slots']]; z = [{int(I): v for I, v in zj.items()} for zj in e['z']]
    assert all(s in idx for s in slots)
    for j in range(q):
        assert sum(z[j].values()) == cells[j]
        for i in range(7): assert sum(v for I, v in z[j].items() if I >> i & 1) == slots[i][j]
    sup = set(I for zj in z for I in zj); assert 0 not in sup and all(a & b for a in sup for b in sup)
    cuts.add(frozenset(-idx[s] for s in slots))
lines = open(base + '.cnf').read().split('\n')
clauses = [list(map(int, l.split()))[:-1] for l in lines[1:] if l.strip()]
for cl in clauses:
    f = frozenset(cl)
    assert f in expected or f in cuts, f"unjustified clause {cl}"
covered = set(frozenset(cl) for cl in clauses)
assert expected <= covered, "a covering clause is missing"


def up_conflict(db, assum):
    val = {}
    for l in assum:
        if val.get(-l): return True
        val[l] = True
    changed = True
    while changed:
        changed = False
        for cl in db:
            unassigned = None; nun = 0; sat = False
            for l in cl:
                if val.get(l): sat = True; break
                if not val.get(-l): nun += 1; unassigned = l
            if sat: continue
            if nun == 0: return True
            if nun == 1: val[unassigned] = True; changed = True
    return False


db = [list(cl) for cl in clauses]
derived_empty = up_conflict(db, [])
nl = 0
for l in open(base + '.drup').read().split('\n'):
    l = l.strip()
    if not l or derived_empty: continue
    if l.startswith('d'):
        continue   # deletions ignored: sound (every clause kept is implied by the input), only slower
    cl = list(map(int, l.split()))[:-1]; nl += 1
    assert up_conflict(db, [-x for x in cl]), f"lemma {cl} is not RUP"
    db.append(cl)
    if not cl: derived_empty = True
if not derived_empty: derived_empty = up_conflict(db, [])
print(f"{base}: {len(clauses)} clauses ({len(cuts)} cuts, each with a re-verified good seven), {nl} lemmas: "
      + ("CERTIFICATE VERIFIED (UNSAT)" if derived_empty else "REJECTED: empty clause not derived"))
