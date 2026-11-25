r"""Independent certificate checker for UNSAT results of cells.py (does not import cells.py, no SAT solver).

For every instance (a, k, T) with status UNSAT and its list of cuts:
 1. each cut is a co-type configuration x[i][S]; check S nonempty subsets of [7], support pairwise intersecting,
    sum_S x[i][S] = a_i; recompute A_m = (sum_{S not containing m} x[i][S])_i and box_m = {j in U : j <= A_m}.
    (Monotone seven criterion: if J meets every box_m then H_J has a good seven.)
 2. recompute the covering sets C_u = {j in U : j <= a - u} for all u with sum u = T, and show by exhaustive
    hitting-set branching that NO J hits every C_u while missing some box of every cut.
    (Both properties are monotone, so branching over 'which element of the first unhit C_u enters J' is complete.)
usage: check_cert.py file.jsonl [file2.jsonl ...]
"""
import json, sys


def comps(total, caps):
    if len(caps) == 1:
        if 0 <= total <= caps[0]:
            yield (total,)
        return
    for v in range(max(0, total - sum(caps[1:])), min(caps[0], total) + 1):
        for t in comps(total - v, caps[1:]):
            yield (v,) + t


def check(r):
    a, k, T = tuple(r['a']), r['k'], r['T']
    q = len(a)
    U = list(comps(k, [min(x, k) for x in a]))
    covers = []
    for u in comps(T, list(a)):
        b = [x - y for x, y in zip(a, u)]
        covers.append(frozenset(t for t, j in enumerate(U) if all(j[i] <= b[i] for i in range(q))))
    if r['status'] == 'TRIVIAL':
        assert any(not c for c in covers), 'TRIVIAL claimed but every C_u nonempty'
        return 'ok-trivial'
    assert r['status'] == 'UNSAT'
    cuts = []
    for cut in r['cuts']:
        xs = [{int(S): c for S, c in cut[str(i)].items()} for i in range(q)]
        sup = [S for i in range(q) for S, c in xs[i].items() if c > 0]
        assert all(0 < S < 128 for S in sup)
        assert all(S & S2 for S in sup for S2 in sup), 'support not pairwise intersecting'
        assert all(sum(xs[i].values()) == a[i] for i in range(q)) and all(c >= 0 for i in range(q) for c in xs[i].values())
        boxes = []
        for m in range(7):
            A = [sum(c for S, c in xs[i].items() if not (S >> m) & 1) for i in range(q)]
            boxes.append(frozenset(t for t, j in enumerate(U) if all(j[i] <= A[i] for i in range(q))))
        cuts.append(boxes)
    # cut violated (= J contains a good seven) iff every box meets J
    covers.sort(key=len)
    nodes = [0]

    def dfs(J, X):
        nodes[0] += 1
        for boxes in cuts:
            if all(bx & J for bx in boxes):
                return False                          # this J (and supersets) has a good seven
        for c in covers:
            if not (c & J):
                cand = sorted(c - X)
                X2 = set(X)
                for e in cand:
                    if dfs(J | {e}, frozenset(X2)):
                        return True
                    X2.add(e)
                return False
        return True                                   # covering and violates no cut: certificate FAILS

    assert not dfs(frozenset(), frozenset()), 'a covering J survives all cuts'
    return f'ok ({len(cuts)} cuts, {nodes[0]} nodes)'


if __name__ == '__main__':
    tot = 0; bad = 0
    for fn in sys.argv[1:]:
        for line in open(fn):
            r = json.loads(line)
            if r['status'] not in ('UNSAT', 'TRIVIAL'):
                print('skip', r['a'], r['status']); continue
            try:
                check(r); tot += 1
            except AssertionError as e:
                bad += 1; print('FAIL', r['a'], r['k'], r['T'], e)
    print(f'checked {tot} instances, {bad} failures')
