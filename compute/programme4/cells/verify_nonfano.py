r"""Re-verify NON-FANO-ONLY families (two cells) without trusting the solvers' 'infeasible':
 (i)  a good seven EXISTS: take the CP-SAT witness x, build the seven members explicitly on labelled points, check
      each has size k and profile in J, and check every pair {x, y} (x = y allowed) is avoided by some member.
 (ii) NO Fano-type seven, by exhaustive enumeration of the brief's criterion: colour-class sizes x^1 (orbit
      representatives under the 168 collineations) and x^2 (all compositions into 7 parts); for every line l
      need j in J with j <= (sum_{p not in l} x^1_p, sum_{p not in l} x^2_p).  No solver involved.
usage: verify_nonfano.py fano_*.jsonl ...   (prints one JSON line per family)"""
import itertools, json, sys
import numpy as np
import cells

LINES = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
LS = set(frozenset(l) for l in LINES)
AUT = [g for g in itertools.permutations(range(7)) if all(frozenset(g[p] for p in l) in LS for l in LINES)]
assert len(AUT) == 168
OFF = np.array([[0 if p in l else 1 for p in range(7)] for l in LINES])          # 7 lines x 7 points


def comps7(a):
    return [c for c in cells.compositions(a, [a] * 7)]


def fano_exists(a, k, J):
    assert len(a) == 2
    J1 = set(j[0] for j in J)
    ok = np.zeros((a[0] + 1, a[1] + 1), dtype=bool)                      # ok[c1, c2]: some j <= (c1, c2)
    for c1 in range(a[0] + 1):
        for c2 in range(a[1] + 1):
            ok[c1, c2] = any(j1 <= c1 and k - j1 <= c2 for j1 in J1)
    reps = {}
    for c in comps7(a[0]):
        key = min(tuple(c[g[p]] for p in range(7)) for g in AUT)
        reps[key] = 1
    X2 = np.array(comps7(a[1])); C2 = X2 @ OFF.T                            # N2 x 7 line-complement sizes
    for r in reps:
        C1 = OFF @ np.array(r)                                               # 7
        if ok[C1[None, :], C2].all(axis=1).any():
            return True
    return False


def explicit_seven(a, k, J, xs):
    pts = []                                    # list of (cell, cotype)
    for i in range(len(a)):
        for S, c in sorted(xs[i].items()):
            pts += [(i, S)] * c
    assert len(pts) == sum(a)
    Js = set(tuple(j) for j in J)
    B = [frozenset(v for v, (i, S) in enumerate(pts) if not (S >> m) & 1) for m in range(7)]
    for b in B:
        prof = tuple(sum(1 for v in b if pts[v][0] == i) for i in range(len(a)))
        assert len(b) == k and prof in Js
    n = len(pts)
    return all(any(x not in b and y not in b for b in B) for x in range(n) for y in range(x, n))


if __name__ == '__main__':
    from fano_suff import UPFANO
    for fn in [f for f in sys.argv[1:] if not f.isdigit()]:
        for line in open(fn):
            r = json.loads(line)
            for e in r['nonfano_only']:
                a, k = tuple(r['a']), r['k']; J = [tuple(j) for j in e['J']]
                xs = {int(i): {int(S): c for S, c in d.items()} for i, d in e['x'].items()}
                from math import comb
                cost = comb(a[0] + 6, 6) / 168 * comb(a[1] + 6, 6) if len(a) == 2 else float("inf")
                fb = fano_exists(a, k, J) if cost <= float(sys.argv[-1] if sys.argv[-1].isdigit() else 3e8) else 'skipped'
                if fb == 'skipped':
                    fb = 'skipped; cpsat=' + cells.find_seven(a, k, J, 3600, types=UPFANO)[0]
                print(json.dumps(dict(k=k, a=a, n=sum(a), tau=e['tau'], J1=[j[0] for j in J],
                                      seven_explicit=explicit_seven(a, k, J, xs), fano_brute=fb,
                                      ntypes=len(set(S for i in xs for S in xs[i])))), flush=True)
