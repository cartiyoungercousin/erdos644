r"""TWIN section 13 checks (exact, small atoms).   py anchors.py
 A. anchor lemma + three-grid criterion vs brute-force 2-cover (random 7-tuples whose first three
    members have empty common intersection; ground set includes points outside the anchors).
 C. |V| <= 2T: the non-adaptive K4 request table has the required cross-intersections.
 D. low overlap p <= T - k/3: exhaustive adversary (all maximal traces, 4 rounds) vs the freeze strategy.
"""
import itertools, random
def coverable(E, pts):
    return any(all((x in e) or (y in e) for e in E) for x in pts for y in pts)

def grids_cover(anc, later):
    a = anc
    for (i, j, c) in ((0, 1, 2), (0, 2, 1), (1, 2, 0)):
        P = a[i] & a[j]; Bc = a[c]
        for x in P:
            for y in Bc:
                if not any((x not in e) and (y not in e) for e in later): return False
    return True

def checkA(trials=4000, seed=5):
    rnd = random.Random(seed); n_ok = 0
    while n_ok < trials:
        n = rnd.randint(5, 10); ks = rnd.randint(2, 4)
        E = [frozenset(rnd.sample(range(n), ks)) for _ in range(7)]
        if E[0] & E[1] & E[2]: continue
        n_ok += 1
        V = E[0] | E[1] | E[2]
        cov = coverable(E, range(n))
        assert cov == coverable(E, V)                     # anchor lemma: covers live in V
        assert cov == (not grids_cover(E[:3], E[3:]))      # three-grid criterion
        tr = [e & V for e in E]                            # traces
        assert cov == coverable(tr, V)
    return trials

def checkC():
    M = {'12': [{4,7},{5,6}], '13': [{4,6},{5,7}], '23': [{4,5},{6,7}]}
    allp = [set(c) for c in itertools.combinations([4,5,6,7], 2)]
    Q = {c: [t for t in allp if t not in M[ab]] for c, ab in (('3','12'), ('2','13'), ('1','23'))}
    for ab, c in (('12','3'), ('13','2'), ('23','1')):
        others = [t for o in M if o != ab for t in M[o]] + Q[c]
        assert all(x & y for x in M[ab] for y in others)
    # loads: every round gets half of each part
    for part in list(M.values()) + list(Q.values()):
        for i in (4,5,6,7): assert 2 * sum(i in t for t in part) == len(part)
    return True

def checkD(k, T, anchors):
    a = [frozenset(x) for x in anchors]
    assert not (a[0] & a[1] & a[2])
    V = a[0] | a[1] | a[2]
    P = (a[0] & a[1]) | (a[0] & a[2]) | (a[1] & a[2]); p = len(P)
    assert 3 * (T - p) >= k, "hypothesis p <= T - k/3"
    Qs = sorted(V - P); leaves = [0]
    def rec(later, X):
        r = len(later)
        if r == 4:
            E = a + later
            assert not coverable(E, V), E
            leaves[0] += 1; return
        pool = Qs if X is None else sorted(X)
        if r == 3: assert len(pool) <= T - p
        S = set(P) | set(pool[:T - p])
        free = sorted(V - S)
        for tr in itertools.combinations(free, min(k, len(free))):
            e = frozenset(tr)
            newX = (e & set(Qs)) if X is None else (X & e)
            rec(later + [e], newX)
    rec([], None)
    return leaves[0]

if __name__ == '__main__':
    print('A: anchor lemma, trace equivalence and three-grid criterion agree with brute force on', checkA(2000), 'tuples')
    print('C: K4 table cross-intersections and half-loads ok:', checkC())
    print('D: k=3,T=2, p=1: leaves all uncoverable:', checkD(3, 2, [{1,2,3},{3,4,5},{6,7,8}]))
    print('D: k=3,T=2, p=1 (disjoint pair + third):', checkD(3, 2, [{1,2,3},{4,5,6},{3,7,8}]))
    # checkD(4, 3, [{1,2,3,4},{4,5,6,7},{8,9,10,11}]) is too slow in pure Python (not run to completion)
