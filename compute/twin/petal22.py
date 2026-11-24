r"""TWIN section 15 checks.  py petal22.py
 1. (2,2) petals, triple-free, with all four cross points: the only petal-covering pairs are
    core_X x core_Y and the two complementary cross pairs (brute force over points).
 2. Design 3 (A: {12},{13}; B: {1},{23}) leaves no 2-cover whatever the three replies are
    (random replies, including fresh points and re-used outside points).
 3. Exact optimum of the 3-round design for an a x b grid by enumeration of all type assignments
    on atoms (small a, b), compared with L*(a,b).
"""
import itertools, random
def coverable(E, pts): return any(all((x in e) or (y in e) for e in E) for x in pts for y in pts)

def build(a, b, k):
    cx = [('cx', i) for i in range(a)]; cy = [('cy', i) for i in range(b)]
    s = {(i, j): ('s', i, j) for i in (1, 2) for j in (3, 4)}
    pet = {1: set(cx) | {s[1, 3], s[1, 4]}, 2: set(cx) | {s[2, 3], s[2, 4]},
           3: set(cy) | {s[1, 3], s[2, 3]}, 4: set(cy) | {s[1, 4], s[2, 4]}}
    for i in pet:
        j = 0
        while len(pet[i]) < k: pet[i].add(('single', i, j)); j += 1
    return cx, cy, s, pet

def check12(a=2, b=2, k=5, T=4, trials=20000, seed=3):
    cx, cy, s, pet = build(a, b, k)
    U = set().union(*pet.values())
    J = {u: frozenset(i for i in pet if u in pet[i]) for u in U}
    pairs = {frozenset((u, v)) for u in U for v in U if J[u] | J[v] == {1, 2, 3, 4}}
    expect = {frozenset((u, v)) for u in cx for v in cy} | {frozenset((s[1, 3], s[2, 4])), frozenset((s[1, 4], s[2, 3]))}
    assert pairs == expect
    # design 3 on rounds 1,2,3 ; cross pairs killed in rounds 2 and 3
    S = None
    for al in range(a + 1):
        for be in range(b + 1):
            S2 = {1: set(cx) | set(cy[:be]), 2: set(cx[:al]) | set(cy[be:]) | {s[1, 3], s[2, 4]},
                  3: set(cx[al:]) | set(cy[be:]) | {s[1, 4], s[2, 3]}}
            if all(len(S2[r]) <= T for r in S2): S = S2
    assert S is not None, 'design 3 does not fit'
    for p in pairs: assert any(p <= S[r] for r in S)
    rnd = random.Random(seed); fresh = [('f', i) for i in range(3 * k)]
    for _ in range(trials):
        E = []
        for r in (1, 2, 3):
            pool = [u for u in list(U) + fresh if u not in S[r]]
            E.append(set(rnd.sample(pool, k)))
        tup = list(pet.values()) + E
        assert not coverable(tup, set().union(*tup))
    return len(pairs), {r: len(S[r]) for r in S}

def Lstar(a, b):
    c = [a + b / 3, b + a / 3, 2 * (a + b) / 3]
    if b >= a / 2: c.append(3 * a / 4 + b / 2)
    if a >= b / 2: c.append(3 * b / 4 + a / 2)
    return min(c)

def exact_design(a, b):
    """min over all kill-type assignments (atoms) of the max round load; brute force"""
    types = [frozenset(t) for r in (1, 2, 3) for t in itertools.combinations((1, 2, 3), r)]
    best = 99
    for A in itertools.combinations_with_replacement(types, a):
        okB = [t for t in types if all(t & x for x in set(A))]
        if not okB: continue
        for B in itertools.combinations_with_replacement(okB, b):
            load = max(sum(r in t for t in A) + sum(r in t for t in B) for r in (1, 2, 3))
            best = min(best, load)
    return best

if __name__ == '__main__':
    print('1,2: covering pairs and design-3 loads (k=5,T=4,a=b=2):', check12())
    print('1,2: (k=8,T=6,a=b=4):', check12(4, 4, 8, 6, trials=5000))
    print('3: exact atom optimum vs ceil-ish L*:')
    for a in range(1, 7):
        row = []
        for b in range(a, 7):
            row.append(f"({a},{b}):{exact_design(a, b)}|{Lstar(a, b):.2f}")
        print('   ', '  '.join(row))
