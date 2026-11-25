r"""Exhaustive checks of the finite Fano-plane facts used in the hand proof (notes section 3)."""
import itertools, random
from core import LSET, PENCIL, ANTI, P0, popc
from construct import TRIANGLES, ODD_TRIPLES, BRIEF_TRIPLES, BRIEF_FIX, HAM, m_vector, colour_of

pts = range(7)
# (F1) N[l][p] = [p not in l]; kernel over F2 = Hamming code = span of lines
ker = [x for x in range(128) if all(sum((x >> p & 1) for p in pts if p not in LSET[l]) % 2 == 0 for l in range(7))]
assert sorted(ker) == HAM, 'F1'
assert (1 << 7) - 1 in HAM
# (F2) admissible patterns: subsets of anti-pencils = sets of lines with no three concurrent... and size <= 4
for J in itertools.chain.from_iterable(itertools.combinations(range(7), r) for r in range(8)):
    adm = any(set(J) <= ANTI[p] for p in pts)
    noconc = all(not set(PENCIL[p]) <= set(J) for p in pts)
    assert adm == noconc, ('F2', J)
# (F3) a triangle's degree-1 points form a line; its degree-0 point is its colour
for T in TRIANGLES:
    deg = [sum(p in LSET[l] for l in T) for p in pts]
    assert frozenset(p for p in pts if deg[p] == 1) in LSET and deg.count(0) == 1 and deg[colour_of(T)] == 0
# (F4) odd triples => pencil parity sum is all-ones (so m is integral when w_i = k mod 2)
for t in ODD_TRIPLES:
    for p in pts:
        assert sum(sum(p in LSET[l] for l in T) for T in t) % 2 == 1
# (F5) the brief's triples: T_i = ANTI(q_i) - l_i, pencil parity of T_i is l_i
for t in BRIEF_TRIPLES:
    for i, T in enumerate(t):
        l = PENCIL[P0][i]
        assert frozenset(p for p in pts if sum(p in LSET[x] for x in T) == 1) == LSET[l]
print('odd triples', len(ODD_TRIPLES), 'brief triples', len(BRIEF_TRIPLES), 'brief fixers', len(BRIEF_FIX))
# (F6) the size formula and lower bound m_p >= (k - 3W - 6f)/4, on random data
rng = random.Random(0)
for _ in range(20000):
    k = rng.randint(1, 400); w = [rng.randint(1, 60) for _ in range(3)]
    w = [x + ((x - k) % 2) for x in w]; W = sum(w); f = ((k - W) % 4) // 2
    t = rng.choice(BRIEF_TRIPLES); Ts = rng.choice(BRIEF_FIX)
    e = [0] * 7
    for i in range(3):
        for l in t[i]: e[l] += w[i]
    if f:
        for l in Ts: e[l] += 2
    m = m_vector(k, e)
    assert m is not None
    assert all(4 * x >= k - 3 * W - 6 * f for x in m)
    assert sum(m) * 4 == 7 * k - 3 * W - 6 * f
    assert all((sum(m[p] for p in pts if p not in LSET[l]) + e[l]) == k for l in range(7))
    assert sum((m[p] & 1) << p for p in pts) in HAM
print('all claims verified')
# (F7) explicit size formulas for the notes' triangles (notes labelling 1..7 = 0..6 here), f = 0,
# and the bound 4 m_p >= k - W - 2*Delta - 6f with the fixer triangle T* = TSTAR
from proof_mode import T_NOTES, TSTAR
names = lambda J: sorted(''.join(str(p + 1) for p in LSET[l]) for l in J)
print('T_1,T_2,T_3 =', [names(T) for T in T_NOTES], ' T* =', names(TSTAR), ' colour of T* =', colour_of(TSTAR) + 1)
for _ in range(20000):
    k = rng.randint(1, 400); w = [rng.randint(1, 60) for _ in range(3)]
    w = [x + ((x - k) % 2) for x in w]; W = sum(w); f = ((k - W) % 4) // 2; D = max(w) - min(w)
    e = [0] * 7
    for i in range(3):
        for l in T_NOTES[i]: e[l] += w[i]
    m0 = m_vector(k, e) if f == 0 else None
    if m0:
        w1, w2, w3 = w
        assert [4 * x for x in m0] == [k - W + 2*w1 + 2*w2, k - W + 2*w1 + 2*w3, k - W - 2*w1 + 2*w2,
                                       k - W + 2*w2 + 2*w3, k - W - 2*w2 + 2*w3, k - W - 2*w3 + 2*w1, k - W]
    if f:
        for l in TSTAR: e[l] += 2
    m = m_vector(k, e)
    assert all(4 * x >= k - W - 2 * D - 6 * f for x in m)
print('explicit formulas and Delta-bound verified')
