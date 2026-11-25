"""Exhaustive Fano check for the 'empty common intersection' relaxation (brief section 3; notes section 9.6).
Labelling as in Task 3: lines 124,235,346,457,156,267,137; p0 = 7; l1 = 457, l2 = 267, l3 = 137;
T_i = ANTI(q_i) - {l_i} with q = (3, 5, 6).  A point of Omega_i cap Omega_j gets colour q on l_m - {7} (m the third
index) and pattern P = ANTI(q) - {l_i, l_j}.  Checks: |P| = 2; P is admissible; P misses l_i and l_j;
T_i + T_j + P lies in the simplex code S = span of the anti-pencils (= kernel of the pencil-parity map), i.e. the
pencil sums are unchanged as vectors; and which element of S it is."""
import itertools
LINES = [frozenset(map(int, s)) for s in ('124', '235', '346', '457', '156', '267', '137')]
def anti(p): return frozenset(i for i, l in enumerate(LINES) if p not in l)
def pencil(p): return frozenset(i for i, l in enumerate(LINES) if p in l)
ell = {1: LINES.index(frozenset({4, 5, 7})), 2: LINES.index(frozenset({2, 6, 7})), 3: LINES.index(frozenset({1, 3, 7}))}
q = {1: 3, 2: 5, 3: 6}
T = {i: anti(q[i]) - {ell[i]} for i in (1, 2, 3)}
assert T[1] == {0, 4, 5} and T[2] == {0, 6, 2} and T[3] == {0, 1, 3}
S = set()
for mask in range(8):
    v = frozenset()
    for b, p in zip(range(3), (1, 2, 4)):
        if mask >> b & 1: v = v ^ anti(p)
    S.add(v)
S = set()
gens = [anti(p) for p in range(1, 8)]
for r in range(8):
    for c in itertools.combinations(gens, r):
        v = frozenset()
        for g in c: v = v ^ g
        S.add(v)
assert len(S) == 8
def parity_vec(J): return tuple(len(J & pencil(p)) % 2 for p in range(1, 8))
assert all(parity_vec(v) == (0,) * 7 for v in S)
ok = True
for i, j in ((1, 2), (1, 3), (2, 3)):
    m = 6 - i - j
    for qq in sorted(LINES[ell[m]] - {7}):
        P = anti(qq) - {ell[i], ell[j]}
        res = T[i] ^ T[j] ^ P
        which = [p for p in range(1, 8) if anti(p) == res]
        good = len(P) == 2 and ell[i] not in P and ell[j] not in P and res in S
        ok &= good
        print(f'Omega_{i} cap Omega_{j}: colour {qq}, P = {sorted("".join(map(str, sorted(LINES[t]))) for t in P)}, '
              f'T_i+T_j+P = {"ANTI(%d)" % which[0] if which else sorted(res)}, in S: {res in S}')
print('all checks pass:', ok)
