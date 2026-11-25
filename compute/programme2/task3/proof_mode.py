r"""Theorem 9' exactly as proved in notes/PROGRAMME2_TASK3.md section 3 (no search anywhere):
fixed triangles T_1, T_2, T_3 of the notes (the brief's form, p0 = point 7), Omega_i on T_i in the given
order, fixer on the fixed triangle T* = ANTI(q*) - m*, unused points = singleton classes first, then the
largest class g*, parity vectors: a line for each odd class (cycling through the 7 lines), 0 for even
classes, the remainder for g*.  check_theorem() tests: hypotheses (H0)-(H4') => construction succeeds
and the seven sets pass the exact verifier."""
import itertools, random
from core import LSET, popc, verify_seven, Coset, evenise
from construct import BRIEF_TRIPLES, BRIEF_FIX, HAM, HAMMING_LINES, m_vector

T_NOTES = [frozenset({0, 4, 5}), frozenset({0, 2, 6}), frozenset({0, 1, 3})]   # T_1, T_2, T_3 of the notes
assert tuple(T_NOTES) in BRIEF_TRIPLES
TSTAR = BRIEF_FIX[0]

def hypotheses(cs, k, Omegas):
    n = cs.n; w = [popc(O) for O in Omegas]; W = sum(w)
    s = 4 * n - 7 * k - W
    H0 = s >= 0
    H1 = all((x - k) % 2 == 0 for x in w)
    if not (H0 and H1): return dict(H0=H0, H1=H1, all=False)
    f = ((k - W) % 4) // 2; u = (s - 2 * f) // 4
    Vp = ((1 << n) - 1) & ~(Omegas[0] | Omegas[1] | Omegas[2])
    cells = cs.cells(Vp); c = len(cells)
    D = max(w) - min(w)
    H2 = k >= W + 2 * D + 4 * c + 6
    H3 = max((len(v) for v in cells.values()), default=0) >= u + 2 * f + 7
    H4 = sum(1 for v in cells.values() if len(v) == 1) <= u
    return dict(H0=H0, H1=H1, H2=H2, H3=H3, H4=H4, all=H0 and H1 and H2 and H3 and H4, f=f, u=u, c=c)

def construct_proof(cs, k, Omegas):
    n = cs.n; w = [popc(O) for O in Omegas]; W = sum(w)
    s = 4 * n - 7 * k - W; f = ((k - W) % 4) // 2; u = (s - 2 * f) // 4
    Vp = ((1 << n) - 1) & ~(Omegas[0] | Omegas[1] | Omegas[2])
    cells = {g: list(v) for g, v in cs.cells(Vp).items()}
    gstar = max(cells, key=lambda g: len(cells[g]))
    unused = [cells[g].pop() for g in list(cells) if len(cells[g]) == 1]
    fixer = [cells[gstar].pop(), cells[gstar].pop()] if f else []
    while len(unused) < u: unused.append(cells[gstar].pop())
    assert len(unused) == u
    e = [0] * 7
    for i in range(3):
        for l in T_NOTES[i]: e[l] += w[i]
    if f:
        for l in TSTAR: e[l] += 2
    m = m_vector(k, e); assert m is not None, 'integrality (Lemma)'
    if min(m) < 0: return None, 'm<0'
    pi = {}; cyc = itertools.cycle(HAMMING_LINES)
    for g, v in cells.items():
        if g != gstar: pi[g] = next(cyc) if len(v) % 2 else 0
    acc = sum((m[p] & 1) << p for p in range(7))
    for g in pi: acc ^= pi[g]
    pi[gstar] = acc
    assert acc in HAM and popc(acc) <= len(cells[gstar]) and (popc(acc) - len(cells[gstar])) % 2 == 0
    Y = [0] * 7; need = list(m)
    for g in cells:
        for p in range(7):
            if pi[g] >> p & 1: Y[p] |= 1 << cells[g].pop(); need[p] -= 1
    assert min(need) >= 0 and all(x % 2 == 0 for x in need), ('loads', need)
    pairs = [(cells[g][i], cells[g][i + 1]) for g in cells for i in range(0, len(cells[g]), 2)]
    assert all(len(cells[g]) % 2 == 0 for g in cells) and 2 * len(pairs) == sum(need)
    it = iter(pairs)
    for p in range(7):
        for _ in range(need[p] // 2):
            x, y = next(it); Y[p] |= (1 << x) | (1 << y)
    B = [0] * 7
    for l in range(7):
        for p in range(7):
            if p not in LSET[l]: B[l] |= Y[p]
        for i in range(3):
            if l in T_NOTES[i]: B[l] |= Omegas[i]
        if f and l in TSTAR: B[l] |= (1 << fixer[0]) | (1 << fixer[1])
    return B, dict(m=m, f=f, u=u)
