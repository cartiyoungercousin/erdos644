r"""The triangle construction (hand proof of the adjustment step, notes/PROGRAMME2_TASK3.md section 3),
implemented literally so that every step is exercised on concrete instances.

Input: coset family (C even, i.e. evenised), k, pairwise disjoint Omega_1..3 in a + C.
Output: seven sets B_l (indexed by Fano lines) or a reason the hypotheses (H1)-(H4) fail.
"""
import itertools
from core import LSET, PENCIL, ANTI, PATTERNS, popc

TRIANGLES = [J for J in PATTERNS if len(J) == 3]
def colour_of(J):
    """the point p with J inside ANTI[p] (unique for |J| >= 3)"""
    return next(p for p in range(7) if J <= ANTI[p])
# triples of triangles covering every line an odd number of times
ODD_TRIPLES = [t for t in itertools.product(TRIANGLES, repeat=3)
               if all(sum(l in J for J in t) % 2 == 1 for l in range(7))]
# the brief's form: T_i = ANTI(q_i) minus l_i, (l_1,l_2,l_3) the pencil at p0, q_i not on l_i
from core import P0
PEN0 = PENCIL[P0]
BRIEF_TRIPLES = [t for t in ODD_TRIPLES
                 if all(PEN0[i] not in t[i] and len(ANTI[colour_of(t[i])] - t[i]) == 1
                        and next(iter(ANTI[colour_of(t[i])] - t[i])) == PEN0[i] for i in range(3))]
# fixer pattern ANTI(q*) minus a line m* not through p0
BRIEF_FIX = [J for J in TRIANGLES if P0 not in LSET[next(iter(ANTI[colour_of(J)] - J))]]
HAMMING_LINES = [sum(1 << p for p in l) for l in LSET]


def m_vector(k, e):
    t = [k - e[l] for l in range(7)]
    S = sum(t)
    if S % 4: return None
    m = []
    for p in range(7):
        q = sum(t[l] for l in PENCIL[p])
        if q % 2: return None
        m.append(S // 4 - q // 2)
    return m

def hamming_words():
    W = set([0])
    for l in HAMMING_LINES:
        W |= {w ^ l for w in W}
    return sorted(W)
HAM = hamming_words(); assert len(HAM) == 16

def construct(cs, k, Omegas, brief=False):
    n = cs.n
    assert cs.is_even(), 'evenise first'
    w = [popc(O) for O in Omegas]
    for O in Omegas: assert cs.syn(O) == cs.alpha
    assert all(not (Omegas[i] & Omegas[j]) for i in range(3) for j in range(i + 1, 3))
    W = sum(w)
    s = 4 * n - 7 * k - W
    if s < 0: return None, 'H0 fails: W > 4n-7k'
    if any((wi - k) % 2 for wi in w): return None, 'H1 fails: some w_i != k mod 2'
    f = ((k - W) % 4) // 2           # 0 or 1 (W = k mod 2 by H1, and s = k - W mod 4)
    assert (s - 2 * f) % 4 == 0
    u = (s - 2 * f) // 4
    Vp = ((1 << n) - 1) & ~(Omegas[0] | Omegas[1] | Omegas[2])
    cells = cs.cells(Vp)                                  # class -> list of points of V'
    # --- choose fixer pair + u unused points (H3/H4): take them from the largest cells, never leaving a
    # singleton cell; a cell keeping >= 7 points becomes the 'last' cell L.
    cells = {g: list(v) for g, v in cells.items()}
    fixer = []
    if f:
        cand = [g for g in cells if len(cells[g]) >= 2]
        if not cand: return None, 'H3 fails: no two points of V\' in one class'
        g = max(cand, key=lambda g: len(cells[g]))
        fixer = [cells[g].pop(), cells[g].pop()]
    unused = []
    for _ in range(u):
        single = [g for g in cells if len(cells[g]) == 1]
        g = single[0] if single else max(cells, key=lambda g: len(cells[g]))
        if not cells[g]: return None, 'not enough points'
        unused.append(cells[g].pop())
    # repair singletons created/existing: move a singleton point into 'unused' is not allowed (u fixed);
    # instead report.
    if any(len(v) == 1 for v in cells.values()):
        return None, 'H4 fails: a class occurs exactly once in V\'\''
    L = max(cells, key=lambda g: len(cells[g]))
    strictH4 = len(cells[L]) >= 7
    best = None
    for tri in (BRIEF_TRIPLES if brief else ODD_TRIPLES):
        for perm in itertools.permutations(range(3)):
            for Ts in ((BRIEF_FIX if brief else TRIANGLES) if f else [frozenset()]):
                e = [0] * 7
                for i in range(3):
                    for l in tri[perm[i]]: e[l] += w[i]
                for l in Ts: e[l] += 2 * f
                m = m_vector(k, e)
                if m is None: continue
                sc = min(m)
                if best is None or sc > best[0]: best = (sc, tri, perm, Ts, m)
    if best is None: return None, 'integrality fails (should not happen)'
    sc, tri, perm, Ts, m = best
    if sc < 0: return None, f'H2 fails: min m_p = {sc} < 0'
    # --- parity vectors pi_g in the Hamming code: wt(pi_g) <= |cell|, wt = |cell| mod 2,
    # sum_g pi_g = (m_p mod 2)_p, and load_p = #{g: p in pi_g} <= m_p.   (hand proof: pi_g = a line for odd
    # cells, 0 for even cells, the last cell takes the remainder; here a small search over the same space)
    mpar = sum((m[p] & 1) << p for p in range(7))
    gl = list(cells)
    opts = {g: [h for h in HAM if popc(h) <= len(cells[g]) and (popc(h) - len(cells[g])) % 2 == 0] for g in gl}
    sol = [None]
    def dfs(i, acc, load, chosen):
        if sol[0] is not None: return
        if i == len(gl):
            if acc == mpar: sol[0] = dict(chosen)
            return
        g = gl[i]
        for h in opts[g]:
            nl = [load[p] + (h >> p & 1) for p in range(7)]
            if any(nl[p] > m[p] for p in range(7)): continue
            if i == len(gl) - 1 and acc ^ h != mpar: continue
            chosen[g] = h; dfs(i + 1, acc ^ h, nl, chosen); del chosen[g]
    dfs(0, 0, [0] * 7, {})
    if sol[0] is None: return None, 'H4 fails: no admissible cell parity vectors'
    pi = sol[0]
    # --- transportation: n_{p,g} = pi + 2 nu
    Mp = []
    for p in range(7):
        x = m[p] - sum(pi[g] >> p & 1 for g in cells)
        if x < 0 or x % 2: return None, f'H2 fails at p={p}: m_p too small for the cell parities'
        Mp.append(x // 2)
    Kg = {g: (len(cells[g]) - popc(pi[g])) // 2 for g in cells}
    assert sum(Mp) == sum(Kg.values()), (sum(Mp), sum(Kg.values()))
    Y = [0] * 7
    pools = {g: list(cells[g]) for g in cells}
    for g in cells:
        for p in range(7):
            if pi[g] >> p & 1: Y[p] |= 1 << pools[g].pop()
    gs = list(cells); gi = 0
    for p in range(7):
        need = Mp[p]
        while need:
            while Kg[gs[gi]] == 0: gi += 1
            take = min(need, Kg[gs[gi]])
            for _ in range(2 * take): Y[p] |= 1 << pools[gs[gi]].pop()
            Kg[gs[gi]] -= take; need -= take
    assert all(not v for v in pools.values())
    # --- assemble
    B = [0] * 7
    for l in range(7):
        for p in range(7):
            if p not in LSET[l]: B[l] |= Y[p]
    for i in range(3):
        for l in tri[perm[i]]: B[l] |= Omegas[i]
    if f:
        F = (1 << fixer[0]) | (1 << fixer[1])
        for l in Ts: B[l] |= F
    info = dict(W=W, s=s, f=f, u=u, m=m, tri=[sorted(tri[perm[i]]) for i in range(3)], Tstar=sorted(Ts),
                cells={g: len(v) for g, v in cells.items()}, strictH4=strictH4)
    return B, info
