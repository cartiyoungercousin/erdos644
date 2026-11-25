r"""PROGRAMME_2 Task 3: the adjustment step of Proposition 9.

Coset family H = (a + C) cap (V choose k), C given by a parity-check matrix (rows = int bitmasks
over V = {0..n-1}); S in a + C  iff  syn(S) = syn(a) = alpha.  The class of a point x in
Q = F2^V / C is its syndrome column; points of equal class form the CELLS.  Membership in a + C
depends only on the parities |S cap cell|, so everything below works with cells.

Fano plane: points 0..6 (= 1..7 in the notes), lines L below.  p0 = point 6 (= 7).
"""
import itertools, random

LINES = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1), (6, 0, 2)]
# notes labelling: {1,2,4},{2,3,5},{3,4,6},{4,5,7},{5,6,1},{6,7,2},{7,1,3}
LSET = [frozenset(l) for l in LINES]
P0 = 6
PENCIL = {p: [i for i, l in enumerate(LSET) if p in l] for p in range(7)}
ANTI = {p: frozenset(i for i, l in enumerate(LSET) if p not in l) for p in range(7)}   # 4 lines missing p
LIDX = {l: i for i, l in enumerate(LSET)}
def line_of(*pts): return LIDX[next(l for l in LSET if set(pts) <= l)]

# admissible patterns J (sets of line indices) = subsets of some anti-pencil
PATTERNS = sorted({frozenset(s) for p in range(7) for r in range(5) for s in itertools.combinations(sorted(ANTI[p]), r)},
                  key=lambda s: (len(s), sorted(s)))
assert len(PATTERNS) == 64

def popc(x): return bin(x).count('1')

class Coset:
    def __init__(self, n, Hrows, alpha, name=''):
        self.n, self.H, self.alpha, self.name = n, list(Hrows), alpha, name
        self.r = len(self.H)
    def syn(self, S):
        return sum(((popc(S & h) & 1) << i) for i, h in enumerate(self.H))
    def cls(self, x): return self.syn(1 << x)
    def member(self, S, k): return popc(S) == k and self.syn(S) == self.alpha
    def cells(self, within=None):
        within = (1 << self.n) - 1 if within is None else within
        d = {}
        for x in range(self.n):
            if within >> x & 1: d.setdefault(self.cls(x), []).append(x)
        return d
    def is_even(self):
        # C even  <=>  all-ones in rowspace(H)
        return in_span((1 << self.n) - 1, self.H)

def in_span(v, rows):
    basis = []
    for r in rows:
        for b in basis: r = min(r, r ^ b)
        if r: basis.append(r)
    for b in basis: v = min(v, v ^ b)
    return v == 0

def rank(rows):
    basis = []
    for r in rows:
        for b in basis: r = min(r, r ^ b)
        if r: basis.append(r)
    return len(basis)

def evenise(cs, k):
    """WLOG reduction: H = (a+C) cap (V choose k) = (a'+C0) cap (V choose k), C0 = C cap Even, wt(a') = k mod 2."""
    full = (1 << cs.n) - 1
    if cs.is_even(): return cs
    return Coset(cs.n, cs.H + [full], cs.alpha | ((k & 1) << cs.r), cs.name + ' [evenised]')

def verify_seven(cs, k, B, require_fano=True):
    """EXACT check: seven distinct members of H with no transversal of size <= 2; optionally Fano-type
    w.r.t. the line labelling (every pencil triple has empty common intersection)."""
    assert len(B) == 7
    for S in B:
        if not cs.member(S, k): return False, 'not in H'
    if len(set(B)) < 7: return False, 'not distinct'
    n = cs.n
    for x in range(n):
        for y in range(x, n):
            T = (1 << x) | (1 << y)
            if all(S & T for S in B): return False, f'transversal {{{x},{y}}}'
    if require_fano:
        for p in range(7):
            i, j, l = PENCIL[p]
            if B[i] & B[j] & B[l]: return False, f'pencil {p} meets'
    return True, 'ok'
