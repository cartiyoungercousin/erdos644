"""Quadratic level-set families for PROGRAMME5_QUAD (n <= 26).

A quadratic form is (G, l): G = list of adjacency bitmasks (symmetric, no loops), l = bitmask of linear terms.
q(S) = #edges of G inside S + |S & l|  (mod 2).  Level set L = {S : |S| = k, q(S) = a}.

Tools
- qtable(n, G, l): q on all 2^n subsets (uint8).
- tau_levelset(n, k, qv, a): exact tau via the up-closure of L on the 2^n cube (no solver).
- fano_sat(...):  is there a Fano-type seven in L?  Colouring encoding (3 colour bits per point, B_u <= R_u).
- seven_sat(...): is there ANY good seven in L (7 k-sets, q = a, no 2-point transversal)?  Set encoding.
  The two encodings share nothing but the clause helpers; a found seven is re-checked by check_seven (plain code).
"""
import numpy as np
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

PAR8 = np.array([bin(i).count('1') & 1 for i in range(256)], dtype=np.uint8)
POP8 = np.array([bin(i).count('1') for i in range(256)], dtype=np.uint8)


def parity_arr(a):
    a = a.astype(np.uint32)
    p = PAR8[a & 255] ^ PAR8[(a >> 8) & 255] ^ PAR8[(a >> 16) & 255] ^ PAR8[(a >> 24) & 255]
    return p


def popcount_arr(n):
    a = np.arange(1 << n, dtype=np.uint32)
    return (POP8[a & 255] + POP8[(a >> 8) & 255] + POP8[(a >> 16) & 255] + POP8[(a >> 24) & 255]).astype(np.uint8)


def qtable(n, G, l):
    qv = np.zeros(1 << n, dtype=np.uint8)
    for i in range(n):
        lo = np.arange(1 << i, dtype=np.uint32)
        Ni = G[i] & ((1 << i) - 1)
        qv[(1 << i):(1 << (i + 1))] = qv[:1 << i] ^ ((l >> i) & 1) ^ parity_arr(lo & Ni)
    return qv


def q_eval(S, G, l):
    v = bin(S & l).count('1')
    x = S
    while x:
        i = (x & -x).bit_length() - 1
        x &= x - 1
        v += bin(G[i] & x).count('1')
    return v & 1


def upclose(A, n):
    A = A.copy()
    for i in range(n):
        B = A.reshape(-1, 2, 1 << i)
        B[:, 1, :] |= B[:, 0, :]
    return A


def tau_levelset(n, k, qv, a, pc=None):
    if pc is None:
        pc = popcount_arr(n)
    mem = (pc == k) & (qv == a)
    if not mem.any():
        return 0, 0
    U = upclose(mem, n)
    notU = ~U
    smax = int(pc[notU].max()) if notU.any() else -1  # largest set containing no member
    return n - smax, int(mem.sum())


def check_seven(seven, n):
    for x in range(n):
        for y in range(x, n):
            t = (1 << x) | (1 << y)
            if all(B & t for B in seven):
                return False
    return True


class _CNF:
    def __init__(self):
        self.nv = 0
        self.cl = []

    def new(self):
        self.nv += 1
        return self.nv

    def xor_eq(self, lits, val):
        """XOR of lits == val (lits may be empty)."""
        if not lits:
            if val:
                self.cl.append([])
            return
        cur = lits[0]
        for x in lits[1:]:
            t = self.new()
            self.cl += [[-t, cur, x], [-t, -cur, -x], [t, -cur, x], [t, cur, -x]]
            cur = t
        self.cl.append([cur] if val else [-cur])

    def and2(self, a, b):
        t = self.new()
        self.cl += [[-t, a], [-t, b], [t, -a, -b]]
        return t

    def card_eq(self, lits, k):
        enc = CardEnc.equals(lits=lits, bound=k, top_id=self.nv, encoding=EncType.seqcounter)
        self.nv = max(self.nv, enc.nv)
        self.cl += enc.clauses


def _q_lits(C, m, n, G, l):
    """Literals whose XOR is q(B) for B given by membership vars m[0..n-1]."""
    lits = [m[i] for i in range(n) if l >> i & 1]
    for i in range(n):
        for j in range(i + 1, n):
            if G[i] >> j & 1:
                lits.append(C.and2(m[i], m[j]))
    return lits


def _solve(C, budget, extract):
    S = Cadical153(bootstrap_with=C.cl)
    if budget:
        S.conf_budget(budget)
        r = S.solve_limited()
    else:
        r = S.solve()
    if r is True:
        mod = set(v for v in S.get_model() if v > 0)
        S.delete()
        return 'SEVEN', extract(mod)
    S.delete()
    return ('NONE', None) if r is False else ('UNKNOWN', None)


U7 = [1, 2, 3, 4, 5, 6, 7]  # nonzero u in F_2^3; R_u = {x : <chi(x),u> = 1}


def fano_sat(n, k, G, l, a, budget=0, extra=None):
    """Fano-type seven: chi: V -> F_2^3 (0 allowed), B_u subset R_u, |B_u| = k, q(B_u) = a.
    extra(C, m) may add constraints on each B_u (membership var list m), e.g. a coset condition."""
    C = _CNF()
    b = [[C.new() for _ in range(3)] for _ in range(n)]
    ms = []
    for u in U7:
        bits = [t for t in range(3) if u >> t & 1]
        m = [C.new() for _ in range(n)]
        for x in range(n):
            r = C.new()  # r = XOR of colour bits selected by u
            C.xor_eq([b[x][t] for t in bits] + [r], 0)
            C.cl.append([-m[x], r])
        C.card_eq(m, k)
        C.xor_eq(_q_lits(C, m, n, G, l), a)
        if extra:
            extra(C, m)
        ms.append(m)

    def ext(mod):
        return [sum(1 << x for x in range(n) if m[x] in mod) for m in ms]
    return _solve(C, budget, ext)


def seven_sat(n, k, G, l, a, budget=0, extra=None):
    """Any good seven: 7 k-sets with q = a whose complements cover all pairs (x = y allowed)."""
    C = _CNF()
    ms = []
    for i in range(7):
        m = [C.new() for _ in range(n)]
        C.card_eq(m, k)
        C.xor_eq(_q_lits(C, m, n, G, l), a)
        if extra:
            extra(C, m)
        ms.append(m)
    for x in range(n):
        for y in range(x, n):
            ps = []
            for i in range(7):
                p = C.new()
                ps.append(p)
                C.cl.append([-p, -ms[i][x]])
                if y != x:
                    C.cl.append([-p, -ms[i][y]])
            C.cl.append(ps)
    # symmetry breaking: point 0 avoided by B_0 (some member avoids 0 in any seven)
    C.cl.append([-ms[0][0]])

    def ext(mod):
        return [sum(1 << x for x in range(n) if m[x] in mod) for m in ms]
    return _solve(C, budget, ext)


# ---------------- builders ----------------

def from_edges(n, edges):
    G = [0] * n
    for i, j in edges:
        G[i] |= 1 << j
        G[j] |= 1 << i
    return G


def circulant(n, D):
    return from_edges(n, [(i, (i + d) % n) for i in range(n) for d in D if (i + d) % n != i and d <= n // 2
                          and not (2 * d == n and i >= n // 2)])


def random_graph(n, p, rng):
    return from_edges(n, [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p])


# ---------------- exact Fano check by deviation vectors ----------------
# A Fano colouring is determined up to point assignment by d_u = |R_u| - k >= 0 (u = 1..7):
# with D = sum d_u, n_0 = (4n - 7k - D)/4 and n_p = (k - D + 2 d(p))/4, d(p) = sum_{u: p.u = 1} d_u.
# Lines with d_u >= r_L (L is (k + r_L)-covering) contain a member automatically; only the others need SAT.

def _dot(p, u):
    return bin(p & u).count('1') & 1


def gl32_perms():
    import itertools
    perms = set()
    for cols in itertools.product(range(1, 8), repeat=3):
        img = []
        for u in range(1, 8):
            v = 0
            for t in range(3):
                if u >> t & 1:
                    v ^= cols[t]
            img.append(v)
        if 0 not in img and len(set(img)) == 7:
            perms.add(tuple(x - 1 for x in img))
    return sorted(perms)


_PERMS = None


def dvectors(n, k):
    """Canonical (under GL(3,2)) deviation vectors with their class sizes."""
    global _PERMS
    if _PERMS is None:
        _PERMS = gl32_perms()
    c = 4 * n - 7 * k
    out = []

    def comps(D, parts):
        if parts == 1:
            yield (D,)
            return
        for x in range(D + 1):
            for rest in comps(D - x, parts - 1):
                yield (x,) + rest
    D = c
    while D >= 0:
        for d in comps(D, 7):
            canon = min(tuple(d[pm[i]] for i in range(7)) for pm in _PERMS)
            if canon != d:
                continue
            sizes = {}
            ok = True
            for p in range(1, 8):
                dp = sum(d[u - 1] for u in range(1, 8) if _dot(p, u))
                num = k - D + 2 * dp
                if num < 0 or num % 4:
                    ok = False
                    break
                sizes[p] = num // 4
            if ok:
                sizes[0] = (c - D) // 4
                out.append((d, sizes))
        D -= 4
    return out


def fano_exact(n, k, G, l, a, qv, rL, budget=0, extra=None, want_witness=True, tries=3000):
    """Exact Fano-seven decision for L = {|B| = k, q(B) = a}, L (k + rL)-covering.
    Returns ('SEVEN', members) / ('NONE', None) / ('UNKNOWN', None), and #dvectors / #SAT calls."""
    from itertools import combinations
    stats = [0, 0]
    for d, sz in dvectors(n, k):
        stats[0] += 1
        tight = [u for u in range(1, 8) if d[u - 1] < rL]
        hit = _random_colourings(n, k, a, qv, d, sz, tight, tries) if tries else None
        if hit is not None:
            stats[1] += 0
            return 'SEVEN', hit, stats
        C = _CNF()
        cv = [[C.new() for _ in range(8)] for _ in range(n)]
        for x in range(n):
            C.card_eq(cv[x], 1)
        for p in range(8):
            C.card_eq([cv[x][p] for x in range(n)], sz[p])
        ms = {}
        for u in tight:
            m = [C.new() for _ in range(n)]
            for x in range(n):
                C.cl.append([-m[x]] + [cv[x][p] for p in range(1, 8) if _dot(p, u)])
            C.card_eq(m, k)
            C.xor_eq(_q_lits(C, m, n, G, l), a)
            if extra:
                extra(C, m)
            ms[u] = m
        stats[1] += 1
        S = Cadical153(bootstrap_with=C.cl)
        if budget:
            S.conf_budget(budget)
            r = S.solve_limited()
        else:
            r = S.solve()
        if r is None:
            S.delete()
            stats.append(d)  # undecided deviation vector; keep trying the others
            continue
        if r is False:
            S.delete()
            continue
        mod = set(v for v in S.get_model() if v > 0)
        S.delete()
        col = [next(p for p in range(8) if cv[x][p] in mod) for x in range(n)]
        seven = []
        for u in range(1, 8):
            R = [x for x in range(n) if _dot(col[x], u)]
            if u in ms:
                seven.append(sum(1 << x for x in range(n) if ms[u][x] in mod))
                continue
            found = None
            for drop in combinations(R, len(R) - k):
                B = sum(1 << x for x in R) - sum(1 << x for x in drop)
                if qv[B] == a and (extra is None or True):
                    found = B
                    break
            assert found is not None, 'covering claim failed'
            seven.append(found)
        return 'SEVEN', seven, stats
    return ('UNKNOWN' if len(stats) > 2 else 'NONE'), None, stats


def _random_colourings(n, k, a, qv, d, sz, tight, tries, seed=0):
    """Heuristic pre-pass: random point assignments with the class sizes of d; a line is good if some k-subset
    has q = a (lines with d_u >= r_L are good by covering, but are searched too, to output a witness)."""
    from itertools import combinations
    import random
    rng = random.Random(seed)
    labels = [p for p in range(8) for _ in range(sz[p])]
    for _ in range(tries):
        rng.shuffle(labels)
        seven = []
        for u in range(1, 8):
            R = [x for x in range(n) if bin(labels[x] & u).count('1') & 1]
            full = sum(1 << x for x in R)
            found = None
            for drop in combinations(R, len(R) - k):
                B = full - sum(1 << x for x in drop)
                if qv[B] == a:
                    found = B
                    break
            if found is None:
                break
            seven.append(found)
        if len(seven) == 7:
            return seven
    return None
