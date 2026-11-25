r"""Piece B, Theorem B1 (notes/PROGRAMME2_B.md section 3): the Venn / sequential-Lemma-C construction of a
Fano-type good seven in a coset family with ARBITRARILY MANY point classes.

Pipeline (no search except where the proof uses an existence statement, which is then constructed):
  Omegas (given)  ->  V' = V - union Omegas
  matroid partition of V' into 4 independent sets (columns = evenised syndrome columns)  ->  A*, 4 bases, X = V' - A*
  X: greedy circuits of the quotient columns (mod span A*) -> monochromatic blocks; remainder X0 (dumped into Z)
  fixer F (codeword, |F| = s mod 4) by Lemma C inside A* minus three bases
  Z = X0 + filler, |Z| = u = (s - |F|)/4
  region sizes m_p (Theorem 9' formulas, fixer of size |F| on T*)
  labels v: V'' -> F2^3 - 0 by three sequential Lemma-C steps (coordinate i of v = 1  <=>  point in D_{l_i})
  B_l = union_{p not on l} Y_p  +  Omegas on T_i  +  F if l in T*
Every output is checked by an independent exact verifier (check_seven) and by task3's core.verify_seven.
"""
import os, sys, random
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'task3'))
from core import LSET, PENCIL, popc, verify_seven, Coset, evenise
from construct import m_vector

T_NOTES = [frozenset({0, 4, 5}), frozenset({0, 2, 6}), frozenset({0, 1, 3})]   # T_1, T_2, T_3 (colours 3, 5, 6)
TSTAR = frozenset({0, 1, 2})                                                   # ANTI(7) - {156}

# ---------- Fano labelling by F2^3 - 0 ----------
def _fano_labels():
    import itertools
    for perm in itertools.permutations(range(1, 8)):
        if all(perm[a] ^ perm[b] ^ perm[c] == 0 for a, b, c in (tuple(l) for l in LSET)):
            return list(perm)
LAB = _fano_labels()
assert LAB is not None
INV = {v: p for p, v in enumerate(LAB)}
# coordinate i of the label is the functional whose kernel is a line l_i; D_{l_i} = {x : bit i of v(x) = 1}
for i in range(3):
    ker = frozenset(p for p in range(7) if not (LAB[p] >> i & 1))
    assert ker in LSET

# ---------- GF(2) helpers (vectors are ints) ----------
class Span:
    """echelon basis with coefficient tracking: each basis vector remembers which input labels it is the sum of"""
    def __init__(self):
        self.rows = []   # (pivot, vec, mask over labels)
    def reduce(self, v, mask=0):
        for piv, b, bm in self.rows:
            if v >> piv & 1: v ^= b; mask ^= bm
        return v, mask
    def add(self, v, label_bit):
        v, mask = self.reduce(v, label_bit)
        if v == 0: return False
        piv = v.bit_length() - 1
        # keep fully reduced on pivot
        newrows = []
        for p2, b, bm in self.rows:
            if b >> piv & 1: b ^= v; bm ^= mask
            newrows.append((p2, b, bm))
        self.rows = newrows + [(piv, v, mask)]
        return True
    def solve(self, v):
        """mask of labels summing to v, or None"""
        r, mask = self.reduce(v)
        return mask if r == 0 else None
    def __len__(self): return len(self.rows)

def rank(vecs):
    S = Span()
    for i, v in enumerate(vecs): S.add(v, 0)
    return len(S)

def represent(vecs, v):
    """indices of vecs (assumed independent) summing to v, or None if v not in span"""
    S = Span()
    for i, w in enumerate(vecs): S.add(w, 1 << i)
    m = S.solve(v)
    if m is None: return None
    return [i for i in range(len(vecs)) if m >> i & 1]

# ---------- Lemma B (rainbow matching) and Lemma C ----------
def rainbow(U, col):
    """disjoint pairs inside U whose differences are a basis of E_U = span{h_x+h_y}; follows the proof of
    Lemma B (Task 2) literally, so it succeeds whenever |U| >= 2 e_U + 1; otherwise returns a maximal family."""
    U = list(U)
    pairs = []
    while True:
        F = Span()
        for t, (i, j) in enumerate(pairs): F.add(col[i] ^ col[j], 1 << t)
        used = {x for p in pairs for x in p}
        un = [x for x in U if x not in used]
        groups = {}
        for x in un: groups.setdefault(F.reduce(col[x])[0], []).append(x)
        if len(groups) >= 2:
            g1, g2 = list(groups.values())[:2]
            pairs.append((g1[0], g2[0])); continue
        if len(un) < 3: return pairs
        c = next(iter(groups)) if groups else None
        # a matched pair outside the coset c + F ?
        bad = [t for t, (i, j) in enumerate(pairs) if F.reduce(col[i])[0] != c]
        if not bad: return pairs           # E_U = F : done
        t0 = bad[0]; i, j = pairs[t0]
        others = Span()
        for t, (a, b) in enumerate(pairs):
            if t != t0: others.add(col[a] ^ col[b], 0)
        u3 = un[:3]
        cand = [(a, b) for a in u3 for b in u3 if a < b and others.reduce(col[a] ^ col[b])[0] == 0]
        assert cand, 'Lemma B exchange: some pair among three unmatched has epsilon = 0'
        uu, vv = cand[0]
        pairs[t0] = (i, uu); pairs.append((j, vv))

def lemma_c(U, a, target, col):
    """a-subset Q of U with sum(col over Q) = target, via Lemma B pairs and swaps. None if impossible this way."""
    U = list(U)
    pairs = rainbow(U, col)
    if not (len(pairs) <= a <= len(U) - len(pairs)): return None
    used = {x for p in pairs for x in p}
    un = [x for x in U if x not in used]
    Q = [p[0] for p in pairs] + un[:a - len(pairs)]
    sig = 0
    for x in Q: sig ^= col[x]
    S = Span()
    for t, (i, j) in enumerate(pairs): S.add(col[i] ^ col[j], 1 << t)
    m = S.solve(sig ^ target)
    if m is None: return None
    Qs = set(Q)
    for t, (i, j) in enumerate(pairs):
        if m >> t & 1: Qs.discard(i); Qs.add(j)
    assert len(Qs) == a
    s2 = 0
    for x in Qs: s2 ^= col[x]
    assert s2 == target
    return Qs

# ---------- matroid partition (4 copies of the column matroid) ----------
def partition4(elems, col, q=4):
    I = [[] for _ in range(q)]; where = {}
    def bfs(x):
        parent = {x: None}; queue = [x]; qi = 0
        while qi < len(queue):
            y = queue[qi]; qi += 1
            for j in range(q):
                if where.get(y) == j: continue
                rep = represent([col[z] for z in I[j]], col[y])
                if rep is None: return (y, j), parent
                for idx in rep:
                    z = I[j][idx]
                    if z not in parent: parent[z] = (y, j); queue.append(z)
        return None, parent
    uncovered = []
    for x in elems:
        found, parent = bfs(x)
        if found is None: uncovered.append(x); continue
        y, j = found
        moves = [(y, j)]
        z = y
        while parent[z] is not None:
            yy, jj = parent[z]; moves.append((yy, jj)); z = yy
        # z == x now. moves: (element, set it enters). Each element leaves its old set.
        for el, jj in moves:
            if el in where: I[where[el]].remove(el)
        for el, jj in moves:
            I[jj].append(el); where[el] = jj
    rk = rank([col[x] for x in elems])
    if all(len(Ij) == rk for Ij in I): return set(elems), [list(Ij) for Ij in I], rk
    reach = set()
    for x in uncovered:
        _, parent = bfs(x); reach |= set(parent)
    A = reach
    rA = rank([col[x] for x in A]) if A else 0
    bases = [[z for z in Ij if z in A] for Ij in I]
    if not all(len(b) == rA for b in bases): return None, None, None
    return A, bases, rA

# ---------- the construction ----------
def b1_construct(cs, k, Omegas, rng=None, report=None):
    rng = rng or random.Random(0)
    rep = report if report is not None else {}
    n = cs.n
    assert cs.is_even()
    w = [popc(O) for O in Omegas]; W = sum(w)
    for O in Omegas: assert cs.syn(O) == cs.alpha
    s = 4 * n - 7 * k - W
    rep.update(W=W, s=s)
    if s < 0 or any((x - k) % 2 for x in w): rep['fail'] = 'H0/H1'; return None
    allO = Omegas[0] | Omegas[1] | Omegas[2]
    col = [cs.cls(x) for x in range(n)]
    Vp = [x for x in range(n) if not (allO >> x & 1)]
    A, bases, rA = partition4(Vp, col)
    if A is None: rep['fail'] = 'partition'; return None
    X = [x for x in Vp if x not in A]
    rep.update(e=rA - 1, X=len(X), cells=len({col[x] for x in Vp}))
    # quotient blocks in X
    SA = Span()
    for x in bases[0]: SA.add(col[x], 0)
    pi = {x: SA.reduce(col[x])[0] for x in X}
    blocks, rest = [], list(X)
    while True:
        # find a circuit among the quotient columns of rest
        Sq = Span(); circ = None
        for idx, x in enumerate(rest):
            if pi[x] == 0: circ = [x]; break
            r_, m_ = Sq.reduce(pi[x], 1 << idx)
            if r_ == 0: circ = [rest[t] for t in range(len(rest)) if m_ >> t & 1]; break
            Sq.add(pi[x], 1 << idx)
        if circ is None: break
        blocks.append(circ); rest = [x for x in rest if x not in circ]
    X0 = rest
    rep.update(X0=len(X0), blocks=len(blocks), maxblock=max((len(b) for b in blocks), default=0))
    R0, RA, RB, RF = [set(b) for b in bases]
    # fixer
    F = set()
    if s % 4 == 2:
        UF = [x for x in A if x not in R0 | RA | RB]
        eF = rA - 1
        a = eF + ((2 - eF) % 4)
        Q = lemma_c(UF, a, 0, col)
        if Q is None: rep['fail'] = 'fixer'; return None
        F = set(Q)
    u = (s - len(F)) // 4
    rep.update(F=len(F), u=u)
    if len(X0) > u: rep['fail'] = f'|X0|={len(X0)} > u={u}'; return None
    filler_pool = [x for x in A if x not in R0 | RA | RB | F]
    rng.shuffle(filler_pool)
    Z = set(X0) | set(filler_pool[:u - len(X0)])
    if len(Z) != u: rep['fail'] = 'filler'; return None
    # region sizes
    e = [0] * 7
    for i in range(3):
        for l in T_NOTES[i]: e[l] += w[i]
    for l in TSTAR: e[l] += len(F)
    m = m_vector(k, e)
    if m is None: rep['fail'] = 'integrality'; return None
    rep['m_min'] = min(m)
    if min(m) < 1: rep['fail'] = 'm<1'; return None
    mv = {LAB[p]: m[p] for p in range(7)}
    Vpp = [x for x in Vp if x not in Z and x not in F]
    assert len(Vpp) == sum(m), (len(Vpp), sum(m))
    label = {}
    resid = dict(mv)
    for blk in sorted(blocks, key=len, reverse=True):
        v = max(resid, key=lambda v: resid[v])
        if resid[v] < len(blk): rep['fail'] = 'block placement'; return None
        for x in blk: label[x] = v
        resid[v] -= len(blk)
    # ---- three sequential Lemma-C steps; bits[x] accumulates the label bit by bit ----
    bits = {x: 0 for x in Vpp}
    fixed = set(label)
    # step 1 (bit 0): forced: blocks (bit known), RA, RB -> bit0 = 1; free U1
    forced1 = {x: (label[x] & 1) for x in fixed}
    for x in RA | RB: forced1[x] = 1
    N1 = sum(c for v, c in mv.items() if v & 1)
    U1 = [x for x in Vpp if x not in forced1]
    a1 = N1 - sum(forced1.values())
    tgt = 0
    for x, b in forced1.items():
        if b: tgt ^= col[x]
    Q = lemma_c(U1, a1, tgt, col)
    if Q is None: rep['fail'] = 'step1'; return None
    for x in Vpp: bits[x] = 1 if (forced1.get(x, 0) or x in Q) else 0
    # step 2 (bit 1): solving part = c1 (bit0 = 1); forced: blocks, RB -> bit1 = 1
    def count(pred): return sum(c for v, c in mv.items() if pred(v))
    out = [x for x in Vpp if bits[x] == 0 and x not in fixed]
    need_out = count(lambda v: not v & 1 and v & 2) - sum(1 for x in fixed if not label[x] & 1 and label[x] & 2)
    if not 0 <= need_out <= len(out): rep['fail'] = 'step2 counts'; return None
    rng.shuffle(out)
    chosen2 = set(out[:need_out]) | {x for x in fixed if label[x] & 2}
    inn_forced = {x for x in RB} | {x for x in fixed if label[x] & 1 and label[x] & 2}
    U2 = [x for x in Vpp if bits[x] == 1 and x not in fixed and x not in RB]
    a2 = count(lambda v: v & 1 and v & 2) - len(inn_forced)
    tgt = 0
    for x in chosen2 | set(RB): tgt ^= col[x]
    Q = lemma_c(U2, a2, tgt, col)
    if Q is None: rep['fail'] = 'step2'; return None
    for x in Vpp:
        if x in chosen2 or x in RB or x in Q: bits[x] |= 2
    # step 3 (bit 2): solving part = bits 0,1 both set
    chosen3 = {x for x in fixed if label[x] & 4}
    for pref in (0, 1, 2):
        part = [x for x in Vpp if bits[x] == pref and x not in fixed]
        need = mv.get(pref | 4, 0) - sum(1 for x in fixed if label[x] == pref | 4)
        if not 0 <= need <= len(part): rep['fail'] = 'step3 counts'; return None
        rng.shuffle(part); chosen3 |= set(part[:need])
    U3 = [x for x in Vpp if bits[x] == 3 and x not in fixed]
    a3 = mv[7] - sum(1 for x in fixed if label[x] == 7)
    tgt = 0
    for x in chosen3: tgt ^= col[x]
    Q = lemma_c(U3, a3, tgt, col)
    if Q is None: rep['fail'] = 'step3'; return None
    for x in Vpp:
        if x in chosen3 or x in Q: bits[x] |= 4
    for x in fixed: assert bits[x] == label[x], 'blocks keep their label'
    # ---- assemble ----
    Y = [0] * 7
    for x in Vpp:
        if bits[x] == 0: rep['fail'] = 'label 0 in V\'\''; return None
        Y[INV[bits[x]]] |= 1 << x
    if [popc(y) for y in Y] != m: rep['fail'] = 'sizes'; return None
    Fm = sum(1 << x for x in F)
    B = [0] * 7
    for l in range(7):
        for p in range(7):
            if p not in LSET[l]: B[l] |= Y[p]
        for i in range(3):
            if l in T_NOTES[i]: B[l] |= Omegas[i]
        if l in TSTAR: B[l] |= Fm
    rep['ok'] = True
    return B

# ---------- independent exact verifier ----------
def check_seven(n, Hrows, alpha, k, B):
    """membership via the ORIGINAL parity-check rows, distinctness, no transversal of size <= 2
    (via 7-bit incidence patterns), Fano-type (pencil triples empty)."""
    def syn(S): return sum(((popc(S & h) & 1) << i) for i, h in enumerate(Hrows))
    for S in B:
        if popc(S) != k or syn(S) != alpha: return False, 'membership'
    if len(set(B)) != 7: return False, 'distinct'
    pats = set()
    for x in range(n):
        pats.add(sum(1 << l for l in range(7) if B[l] >> x & 1))
    pats = list(pats)
    for i in range(len(pats)):
        for j in range(i, len(pats)):
            if pats[i] | pats[j] == 127: return False, 'transversal <= 2'
    for p in range(7):
        a, b, c = PENCIL[p]
        if B[a] & B[b] & B[c]: return False, 'pencil'
    return True, 'ok'

# ---------- multipart variant (B1m): Lemma C* over all parts of the current Venn level ----------
def multi_lemma_c(parts, target, col):
    """parts: list of (U, a). Find Q_u subset of U, |Q_u| = a, with XOR of all chosen columns = target.
    Pairs: Lemma B inside each part, modulo the span of the pairs already taken (quotient), at most
    b_u = min(a, |U| - a) pairs in part u.  Then one endpoint per pair, fill, and swap (Lemma C*)."""
    F = Span(); allpairs = []
    for pi_, (U, a) in enumerate(parts):
        b = min(a, len(U) - a)
        if b <= 0: continue
        red = {x: F.reduce(col[x])[0] for x in U}
        pr = rainbow(U, red)[:b]
        for (x, y) in pr:
            if F.add(col[x] ^ col[y], 1 << len(allpairs)): allpairs.append((pi_, x, y))
    Qs = []; sig = 0
    for pi_, (U, a) in enumerate(parts):
        mine = [(x, y) for (p2, x, y) in allpairs if p2 == pi_]
        used = {z for p in mine for z in p}
        rest = [x for x in U if x not in used]
        Q = [x for x, y in mine] + rest[:a - len(mine)]
        if len(Q) != a: return None
        Qs.append(set(Q))
        for x in Q: sig ^= col[x]
    m = F.solve(sig ^ target)
    if m is None: return None
    for t, (pi_, x, y) in enumerate(allpairs):
        if m >> t & 1: Qs[pi_].discard(x); Qs[pi_].add(y)
    chk = 0
    for Q in Qs:
        for x in Q: chk ^= col[x]
    assert chk == target
    return Qs

def b1m_construct(cs, k, Omegas, rng=None, report=None):
    """as b1_construct, but the three label bits are each solved by Lemma C* over ALL parts of the level
    (no reserved bases; X, blocks, X0, fixer and Z exactly as in b1_construct)."""
    rng = rng or random.Random(0)
    rep = report if report is not None else {}
    n = cs.n
    w = [popc(O) for O in Omegas]; W = sum(w)
    s = 4 * n - 7 * k - W; rep.update(W=W, s=s)
    if s < 0 or any((x - k) % 2 for x in w): rep['fail'] = 'H0/H1'; return None
    allO = Omegas[0] | Omegas[1] | Omegas[2]
    col = [cs.cls(x) for x in range(n)]
    Vp = [x for x in range(n) if not (allO >> x & 1)]
    rep.update(e=rank([col[x] ^ col[Vp[0]] for x in Vp]), cells=len({col[x] for x in Vp}))
    F = set()
    if s % 4 == 2:
        Q = multi_lemma_c([(Vp, 2 + 4 * ((rep['e'] + 1) // 4))], 0, col)
        if Q is None: rep['fail'] = 'fixer'; return None
        F = Q[0]
    u = (s - len(F)) // 4; rep.update(F=len(F), u=u)
    pool = [x for x in Vp if x not in F]; rng.shuffle(pool)
    Z = set(pool[:u])
    e = [0] * 7
    for i in range(3):
        for l in T_NOTES[i]: e[l] += w[i]
    for l in TSTAR: e[l] += len(F)
    m = m_vector(k, e)
    if m is None or min(m) < 1: rep['fail'] = 'm'; return None
    rep['m_min'] = min(m)
    mv = {LAB[p]: m[p] for p in range(7)}; mv[0] = 0
    Vpp = [x for x in Vp if x not in Z and x not in F]
    bits = {x: 0 for x in Vpp}
    for i in range(3):
        parts = []
        for pref in range(1 << i):
            U = [x for x in Vpp if bits[x] == pref]; rng.shuffle(U)
            a = sum(c for v, c in mv.items() if v & ((1 << i) - 1) == pref and v >> i & 1)
            parts.append((U, a))
        Qs = multi_lemma_c(parts, 0, col)
        if Qs is None: rep['fail'] = f'step{i+1}'; return None
        for Q in Qs:
            for x in Q: bits[x] |= 1 << i
    Y = [0] * 7
    for x in Vpp:
        if bits[x] == 0: rep['fail'] = 'label0'; return None
        Y[INV[bits[x]]] |= 1 << x
    if [popc(y) for y in Y] != m: rep['fail'] = 'sizes'; return None
    Fm = sum(1 << x for x in F)
    B = [0] * 7
    for l in range(7):
        for p in range(7):
            if p not in LSET[l]: B[l] |= Y[p]
        for i in range(3):
            if l in T_NOTES[i]: B[l] |= Omegas[i]
        if l in TSTAR: B[l] |= Fm
    rep['ok'] = True
    return B
