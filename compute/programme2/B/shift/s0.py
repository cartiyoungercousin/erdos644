r"""Theorem S0 (notes/PROGRAMME2_B.md section 8.3): shift-0 linear layers H = C0 cap (V choose k), C0 even, k even.
Construction, literally as in the proof:
  1. U = an affine basis of the columns (e+1 points) padded to k + r points; x1 = member inside U (Lemma C).
  2. Quotient by E_{x1}; B = (k/2)-subset of V - x1 with sum in (k/2) h_u + E_{x1} (Lemma C in the quotient).
  3. A = (k/2)-subset of x1 with sum(A) = sum(B) (Lemma C on x1).  x2 = A + B, x3 = x1 + x2: a Schur triangle.
  4. NC1 colouring with W = V, d = r: colour 7 off the union, X_1 = B, X_2 = x1 - A, X_3 = A, each split into
     halves; the three lines through 7 are closed by x1, x2, x3; each of the four other lines by a member inside
     R_l (|R_l| >= k + r) found by Lemma C (fallback: exhaustive search when R_l is small).
Every seven is checked by verify7.verify (independent).  Also runs Theorem B1 with Omega = (0,0,0) (shift 0)."""
import sys, os, random, itertools, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'task3'))
from b1 import Span, lemma_c, rank, b1_construct
from core import Coset
from verify7 import verify, popc


def instance(n, k, M, rng, planted=0):
    """columns: M random bits + parity bit (bit M) -> C0 = ker, even.  planted: extra rows of support 2 or 4
    (short dual words, even weight) to stress the span hypotheses."""
    cols = [rng.getrandbits(M) | (1 << M) for _ in range(n)]
    R = M + 1
    for t in range(planted):
        for x in rng.sample(range(n), rng.choice([2, 4])):
            cols[x] |= 1 << R
        R += 1
    rows = [sum(1 << x for x in range(n) if cols[x] >> i & 1) for i in range(R)]
    return cols, rows, R


def dual_words(rows):
    S = Span(); basis = []
    for r_ in rows:
        if S.add(r_, 0):
            basis.append(r_)
    out = []
    for m in range(1, 1 << len(basis)):
        v = 0
        for i, b in enumerate(basis):
            if m >> i & 1:
                v ^= b
        out.append(v)
    return out


def cover_r(n, k, cols, rows):
    """least r for which the covering certificate holds: r >= e, and every nontrivial dual word lam has
    |lam| < k + r and n - |lam| < k + r (then every (k+r)-set U has E_U = E, and Lemma C gives a member in U)."""
    e = rank([c ^ cols[0] for c in cols])
    full = (1 << n) - 1
    worst = max([max(popc(l), n - popc(l)) for l in dual_words(rows) if l != full] + [0])
    return max(e, worst - k + 1), e


def find_member(Uset, k, col):
    U = sorted(Uset)
    Q = lemma_c(U, k, 0, col)
    if Q is not None:
        return set(Q)
    if len(U) <= 22:
        for c in itertools.combinations(U, k):
            s = 0
            for x in c:
                s ^= col[x]
            if s == 0:
                return set(c)
    return None


def schur_triangle(n, k, col, r, rng):
    e = rank([c ^ col[0] for c in col])
    S = Span(); basis = [0]
    for x in range(1, n):
        if S.add(col[x] ^ col[0], 0):
            basis.append(x)
    assert len(basis) == e + 1
    rest = [x for x in range(n) if x not in basis]; rng.shuffle(rest)
    U = set(basis) | set(rest[:max(0, k + r - len(basis))])
    x1 = find_member(U, k, col)
    if x1 is None:
        return None, 'no member in U'
    x1 = sorted(x1); sx1 = set(x1); P2 = [x for x in range(n) if x not in sx1]
    Ex = Span()
    for x in x1:
        Ex.add(col[x] ^ col[x1[0]], 0)
    colq = {x: Ex.reduce(col[x])[0] for x in range(n)}
    tq = Ex.reduce(col[x1[0]] if (k // 2) % 2 else 0)[0]
    B = lemma_c(P2, k // 2, tq, colq)
    if B is None:
        return None, 'quotient Lemma C on V - x1 failed'
    sB = 0
    for x in B:
        sB ^= col[x]
    A = lemma_c(x1, k // 2, sB, col)
    if A is None:
        return None, 'Lemma C on x1 failed'
    g1 = sum(1 << x for x in x1); g2 = sum(1 << x for x in A) | sum(1 << x for x in B); g3 = g1 ^ g2
    return (g1, g2, g3, sorted(A), sorted(sx1 - set(A)), sorted(B)), 'ok'


# Fano on F2^3 - 0: lines {a, b, a^b}; NC1's point 0 is 7; pairs through 7: {1,6}, {2,5}, {3,4}
LINES = sorted({frozenset((a, b, a ^ b)) for a in range(1, 8) for b in range(1, 8) if a != b}, key=sorted)
PAIRS = [(1, 6), (2, 5), (3, 4)]
BIG = (1, 2, 4)                       # colours receiving the larger half; {1,2,4} is not a line
assert frozenset(BIG) not in LINES and len(LINES) == 7


def nc1_seven(n, k, col, tri, rng):
    g1, g2, g3, A, Qd, Bset = tri
    # X_s = points of the union outside G_s: B misses g1, x1 - A misses g2, A misses g3
    X = {0: Bset, 1: Qd, 2: A}
    G = [g1, g2, g3]
    chi = [7] * n
    for s in range(3):
        pts = X[s][:]; rng.shuffle(pts)
        a, b = PAIRS[s]
        big = a if a in BIG else b; small = b if big == a else a
        hb = (len(pts) + 1) // 2
        for x in pts[:hb]:
            chi[x] = big
        for x in pts[hb:]:
            chi[x] = small
    Bl = {}
    for l in LINES:
        L = sum(1 << x for x in range(n) if chi[x] in l)
        R = {x for x in range(n) if chi[x] not in l}
        if 7 in l:
            s = next(i for i, (a, b) in enumerate(PAIRS) if a in l)
            assert G[s] & L == 0
            Bl[l] = G[s]
        else:
            Q = find_member(R, k, col)
            if Q is None:
                return None, 'no member in R_l, |R_l| = %d' % len(R)
            Bl[l] = sum(1 << x for x in Q)
    return [Bl[l] for l in LINES], 'ok'


def run(cases, seed, log):
    """for each case, draw instances until `want` of them satisfy the certified hypotheses (cap 3000 draws);
    hypothesis-free instances are also run (first `want` of them) and logged separately."""
    rng = random.Random(seed); stats = {}
    for (n, k, M, planted, want) in cases:
        got = {True: 0, False: 0}
        for draw in range(3000):
            if got[True] >= want and got[False] >= want:
                break
            cols, rows, R = instance(n, k, M, rng, planted)
            r, e = cover_r(n, k, cols, rows)
            T = n - k - r
            hyp = (4 * T >= 3 * k) and (e <= (k - 1) // 2) and n >= k + r + 2
            if got[hyp] >= want:
                continue
            got[hyp] += 1
            rec = dict(n=n, k=k, M=M, planted=planted, e=e, r_cert=r, T_cert=T, hyp=hyp)
            tri, why = schur_triangle(n, k, cols, r, rng)
            if tri is None:
                rec.update(s0='fail', why=why)
            else:
                assert popc(tri[0]) == popc(tri[1]) == popc(tri[2]) == k and tri[0] ^ tri[1] ^ tri[2] == 0
                assert tri[0] & tri[1] & tri[2] == 0
                B, why = nc1_seven(n, k, cols, tri, rng)
                if B is None:
                    rec.update(s0='nc1-fail', why=why)
                else:
                    ok, msg = verify(n, rows, 0, k, B)
                    rec.update(s0='verified' if ok else 'VERIFY-FAIL', why=msg)
            cs = Coset(n, rows, 0)
            try:
                Bb = b1_construct(cs, k, [0, 0, 0], random.Random(draw))
                if Bb is None:
                    rec['b1'] = 'no construction'
                else:
                    BB = list(Bb.values()) if isinstance(Bb, dict) else list(Bb)
                    ok, msg = verify(n, rows, 0, k, BB)
                    rec['b1'] = 'verified' if ok else 'VERIFY-FAIL ' + msg
            except Exception as ex:
                rec['b1'] = 'error ' + type(ex).__name__ + ' ' + str(ex)[:40]
            log.write(json.dumps(rec) + chr(10)); log.flush()
            st = stats.setdefault((n, k, planted, 'hyp' if hyp else 'nohyp'), {})
            for key in ('S0:' + rec['s0'], 'B1:' + rec['b1'][:15]):
                st[key] = st.get(key, 0) + 1
    return stats


if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    cases = [(17, 8, 2, 0, 20), (19, 10, 2, 0, 20), (26, 12, 3, 0, 20), (30, 14, 3, 0, 20),
             (60, 32, 3, 0, 20), (62, 32, 4, 1, 15), (74, 40, 4, 0, 15), (78, 42, 4, 0, 15),
             (112, 60, 5, 0, 10), (116, 62, 5, 1, 10), (150, 80, 6, 0, 8), (198, 106, 6, 2, 6),
             (370, 200, 9, 0, 4), (370, 202, 8, 3, 4)]
    t0 = time.time()
    os.makedirs(os.path.join(HERE, 'logs'), exist_ok=True)
    with open(os.path.join(HERE, 'logs', 's0_seed%d.jsonl' % seed), 'w') as log:
        stats = run(cases, seed, log)
    for key in sorted(stats):
        print(key, stats[key])
    print('time', round(time.time() - t0, 1))
