"""Checks for notes/PROGRAMME5_ALG.md.

(a) line-free lemma: J subset of PG(2,2) has c with <c,u>=1 for all u in J  iff  J contains no line.
(b) M(n) = max over class sizes m (sum <= n) of min_u |R_u|; the largest critical number of a
    PG(2,2)-free up-set in F_2^n is n - M(n) (attained by a layer).
(c) Fano subhypergraph in the pencil 3-graph of K^(k)_n  vs  M(n) >= k (Fano-type seven in K^(k)_n).
(d) anchor-quotient construction (section 3 of the note) on random families: from a pencil of
    weight w <= 4*tau - 3k - 4 (k even), build seven members by requests and check that they form
    a Fano-type seven (no 2-point transversal).

usage: py -3.14 alg_checks.py [trials]
"""
import sys, itertools, random
from pencil_graph import complete_family, pencil_edges

PTS = list(range(1, 8))                      # nonzero vectors of F_2^3 as ints 1..7
dot = lambda c, u: bin(c & u).count("1") & 1
LINES = [(u, v, u ^ v) for u in PTS for v in PTS if u < v < (u ^ v)]
assert len(LINES) == 7


def part_a():
    bad = 0
    for mask in range(128):
        J = [u for u in PTS if (mask >> (u - 1)) & 1]
        solv = any(all(dot(c, u) for u in J) for c in range(8))
        linefree = not any(all(x in J for x in L) for L in LINES)
        bad += solv != linefree
    print(f"(a) line-free lemma: {128 - bad}/128 subsets agree")


def M_closed(n):
    """closed form (proved in the note): 4*floor(n/7) + g(n mod 7)."""
    return 4 * (n // 7) + (0, 0, 0, 1, 2, 2, 3)[n % 7]


def M_exhaustive(n):
    """max_m min_u sum_{c: <c,u>=1} m_c over all m in Z_{>=0}^7 with sum m <= n (full enumeration)."""
    best = 0
    def rec(i, left, m):
        nonlocal best
        if i == 7:
            best = max(best, min(sum(m[c - 1] for c in PTS if dot(c, u)) for u in PTS))
            return
        for x in range(left + 1):
            m.append(x); rec(i + 1, left - x, m); m.pop()
    rec(0, n, [])
    return best


def M(n):
    return M_closed(n)


def part_b(nmax=35, nexh=13):
    agree = all(M_exhaustive(n) == M_closed(n) for n in range(1, nexh + 1))
    print(f"(b) closed form for M(n) agrees with full enumeration for n <= {nexh}: {agree}")
    rows = []
    for n in range(1, nmax + 1):
        mn = M(n)
        rows.append((n, mn, n - mn, (3 * (n + 7)) // 7))
    print("(b) n, M(n), max crit of PG(2,2)-free up-set = n-M(n), static bound floor(3(n+7)/7)")
    print("   " + " ".join(f"{n}:{c}" for n, _, c, _ in rows))
    print("   n - M(n) - floor(3n/7) over n=1..%d: %s" % (nmax, sorted(set(c - (3 * n) // 7 for n, _, c, _ in rows))))


def has_fano(m, edges, transitive=False):
    """Fano subhypergraph: edge xyz plus a,b,c,d with xab, xcd, yac, ybd, zad, zbc edges.
    transitive=True (vertex-transitive host, e.g. complete families): only edges through vertex 0 as x."""
    from collections import defaultdict
    link = [defaultdict(set) for _ in range(m)]
    for (i, j, l) in edges:
        for (x, y, z) in ((i, j, l), (j, i, l), (l, i, j)):
            link[x][y].add(z); link[x][z].add(y)
    cand = []
    for (i, j, l) in edges:
        for (x, y, z) in ((i, j, l), (j, l, i), (l, i, j), (i, l, j), (j, i, l), (l, j, i)):
            if not transitive or x == 0:
                cand.append((x, y, z))
    for (x, y, z) in cand:
        Lx, Ly, Lz = link[x], link[y], link[z]
        for a in Lx:
            if a in (y, z):
                continue
            for b in Lx[a]:
                if b in (y, z):
                    continue
                for c in Ly.get(a, ()):
                    if c in (x, z, b):
                        continue
                    for d in Lx.get(c, ()):
                        if d in (y, z, a, b):
                            continue
                        if d in Ly.get(b, ()) and d in Lz.get(a, ()) and c in Lz.get(b, ()):
                            return (x, y, z, a, b, c, d)
    return None


def part_c():
    out = []
    for k in range(3, 7):
        for n in range(k + 2, 2 * k):
            if n > 11:
                continue
            H = complete_family(n, k)
            E = pencil_edges(H, n)
            f = has_fano(len(H), E, transitive=True) is not None
            out.append((k, n, f, M(n) >= k))
    agree = all(f == g for _, _, f, g in out)
    print("(c) Fano in pencil graph of K^(k)_n vs M(n)>=k: " +
          " ".join(f"({k},{n}):{int(f)}{int(g)}" for k, n, f, g in out) + f"  agree={agree}")


# ---------- (d) anchor-quotient construction ----------
def popcount(x):
    return bin(x).count("1")


def tau(H, n):
    for t in range(n + 1):
        for T in itertools.combinations(range(n), t):
            m = sum(1 << p for p in T)
            if all(b & m for b in H):
                return t
    return n


def avoid(H, X):
    """a member disjoint from X (exists whenever |X| < tau)."""
    for b in H:
        if not (b & X):
            return b
    return None


def good_seven(S, n):
    for x in range(n):
        for y in range(x, n):
            m = (1 << x) | (1 << y)
            if all(b & m for b in S):
                return False
    return True


def construct(H, n, k, t, A, G, Gp):
    """Pencil {A,G,Gp}, |G cap A|, |Gp cap A| <= k/2, k even. Returns seven members or None."""
    W = ((1 << n) - 1) & ~A
    Apts = [p for p in range(n) if (A >> p) & 1]
    GA = [p for p in Apts if (G >> p) & 1]
    GpA = [p for p in Apts if (Gp >> p) & 1]
    rest = [p for p in Apts if p not in GA and p not in GpA]
    # halves of size k/2: A1 contains G cap A, A0 contains Gp cap A
    need1 = k // 2 - len(GA)
    A1 = GA + rest[:need1]
    A0 = GpA + rest[need1:]
    assert len(A1) == len(A0) == k // 2
    # quarters: Q11, Q10 split A1; Q01, Q00 split A0 (v1 = (1,0): A^1 = Q10+Q11)
    Q = {3: A1[:k // 4], 2: A1[k // 4:], 1: A0[:k // 4], 0: A0[k // 4:]}   # c = 2*c1 + c2
    msk = lambda pts: sum(1 << p for p in pts)
    def halves(v):   # v in {1,2,3} as 2*v1+v2 ; A_v^1 = quarters c with <c,v>=1
        one = msk([p for c in range(4) for p in Q[c] if dot(c, v)])
        return A & ~one, one
    h = k // 2
    Y1 = (G | Gp) & W
    if popcount(Y1) > 2 * t - 2 * h - 2:
        return None
    v1, v2, v3 = 2, 1, 3           # v1 = (1,0)
    # Y2: two members avoiding S u A_{v2}^0 and S u A_{v2}^1, S subset of Y1 of size |Y1| - (t-h) + 1
    Y1pts = [p for p in range(n) if (Y1 >> p) & 1]
    s = max(0, len(Y1pts) - (t - h) + 1)
    S = msk(Y1pts[:s])
    a0, a1 = halves(v2)
    M1, M2 = avoid(H, S | a0), avoid(H, S | a1)
    Y2 = (M1 | M2) & W
    X = Y1 & Y2
    b0, b1 = halves(v3)
    M3, M4 = avoid(H, X | b0), avoid(H, X | b1)
    Y3 = (M3 | M4) & W
    if Y1 & Y2 & Y3:
        return None
    return [A, G, Gp, M1, M2, M3, M4]


def part_d(trials):
    rng = random.Random(1)
    tested = ok = 0
    for trial in range(trials):
        k = rng.choice([4, 6])
        n = rng.randint(3 * k // 2 + 1, 9 if k == 4 else 10)
        allk = complete_family(n, k)
        p = rng.uniform(0.3, 0.9)
        H = [b for b in allk if rng.random() < p]
        if len(H) < 3:
            continue
        t = tau(H, n)
        bound = 4 * t - 3 * k - 4
        if bound < 0:
            continue
        found = None
        for (i, j) in itertools.combinations(range(len(H)), 2):
            I = H[i] & H[j]
            for l in range(j + 1, len(H)):
                if not (H[l] & I) and popcount(H[i] ^ H[j] ^ H[l]) <= bound:
                    found = (i, j, l); break
            if found: break
        if found:
            i, j, l = found
            x = [H[i], H[j], H[l]]
            # choose the anchor: the member meeting both others in <= k/2
            for a in range(3):
                A, G, Gp = x[a], x[(a + 1) % 3], x[(a + 2) % 3]
                if popcount(G & A) <= k // 2 and popcount(Gp & A) <= k // 2:
                    break
            S7 = construct(H, n, k, t, A, G, Gp)
            tested += 1
            ok += S7 is not None and all(b in H for b in S7) and good_seven(S7, n)
    print(f"(d) anchor-quotient construction: {ok}/{tested} pencils with w <= 4tau-3k-4 gave a good seven")


if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    part_a()
    part_b()
    part_c()
    part_d(trials)
