"""Part X §53: Kupavskii-Zakharov Lemma 10 run on the REQUEST measure nu of a reply map, exact (Fractions).
Checks Prop 53.1 (each piece homogeneous relative to its head's link; remainder bound) and Example 53.3
(junta selector vs hash selector with the same class heads give the same heads/masses).
py compute/spread/kz_request.py
"""
import itertools, random
from fractions import Fraction as Fr
from math import comb

def popc(x): return bin(x).count("1")

def run(n, k, T, reply, tau, q):
    c = n - k
    reqs = [sum(1 << i for i in S) for S in itertools.combinations(range(n), T)]
    nu = {}
    for S in reqs:
        K = reply(S); assert popc(K) == c and K & S == S
        nu[K] = nu.get(K, 0) + Fr(1, len(reqs))
    A = lambda x: comb(n - x, c - x)          # |A(X)| for |X| = x, A = C(V, c)
    rest = dict(nu); pieces = []
    subsets = sorted(range(1 << n), key=popc)
    while rest:
        tot = sum(rest.values())
        def mass(X): return sum(v for K, v in rest.items() if K & X == X)
        good = [X for X in subsets if popc(X) <= c and mass(X) >= Fr(tau) ** popc(X) * Fr(A(popc(X)), A(0)) * tot]
        # inclusion-maximal good set (largest size suffices for maximality)
        X = max(good, key=popc)
        if popc(X) > q:
            break
        piece = {K: v for K, v in rest.items() if K & X == X}
        pm = sum(piece.values())
        # homogeneity of the piece relative to A(X): for all Y >= X
        b = popc(X)
        for Y in subsets:
            if Y & X == X and popc(Y) <= c:
                mY = sum(v for K, v in piece.items() if K & Y == Y)
                assert mY <= Fr(tau) ** (popc(Y) - b) * Fr(A(popc(Y)), A(b)) * pm, "piece not homogeneous"
        pieces.append((X, pm))
        for K in piece: del rest[K]
    rem = sum(rest.values()) if rest else Fr(0)
    M = Fr(comb(c, T), comb(n, T))
    bound = Fr(tau) ** (-(q + 1)) * comb(n, c) * M
    assert rem <= bound
    return pieces, rem, bound

def greedy(n, k, T, orders, sel):
    c = n - k; om = c - T
    def reply(S):
        o = orders[sel(S)]
        D = [p for p in o if not (S >> p) & 1][:om]
        return S | sum(1 << p for p in D)
    return reply

if __name__ == "__main__":
    n, k, T = 12, 5, 4            # c = 7, omega = 3 (sanity sizes; not in the window)
    rnd = random.Random(1)
    tau, q = Fr(9, 5), 7       # tau0 = 56^(1/7) = 1.776 < tau < tau_pool = (792/126)^(1/3) = 1.846
    base = list(range(n))
    orders = [base[:], base[4:] + base[:4], base[8:] + base[:8]]   # heads {0,1,2}, {4,5,6}, {8,9,10}
    for i in range(3):
        tail = orders[i][3:]; rnd.shuffle(tail); orders[i] = orders[i][:3] + tail
    W = [3, 7]                                                     # junta window (2 points)
    junta = lambda S: ((S >> 3) & 1) + ((S >> 7) & 1)              # 0, 1, 2 by the trace on W
    table = {}
    def hsh(S):
        if S not in table: table[S] = rnd.randrange(3)
        return table[S]
    pool = lambda S: 0
    for name, sel in [("pool (one class)", pool), ("junta selector", junta), ("hash selector", hsh)]:
        pieces, rem, bound = run(n, k, T, greedy(n, k, T, orders, sel), tau, q)
        hs = [(sorted(i for i in range(n) if (X >> i) & 1), float(m)) for X, m in pieces]
        print("%-18s pieces=%d  remainder=%.4f (bound %.3g)" % (name, len(pieces), float(rem), float(bound)))
        for hd, m in hs[:6]:
            print("    head", hd, "nu-mass %.3f" % m)
    print("all pieces homogeneous relative to their heads; remainder bounds hold (asserted, exact)")
