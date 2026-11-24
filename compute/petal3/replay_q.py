"""PETAL section 18.2: scripted exact replay of J' Step 2 on the extremal-singles configuration Q(c).
Petals: V = 4 blocks of c/2 (points), X_i = (V minus block_i) + private part of rho = k - 3c/2 points.
Centres (class Y): a fixed core of k - 4*mu - 4 points outside everything, mu unrequested points from each private part
(preferring points of earlier centres when unrequested), and one unrequested point of every block (sliver in T_d).
Requester: J' Step 2 (force k - c points inside the petal X_a minimising the outside trace, seal observed traces);
a request over T is truncated and reported.  Exact 2-cover test on the 7 sets at the end.
usage: py replay_q.py k T c mu
"""
import sys


def run(k, T, c, mu):
    assert c % 2 == 0
    blk = c // 2; rho = k - 3 * blk
    assert rho >= 0 and 2 * mu <= rho
    pts = 0
    def new(m):
        nonlocal pts
        r = list(range(pts, pts + m)); pts += m; return r
    blocks = [new(blk) for _ in range(4)]
    priv = [new(rho) for _ in range(4)]
    core = new(k - 4 * mu - 4)
    P = [set(x for j in range(4) if j != i for x in blocks[j]) | set(priv[i]) for i in range(4)]
    assert all(len(p) == k for p in P) and not set.intersection(*P)
    U = set().union(*P)
    cents = []; over = []
    for j in range(3):
        Z = set()
        for C in cents: Z |= (C & U)
        a = min(range(4), key=lambda i: len(Z - P[i]))
        inside = sorted(Z & P[a])
        rest = [x for x in priv[a] if x not in Z] + [x for b in range(4) if b != a for x in blocks[b] if x not in Z]
        F = set(inside) | set(rest[:max(0, (k - c) - len(inside))])
        outside = sorted(Z - P[a]); room = T - len(F)
        if len(outside) > room: over.append((j + 1, len(F) + len(outside) - T)); outside = outside[:room]
        S = F | set(outside)
        E = set(core)
        prev = set().union(*cents) if cents else set()
        for i in range(4):
            free = [x for x in priv[i] if x not in S]
            free.sort(key=lambda x: x not in prev)          # re-use earlier trace points when not sealed
            E |= set(free[:mu])
            fb = [x for x in blocks[i] if x not in S]
            if fb: E.add(fb[0])
        filler = 0
        while len(E) < k: E.add(10 ** 6 + 1000 * j + filler); filler += 1     # fresh points
        assert len(E) == k and not (E & S)
        cents.append(E)
    seven = P + cents
    types = set()
    for x in set().union(*seven): types.add(sum(1 << i for i in range(7) if x in seven[i]))
    cover = any((m1 | m2) == 127 for m1 in types for m2 in types)
    tr = [C & U for C in cents]
    return dict(rho=rho, need_C3=(k - c) + 6 * mu, T=T, over=over, traces=[len(x) for x in tr],
                result="2-cover exists (J' fails)" if cover else "NO 2-COVER (requester wins)")


if __name__ == "__main__":
    k, T, c, mu = map(int, sys.argv[1:5])
    print("k=%d T=%d c=%d mu=%d: %s" % (k, T, c, mu, run(k, T, c, mu)))


def run_plan(k, T, c, nu, al2):
    """Section 22: mixed plan.  Rotation a_j = j (j = 0,1,2), b = 3.  Request 1 = F_1 + whole private of petal a_2;
    request 2 = F_2 + observed trace of C_1 + al2 further points of private b; request 3 = F_3 + observed traces.
    F_j = k - c points of X_{a_j} containing its private part and the observed traces inside X_{a_j}.
    Scripted centres: nu unrequested points of every private part (earlier trace points first), one point per block."""
    blk = c // 2; rho = k - 3 * blk
    pts = 0
    def new(m):
        nonlocal pts
        r = list(range(pts, pts + m)); pts += m; return r
    blocks = [new(blk) for _ in range(4)]; priv = [new(rho) for _ in range(4)]
    core = new(max(0, k - 4 * nu - 4))
    P = [set(x for j in range(4) if j != i for x in blocks[j]) | set(priv[i]) for i in range(4)]
    U = set().union(*P); cents = []; sizes = []
    for j in range(3):
        a = j
        Z = set()
        for C in cents: Z |= (C & U)
        inside = set(priv[a]) | (Z & P[a])
        rest = [x for b in range(4) if b != a for x in blocks[b] if x not in inside]
        F = set(inside) | set(rest[:max(0, (k - c) - len(inside))])
        S = F | (Z - P[a])
        if j == 0: S |= set(priv[1])
        if j == 1: S |= set([x for x in priv[3] if x not in Z][:al2])
        sizes.append(len(S))
        if len(S) > T: return dict(rho=rho, sizes=sizes, result="request %d over by %d" % (j + 1, len(S) - T))
        prev = set().union(*cents) if cents else set()
        E = set()
        for i in range(4):
            free = [x for x in priv[i] if x not in S]; free.sort(key=lambda x: x not in prev)
            E |= set(free[:nu])
            fb = [x for x in blocks[i] if x not in S]
            if fb: E.add(fb[0])
        E |= set(core[:k - len(E)]); f = 0
        while len(E) < k: E.add(10 ** 6 + 1000 * j + f); f += 1
        assert len(E) == k and not (E & S)
        cents.append(E)
    seven = P + cents; types = set()
    for x in set().union(*seven): types.add(sum(1 << i for i in range(7) if x in seven[i]))
    cover = any((m1 | m2) == 127 for m1 in types for m2 in types)
    return dict(rho=rho, sizes=sizes, traces=[len(C & U) for C in cents],
                result="2-cover exists" if cover else "NO 2-COVER (requester wins)")
