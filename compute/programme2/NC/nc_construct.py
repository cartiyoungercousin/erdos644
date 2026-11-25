r"""Exact check of the three-member criterion (PROGRAMME2_NC.md, Lemma NC1) on random instances.
H = H[W] (complete K_W^(k), d = 0, or parity twist odd-on-W1 with |W1|,|W2| <= k, d = 1) plus random outside members
(sets of size <= k meeting Z = V \ W, partly inside W).  Find three members with empty common intersection and
|W n (G1 u G2 u G3)| <= 2(w-k-d)-3, build the colouring of the proof, take members inside W \ L for the four lines
avoiding 0, and brute-force check that the seven have no 2-point transversal."""
import random, itertools, sys
LINES = [(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
PAIRS = [(1,3),(4,5),(6,2)]           # lines through 0 are 0+pair
def member_inside(U, k, W1, par):
    U = sorted(U)
    if par is None: return frozenset(U[:k]) if len(U) >= k else None
    a = [x for x in U if x in W1]; b = [x for x in U if x not in W1]
    for i in range(1 if par else 0, len(a)+1, 2):
        if k - i <= len(b) and i <= k: return frozenset(a[:i] + b[:k-i])
    return None
def no2t(seven, V):
    for x in V:
        for y in V:
            if all((x in B) or (y in B) for B in seven): return False
    return True
def run(seed):
    R = random.Random(seed); k = R.randint(4, 9); w = R.randint(k+3, 2*k+2); z = R.randint(k, 2*k+4)
    W = list(range(w)); Z = list(range(w, w+z)); V = W + Z
    par = R.choice([None, 1]); W1 = set(W[:w//2])
    if par is not None and (len(W1) > k or w - len(W1) > k): par = None
    d = 0 if par is None else 1
    out = []
    for _ in range(R.randint(5, 40)):
        s = R.randint(1, k); t = R.randint(0, s - 1)        # t points of W, s-t of Z (s-t >= 1)
        if s - t > z: continue
        out.append(frozenset(R.sample(W, t) + R.sample(Z, s - t)))
    bound = 2*(w - k - d) - 3
    Ws = set(W); best = None
    for G1, G2 in itertools.combinations_with_replacement(out, 2):
        I = G1 & G2
        for G3 in out:
            if not (I & G3):
                tr = len(Ws & (G1 | G2 | G3))
                if best is None or tr < best[0]: best = (tr, (G1, G2, G3))
    if best is None or best[0] > bound: return 'no-triple'
    G = best[1]; U = G[0] | G[1] | G[2]
    col = {}
    for v in V:
        if v not in U: col[v] = 0
    X = [[], [], []]
    for v in V:
        if v in U: X[next(s for s in range(3) if v not in G[s])].append(v)
    for s in range(3):
        xw = [v for v in X[s] if v in Ws]; xo = [v for v in X[s] if v not in Ws]
        h = len(xw) // 2
        for v in xw[:h] + xo: col[v] = PAIRS[s][0]
        for v in xw[h:]: col[v] = PAIRS[s][1]
    seven = []
    for L in LINES:
        Lset = {v for v in V if col[v] in L}
        if 0 in L:
            s = next(s for s in range(3) if set(PAIRS[s]) <= set(L)); B = G[s]
        else:
            B = member_inside([v for v in W if v not in Lset], k, W1, par)
            if B is None: return 'BUG: no W-member'
        assert not (B & Lset)
        seven.append(B)
    return 'ok' if no2t(seven, V) else 'BUG: 2-transversal'
if __name__ == '__main__':
    from collections import Counter
    c = Counter(run(s) for s in range(int(sys.argv[1]) if len(sys.argv) > 1 else 3000)); print(dict(c))
