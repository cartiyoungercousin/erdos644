"""Checks for Theorem QK (PROGRAMME5_QUAD.md section 2).
(1) Lemma K1: all graphs on 5, 6 points (all l on 5, five l on 6/7), 7 points: 3000 random graphs + all with <= 2 edges: for every graph G and linear part l, every k with 2 <= k <= n-2:
    q constant on C(V,k)  <=>  the two-graph t(abc) = G_ab+G_bc+G_ac is constant on C(V,3)  AND  the affine form
    lambda = l + (k-1) 1_P (G = switch of empty/complete by P) is in {0, 1_V}.
(2) The matching colouring of the proof, on random q (n = 60..90): build seven disjoint mixed 4-sets, colour them
    one point per colour of P_u, balance the classes, and check that every R_u contains k-subsets of both q-values
    (found by a swap walk), hence a Fano seven in either level set; the seven is re-checked pair by pair."""
import itertools, random
from qlib import from_edges, q_eval, check_seven

def tconst(n, G):
    vals = {(G[a] >> b & 1) ^ (G[b] >> c & 1) ^ (G[a] >> c & 1) for a, b, c in itertools.combinations(range(n), 3)}
    return len(vals) == 1

def part_one(n):
    pairs = list(itertools.combinations(range(n), 2))
    bad = 0; cnt = 0
    rng = random.Random(1)
    masks = range(1 << len(pairs)) if n <= 6 else [rng.getrandbits(len(pairs)) for _ in range(3000)] +         [m for m in range(1 << len(pairs)) if bin(m).count('1') <= 2]
    for mask in masks:
        G = from_edges(n, [pairs[i] for i in range(len(pairs)) if mask >> i & 1])
        tc = tconst(n, G)
        for l in (range(1 << n) if n <= 5 else [0, 1, 3, (1 << n) - 1, 0b1010101 & ((1 << n) - 1)]):
            for k in range(2, n - 1):
                vals = {q_eval(sum(1 << x for x in S), G, l) for S in itertools.combinations(range(n), k)}
                const = len(vals) == 1
                cnt += 1
                if const and not tc:
                    bad += 1
                if tc:  # predicted: q affine on slice: q(B) = C0 + lambda(B); constant iff lambda in {0,1_V}
                    # recover P: switch class, P = N(0) (t == 0) or complement-based (t == 1)
                    t1 = (G[0] >> 1 & 1) ^ (G[1] >> 2 & 1) ^ (G[0] >> 2 & 1) if n >= 3 else 0
                    Gs = G if t1 == 0 else [((1 << n) - 1) & ~G[i] & ~(1 << i) for i in range(n)]
                    P = Gs[0] | 1  # vertex 0 on side P; its neighbours on the other side
                    P = ((1 << n) - 1) & ~Gs[0]
                    lam = l ^ (P if (k - 1) % 2 else 0)
                    pred = lam in (0, (1 << n) - 1)
                    if pred != const:
                        bad += 1
    return cnt, bad

def mixed(G, w):
    a, b, c, d = w
    t = lambda x, y, z: (G[x] >> y & 1) ^ (G[y] >> z & 1) ^ (G[x] >> z & 1)
    return len({t(a, b, c), t(a, b, d), t(a, c, d), t(b, c, d)}) == 2

def part_two(trials=20, seed=5):
    rng = random.Random(seed); ok = 0
    for tr in range(trials):
        n = rng.randint(60, 90); k = (4 * n - 38) // 7
        p = rng.choice([0.02, 0.1, 0.5])
        G = from_edges(n, [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p])
        l = rng.getrandbits(n)
        # greedy disjoint mixed 4-sets
        free = list(range(n)); rng.shuffle(free); W = []
        used = set()
        for w in itertools.combinations(free[:40], 4):
            if not used & set(w) and mixed(G, w):
                W.append(w); used |= set(w)
                if len(W) == 7: break
        if len(W) < 7:
            print('trial', tr, 'fewer than 7 disjoint mixed 4-sets among 40 points (p =', p, ') - skipped'); continue
        col = {}
        for u in range(1, 8):
            Pu = [p_ for p_ in range(1, 8) if bin(p_ & u).count('1') & 1]
            for x, pcol in zip(W[u - 1], Pu):
                col[x] = pcol
        cnts = {p_: 4 for p_ in range(1, 8)}
        rest = [x for x in range(n) if x not in col]
        for x in rest:
            pcol = min(cnts, key=lambda z: cnts[z]); col[x] = pcol; cnts[pcol] += 1
        seven = {0: [], 1: []}
        for u in range(1, 8):
            R = [x for x in range(n) if bin(col[x] & u).count('1') & 1]
            assert len(R) >= k + 2 and set(W[u - 1]) <= set(R)
            got = {}
            B = set(R[:k]); out = R[k:]
            for _ in range(4000):
                v = q_eval(sum(1 << x for x in B), G, l)
                got.setdefault(v, sum(1 << x for x in B))
                if len(got) == 2: break
                i = rng.choice(sorted(B)); j = rng.choice(out)
                B.remove(i); B.add(j); out.remove(j); out.append(i)
            assert len(got) == 2, 'line with constant q: contradicts Lemma K1'
            for a in (0, 1): seven[a].append(got[a])
        assert check_seven(seven[0], n) and check_seven(seven[1], n)
        ok += 1
    return ok

if __name__ == '__main__':
    for n in (5, 6, 7):
        print('part 1, n =', n, '(checks, violations) =', part_one(n), flush=True)
    print('part 2: Fano sevens built in both level sets in', part_two(), 'random instances', flush=True)
