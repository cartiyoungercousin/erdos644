r"""Greedy deletion from the saturated template H1 (notes/SATURATION.md 1.3) at (k,T,n) = (12,9,22).
H1 = {12-sets A of X+Y (|X|=12,|Y|=10) with |A&X| in {3,5,7,9}} + {X - x}. tau(H1) = 10 > 9 and H1 is (7,2)
(SATURATION 1.3). Subfamilies inherit (7,2). A member B is deleted iff every 9-subset of its co-edge K_B lies in
another co-edge, so tau > 9 is kept. Result: deletion-minimal (every member has a private 9-set, Lemma 3).
Usage: py -3.14 h2_delete.py seed  -> writes logs/h2_seed<seed>.txt (one member per line, as point lists)."""
import sys, itertools, random
from collections import Counter
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
nX, nY, n, T = 12, 10, 22, 9
X = list(range(12)); Y = list(range(12, 22)); FULL = (1 << n) - 1
def mask(s): 
    m = 0
    for p in s: m |= 1 << p
    return m
H = []
for j in (3, 5, 7, 9):
    for a in itertools.combinations(X, j):
        for b in itertools.combinations(Y, 12 - j):
            H.append(mask(a + b))
for x in X:
    H.append(mask([p for p in X if p != x]))
print("H1 members", len(H))
def pts(m): return [i for i in range(n) if m >> i & 1]
def subs9(K):
    P = pts(K)
    for c in itertools.combinations(P, len(P) - T):   # remove |K|-9 points
        r = K
        for p in c: r &= ~(1 << p)
        yield r
cnt = Counter()
for B in H:
    for S in subs9(FULL & ~B): cnt[S] += 1
print("9-sets covered", len(cnt), "of", 497420)
assert len(cnt) == 497420
rnd = random.Random(seed); order = list(range(len(H))); rnd.shuffle(order)
alive = [True] * len(H)
changed = True; rounds = 0
while changed:
    changed = False; rounds += 1
    for i in order:
        if not alive[i]: continue
        K = FULL & ~H[i]; ss = list(subs9(K))
        if all(cnt[S] >= 2 for S in ss):
            for S in ss: cnt[S] -= 1
            alive[i] = False; changed = True
    print("round", rounds, "alive", sum(alive), flush=True)
H2 = [H[i] for i in range(len(H)) if alive[i]]
assert all(cnt[S] >= 1 for S in cnt)
with open(f"logs/h2_seed{seed}.txt", "w") as f:
    for B in H2: f.write(" ".join(map(str, pts(B))) + "\n")
prof = Counter((bin(B & 0xFFF).count("1"), bin(B >> 12).count("1")) for B in H2)
print("H2 members", len(H2), "profiles", sorted(prof.items()), "total size", sum(bin(B).count("1") for B in H2))
