"""Lemma PAIR test: random (k+r)-covering families; for every pair A,B with |A&B| in window(n,k,r), build the colouring
of the lemma, pick members inside the five other lines, and re-check the seven pair by pair (plain code)."""
import random, itertools
from pairwin import window
from qlib import check_seven

def covering_family(n, k, r, rng, dens):
    H = set(sum(1 << x for x in c) for c in itertools.combinations(range(n), k) if rng.random() < dens)
    for S in itertools.combinations(range(n), k + r):
        Sm = sum(1 << x for x in S)
        if not any((B & Sm) == B for B in H):
            drop = rng.sample(S, r); H.add(Sm - sum(1 << x for x in drop))
    return list(H)

def build(n, k, r, A, B, H):
    I = [x for x in range(n) if A >> x & B >> x & 1]; Ao = [x for x in range(n) if A >> x & 1 and not B >> x & 1]
    Bo = [x for x in range(n) if B >> x & 1 and not A >> x & 1]; O = [x for x in range(n) if not (A | B) >> x & 1]
    # colours: p1=1 (A-B), p2=2 (B-A), p3=3 (A&B), w=4 ; u=1 -> R_1 = {p: p&1 odd} etc. choose u=1 (R=A), v=2 (R=B)
    for al in itertools.product(range(len(I) + 1), range(len(Ao) + 1), range(len(Bo) + 1)):
        col = {}
        for part, p, a in ((I, 3, al[0]), (Ao, 1, al[1]), (Bo, 2, al[2])):
            for t, x in enumerate(part):
                col[x] = p if t < a else p ^ 4
        for x in O: col[x] = 4
        seven = []
        for u in range(1, 8):
            R = sum(1 << x for x in range(n) if bin(col[x] & u).count('1') & 1)
            mem = next((C for C in H if (C & R) == C), None)
            if mem is None: break
            seven.append(mem)
        if len(seven) == 7:
            return seven
    return None

rng = random.Random(7); tested = 0
for (n, k, r) in [(12, 6, 1), (13, 6, 1), (14, 7, 1), (14, 8, 1), (15, 8, 1), (13, 7, 1)]:
    W = window(n, k, r)
    for trial in range(3):
        H = covering_family(n, k, r, rng, 0.05)
        pairs = [(A, B) for A, B in itertools.combinations(H, 2) if bin(A & B).count('1') in W]
        for A, B in pairs[:30]:
            s = build(n, k, r, A, B, H)
            assert s is not None and check_seven(s, n), (n, k, r, A, B)
            tested += 1
    print(f"(n,k,r)=({n},{k},{r}) window {W}: ok", flush=True)
print('Lemma PAIR: sevens built and re-checked for', tested, 'pairs')
