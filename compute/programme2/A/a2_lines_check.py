r"""Theorem A2 is a weight statement (special case of Theorem 3H with every heavy atom on colour 0).
Exact test: random weight vectors with heavy set A (any masses) and light atoms <= a', with
Lam + 3a' >= 2 and y(V) + 7a' < 7/3; run the fill of construct_A2 and check every Fano line has mass < 1."""
import random, sys
from fractions import Fraction as F
from theorem_a_check import construct_A2, LINES
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
ok = bad = 0
while ok + bad < 3000:
    nh = rng.randint(0, 4); ap = F(1, rng.randint(15, 200))
    nl = rng.randint(1, 400)
    light = [ap * F(rng.randint(1, 100), 100) for _ in range(nl)]; light[0] = ap
    Lam = sum(light)
    if Lam + 3 * ap < 2: continue
    room = F(7, 3) - 7 * ap - Lam
    if room <= 0: continue
    heavy = [room * F(rng.randint(0, 99), 100) / max(nh, 1) for _ in range(nh)]
    y = heavy + light; n = len(y); A = (1 << nh) - 1
    assert sum(y) + 7 * ap < F(7, 3)
    col = construct_A2(n, y, A, max(light))
    mass = [sum((y[v] for v in range(n) if col[v] in ln), F(0)) for ln in LINES]
    if max(mass) < 1: ok += 1
    else: bad += 1; print('BAD', float(max(mass)), nh, float(ap), float(Lam))
print({'ok': ok, 'bad': bad})
