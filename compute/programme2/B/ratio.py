r"""Deficiency per pencil-incidence for Fano-type sevens on blocks with an even-intersection constraint.
A point with admissible pattern J costs 4 - |J| (size deficiency) and has |J|(4 - |J|) pencil incidences
(number of p with |J cap pencil(p)| odd = number of pencil sums s_p containing it; Lemma 5).
Block 'even w': w points whose patterns XOR to 0 (members, hence the B_l, meet the block evenly).
Block 'fan q': pair y, y' plus q points x with J(x) = J(y) xor J(y') (dual words {x, y, y'}).
Prints the minimum of cost / incidences over assignments with incidences > 0 [computed exact, exhaustive]."""
import itertools, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'task3'))
from core import PATTERNS, PENCIL
P = [sum(1 << l for l in J) for J in PATTERNS]
ADM = set(P)
def cost(m): return 4 - bin(m).count('1')
def inc(m): return sum(1 for p in range(7) if sum(1 for l in PENCIL[p] if m >> l & 1) % 2)
for m in P: assert inc(m) == bin(m).count('1') * (4 - bin(m).count('1'))
best_free = min(cost(m) / inc(m) for m in P if inc(m))
print('free points: min cost/incidence =', best_free)
for w in range(2, 7):
    best = None
    for combo in itertools.combinations_with_replacement(P, w - 1):
        last = 0
        for m in combo: last ^= m
        if last not in ADM: continue
        ms = list(combo) + [last]
        I = sum(inc(m) for m in ms)
        if I == 0: continue
        c = sum(cost(m) for m in ms)
        if best is None or c / I < best[0]: best = (c / I, c, I, [PATTERNS[P.index(m)] for m in ms])
    print(f'even block w={w}: min cost/incidence = {best[0]:.4f} (cost {best[1]}, incidences {best[2]})', [sorted(J) for J in best[3]])
for q in (1, 2, 3, 5, 10):
    best = None
    for a in P:
        for b in P:
            x = a ^ b
            if x not in ADM: continue
            I = inc(a) + inc(b) + q * inc(x); c = cost(a) + cost(b) + q * cost(x)
            if I and (best is None or c / I < best[0]): best = (c / I, c, I)
    print(f'fan q={q}: min cost/incidence = {best[0]:.4f}', best[1:])
