r"""Confined pair-cover game on a ground set of n atoms (default n = 2k), exact AND/OR search.
C-language: reply B_i = V \ C_i, C_i = S_i (requested, T atoms) + O_i (omitted by adversary, n-k-T atoms).
Seven rounds, no discard.  Requester wins iff final C-types are pairwise intersecting (TWIN Thm 7.1),
including the sliver types: when the adversary omits an atom of type I at round i he may keep one point of
that class in the reply; that point is requested for free ever after, final type I + {i+1..7}.
usage: py confined.py k T [n] [rounds]
"""
import sys, itertools, time
from functools import lru_cache
k = int(sys.argv[1]); T = int(sys.argv[2]); n = int(sys.argv[3]) if len(sys.argv) > 3 else 2 * k
R = int(sys.argv[4]) if len(sys.argv) > 4 else 7
SLIVER = (len(sys.argv) <= 5) or sys.argv[5] != "nosliver"
om = n - k - T
assert om >= 0
FUT = [sum(1 << j for j in range(i + 1, R)) for i in range(R)]
sys.setrecursionlimit(10000)
nodes = [0]

def minimal(sl):
    sl = sorted(set(sl), key=lambda s: bin(s).count("1"))
    out = []
    for s in sl:
        if not any((m & s) == m for m in out): out.append(s)
    return tuple(sorted(out))

def choose(counts, tot):
    """all ways to take `tot` atoms from classes with given multiplicities"""
    if not counts:
        if tot == 0: yield ()
        return
    for a in range(min(counts[0], tot), -1, -1):
        for r in choose(counts[1:], tot - a): yield (a,) + r

@lru_cache(maxsize=None)
def win(i, atoms, sl):
    nodes[0] += 1
    fut_all = FUT[i - 1] if i > 0 else (1 << R) - 1     # bits i..R-1 still available
    # prune: a sliver that can never meet an atom, atoms that can never get 1 bit
    for s in sl:
        for a in set(atoms):
            if not (s & (a | fut_all)): return False
    if n == 2 * k:   # every point needs >= 3 memberships (TWIN 7.3); counting prune
        need = sum(max(0, 3 - bin(a).count("1")) for a in atoms)
        if need > (R - i) * k: return False
    if i == R:
        ts = set(atoms) | set(sl)
        return all(a & b for a in ts for b in ts)
    # counting prune: disjoint atoms must still be able to meet
    types = sorted(set(atoms)); cnt = [atoms.count(t) for t in types]
    bit = 1 << i
    # requester options, fewest-membership atoms first
    order = sorted(range(len(types)), key=lambda j: (bin(types[j]).count("1"), types[j]))
    types = [types[j] for j in order]; cnt = [cnt[j] for j in order]
    for s in choose(tuple(cnt), T):
        rem = tuple(c - a for c, a in zip(cnt, s))
        ok = True
        for o in choose(rem, om):
            new = []; nsl = list(sl)
            for t, c, a, b in zip(types, cnt, s, o):
                new += [t | bit] * (a + b) + [t] * (c - a - b)
                if b and SLIVER: nsl.append(t | FUT[i])
            if not win(i + 1, tuple(sorted(new)), minimal(nsl)):
                ok = False; break
        if ok: return True
    return False

t0 = time.time()
res = win(0, tuple([0] * n), ())
print(f"k={k} T={T} n={n} rounds={R} slivers={SLIVER}: requester {'WINS' if res else 'LOSES'}  nodes={nodes[0]} time={time.time()-t0:.1f}s", flush=True)
