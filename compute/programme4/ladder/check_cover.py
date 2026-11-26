r"""Plain check of tau for an explicit co-edge family (for any candidate the searches produce).
Input: file of co-edges (c-subsets of [n]); members are their complements (k = n - c).  Reports whether every T-set
lies in a co-edge (=> tau >= T+1) for the given T, and the record threshold floor((3k+5)/4).
Usage: py check_cover.py famfile n T
"""
import sys, itertools
fam = [frozenset(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
n, T = int(sys.argv[2]), int(sys.argv[3]); c = len(next(iter(fam))); k = n - c
F = set(fam); assert all(len(f) == c and max(f) < n for f in fam)
bad = 0
for X in itertools.combinations(range(n), T):
    Xs = frozenset(X); comp = [y for y in range(n) if y not in Xs]
    if not any(Xs | frozenset(Y) in F for Y in itertools.combinations(comp, c - T)):
        bad += 1
        if bad <= 3: print("uncovered T-set:", X)
print(f"{len(fam)} co-edges, k={k}, n={n}: T-sets (T={T}) not in a co-edge: {bad} -> tau >= {T+1}: {bad == 0}; "
      f"record threshold floor((3k+5)/4) = {(3*k+5)//4}")
