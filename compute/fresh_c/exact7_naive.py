"""Brute-force cross-check of exact7.py on tiny k: actual point sets, no type symmetry, no dominance rules.
Same game: A_1 fixed, 6 requests of at most T points, adversary answers any k-subset avoiding the request,
requester wins iff the 7 edges have no 2-cover."""
import sys, itertools
from functools import lru_cache
def solve(k, T):
    V = tuple(range(2 * k))
    ksets = [frozenset(c) for c in itertools.combinations(V, k)]
    reqs = [frozenset(c) for c in itertools.combinations(V, T)]
    def coverable(edges):
        for x in V:
            for y in V[x:]:
                if all((x in e) or (y in e) for e in edges):
                    return True
        return False
    @lru_cache(maxsize=None)
    def win(edges, rounds_left):
        # edges: frozenset of distinct edges so far (repeats do not matter for coverability)
        if not coverable(edges):
            return True
        if rounds_left == 0:
            return False
        for S in reqs:
            if all(win(edges | {A}, rounds_left - 1) for A in ksets if not (A & S)):
                return True
        return False
    return win(frozenset([frozenset(range(k))]), 6)
if __name__ == "__main__":
    from exact7 import Game
    for k in (2, 3):
        for T in range(1, k + 1):
            a = solve(k, T); b = Game(k, T).solve()
            print(f"k={k} T={T}: brute force {'R' if a else 'A'}   type solver {'R' if b else 'A'}   {'OK' if a == b else 'MISMATCH'}", flush=True)
