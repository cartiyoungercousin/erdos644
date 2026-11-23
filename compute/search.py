"""Branch-and-bound search for block-type families with property (7,2) and large tau.

Fix block sizes and uniformity r. A family = a subset S of allowed types. tau(S) is monotone
in S, property (7,2) is anti-monotone. We look for S maximizing tau(S) subject to (7,2):

  node S:  if tau(S) <= best: prune
           if S contains a known conflict C (set of types forming a bad 7-tuple): branch on C
           else ask the ILP for a bad tuple; none -> S is good (record); else its type set is a
           new conflict, branch on removing each of its types.

Usage: py search.py r nblocks [max_n] [budget_s] [min_n]
"""
import itertools
import sys
import time

from typefam import TypeFamily, compositions_bounded


def search(sizes, r, p=7, time_budget=600):
    all_types = list(compositions_bounded(r, list(sizes)))
    full = TypeFamily(list(sizes), all_types)
    base_tau = full.tau()[0]
    conflicts: list[frozenset] = []
    best = {"tau": 0, "S": None}
    t_start = time.time()
    seen = set()

    def tau_of(S):
        return TypeFamily(list(sizes), list(S)).tau()[0]

    def rec(S: frozenset, banned: frozenset):
        if time.time() - t_start > time_budget:
            return
        if S in seen:
            return
        seen.add(S)
        if not S:
            return
        t = tau_of(S)
        if t <= best["tau"]:
            return
        C = next((c for c in conflicts if c <= S), None)
        if C is None:
            w = TypeFamily(list(sizes), list(S)).find_bad_tuple(p)
            if w is None:
                best["tau"], best["S"] = t, S
                return
            C = frozenset(w["edge_types"])
            conflicts.append(C)
        for typ in sorted(C - banned):
            rec(S - {typ}, banned)
            banned = banned | {typ}   # later branches keep typ (avoid duplicate subtrees)

    rec(frozenset(all_types), frozenset())
    return base_tau, best, len(conflicts), time.time() - t_start


if __name__ == "__main__":
    r = int(sys.argv[1])
    m = int(sys.argv[2])
    max_n = int(sys.argv[3]) if len(sys.argv) > 3 else 2 * r
    budget = float(sys.argv[4]) if len(sys.argv) > 4 else 120
    min_n = int(sys.argv[5]) if len(sys.argv) > 5 else r + 1
    target = 3 * r // 4   # complete-family value floor(3r/4) (r = 4k gives 3k)
    print(f"r={r}, blocks={m}, looking for tau > {target} (3r/4)", flush=True)
    results = []
    for n in range(min_n, max_n + 1):
        for sizes in itertools.combinations_with_replacement(range(1, n), m):
            if sum(sizes) != n:
                continue
            base, best, nconf, dt = search(sizes, r, time_budget=budget)
            if base <= target:
                continue
            flag = "  <-- beats 3r/4" if best["tau"] > target else ""
            print(f"sizes={sizes} n={n}: tau(all types)={base}  best good tau={best['tau']}"
                  f"  conflicts={nconf} ({dt:.0f}s){flag}", flush=True)
            if best["tau"] > target:
                results.append((best["tau"], sizes, sorted(best["S"])))
    print("\nFamilies beating 3r/4:")
    for t, s, S in sorted(results, reverse=True):
        print(f"  tau={t} sizes={s} types={S}")
