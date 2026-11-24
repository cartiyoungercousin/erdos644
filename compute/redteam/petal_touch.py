"""RED TEAM 6.3 check [computed exact]: on an N-set, any three k-sets WITH EMPTY COMMON INTERSECTION have at least
3k - N points lying in two of them (without that hypothesis the bound is only (3k-N)/2: first version of this
script, corrected), so for N < 3k - T their pair set P cannot be requested and the next reply can contain a point of it ("touch every triple").  Exhaustive over all
triples of k-subsets; also the static fact that four k-sets with no point in three of them need N >= 2k."""
import itertools, sys
for k, T, N in ((3, 2, 6), (4, 3, 7), (4, 3, 8), (5, 4, 9), (5, 4, 10)):
    sets = [sum(1 << i for i in c) for c in itertools.combinations(range(N), k)]
    worst = min(bin((a & b) | (a & c) | (b & c)).count("1") for a, b, c in itertools.combinations(sets, 3) if not (a & b & c))
    print(f"k={k} T={T} N={N}: min over triples with empty common intersection of #points in >=2 of them = {worst}  (3k-N = {3*k-N}; > T: {worst > T}; N < 3k-T: {N < 3*k-T})")
for k, N in ((3, 5), (3, 6), (4, 7), (4, 8)):
    sets = [sum(1 << i for i in c) for c in itertools.combinations(range(N), k)]
    ok = any(not ((a & b & c) | (a & b & d) | (a & c & d) | (b & c & d)) for a, b, c, d in itertools.combinations(sets, 4))
    print(f"k={k} N={N}: four k-sets with no point in three of them exist: {ok}  (N >= 2k: {N >= 2*k})")
