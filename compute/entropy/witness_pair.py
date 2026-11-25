r"""CORE 73.4: witness-pair entropy test (coordinator's suggestion).  [computed exact; logs float]
For a family C of co-edges on n points: pair-link sizes |K_xy| = #{K in C : K >= {x,y}} (x = y included as the
point-link), the codegree bound C(n-2,T-2)/C(c-2,T-2), and for nu = 7 iid uniform members the witness/union bound
U = sum_{x<=y} (1 - |K_xy|/|C|)^7 = E[#uncovered pairs].  Entropy form: H(seven | bad) <= log #pairs + max_xy 7 log|C - K_xy|.
Usage: py witness_pair.py k T n famfile
"""
import sys, math, itertools
k, T, n = map(int, sys.argv[1:4]); c = n - k
M = [sum(1 << int(x) for x in l.split()) for l in open(sys.argv[4]) if l.split()]
m = len(M)
L = {}
for x in range(n):
    for y in range(x, n):
        b = (1 << x) | (1 << y); L[(x, y)] = sum(1 for K in M if K & b == b)
pairs = [v for (x, y), v in L.items() if x != y]
U = sum((1 - v / m) ** 7 for v in L.values())
bound = math.comb(n - 2, T - 2) / math.comb(c - 2, T - 2)
Hseven = 7 * math.log(m); Hbad = math.log(len(L)) + 7 * math.log(m - min(pairs))
print(f"{sys.argv[4]}: |C|={m}; pair-link min {min(pairs)} mean {sum(pairs)/len(pairs):.1f} max {max(pairs)} "
      f"(codegree bound {bound:.1f}); min link fraction {min(pairs)/m:.4f}, (c/n)^2 = {(c/n)**2:.4f}")
print(f"   iid-uniform union bound E[#uncovered pairs] = {U:.2f}  (need < 1)")
print(f"   entropy form: H(uniform 7-tuple) = {Hseven:.3f}  vs  log#pairs + 7 log|C - K_xy|max = {Hbad:.3f}  (need first > second)")
