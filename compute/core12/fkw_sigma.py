r"""CORE 111: (Σ)-shapes inside the FKW parity family, finite-k, eps = 0. [computed exact, exhaustive over triples]
Family: n = 7m+1, X of size 4m, co-edges = (3m+1)-sets K with |K ∩ X| odd (edges A = V∖K with |A∩X| odd).
Triples of co-edges up to Sym(X) x Sym(Y) are exactly the pairs of Venn-count vectors (x_r), (y_r), r ⊆ {1,2,3}.
We enumerate every combined vector n_r = x_r + y_r (Σ = n, all three sizes = c), decide by exact DP whether a split
with Σx = |X| and every |K_i ∩ X| odd exists, and test
 (b) pencil:  n_0 = 0 (union V) and n_123 >= n - 2T,
 (c) Thm T:   n_123 = 0, pair intersections <= (T + n - 2k)/2, sum >= (3n - 3k - T)/2.
Also the same without the parity condition (complete family on n points), to see what kills what.
Usage: py -3.14 fkw_sigma.py m"""
import sys
from fractions import Fraction as F
m = int(sys.argv[1]); n, k, T, xs = 7 * m + 1, 4 * m, 3 * m, 4 * m; c = n - k
regs = list(range(8))
def comps(total, parts):
    if parts == 1: yield (total,); return
    for a in range(total + 1):
        for rest in comps(total - a, parts - 1): yield (a,) + rest
def split_ok(nv):
    # exists x_r in [0, n_r], Σx = xs, |K_i∩X| = Σ_{r∋i} x_r odd for i=1,2,3
    st = {(0, 0)}
    for r in regs:
        st = {(s + x, p ^ (r if x & 1 else 0)) for (s, p) in st for x in range(nv[r] + 1) if s + x <= xs}
    return (xs, 7) in st
pen_thr, a_max, sum_min = n - 2 * T, F(T + n - 2 * k, 2), F(3 * n - 3 * k - T, 2)
stats = dict(triples=0, par=0, pencil_nopar=0, pencil_par=0, T_nopar=0, T_par=0)
best_kappa = {True: -1, False: -1}
for nv in comps(n, 8):
    sizes = [sum(nv[r] for r in regs if r >> i & 1) for i in range(3)]
    if sizes != [c, c, c]: continue
    stats['triples'] += 1
    par = split_ok(nv); stats['par'] += par
    pa = [nv[3] + nv[7], nv[5] + nv[7], nv[6] + nv[7]]
    if nv[0] == 0:
        best_kappa[False] = max(best_kappa[False], nv[7])
        if par: best_kappa[True] = max(best_kappa[True], nv[7])
        if nv[7] >= pen_thr: stats['pencil_nopar'] += 1; stats['pencil_par'] += par
    if nv[7] == 0 and max(pa) <= a_max and sum(pa) >= sum_min: stats['T_nopar'] += 1; stats['T_par'] += par
print(f"m={m}: n={n} k={k} T={T} c={c}; pencil needs union V and kappa >= {pen_thr}; Thm T needs a,b,d <= {a_max}, sum >= {sum_min}")
print("  combined Venn vectors with sizes c:", stats['triples'], "; parity-realizable:", stats['par'])
print("  max triple intersection over triples with union V: complete family", best_kappa[False], "; parity family", best_kappa[True])
print("  pencil triples: complete family", stats['pencil_nopar'], "; parity family", stats['pencil_par'])
print("  Theorem-T triples: complete family", stats['T_nopar'], "; parity family", stats['T_par'])
