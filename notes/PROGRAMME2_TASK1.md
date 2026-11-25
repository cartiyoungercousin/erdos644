# PROGRAMME_2 Task 1: tau*_b for every stored family

Code: `compute/programme2/task1/` (`tau_star.py` solver, `families.py` loaders/generators, `run_all.py`, `u1_run.py`, `gen_table.py`).
Raw results: `compute/programme2/task1/out/results.jsonl`; one row per family: `out/table_full.md`. Tags: [computed exact, float LP, tolerance 1e-9].

## Method
tau*_b(H) = min y(V), y >= 0, y(M) >= 1 for every transversal M. LP over a growing cut pool, separation by a minimum-y-weight transversal.
- **Oracle (n <= 25):** exact bitset form of the ILP. Superset-closure over all 2^n subsets; M is a transversal iff V∖M contains no member. This is the same minimisation as the ILP, and it returns the 150 lightest violated transversals per round. An HiGHS ILP oracle (`ilp_oracle`) is also in the code and agrees on FKW m = 2. On the 100k-row, 34-point U1 the ILP was too slow (> 5 min per call, aborted), so U1 uses the exact oracle below.
- **U1 (n = 34):** exact oracle = bitset over the 22 old points, plus a closed-form choice of fresh points. The 11-member X−x is missed by M0 iff M0∩X is empty or {x}, and then f_x is needed. Cuts are re-checked as genuine transversals of U1 (so the LP value is a certified lower bound). Completeness of the oracle is by hand, not cross-checked by ILP.
- **Symmetry:** FKW, H1, the near-pool families and the complete families are invariant under Sym(X) x Sym(Y) (resp. Sym(A) x Sym(Y), Sym(V)). There the LP is run over orbit-constant y (orbit-averaging keeps feasibility and y(V)). For FKW m = 2, 3 and H1 the unsymmetrised LP was also run and gives the same value. All other families were solved directly.
- **Three numbers per family:**
  - tau*_b;
  - the smallest max-atom among optimal y;
  - Phi = min over feasible y of y(V) + 7 max y. Theorem 3 closes H (rich) iff Phi < 7/3. The condition with the tau*_b-optimal y of smallest atom is never better than Phi.

## Table
tau = minimum transversal size (exact). margin = 7/3 − tau*_b. max atom = max y(x) (smallest among optimal y).

| family | n | members | tau | tau*_b | margin | max atom | Phi | class |
|---|---|---|---|---|---|---|---|---|
| FKW m=2 (k=8) | 15 | 3200 | 7 | 15/7 = 2.1429 | +0.1905 | 1/7 | 3.1429 | thin |
| FKW m=3 (k=12) | 22 | 323344 | 10 | 11/5 = 2.2000 | +0.1333 | 1/10 | 2.9000 | thin |
| H1 | 22 | 323236 | 10 | 11/5 | +0.1333 | 1/10 | 2.9000 | thin |
| H1min (8 stored orderings), FKWmin, G' | 22 | 100329-100524 | 10 | 11/5 | +0.1333 | 1/10 | 2.9000 | thin |
| U1 = G' padded (and H1min padded) | 34 | 100428 / 100506 | 10 | 533/220 = 2.4227 | **−0.0894** | 49/440 = 0.1114 | 3.2023 | thin |
| k=8 core9 `fam_8_6_15_rev`, entropy `randdump_s1`, `tgw_fam_8_6_15` | 15 | 2352-3599 | 7 | 15/7 | +0.1905 | 1/7 | 3.1429 | thin |
| entropy `fam_8_6_15_pool` | 15 | 3003 | 7 | 2 | +0.3333 | 1/7 | 3.0000 | thin |
| entropy `fam_8_6_15_sevenfree` (tau = 6 = T: NOT T-covering) | 15 | 1287 | 6 | 13/6 | +0.1667 | 1/6 | 3.3333 | thin |
| `tgw_fam_8_6_16` | 16 | 2814 | 7 | 16/7 = 2.2857 | +0.0476 | 1/7 | 3.2857 | thin |
| k=10 `tgw_fam_10_8_21`, `rand3s1`, `rand3s2` | 21 | 23346-53768 | 9 | 7/3 | **0.0000** | 1/9 | 3.1111 | thin |
| k=10 `rand2s1` / `rand2s2` | 21 | 44437 / 43922 | 9 | 20/9 / 37/17 | +0.1111 / +0.1569 | 1/9 / 2/17 | 3.0000 | thin |
| k=13 `tgw_fam_13_10_25` | 25 | 1172984 | 11 | 25/11 = 2.2727 | +0.0606 | 1/11 | 2.9091 | thin |
| hash/greedy rules (k=8,T=6,n=15), 30 instances (hash, linear, parity, early, late, early^hash, junta+, midhash; R = 2, 4, 8; rand and rev) | 15 | 2697-3698 | 7 | 15/7 (26), 2 (4: `early`) | +0.1905 / +0.3333 | 1/7 | 3.1429 / 3.0000 | thin |
| same rules at (8,6,16), 30 instances | 16 | 2073-5875 | 7 | 2 to 16/7 (values 2, 15/7, 13/6, 28/13, 29/13, 43/19, 16/7) | +0.0476 to +0.3333 | 1/7 to 3/19 | 3.00 to 3.29 | thin |
| near-pool (10,8,21), P = {(8,3)} | 21 | 43758 | 9 | 2 | +0.3333 | 1/9 | 2.7778 | thin |
| P = {(8,3),(9,2)} | 21 | 189618 | 10 | 19/10 | +0.4333 | 1/10 | 2.6000 | thin |
| P = {(8,3),(10,1)} | 21 | 175032 | 11 | 21/11 | +0.4242 | 1/11 | 2.5455 | thin |
| P = {(8,3),(11,0)} | 21 | 75582 | 10 | 2 | +0.3333 | 1/9 | 2.7778 | thin |
| P = {(8,3),(9,2),(10,1)} | 21 | 320892 | 11 | 20/11 | +0.5152 | 1/11 | 2.4545 | thin |
| P = {(8,3),(9,2),(11,0)} | 21 | 221442 | 11 | 13/7 | +0.4762 | 2/21 | 2.5238 | thin |
| P = {(8,3),(10,1),(11,0)} | 21 | 206856 | 11 | 15/8 | +0.4583 | 1/8 | 2.5455 | thin |
| P = all four (= complete K_21^(10)) | 21 | 352716 | 12 | 7/4 | +0.5833 | 1/12 | 2.3333 | thin (Phi = 7/3 exactly, not strict) |
| complete near-miss k=5, n=9 | 9 | 126 | 5 | 9/5 | +0.5333 | 1/5 | 3.2000 | thin |
| complete k=9, n=16 | 16 | 11440 | 8 | 2 | +0.3333 | 1/8 | 2.8750 | thin |
| complete k=13, n=23 | 23 | 1144066 | 11 | 23/11 | +0.2424 | 1/11 | 2.7273 | thin |

(The near-pool rows are the 8 profile families of SATURATION §3: co-edges = all 11-sets with (|K∩A|,|K∩Y|) in P.)

## Findings
- **No stored family is rich.** The best Phi is 7/3 exactly (complete K_21^(10)); every other family has Phi >= 2.45. Theorem 3 closes none of them. With atoms near 1/tau, 7·max y alone is about 0.6, and y(V) is about 2.
- **tau*_b equals n/tau (uniform y = 1/tau is optimal)** for FKW, H1, H1min, FKWmin, G', the complete families, the k=8 `fam_8_6_15` SAT families (except `pool`, `sevenfree`), `tgw` 8_6_*, and 3 of 5 `tgw` 10_8_21 families. It is strictly below n/tau for 6 of the 8 near-pool families (e.g. 13/7 < 21/11, 2 < 7/3), `rand2s1/s2`, the `pool` and `sevenfree` families, and about a third of the rule instances. Over all 101 result rows (including duplicate symmetric/direct runs) 73 have equality. Phi is dominated by the 7·max y term, not by tau*_b.
- **Thin by margin, not by Theorem 3.** tau*_b is below 7/3 for every family except U1 and the three k=10 `tgw` families (exactly 7/3).
- **U1 exceeds 7/3 (533/220 > 7/3).** Padding the 11-members with private fresh points creates extra transversals (those using f_x), so tau*_b rises from 11/5 to 533/220 while tau stays 10. The optimal y puts 1/110 on each fresh point and 0.100-0.111 on old points.
- **Three k=10 `tgw_fam_10_8_21` families sit exactly at 7/3** (margin 0).
- **Not computed: the large rules.** The CORE §56 rules at (k,T,n) = (40,31,74..88) and (100,76,180..210) cannot be enumerated (C(74,31) requests). For any T-covering family, uniform y = 1/(T+1) is feasible, so tau*_b <= n/(T+1): 2.3125, 2.375, 2.5, 2.75 for k=40 and 2.338, 2.468, 2.727 for k=100. These are upper bounds only, with max atom 1/32 and 1/77. Uniform y gives Phi >= 2.53, so they are thin or undecided. They are reported as thin only by analogy with the small-n instances; no lower bound on tau*_b was computed.
- The two stored families at n = 15, 16 that are not (7,2) (FKW m = 2, and the k=8 SAT families) are classified the same way; (7,2) status plays no role here.
