# STABILITY_DATA: testing the bridge C as a stability statement (PARTIAL, in progress)

Status: **INCOMPLETE.** Tooling is built and validated; the family generation is slow and only a handful of families are measured. No distribution claim is made. Nothing committed. Code and raw output: `compute/stability/` (`out/results.jsonl`, `fam/*.npy`).

## Tools (compute/stability/)
- `common.py`: exact (7,2) test. H is not (7,2) iff 7 members have complements covering all pairs, i.e. min set cover of the pairs by complements is <= 7. Certified by a HiGHS set-cover ILP (status optimal). Numba DFS (`pc72.py`) and SAT (`vt.py`) exist but proving UNSAT was too slow on n = 15 families. tau by ILP, cross-checked by bitset enumeration. Coset distance: best-first restriction search; rho >= 1 is solved EXACTLY by the Walsh transform (H' has rho >= 1 iff it lies in {w.x = 1}), rho >= 2, 3 are lower bounds. Per best coset: codimension, dim C, rho, dual distance d-perp of C.
- Generators: `gen_greedy.py` (random greedy, every added set exactly certified), `topdown.py` (tau-constrained removal from complete / random / FKW + extra sets until no seven; local search maximising tau), `gen_sat.py` (CEGAR SAT for "(7,2) and tau >= T").
- `analyze.py`: certification + tau + coset measures per family.

## Results so far
| family | n,k | #H | tau | (7,2) | best coset fraction (rho>=1 exact; rho>=2) | codim, rho, d-perp of best coset |
|---|---|---|---|---|---|---|
| complete K_13^(8) | 13, 8 | 1287 | 6 = 3k/4 | **yes (min cover 10)** | 0.615 ; 0.615 | 2, 2, 1 |
| random greedy, one seed | 14, 8 | 162 | 4 | yes | 0.660 ; 0.660 | 2, 2, 1 |
| FKW m=2 | 15, 8 | 3200 | 7 | **ILP says NO (min cover 7)** | 1.0 ; 1.0 | 2, 2, 7 |

Findings:
1. **Stability counterexample at the boundary.** The complete family K_n^(k) with n < 7k/4 is (7,2) (n - k < 3n/7 defeats every Fano colouring) with tau = n - k + 1 about 3k/4 + 1. For k = 8, K_13^(8) has tau = 6 = 3k/4 exactly, is (7,2) (exact), and has at most 61.5% of its members in any rho >= 1 coset (exact). So the statement "(7,2) and tau >= (3/4 - gamma)k implies near-coset" is FALSE at gamma = 0 for k = 8; it can only hold above 3k/4. Same construction for every k.
2. **FKW m=2 is not (7,2)**: the ILP's 7-cover was re-checked directly (seven 8-sets with no 2-point transversal). This agrees with PROGRAMME2_TASK1.md; not new. At n = 15 > 11k/6 good sevens need not be Fano-type, and Cor. 7 only excludes Fano-type ones. So no certified (7,2) family with tau > 3k/4 exists in this data.
3. Random greedy gives tau = 3 to 4, far below 3k/4: typical (7,2) families are low-tau and far from cosets (rho >= 1 fraction about 0.66).
4. Top-down removal from complete families on n = 15 with target tau >= 7 got stuck on every seed (the remaining family still has a seven); with target tau >= 6 two runs reached 660 and 706 members with no Fano colouring but the ILP certificate timed out (uncertified). Nothing at tau >= 7 was certified.
5. Codimension (coordinator request): every measured best coset has codim 2 (FKW d-perp 7; the low-tau ones d-perp 1, i.e. coordinate-type cosets), so no evidence yet of large-codimension structure; not enough data to conclude.

## Uncertified measurements (ILP timed out, (7,2) not established; coset data only)
| family | n,k | #H | tau | rho>=1 fraction (exact) | codim, rho, d-perp |
|---|---|---|---|---|---|
| top-down from complete, T=6, seed 1 | 15, 8 | 660 | 6 | 0.580 | 2, 2, 2 |
| top-down from complete, T=6, seed 2 | 15, 8 | 706 | 6 | 0.613 | 2, 2, 1 |
| top-down from complete, T=7 (stuck, a seven remains) | 15, 8 | 1301 | 7 | 0.553 | 2, 2, 6 |
| FKW + 30% extra sets, T=7 (stuck, a seven remains) | 15, 8 | 1294 | 7 | 0.821 | 2, 2, 7 |
| complete K_17^(10) (tau 8 > 3k/4 = 7.5; (7,2) not certified) | 17, 10 | 19448 | 8 | 0.588 | 2, 2, 1 |

All are far from a coset (best fraction <= 0.82). Run stopped here at the coordinator's request.

## Not done
k = 10, 12, 16 families; SAT method (15,8,7 timed out after 8000 CEGAR iterations); distribution and threshold; exact certification of the top-down outputs. Bottleneck is exact (7,2) certification at n >= 15 (ILP and DFS/SAT take minutes to hours).
