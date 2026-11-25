# PROGRAMME_2 Task 4: measuring the bridge (D2)

Status: **MEASUREMENT, computed**; nothing here is proved. Notation as in `PROGRAMME_2.md`. Edges are the k-sets (co-edge files are complemented). C(H) is the span of pairwise symmetric differences, and ρ = min wt(a + C(H)) for a in H. T = τ − 1, the largest T for which H is T-covering. τ comes from the exact transversal oracle of Task 1; for the two n = 34 families τ = 10 is taken from Task 1's table, because the ILP timed out here. Code and raw output are in `compute/programme2/task4/` (`out/measure.jsonl`; `out/table.md` has every row). Rich/thin labels are NOT attached (Task 1 is separate). The column that matters below is "has a Fano-type good seven".

## Methods (exact unless marked)
1. dim C by Gaussian elimination. **ρ is exact** (enumeration of the coset when dim C ≤ 26, otherwise MILP). The parity checks of C are listed ("all" is the all-ones check, trivial for even uniform k).
2. Least wt(x1+x2+x3) over triples with x1∩x2∩x3 = ∅.
   - Upper bound: a deterministic sample (exact for ≤ 500 members).
   - Lower bound: ρ, since a triple sum is an odd sum.
   - For even uniform k the value is even. For 4T−3k = 0 a "pencil-shape triple" is exactly a triple with x1+x2 = x3. These were **counted exactly** for ≤ 5000 members.
3. Fano-type seven.
   - Random balanced colourings, with the Lemma 2 test exact and coordinate descent on Σ_p wt(s_p). The identity Σ_x j_x(4−j_x) is asserted for every reported seven.
   - For families where that found nothing, simulated annealing over arbitrary colourings (`fano_ls.py`). Cost 0 is an exact certificate of a seven; failure proves nothing.
   - Lemma 5's bound 3(4|∪B|−Σ|B|) holds for every seven, so the informative comparison is with 7ρ (each s_p is an odd sum when all members lie in one coset).
4. Coset fraction. Walsh transform over all functionals u (n ≤ 25). The majority side of u is a subfamily H′; report |H′|/|H| and ρ(H′). `coset_scan.py` takes the best of the top 25 functionals subject to ρ(H′) > max(4T−3k, 0).
5. Affineness of pencil-free selectors.
   - Walsh transform of the stored selector.
   - Exact SAT (CaDiCaL): does some AFFINE selector σ(S) = c0 + ⟨c, 1_S⟩ leave the same orders pencil-free? (`selectors.py`)

## Table (condensed; budget = 3(4n−7k))
| family | n | #H | k | τ | dim C | ρ | 4T−3k | min triple | budget | 7ρ > budget | seven | Fano min Σwt |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| FKW m=2 (n=7m+1) | 15 | 3200 | 8 | 7 | 13 | **2** | 0 | 2 (exact) | 12 | yes | none (Cor. 7, exact) | – |
| FKW m=3 | 22 | 323344 | 12 | 10 | 20 | **2** | 0 | 2 (exact) | 12 | yes | none (Cor. 7, exact) | – |
| control FKW m=2, n=7m+2 | 16 | 6400 | 8 | 8 | 14 | 2 | 4 | 2 | 24 | no | yes | **14 = 7ρ**, all s_p of weight 2 |
| control FKW m=3, n=7m+2 | 23 | 675808 | 12 | 11 | 21 | 2 | 4 | 2 | 24 | no | yes | **14 = 7ρ** |
| H1 | 22 | 323236 | 12 | 10 | 21 | 1 (2 without the 12 sets of size 11) | 0 | ≥ 1 | 12 | no | none (annealing) | – |
| G′ and 9 H1min variants (task3) | 22 | ~1.0e5 | 12 | 10 | 21 | 1 (2 likewise) | 0 | ≥ 1 | 12 | no | none (annealing on G′; random on the rest) | – |
| fkwmin_random_1 | 22 | 100524 | 12 | 10 | 20 | **2** | 0 | 2 | 12 | yes | none (random) | – |
| U1 = pad(G′), pad(H1min) | 34 | ~1.0e5 | 12 | 10 | 32 | **2** | 0 | 2 | 156 | no | none (random only) | – |
| core9 `fam_8_6_15_rev` (SAT, R=2) | 15 | 2352 | 8 | 7 | 13 | **2** | 0 | 2 (0 pencil triples) | 12 | yes | none (annealing) | – |
| SAT pencil-free (8,6,15), R=3 rand 1 | 15 | 2348 | 8 | 7 | 13 | **2** | 0 | 2 (0 pencil triples) | 12 | yes | none (annealing) | – |
| core12 `tgw_fam_8_6_15` | 15 | 2352 | 8 | 7 | 14 | 0 | 0 | 2 (0 pencil triples) | 12 | no | none (annealing) | – |
| SAT pencil-free (8,6,17), R=2 rev | 17 | 1433 | 8 | 7 | 16 | 0 | 0 | 2 (0 pencil triples) | 36 | no | **yes (annealing)** | not minimised |
| SAT pencil-free (8,6,17), R=3 rand 1 | 17 | 1578 | 8 | 7 | 16 | 0 | 0 | 2 | 36 | no | yes | 22 |
| SAT pencil-free (8,7,16), R=2 rev | 16 | 4917 | 8 | 8 | 15 | 0 | 4 | 2 | 24 | no | yes | 14 |
| pool, randdump, tgw_8_6_16 (k=8) | 15–16 | 2814–3599 | 8 | 7 | 13–15 | 0 | 0 | 0 (many pencil triples) | 12–24 | no | yes | 0 |
| entropy `sevenfree` | 15 | 1287 | 8 | 6 | 12 | 0 | −4 | 0 | 12 | no | none (it is K_13^(8): points 0 and 1 are avoided) | – |
| tgw k=10 (five families) | 21 | 2.3e4–5.4e4 | 10 | 9 | 19–20 | 0 | 2 | 0 | 42 | no | yes | 6–12 |
| tgw k=13 | 25 | 1172984 | 13 | 11 | 24 | 1 | 1 | 1 (exact) | 27 | no | yes | 7 = 7ρ |
| near-pool (10,8,21), 8 profiles | 21 | 4.4e4–3.5e5 | 10 | 9–12 | 17–20 | 0 | 2–14 | 0 | 42 | no | yes | 6 |
| hash/greedy rules of CORE 56, 60 families | 15, 16 | 2083–5875 | 8 | 7 | 13–15 | 0 (all 60) | 0 | 0 | 12, 24 | no | yes in 60/60 | 0 in 45, 6–10 in the rest |
| complete K_9^(5), K_16^(9), K_23^(13) | 9–23 | – | 5, 9, 13 | 5, 8, 11 | n−1 | 1 | 1 | 1 | 3 | yes | none (degenerate: odd k, all-ones coset) | – |

"Pencil triple" means x1+x2 = x3. For (8,6,17) the SAT's "pencil-free" concerns perfect pencils (weight 0) only. For 4T−3k = 0 that is the whole shape (b). For 4T−3k > 0 (the (8,7,16) row and k = 10, 13) shape (b) allows weights up to 4T−3k, and every family there has a triple of weight ≤ 4T−3k (2, 0, 1).

## Findings
**(1) dim C, ρ.** Every family with no Fano-type seven found is an exact coset family, or one after deleting at most 12 members. That is 18 stored families.
- Exact, ρ = 2: FKW m=2, 3, fkwmin, core9 `fam_8_6_15_rev`, the R=3 SAT family at (8,6,15), and the two U1 (7 families). Codimension 2: parity of the whole set and parity on one block, i.e. FKW's "odd on X and odd on Y".
- H1, G′ and the 8 H1min variants (10 families) lie in {odd on X} (codim 1, ρ = 1). Deleting the 12 members of size 11 gives ρ = 2.
- `tgw_fam_8_6_15` has all but ONE member (2351 of 2352, dim 13) in a ρ = 2 coset.
- Every family with a seven found has ρ = 0, except the k = 13 family (ρ = 1) and the controls (ρ = 2, 4T−3k = 4).

**(2) triples vs 4T−3k.**
- In all families without a seven, 4T−3k = 0 and no triple has weight 0. The exact count of x1+x2 = x3 is 0 for ≤ 5000 members, and ρ ≥ 1 for the rest. So min triple weight is 2 > 0 = 4T−3k.
- In every family with a seven, min triple ≤ 4T−3k.
- No family has 4T−3k > 0, no triple of weight ≤ 4T−3k, and no seven. The data say nothing about the 4T−3k > 0 regime for seven-free families.

**(3) pencil sums.**
- Controls (FKW at n = 7m+2, where Cor. 7 allows a seven): the best Fano-type seven found has all seven s_p of weight exactly 2 = ρ, so Σ = 14 = 7ρ against budget 24 (m = 2, 3).
- k = 13: Σ = 7 = 7ρ against budget 15.
- Where a coset obstruction exists the sevens sit exactly at 7ρ, and the slack is only in the budget.
- All other families reach Σ ≤ 12 (k = 8) or 6 (k = 10), often 0.

**(4) affine selectors (R = 2, exact for these orders).**
| case | stored selector vs best affine | SAT: pencil-free affine selector exists |
|---|---|---|
| (8,6,15) rev | **exactly affine**: σ(S) = parity of \|S ∩ {0..7}\| (+ const), agreement 1.0 | **yes** |
| (8,7,16) rev | 0.9997 (3 of 11440 T-sets differ), same u = {0..7} | **yes** |
| (8,6,17) rev | 0.733 | **no** (UNSAT, 4 s) |

For R = 3 at (8,6,15) the class-0 indicator is 0.997 affine (the other two classes are uninformative; class 2 has 3.7%). At (8,6,17) no class is affine. This matches CORE 48.4: parity selectors are the two cosets of one hyperplane. Such a selector really is pencil-free at (8,6,15) and (8,7,16), because the slack ωk is too small for the junk-point flip. It is not pencil-free at (8,6,17).

**(5) coset fraction (`coset_scan.py`, 92 families, n ≤ 22).** Largest fraction of H on the majority side of one functional with ρ(H′) > max(4T−3k, 0):
- No seven found: 1.0 (exact coset) for FKW, H1, G′, H1min, fkwmin, core9; **0.99957** for `tgw_fam_8_6_15`.
- Seven found:
  - the 60 hash/greedy families: ≤ **0.835**;
  - the SAT (8,6,17) families: 0.871–0.873 (greedy chain; `coset_scan.py` was not run on them);
  - near-pool and tgw k = 10: 0, since their dense cosets have ρ′ = 0 or ρ′ ≤ 4T−3k;
  - tgw_8_6_16: ≤ 0.63.

## The strongest inverse statement the data support
> **(INV, 4T−3k = 0, k = 8..12)** Among the stored families, the 18 with no Fano-type good seven found (n = 15, 22, 34) have at least 1 − 12/|H| of their members in one coset a + C′ with ρ = 2 > 0 = 4T − 3k; 7 are exact cosets. No stored family with a seven has even 0.9 of its members in such a coset (max 0.873). So "thin, no pencil, no seven ⇒ most members in one coset with ρ > 4T−3k" is **not refuted**, and with "most" ≥ 0.9 it separates the two classes in the data.

Caveats:
- All seven-free instances have 4T−3k = 0. There ρ > 0 only says that H avoids the zero-sum coset, i.e. one non-trivial parity check. The statement is weak there. A seven-free family with 4T−3k > 0 (the case that matters for D1/c*) is not among the stored families; the k = 10 and 13 families all have sevens.
- Seven-freeness is certified exactly only for FKW (Cor. 7). For the rest it means "not found", by random balanced colourings and then annealing. Balanced colourings miss sevens: the (8,6,17) R=2 family has 0 of 1500 balanced successes, yet annealing finds a seven in 11 restarts. The n = 34 and fkwmin rows rest on random colourings only.
- The seven-free families are few and partly constructed (FKW by theory, H1 by minimisation, three SAT/tgw outputs at one parameter set). The only generic producer, the SAT selectors, gives affine, coset-structured output at n = 15, and non-affine output with a seven at n = 17.
- Thin/rich labels are not applied here. Task 1's `results.jsonl` marks all families listed above as not rich.

**D2 reading.** The stored thin pencil-free families without a seven are close to linear (an exactly affine selector at (8,6,15); coset families up to O(1) members). The hash-like thin families are NOT close to linear, but they have sevens. So the bridge step reduces to: a pencil-free thin family without a seven lies within o(|H|) members of one coset with ρ > 4T−3k. The first thing to test is a seven-free example with 4T−3k ≥ 2, e.g. the SAT of `core9/two_ground_sat.py` at such (k,T,n) together with `selectors.py` and `fano_ls.py`.

## Reproduction
Run from `compute/programme2/task4/` with `py -3.14`:
- `run.py fkw ctrl h1 task3 k8 u1 hash nearpool complete` (measure; appends to `out/measure.jsonl`)
- `coset_struct.py`, `coset_scan.py`
- `selectors.py k T n R mode [seed]`, `sel_measure.py k T n R mode [seed]`
- `fano_ls.py case`
- `table.py`

It reuses Task 1's `families.py` and `tau_star.py` read-only.
