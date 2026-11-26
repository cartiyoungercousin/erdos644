# Programme 5: spectrum forcing and drop finishes at the critical bridge triple — partial (run cut short)

Tags: [proved by hand] / [computed exact] / [computed, grid] / [heuristic] / [open]. Units: k/14 unless stated, so
members have size 14, t = 12 − δ. Code and logs: `compute/programme5/spectrum/` (`logs/`), `py -3.14`.
The run was cut to 2 cores and about 30 minutes by the coordinator, so less than 15 core-minutes of compute were used.
Nothing committed; LEDGER, Lean644/ and notes/sources/ untouched. Nothing here is independently verified.

## 0. Headline (pre-registered form)
**CAPPED AT 6/7 INCLUDING SPECTRUM, for the closure class "class-A first request, keep E, F, G, K, then three later
answers in a near-rigid cover" (route A)** [proved by hand, §2; level-1 legality computed exact on grids, §3].
- No closure was found, so the S-game was not rerun and t* stays 6/7.
- Route B [computed, grid]: dropping any one of E, F, G and keeping K gives no closing triple (§4).
- Not decided [open]:
  - route A, general off-rigid play. The spectrum DOES force answers off passive play there (§3), so it is the one
    live lead;
  - route A, class B with the spectrum;
  - route B beyond the triple-table test (exhaustive 7-of-9 selection).
- Hence no claim covers all closures.

## 1. Setting
- Critical triple at t = 12 − δ: X = E∩F = 6, Y = E∩G = 5, Z = F∩G = 0⁺, E' = 3, F' = 8, G' = 9. These limit-point
  cells form a valid critical triple for every small δ > 0.
- S* (G = 168, t ∈ [.855, .857]) = [0, 45] ∪ [60, 73] ∪ [80, 167] / 168. In units of k/14 that is
  [0, 3.75] ∪ [5, 6.083] ∪ [6.667, 14). S* is only known for t ≥ .855, so δ ≤ .03 and his slack 3δ is at most .09.
- Class A, R1 = X ∪ Y ∪ Z + (e, f, g). He answers with Theorem P's K = B ∪ A, where |B| = β ⊆ F' ∖ R1,
  |A| = α ⊆ G' ∖ R1 and α + β = 14. Its traces are (E, F, G) = (0, β, α).
  - **K is S*-legal** [proved by hand]: take α ∈ [max(6.667, 6 + f), 7). This is always non-empty since f ≤ 1 − δ.
    Then β ∈ (7, 7.333], and x + α > t, y + β > t, α ≥ x, β ≥ y all hold.
  - So the spectrum never blocks Theorem P's first answer.
- After K: live X×A ∪ Y×B. Dead cells: E' = 3 (E), Fd = 8 − β (F), Gd = 9 − α (G), Z, and outside (unlimited, ν = ∞).
- **Effective kill.** For a later answer M, eff(M) = φ(X∖M, A∖M) + φ(Y∖M, B∖M), where φ(u, w) = u + w if both are
  non-empty, and 0 otherwise.
- **Accounting.** By the biclique lemma, three kept later answers close only if Σ eff ≥ 2x + 2y + α + β = 36.
  So eff ≤ t for each answer caps the frame (E, F, G, K + three later answers) at every depth (Theorem P).

## 2. Rigidity: forcing cannot reach a near-rigid cover [proved by hand]
- **Rigid cover.** Equality in the biclique lemma forces:
  - every point of X to lie in the same two sets, with A split between those two sets; likewise for Y and B, on a
    different pair. (If one X-point uses {1, 2} and another uses {1, 3}, then A ⊆ S1, so |S1| ≥ x + α > t.)
  - Hence, with slack O(δ): S1 ⊇ X ∪ Y + (a1, b1), S2 = X ∪ A2 with a2 = 6, S3 = Y ∪ B3 with b3 = 7, where
    a1 = α − 6 and b1 = 7 − α.
  - Each request of a closure must contain X or Y in full, up to O(slack).
- **Passive traces of the three answers, at δ = 0:**

| answer | E | F | G | K | pairwise with the others |
|---|---|---|---|---|---|
| M(S1) = A2 ∪ B3 | 0 | 7 | 6 | 13 | M1∩M2 = B3 = 7 |
| M(S2) = Y ∪ A1 ∪ B | 5 | β ∈ (7, 7.33] | α − 1 ∈ [5.67, 6) | 8 | M1∩M3 = A2 = 6 |
| M(S3) = X ∪ A ∪ B1 | 6 | 13 − α ∈ (6, 6.33] | α | 7 | M2∩M3 = 1 |

- Every entry is in S* or can be lifted into S* by padding.
  - 13 − α is lifted by ≤ .58 of Fd (Fd = α − 6 ≥ .67).
  - Values in (6.083, 6.667) are lifted with Gd or E' (≥ 2 available).
  - Each answer has ≥ 1 of outside room.
- The K-trace has no pads, but it is 14 − |R∩(A∪B)|. This is ≥ 8 when R ⊇ X and ≥ 7 when R ⊇ Y, so it never
  reaches the K-gaps (3.75, 5) or (6.083, 6.667) inside a rigid cover.
- Margins to a forcing zone are ≥ .083 (for example G-trace 6 vs 6.083 in S1) or are pad-fixable. Steering a trace into
  a gap needs Θ(1) of request off the rigid sets. That costs more than the forced drop it buys: at most .25 for E/F/G
  traces with pad room 1, at most .58 or 1.25 for K.
- **Last answer.** It only needs to keep one point (0⁺) of some still-uncovered vertex class, so a forced *partial*
  drop in the last answer never gives closure. Drops help her only in earlier answers.
- **Conclusion (near-rigid class).** The S*-legal passive adversary (pads with dead or outside points, no live drops)
  answers all three structural requests legally with eff ≤ t. So the cover is short by 3δ, exactly as in Theorem P.

## 3. Level-1 legality, exact MILP per request [computed exact, grid]
- `level1.py alpha h delta`. For every request R after K, the script finds his legal answer minimising eff, by MILP.
  - Binaries: the S* interval of each of the four traces, and φ switches.
  - Live cells on grid h, the remainder fills t; dead cells are requested 0 or in full.
  - Parameters: α = 6.75, δ = .02.

| grid h | requests | min-eff > t forced | max excess | among R ⊇ X or R ⊇ Y |
|---|---|---|---|---|
| 1 (= k/14) | 5432 | 141 | 1.25 at R = (X 2, Y .73, A 2, B 7.25) | 21, max .27 at R = (X 6, Y .98, A 2, B 3) |
| 0.5 (= k/28) | 35133 | 1494 | 1.25 (same R) | 78, max .27 at R = (X 1.5, Y 5, A 2.5, B 2.98) |

- The rigid requests (X∪Y + .75A + .23B; X + 5.98A; Y + 6.98B) all have excess 0.
- **Spectrum forcing is real.** Off the rigid cover she forces answers off passive play by up to 1.25 (the depth of
  the K-gap (3.75, 5)). For example R = (2.5, 2, 4, 3.48) forces eff = 12.42 > t.
  - The worst case pushes the K-trace 14 − rA − rB into a gap. K has no dead points, so he must drop live
    K-points, and with rX, rY > 0 every drop counts.
  - So "eff ≤ t for every request" is FALSE, and Theorem P alone does not cap the spectrum game.
- **Open point.** The 21 structural forcers keep X (or Y) whole but waste ≥ 1 of request on the wrong hub or on too
  little A/B. Is that waste always ≥ the forced excess inside any three-set cover (quantified rigidity)? Hand estimate
  [heuristic]: yes, by a factor of at least 3. Not proved, and not computed beyond level 1 [open].
- 1/42 grid, α = 6.9 and the alternative branch α ∈ (6, 6.083]: not run [open].

## 4. Route B: drop E, F or G and keep K [computed, grid]
- Dropping a member turns K into an anchor. The new triples are:
  - (F, G, K) = (Z, B, A) = (0⁺, β, α);
  - (E, G, K) = (Y, ∅, α);
  - (E, F, K) = (X, ∅, β).
- If the S-game closure table closes any of them, she wins (a sound lemma, depth ≤ 1 + 3). The table covers static
  t*_+, Lemmas 4.1–4.7 with S* gaps, and the heavy route; β > 1/2 makes the heavy route relevant.
- `routeB_triples.py 168 0.8557` (S* recomputed: [0-45, 60-73, 80-167]/168, adversary wins) checks every legal
  Theorem-P K, α ∈ {72, 73, 80..84}/168. **None of the 7 × 3 drop triples closes.** The critical triple does not
  close either. So Theorem P's K also survives every drop finish that keeps K plus two of E, F, G and closes by an
  S-game lemma.
- An exhaustive depth-≤3 selection of 7 from 9 members (E, F, G + six answers) was not run [open].

## 5. What is ruled out, and the seed
- Ruled out [proved by hand]:
  - class-A first request; Theorem-P K (S*-legal);
  - kept seven E, F, G, K + three later answers whose requests form a near-rigid cover (slack ≤ the .083 margins);
  - any depth, with the adversary's answers S*-legal.
- **Live lead [open].** Off-rigid requests do force drops of up to 1.25 (§3). A win needs a cover that uses ONE
  forcing request and loses less to waste than it gains. Next steps:
  - a joint MILP over (R1, R2, R3) with his answers fixed to the level-1 minimisers;
  - then a depth-2 run with exact L.
- **Counterexample seed, if the cap holds.**
  - A family with spectrum ⊆ S*, containing a bridge triple: |E∩F| = 3/7, |E∩G| = 5/14, F∩G tiny.
  - Two near-disjoint "regions" F, G. Every answer to a hub-complete request is a K = (≈ 1/2 of F' ∪ ≈ 1/2 of G')
    with G-trace ∈ [10/21, 1/2).
  - All later members meet K in ≥ 1/2, or in ≤ .268.
  - At finite k this means all pair intersections avoid (.268k, 5k/14) and (.435k, 10k/21). The family is two
    clusters joined by bridges, with medium feet of size ≈ 5k/14.

## 6. Files (`compute/programme5/spectrum/`)
- `level1.py`: exact per-request MILP.
- `routeB_triples.py`: S-game table test of the drop triples.
- Logs: `logs/level1_a6.75_h1.log`, `logs/level1_a6.75_h0.5.log` (may be partial),
  `logs/routeB_triples_168_0.8557.log`.
