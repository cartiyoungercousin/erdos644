# Programme 5: the region n ≥ 11k/6, (S≥) — exact map, a two-stage dump, non-Fano finishes

Tags: [proved by hand] / [computed] (exact integers unless "grid") / [heuristic] / [open].
Code and logs: `compute/programme5/bulk/` (`logs/`). Nothing committed; LEDGER and Lean644/ untouched.
Units: ν = n/k, σ = ν − 7/4, e = τ − 3k/4 = εk, T = τ − 1, r = n − k − T (so e = s − r + 1).
Nothing here is independently verified. The two new results (§2.1, §3.2) are hand proofs plus exact checks.

## 1. Exact map of (S≥)
### 1.1 Best bound on ε for each ν (asymptotic)
| bound on ε | valid for | source | best on |
|---|---|---|---|
| σ/5 + o(1) | ν ≤ 1.794 (Frankl–Wilson; its other branch s+1−c0k is weaker above 1.80) | Thm 9.6 | ν ≤ 1.7994 |
| 3σ/11 (+21/(11k)) | **ν ≤ 8/3 + 11/(3k)** (was n ≤ 2k) | Thm 9.1 + §2.1 | 1.7994 ≤ ν ≤ 53/24 |
| σ/3 (NC, W = V); 3N/7 − 3/4; one-anchor | all ν | paper | **never best for ν ≥ 7/4 now** |
| 1/8 (+1/k) | all ν | FKW | ν ≥ 53/24 |
- **New** [proved by hand]: for every k, a k-uniform (7,2)-family on n ≤ (8k+11)/3 points has τ ≤ (3n+3k+21)/11 (§2.1).
- **FKW-only threshold: ν\* = 53/24 ≈ 2.2083**, where 3σ/11 = 1/8. Before this it was 17/8 = 2.125 (slope 1/3 for
  n > 2k). The unverified 11k/13 and 6k/7 claims (LITERATURE §5) are not used.
- **Open region** [open]: 0 < ε ≤ 3σ/11 on 11/6 ≤ ν ≤ 53/24 (1/44 at 11/6, 3/44 at 2), and 0 < ε ≤ 1/8 for
  ν ≥ 53/24. Rich families (RA) and blocks of small excess (NC) are excluded at every ν.
- **Cross-check** [computed]. `graded_dump.py` solves an exact integer game over all iterated two-member dumps
  plus P1 (k = 120, 200, 400; ν up to 3; `logs/graded_k*.log`).
  - It follows the 3/11 line to within 1 up to ν ≈ 2.65 and then stalls.
  - The plateau at τ = k + 2 is a T ≥ k artefact, far beyond FKW.
  - At k = 400 it beats FKW exactly for ν < 2.20.
  - So 8/3 is the real limit of two-member dumps, not slack in the proof.
### 1.2 No ν where the problem becomes easy [proved by hand]
- **Padding.** Give every member of a k-uniform (7,2)-family H one new private point.
  - The result is (k+1)-uniform and still (7,2), with the same τ (Lemma 2.1) and n + |H| points.
  - So e drops by 3/4, and ν jumps to ≥ |H|/(k+1), which is exponential in k since |H| ≥ C(n,k)/C(k+r,r).
  - Doing this p = o(k) times keeps ε' → ε.
- **Consequence.** For every ν0 (even ν0 = 2^{o(k)}), (G) restricted to ν ≥ ν0 is **equivalent to all of (G)**:
  every counterexample at any ν reappears at every large ν.
  - So large n cannot force richness, a block, or any compression that counterexamples lack.
  - Any bound ε ≤ f(ν) with f increasing is useless far out. Large ν needs **n-independent** tools: P1, HUB (§3.2),
    FKW's good-triple lemma.
- **Stripping** (the converse). A point of degree 1 can be deleted: (7,2) and τ survive (in a 2-cover, swap it for
  another point of the shrunk member).
  - So (G) is equivalent to (G) for sets of size ≤ k with minimum degree ≥ 2.
  - Nothing cheaper is available: deleting a point of degree ≥ 2 can destroy (7,2), and merging points can lower τ.
  - A reduction of large n to n ≤ 2k would need members enlarged by *shared* new points without lowering τ [open].
- The non-uniform one-anchor bound τ < (2n'+b)/6 + 23/6 (PROGRAMME3_BULK §2.4) is the only known bound that sees
  through padding. It counts only points of degree ≥ 2, and b is the minimum member size.
### 1.3 The strip 11/6 ≤ ν < 2 (coordinator's item (i))
- **Bound there:** ε ≤ 3σ/11, from P1 + the pencil bound [VERIFIED, Thm 9.1]. Frankl–Wilson gives nothing
  (c0(11/6) = 0.040 < 8σ/11).
- **Fano-sufficiency is not the gap for upper bounds.** P1 is Fano-only and needs no classification. Sufficiency
  matters only for "no Fano seven ⇒ (7,2)" tools (coset obstruction, Lemma Q, pencil-sum barrier), and those fail
  here because the four LP-11/6 types appear.
- **Conjecture (F2)** [open]. For large k and n < 2k, a covering family with τ > (3/4+ε)k that has a good seven has a
  Fano-type one. Evidence: 0 non-Fano-only cell families below 2k for k ≥ 9 (PROGRAMME4_CELLS §3b).
  - (F2) would carry the Fano-range structure theory (pencil sums, Theorem D) up to 2k.
  - The coset counting (Cor 7.2) holds only to N < 1.938.

## 2. Extending the pencil machinery (Task 2)
### 2.1 Theorem 2S: two-stage centred dump [proved by hand; conditions checked exactly, k ≤ 120]
**Statement.** Let H be k-uniform and (k+r)-covering on n points, T = n − k − r, 3 ≤ r ≤ 2k − 4, and
**4T ≥ 2k + 3r + 3**. Then H has a pencil of weight ≤ r + D ≤ ⌊3r/2⌋ + 1 (w, D, I* = {h−w..h} as in Thm 9.4).
The paper's conditions were 4T ≥ 2k + 5r + 3 and 3r ≤ 2k − 2.
**Proof.** Paper: 2h ∈ [k − r/2 − 3/2, k − r/2] and w ≤ r/2. Put h' = k − h.
- **Start.** S = (h points of x1) ∪ (k + r − h points off x1); this fits since h ≥ k − T. A member x2 ⊆ S has
  j = |x1 ∩ x2| ∈ [max(0, h − r), h].
- **Intermediate dump.** Lemma 9.3 on (x1, x2) with block [h' − w, h'].
  - j ≤ k − h' = h holds. 0 ≤ k + r − 2h' = 2h + r − k holds since r ≥ 3.
  - k + r − 2h' ≤ n − 2k + j for j ≥ h − r ⇔ T ≥ h + r, true as h + r ≤ k/2 + 3r/4.
  - It gives y with j' = |y ∩ x_i| ∈ [max(0, h' − w), h'], and y ≠ x_i since h' ≤ k − 1.
- **Final dump.** Lemma 9.3 on (x_i, y) with block I*.
  - j' ≤ k − h holds.
  - k + r − 2h ≤ n − 2k + j' for j' ≥ k − h − w ⇔ T ≥ k + w − h, true as k + w − h ≤ k/2 + 3r/4 + 3/4.
  - It gives a pair with intersection in [0, h], and h ≤ T.
- **Finish.** Lemma 9.2 gives weight ≤ r + D. ∎
The *intermediate* dump returns a window of length w ≈ r/2, not r, so the room condition drops from 5r/4 to 3r/4.
**Checks** [computed]:
- `two_stage_check.py 120`: 831 958 cases (k, r, T). All conditions hold when 2k − r ≥ 4; the only failures are
  at r ≥ 2k − 3.
- All 194 171 (n, k, T) above the 3/11 line with n ≤ (8k+11)/3 are covered (cases with r ≤ 2 fall under Thm 9.4).
**Corollary** [proved by hand]. If 11T ≥ 3n + 3k + 11 and n ≤ (8k+11)/3, then 7T ≥ 3n − k + 3 (i.e.
4T ≥ 2k + 3r + 3) and r ≤ 2k/3 + 2. Thm 9.1's lightness step uses only D. Hence τ ≤ (3n+3k+21)/11.
### 2.2 What does not extend
- **More stages** [proved by hand]. The final dump needs a w-window inside G = [2k − T − 2h, k − h], whose length is
  T − k − w + h. So T ≥ k/2 + 3r/4 is forced whatever comes before: 4T ≥ 2k + 3r is the limit (confirmed by §1.1).
- **Three references** [heuristic]. Misses split three ways would give w ≈ r/3, hence slope 1/4.
  - This needs three members with private parts ≥ k/2 − r/3 and union ≤ T + 3h.
  - With r slack per answer, the adversary puts x3 almost inside x1 ∪ x2 (no private part) or almost outside
    (no room). No request schedule tried beats this.
- **Frankl–Wilson (slope 1/5)** needs r ≤ c0(ν)k, which is too small above 1.80.
- Even the sharp PEN* would give slope ≈ 0.18, which beats 1/8 only for ν < 2.46 [heuristic, paper §11(b)].

## 3. Non-Fano sevens (Task 3)
### 3.1 Which types do the work in the cell families [computed]
- `which_types.py` re-tested the 302 distinct non-Fano-only two-cell families of PROGRAMME4_CELLS §3b against
  every type of LP value ≤ 15/8. It uses exact CP-SAT; the cell criterion is symmetric in the 7 labels, so one model
  per class suffices.
- **Result:** 300/302 have a seven of an LP-15/8 class, and 289–293 have a seven of each of the **four LP-11/6
  classes** (430, 574, 675, 707). The 2 exceptions are k = 8, cells (9,9) and (9,10).
- **Structure.** All of these, and class 195 below, are **"Fano minus a line"**.
  - Six Fano co-types (lines) are kept.
  - The line {0,1,2} is replaced by 4-sets 012x and/or other triples (707 = six lines + 012x, x = 3..6, + 3456),
    or, in class 195 (LP value 2), by the four triples of the opposite quadrangle {3,4,5,6}.
  - In seven terms: one colour class misses one extra member.
### 3.2 HUB lemma: n-independent non-Fano analogue of P1 [proved by hand; brute-force tested]
**Statement.** Let H have members of size ≤ k and τ > T. Let x_a, x_b, x_c ∈ H have empty common intersection,
with pairwise-only parts of sizes d_ij. If
**Σ_i max(0, d_ij + d_il − d_jl − (k − T)) ≤ 4T − 3k**   ({j,l} = the other two indices),
then H has a good seven. It is of type 195 (Fano minus a line, LP value 2), not Fano type. No condition on n.
**Proof.**
- Candidate pairs (pairs meeting all three anchors) are D_ij–D_il and E_i–D_jl. Use four blocks:
  - the hub L0 = D_ab ∪ D_ac ∪ D_bc plus spill;
  - L_i = D_jl ∪ (E_i minus spill_i), with spill_i = max(0, |E_i| + d_jl − T).
- Then |L_i| ≤ T, and |L0| = Σ max(0, g_i) + 3(k − T) ≤ T, where g_i = d_ij + d_il − d_jl − (k − T).
- Every candidate pair lies in a block. Each L_g is avoided by a member B_g, and the anchors miss every other pair. ∎
**Special cases.** All d_ij ≤ T/3: the condition holds iff 4T ≥ 3k. If d_ij + d_il ≤ d_jl + k − T for every i, it
holds at T = 3k/4.
**Test** [computed]. `hub_check.py 4000 1` (random pencils, k ≤ 12, n ≤ 4k): 1403 instances satisfy the condition,
0 failures. Each was checked two ways: every candidate pair lies in a block of size ≤ T, and an explicit seven has
no 2-cover (brute force). The two forms of the condition agree throughout.
**Contrapositive.** In a (7,2)-family every pencil has *both* weight ≥ 4T − 3k − 5 (P1) *and*
Σ max(0, g_i) ≥ 4T − 3k + 1 (HUB). So P1 kills pencils with large pairwise parts, and HUB kills pencils with small or
balanced ones.
### 3.3 All static three-anchor finishes: worst pencil 9/10 [computed, grid]
- **Model.** `pencil_cover.py` computes, as a MILP over patterns, the least t for which 4 blocks of mass ≤ t cover
  the candidate pairs of a pencil shape. This equals the minimum over all 715 types and all labellings;
  `anchor3_lp.py` checks it class by class.
- **Values:**
  - Fano gives (3 − Σd)/2.
  - t* = 3/4 at the perfect pencil, at every symmetric d ≤ 1/4, and at disjoint triples.
  - t* = 0.80 at d = 1/3 and 0.84 at d = 0.4.
  - **Maximum over a 1/24 grid: 9/10**, at (0, 1/2, 1/2): two anchors disjoint, the third inside their union
    (Fano needs 1 there).
  - So no static three-anchor argument of any type beats 9/10.
- **Two-request game** (`game3.py`). x2 avoids T points of x1. x3 avoids the pair core plus a + b chosen points. The
  adversary picks the intersections in its box, and the finish is static.
  - At t = 7/8 the value is 15/16 [grid 1/6, 4 values of d12]. The adversary plays d12 = 0 and
    |x3 ∩ x1| = |x3 ∩ x2| = 9k/16.
  - So FKW's 7/8 needs adaptive *finishing* requests as well. The t = 0.85 run was stopped as moot.
### 3.4 Where a P1-like lemma would have to come from [heuristic / open]
- Covering forces d12 ≤ k − T. The adversary then places x3 freely in its box, since room is no constraint at large n.
- The worst answers (x3 split evenly over x1 and x2; the (0, 1/2, 1/2) shape) defeat P1, HUB and every other
  static type below 15/16 (resp. 9/10).
- **Next target [open]:** a four-anchor n-independent finish (co-type of Z a 4-set of the type), or adaptive finishes
  of type 195 or 11/6, for exactly those shapes.

## 4. Files (`compute/programme5/bulk/`)
`graded_dump.py`, `two_stage_check.py` (§1.1, §2; `logs/graded_k120,200,400.log`, `logs/two_stage_check_120.log`) ·
`nonfano_types.py`, `which_types.py` (§3.1; `logs/nonfano_types.log`, `logs/which_types_15_8.jsonl`) ·
`anchor3_lp.py`, `pencil_cover.py`, `game3.py`, `hub_check.py` (§3.2–3.3; `logs/anchor3_12_1.log`,
`logs/pencil_cover_12.log`, `logs/game3.log`, `logs/hub_check.log`).
