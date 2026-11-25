# Verification: PROGRAMME2_NC.md (Lemma NC1, Theorem NC, Corollary NC, NC0, E_k)

Adversarial check of the exact statements in §2, §3 and §5.1, 2026-11-25. The code is fresh and does not import
`compute/programme2/NC`: `compute/programme2/verify/nc_verify.py`, `nc_targets.py`, `nc_nc0.py`, `nc_linear.py`,
`nc_seam_sat.py`. Logs are in `compute/programme2/verify/out/nc_*.log`. Convention: (7,2) means every subfamily of
**at most** 7 members has a ≤2-point transversal, as in `HasPropertyAtMost` (Lean644/Statements.lean).

## Verdicts
| Item | Verdict |
|---|---|
| Lemma NC1 | **PASS** |
| Theorem NC | **PASS** under the at-most-7 convention. Under the exactly-7-distinct wording it is FALSE for \|H\| ≤ 6 (see 2). |
| Corollary NC, as literally stated (τ > (3/4+ε)k) | **GAP** (rounding): Theorem NC does not imply it when k is odd. Fine with the note's own convention τ ≥ T+1. |
| NC0(a), NC0(b) | **PASS** |
| E_k is (7,2) with τ = 3k/4 | **PASS** (hand proof checked; exact at k = 4; ILP at k = 8, 12) |

## 1. Lemma NC1: PASS
- **Fano.** Pairs {13}, {45}, {62} lie on lines 013, 450, 602. Each of 124, 235, 346, 561 takes exactly one point of each
  pair. Checked in code (`fano_sanity`).
- **Lines through 0.** L = C₀ ∪ X_s, and G_s ∩ C₀ = ∅ and G_s ∩ X_s = ∅ by construction. So G_s closes the line.
- **Lines avoiding 0.** |L∩W| ≤ Σ_s ⌈|X_s∩W|/2⌉ ≤ (|W∩∪G| + 3)/2 ≤ w−k−d. Points of X_s∖W and C₀∖W never enter the
  W-count. So |W∖L| ≥ k+d, and (W,d)-completeness puts a member inside W∖L. The four members exist. They need not have
  size k, and they need not be distinct from each other or from the G_s.
- **Boundary.** The bound 2(w−k−d)−3 is exactly what ⌈·/2⌉ rounding allows. The hypothesis w ≥ k+d+2 only makes the
  bound ≥ 1.
- **Distinctness.** The seven may repeat. That is harmless under at-most-7, and also under exactly-7 once \|H\| ≥ 7,
  since one can pad with other members.
- **Computed.** 1,003 instances met the hypothesis: 746 random (`nc_verify` rand) and 257 adversarial (`kill`).
  - The proof's colouring was rebuilt each time, with every line checked to be closed and \|L∩W\| ≤ w−k−d.
  - A good seven was found by independent SAT in every case. 0 failures.
  - SAT and exhaustive 7-subset search agree on 200 random small families.

## 2. Theorem NC: PASS (statement as in §3)
- **Choice of A.** a ≤ w ⟺ w ≥ k+d+3/2, which holds.
- **Deletion.** τ(H_A) ≥ τ − a > (k+1)/2, so H_A ≠ ∅.
- **Lemma A0** needs only nonempty members of size ≤ k, which H_A has. Its proof (\|B₁∩B₂\| ≥ τ, then any (\|B₁\|−τ+1)-subset
  of B₁ is a transversal) checks. 3,000 random 3-wise intersecting families gave 0 violations, but these are weak tests
  (mostly stars).
- **Covering does not need to survive deletion.** NC1 is applied to H itself, with the same W and the same d. Only the
  triple comes from H_A. Points of A lie outside ∪G and so get colour 0. Lines avoiding 0 contain no A-points, so
  W∖L ⊇ A, which is fine.
- **W-trace.** \|W∩∪G\| ≤ w − a ≤ 2(w−k−d)−3 ⟺ a ≥ 2k+2d+3−w. ✓
- **"In points" form.** (k+1)/2 + 2k+2d+3−w = 3k/4 + 2d − (w−7k/4) + 7/2. ✓
- **Computed.** 526 instances met the hypothesis exactly (351 random, 175 adversarial). 0 failures.
  - The adversarial mode raised τ by repeatedly adding a member that avoids the current minimum transversal. Each such
    member has large W-trace plus 1..k/3 outside points.
  - In every instance a random A of size a was deleted, A0 produced a triple, its W-union met the bound, and the
    colouring closed all 7 lines.
- **Threshold is not sharp.** 103 snapshots sat just below the threshold, and none of them was (7,2).
- **Convention caveat.** H = {{1},{2},{3},{4},{5},{6,7,8}}, k = 3, W = [8], d = 0.
  - H is (W,0)-complete and τ = 6 > (k+1)/2 + a = 3.
  - It has 6 members, so it is vacuously (7,2) in the exactly-7-distinct wording (`HasProperty`). Theorem NC is false in
    that wording. It holds in the repo's at-most-7 form, or under the wording with \|H\| ≥ 7.

## 3. Corollary NC: GAP (rounding), otherwise PASS
- **Proof's equivalence.** (3/4+ε)k + 1 > (k+1)/2 + 2k+2d+3−w ⟺ w > (7/4−ε)k + 2d + 5/2. ✓ It uses τ ≥ (3/4+ε)k + 1,
  which is the note's notation τ ≥ T+1, T = ⌈(3/4+ε)k⌉.
- **Literal statement fails to follow.** Assume only integer τ > (3/4+ε)k, i.e. τ = ⌊x⌋+1 with x = (3/4+ε)k. Then
  Theorem NC fails to apply exactly when k is odd, frac(x) ≥ 1/2 and w = ⌈(7/4−ε)k + 2d + 3⌉.
  - The case is realizable: K_10^(5), K_17^(9) and K_24^(13) (4n = 7k+5) meet the literal hypotheses, but neither Theorem
    NC nor NC1 applies to them.
  - They are not counterexamples: each has a good seven, found by ILP and pair-checked.
- **Fix.** State τ ≥ ⌈(3/4+ε)k⌉ + 1, or require w ≥ (7/4−ε)k + 2d + 7/2.
- The implicit condition w ≥ k+d+2 holds for ε ≤ 3/4 + (d+1)/k.

**Parameter range** (w = (7/4+δ)k; the corollary needs d ≤ d_max := ⌊((ε+δ)k − 3)/2⌋):

| k, ε | w ≥ (d = 0 / 1 / 5) | d_max at δ = 7ε/3 | NC alone covers δ ≥ 7ε/3 − η′ iff |
|---|---|---|---|
| 100, 0.05 | 173 / 175 / 183 | 6 | d ≤ (5ε/3 − η′/2)k − 3/2 ≈ 6.8 − 50η′ |
| 1000, 0.01 | 1743 / 1745 / 1753 | 15 | d ≲ 15 − 500η′ |
| general | (7/4−ε)k + 2d + 3 | ⌊(10εk/3 − 3)/2⌋ | d < (5ε/3 − η′/2)k − 3/2 |

- **Against RA.** There is no gap at δ ≈ 7ε/3 **provided d < (5ε/3 − η′/2)k − 3/2**. §0's sentence "includes the whole
  range from 7ε/3 − η′ upward" silently assumes this.
- For larger d there is no RA fallback either. RA (Theorem 3) needs V = W, up to O(1) points, and does not use d.
- The branch as defined in §7 (C₂) builds \|W\| ≥ (7/4−ε)k + 2d + 3 into "near-complete", so "C₂ ⟺ C" is correct, but it
  is true by definition.

**Not covered; these stay inside C:**
- (W,d)-complete with d > (w − (7/4−ε)k − 3)/2, i.e. w < (7/4−ε)k + 2d + 3;
- the fraction form with constant ξ for (7/4−ε)k ≤ w < (7k+18)/4 (NC0(b) needs w ≥ (7k+18)/4);
- every k-uniform family with n < 7k/4 + d + 3/2. For these no form of NC can fire: three k-sets with empty intersection
  have \|∪G\| ≥ 3k/2, so \|W∩∪G\| ≥ 3k/2 − (n−w), and NC1's bound then forces n ≥ 7k/4 + d + 3/2.

## 4. NC0 and E_k: PASS
- **NC0(a).** 3⌈w/7⌉ ≤ 3(w+6)/7 ≤ w−k−d ⟺ 4w ≥ 7(k+d)+18. ✓
- **NC0(b).** σ(B_ℓ) is uniform on k-sets, and the union bound 7ξ < 1 gives the seven. ✓
- **§1 relation.** ξ < C(k+d,k)/C(w,k) implies (W,d)-complete. ✓
- **NC0 computed.** 49 (a)-instances and 60 (b)-instances (random, pair-, triple- and half-structured deletions of fewer
  than C(w,k)/7 k-sets, plus outside members). All have good sevens.
- **E_k hand proof.** Equality Σ\|L_ℓ\| = 3w = 7(w−k) forces classes of size k/4 and B_ℓ = R_ℓ. The constant-line-sum
  parity vectors are the simplex code (even total) and its complement (odd total), so the parity is contradictory. ✓
  - It relies on "Fano-type for n < 11k/6" (Task 0).
  - τ = 3k/4 checked by hand and exactly.
- **E_k computed.**
  - k = 4, splits (3,4) and (4,3): no good seven by exhaustive search and by SAT. Control (4,4), w = 8: good seven found.
  - k = 8, splits (6,8), (7,7), (8,6), and k = 12, split (10,11): co-type ILP (all 127 co-types, any good seven) is
    infeasible [HiGHS, solver-only]. A direct member-SAT at k = 8 was still running when this was written.

## 5. Reviewer targets (exact τ, completeness and NC1 by type; triple ILP cross-checked against the 3k/2 bound)
| Family | n, k | τ | Thm NC | NC1 | Good seven | Consistent? |
|---|---|---|---|---|---|---|
| K_13^(8) (7m−1) | 13, 8 | 6 | no | no | none (ILP) | yes, must not fire |
| FKW m = 2 (odd on X, \|X\| = 8) | 15, 8 | 7 | no | no | **FOUND, checked** | yes |
| FKW m = 3 | 22, 12 | 10 | no | no | none (ILP) | yes |
| FKW m = 4 / K_27^(16) | 29 / 27, 16 | 13 / 12 | no | no | not run | yes |
| parity 7m+2, m = 2 (X = 8, Y = 8), d = 1 | 16, 8 | 8 | **no** | **no** | FOUND, checked | NC misses it |
| parity 7m+2, m = 3 (X = 12, Y = 11) | 23, 12 | 11 | **no** | **no** | FOUND, checked | NC misses it |
| K_n^(k), k = 4..12, n ∈ [⌈7k/4⌉−1, ⌈7k/4⌉+3] | | n−k+1 | iff 4n ≥ 7k+6 | same | found whenever NC fires | yes |

- **FKW at m = 2 is not (7,2).** The reviewer's premise is wrong here. This agrees with CORE §110.3 (the m = 2 control
  fails). NC still does not fire there.
- **Parity 7m+2: NC does not apply.** The reviewer expected it to.
  - τ = 3m+2, and Theorem NC needs τ > 3m + 7/2.
  - NC1 needs W-union ≤ 6m−1, but every triple has union ≥ 6m (ILP: 6m+1).
  - This is the k-uniform barrier n ≥ 7k/4 + 5/2 at d = 1. The good seven comes from the coset machinery (Task 3), not
    from NC.
- **Complete families.** NC fires iff εk ≥ 3/2. Theorem 3 needs n > (7k+14)/4. Theorem A needs η = (4c+7)/(3τ) with
  c = n − 7k/4, so 49/(3η) < τ only once c > 10.5.
  - All three agree with the ground truth wherever they apply, and NC is the strongest of them.
  - The complete families that NC misses near the seam include K_17^(9), K_18^(10), K_21^(12) and K_22^(12), which have
    good sevens, and K_16^(9), which is (7,2).
- **Shift-0 linear layers.**
  - "Even on X": d = 1 (d = 0 only in degenerate W), and τ = n − k with W = V. Theorem NC fires iff n > 7k/4 + 11/4.
    Checked: it fires for (9,9; 8), (10,10; 8), (7,7; 6), and not for (8,8; 8), (12,11; 12). Every instance where it
    fired has a good seven.
  - Random proper codes (40 codes, codimension r ≤ 3, n ≤ 14): least d ∈ {1, 2, 3}, mostly d = r, once d = r+1. NC
    fired on 6 (NC1) / 4 (Theorem NC). All had good sevens.
  - No general bound d = O(r) is proved; the note's heuristic stands.

## 6. Coverage of the computations
- My random and adversarial tests: k = 3..8, w ≤ 13, d ∈ {0,1,2}, up to 5 outside points.
- The type-invariant families: k ≤ 16.
- The note's 2,992 NC1 checks: k = 4..9.
- The asymptotic regime (linear d, small ε, large k) is covered **only by the hand proof**. I re-derived that proof line
  by line and found no gap beyond the rounding point in 3 and the convention point in 2.
