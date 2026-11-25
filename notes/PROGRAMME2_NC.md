# Programme 2, bridge C: the near-complete lemma

Tags: [proved by hand], [computed exact], [heuristic], [dead], [open]. Nothing here is independently verified.
Code and logs: `compute/programme2/NC/`. Nothing committed.
Notation: H is a family of nonempty sets of size ≤ k, V = ∪H, T = ⌈(3/4+ε)k⌉, and τ = τ(H) ≥ T + 1.
For W ⊆ V with w = |W| = (7/4+δ)k, put H[W] = {B ∈ H : B ⊆ W}. Π, Lemma 2, Theorem 3 and Lemma A0 are as in
PROGRAMME_2.md and PROGRAMME2_A.md.

## 0. Verdict
- **The near-complete branch of C is empty for every ε > 0.** Theorem NC (§3) is proved by hand. It needs no thinness, no
  uniformity and no condition on the members outside W. It covers every δ ≥ −ε + (2d+3)/k, which includes the whole
  range from 7ε/3 − η′ upward, so RA is not needed for this branch at all (§4).
- The right density notion is the **covering form** "every (k+d)-subset of W contains a member", i.e.
  τ(H[W]) ≥ w − k + 1 − d. Here d may be linear: any d < (ε+δ)k/2 − 3/2 works.
- With the **fraction form** ("all but ξ of the k-subsets of W contain a member"):
  - for w ≥ (7k+18)/4, ξ < 1/7 suffices (NC0), with no τ hypothesis;
  - below that, constant ξ is **open** (§6).
- **Mixed families at the seam.** The parity twist E_k (the k-subsets of W, |W| = 7k/4, that are odd on W₁) is (7,2) with
  τ = 3k/4 [hand; computed exact at k = 4, 8]. So the seam has a third boundary example. It is near-complete (d = 1) and
  a ρ = 1 coset at once. It is removed for ε > 0 by Theorem NC (d = 1), and also by Theorem 3 when V = W. No mixed family
  is a counterexample (§5).

## 1. Density notions
- **(W,d)-complete:** every (k+d)-subset of W contains a member of H. Equivalently τ(H[W]) ≥ w − k − d + 1. This is
  T-covering restricted to W, in co-edge form. Complete K_W^(k) has d = 0. Shrinking W keeps the property for the same d.
  [proved by hand]
- **ξ-dense:** at most ξ·C(w,k) of the k-subsets of W contain no member.
  - ξ < C(k+d,k)/C(w,k) implies (W,d)-complete, since a member-free (k+d)-set contributes C(k+d,k) uncovered k-sets.
  - By normalized matching, ξ-dense implies that at most a ξ-fraction of the (k+d)-subsets are member-free, for every d.
  - The converse fails: "the k-subsets of W meeting a fixed 3-set" is ξ-dense with ξ ≈ (3/7)³ < 1/7, but it is not
    (W,d)-complete for any d < w − k − 3. [proved by hand]

## 2. Top range: no τ needed (Lemma NC0) [proved by hand]
(a) If H is (W,d)-complete and w ≥ (7(k+d)+18)/4, then H is not (7,2).
(b) If H is ξ-dense on W with ξ < 1/7 and w ≥ (7k+18)/4, then H is not (7,2).

*Proof.*
- (a) Colour W into 7 classes, each of size ⌊w/7⌋ or ⌈w/7⌉, and colour V∖W arbitrarily.
  - Every line has |L_ℓ ∩ W| ≤ 3(w+6)/7 ≤ w − k − d.
  - So W∖L_ℓ has at least k + d points and contains a member B_ℓ ⊆ W∖L_ℓ ⊆ R_ℓ.
  - Lemma 2 finishes.
- (b) Take the seven k-sets B_ℓ = (k points of W∖L_ℓ) from (a) with d = 0, and apply a uniform random σ ∈ Sym(W).
  - Each σ(B_ℓ) is a uniform k-subset of W, so it contains no member with probability ≤ ξ.
  - Since 7ξ < 1, some σ makes every σ(B_ℓ) contain a member B′_ℓ.
  - Subsets of a seven with no 2-point transversal have none either. ∎

## 3. The main lemma
**Lemma NC1 (three-member criterion).** Let H be (W,d)-complete with w ≥ k + d + 2. Suppose some G₁, G₂, G₃ ∈ H
(repeats allowed) have G₁∩G₂∩G₃ = ∅ and |W ∩ (G₁∪G₂∪G₃)| ≤ 2(w − k − d) − 3. Then H is not (7,2).
[proved by hand; computed exact: `nc_construct.py`, 2992 random instances (k = 4..9, complete and parity-twisted H[W],
random outside members), every produced seven brute-force checked to have no 2-point transversal, 0 failures; in the
other 8 instances no qualifying triple existed]

*Proof.* Use the Fano labelling of PROGRAMME2_A.md (pairs {13}, {45}, {62} through 0).
- Put C₀ = V ∖ (G₁∪G₂∪G₃) and give it colour 0.
- Each v ∈ ∪G_s lies outside some G_s, because the triple intersection is empty. Put v into X_s for one such s.
- Split X_s ∩ W into two halves whose sizes differ by ≤ 1. Add X_s ∖ W to either half. Give the halves the two colours of
  pair s.
- **Lines through 0:** L = C₀ ∪ X_s, and G_s avoids it.
- **Lines avoiding 0:** L is one half from each pair, so |L ∩ W| ≤ (|W ∩ ∪G| + 3)/2 ≤ w − k − d.
  - Hence |W∖L| ≥ k + d, and some member B ⊆ W∖L avoids L, since B ⊆ W.
- No L_ℓ is a transversal, so Lemma 2 gives a Fano-type good seven. ∎

This is RA's Theorem A1 with the y-mass bound replaced by completeness on W. The four lines avoiding 0 are closed by
W-members, and the three lines through 0 by G₁, G₂, G₃.

**Theorem NC.** Let H be (W,d)-complete with w ≥ k + d + 2, and put a = max(0, 2k + 2d + 3 − w). If
  τ(H) > (k+1)/2 + a,
then H is not (7,2). [proved by hand]

*Proof.*
- Take any A ⊆ W with |A| = a. This is possible since a ≤ w when w ≥ k + d + 2.
- Let H_A be the members of H disjoint from A. A transversal of H_A together with A is a transversal of H, so
  τ(H_A) ≥ τ − a > (k+1)/2.
- By Lemma A0, three members G₁, G₂, G₃ of H_A (repeats allowed) have empty common intersection.
- Their W-traces lie in W∖A, so |W ∩ ∪G| ≤ w − a ≤ 2(w − k − d) − 3.
- Lemma NC1 finishes. ∎

**Corollary NC.** If τ > (3/4+ε)k, H is (W,d)-complete and w ≥ (7/4 − ε)k + 2d + 3, then H is not (7,2).
- Proof: (3/4+ε)k + 1 > (k+1)/2 + 2k + 2d + 3 − w if and only if w > (7/4 − ε)k + 2d + 5/2.
- In δ-form: δ ≥ −ε + (2d+3)/k, for every d ≥ 0. With d = θk, this needs θ < (ε+δ)/2. [proved by hand]
- Sanity check with H = K_W^(k) alone: τ = w − k + 1, and the hypothesis then reads w > 7k/4 + d + 5/4, consistent with
  NC0(a). [proved by hand]

## 4. Ranges in δ, and the RA margin (the coordinator's precision point)
- **RA.** RA needs a fixed η. With y ≡ 1/τ on V we get τ*_b ≤ n/τ, where n = |V| and **not** w. So RA covers only the
  families with V = W (up to O(1) points), in the range δ ≤ 7ε/3 − η′ with η′ ≈ η(3/4+ε). That is the correct statement.
  - For V = W one can use Theorem 3 directly instead, with no η: a (7,2) family on n points has τ ≤ 3(n+7)/7. So δ < 7ε/3 −
    14/(3k) is excluded outright. [proved by hand, Theorem 3]
- **NC.** Corollary NC covers every δ ≥ −ε + (2d+3)/k, for any V and any outside members. This contains [7ε/3 − η′, ∞)
  with room to spare.
  - NC0 also covers w ≥ (7(k+d)+18)/4 with no τ hypothesis, and in the fraction form with ξ < 1/7.
- **Net.** For the near-complete branch, the "δ from 7ε/3 − η′ upward" requirement is met by NC alone. The overlap with RA is
  the whole interval [−ε + O(d/k), 7ε/3 − η′]. No case of the branch relies on RA or on V = W.

## 5. Mixed families at the seam
**5.1 The parity twist at w = 7k/4 (4 | k).** Let W = W₁ ⊔ W₂ with |W| = 7k/4, 0 < |W₁| ≤ k and |W₂| ≤ k, and let
E_k = {B ∈ (W choose k) : |B∩W₁| odd}.
- **E_k is (7,2) and τ(E_k) = 3k/4.** [proved by hand]
  - n = 7k/4 < 11k/6, so every good seven is Fano-type. This is LEDGER Task 0, VERIFIED EXACT.
  - Σ_ℓ |L_ℓ| = 3w = 7(w − k), so every line has exactly w − k points. The line-incidence matrix is invertible, so every
    class has exactly k/4 points.
  - Every R_ℓ then has exactly k points, so B_ℓ = R_ℓ. Write a_p = |class p ∩ W₁|. Oddness of every B_ℓ ∩ W₁ says that
    Σ_{p∈ℓ} a_p ≡ |W₁| + 1 (mod 2) for every line ℓ.
  - The parity vectors with constant line sums are the simplex code [7,3] (constant 0, total even) and its translate by 1
    (constant 1, total odd). Either way the total Σ a_p = |W₁| has the wrong parity. So there is no good seven.
  - τ: every (k+1)-subset of W contains an odd k-set, because |W₁|, |W₂| ≤ k. A k-set U with |U∩W₁| even gives a
    transversal W∖U of size w − k = 3k/4.
- **Exact checks** [computed exact]:
  - k = 4, w = 7, (|W₁|, |W₂|) = (4,3) and (3,4): (7,2), τ = 3. Control: K_7^(4) is not (7,2).
  - k = 8, w = 14, (7,7): τ = 6 by enumeration. (7,2) by the dual ILP `seam_dual_ilp.py`: a cover by 7 co-edges puts every
    point in exactly 3 co-edges (13 neighbours, 5 per co-edge, and 42 = 14·3). So each point becomes a 3-subset of the 7
    labels, the 3-subsets are pairwise intersecting, and every label has degree 6. The parity rule is then INFEASIBLE.
    The control (no parity) is FEASIBLE, and the solver returned the Fano blow-up with every line twice.
  - At w = 8, k = 4 the twist is not (7,2) (`seam_exact.py`). The twist matters only at the exact boundary.
  - `seam_k8.py` (direct SAT) was too slow on the loaded machine and gave no verdict. Its τ lines agree.
- **Meaning.**
  - E_k is a coset family with ρ = 1, and Corollary 7 holds since 7 > 3(4n − 7k) = 0.
  - It is also (W,1)-complete.
  - Like K_{7k/4−1}^(k), it is a τ ≈ 3k/4 boundary example. It sits in **both** structures, so at ε = 0 the two
    alternatives of C overlap.

**5.2 Who covers twisted near-complete blocks for ε > 0.**
- **Two cells (one parity check), by NC** [proved by hand].
  - "Odd on W₁" on W is (W,d)-complete if and only if |W₂| < k + d and (k is odd or |W₁| < k + d). A (k+d)-set U contains
    an odd k-subset unless U ⊆ W₂, or U ⊆ W₁ with k even.
  - If a part is too large, shrink W to W′ by keeping at most k points of each part. Then H[W′] is (W′,1)-complete.
  - Corollary NC applies once |W′| ≥ (7/4 − ε)k + 5. For example, every twist with min(|W₁|, k) + min(|W₂|, k) ≥
    (7/4 − ε)k + 5 is covered, whatever the rest of H is.
- **Many cells (an r-check coset (a+C) ∩ (W choose k)).**
  - (W,d)-completeness holds if and only if every (k+d)-set U ⊆ W has a d-subset D with σ(D) = σ(U) + σ(a), where σ is
    the syndrome. [proved by hand: restatement]
  - It fails when U is concentrated on cells whose columns span a subspace missing the required syndrome, for example one
    cell of size ≥ k + d with the wrong parity. Removing such excess from W gives d = O(r) whenever the cells are spread.
    [heuristic: no general bound on d proved]
  - If the whole of H is a coset family, the block is B's business (Theorem B1 for small linear codimension, Theorem D).
  - If the whole of H is invariant under ∏Sym(V_j) with m ≤ 4εk − 12 cells and n/3 + m ≤ T, S⁺ applies (CORE §45.1).
  - NC is the only one of the three that allows arbitrary members outside W.
- **S⁺ against NC on profile families** [proved by hand]: H = {k-sets B ⊆ W ⊔ Z : |B∖W| ≤ j} with j = T − w + k, so that
  τ = T + 1.
  - Every triple with empty intersection has W-union ≥ 3(w − T)/2. So NC1 applies to this H exactly when
    w ≥ (7/4 − 3ε)k + O(d).
  - S⁺ (2 cells, after cutting Z to j points) covers it at every w.
  - So NC1 itself reaches past Corollary NC's (7/4 − ε)k on such families. The loss is in the A0 step, not in the colouring.

## 6. Where the lemma stops (exact obstructions)
- **Below w = (7/4 − ε)k + 2d + 3** [open].
  - There H[W] contributes τ(H[W]) ≤ (3/4 − ε)k + 1, so most of τ comes from outside W.
  - NC1 still applies whenever its triple exists. Its absolute limit is w ≥ k + d + 2, with G's outside W.
  - The step that fails is "τ(H_A) ≥ τ − |A| > (k+1)/2". A0 is tight, so a better triple needs the members with small
    W-trace: for every (w−T)-set S ⊆ W, some member has B∩W ⊆ S [proved by hand: W∖S is not a transversal]. Then three
    such members in pencil position, with outside parts not 3-wise intersecting. Bounding their outside overlap reproduces
    the condition w > (7/4 − ε)k [heuristic].
  - No example defeating NC1 with τ > T is known. Defeating it would require every triple with empty intersection to spread
    over more than 2(w−k−d) − 3 points of W.
- **Fraction form with constant ξ, at w < (7k+18)/4** [open; heuristic obstruction].
  - The four W-members in NC1's seven all contain W∖∪G together with half of W∩∪G.
  - For a fixed G-triple, the k-sets of that shape have exponentially small density in (W choose k). So a ξ-fraction
    deletion, correlated with the outside members, can remove all of them.
  - A constant-ξ lemma would need control over which G-triples H offers, which is the general problem again. With
    ξ ≤ C(k+d,k)/C(w,k) (exponentially small) Corollary NC applies.
- **"Near-complete ⟹ rich" as a route** [dead for general V]: τ*_b ≤ n/τ uses all of V. With many outside points the family
  is thin, which is exactly the case NC handles without weights.

## 7. Proposed restatement of C
- **C(ε) (as used by the programme):** for k ≥ k₀(ε), every thin (7,2) family H with τ > (3/4+ε)k is γ(ε)-close to a
  covering coset family (near-coset, FKW type).
- **C₂(ε) (two structures):** under the same hypotheses, H is near-coset **or** near-complete, meaning that some W ⊆ V and
  d ≤ θk with |W| ≥ (7/4 − ε)k + 2d + 3 have τ(H[W]) ≥ |W| − k + 1 − d.
- **What Theorem NC removes.** The near-complete alternative of C₂(ε) never occurs (Corollary NC). Hence **C₂(ε) ⟺ C(ε) for
  every ε > 0**, and inside C one may additionally assume, for free:
  - (i) τ(H[W]) ≤ |W| − k − d for every W and d with |W| ≥ (7/4 − ε)k + 2d + 3. In particular H contains no K_W^(k), and no
    twisted block as in §5.2, on (7/4 − ε)k + O(1) points.
  - (ii) For |W| ≥ (7k+18)/4, at least 1/7 of the k-subsets of W contain no member (NC0b).
- **Where two structures are genuinely needed: the stability form at ε = 0.** "τ ≥ (3/4 − γ)k and (7,2) ⟹ near-coset OR
  near-complete" [heuristic statement]. The boundary examples are K_{⌈7k/4⌉−1}^(k) (near-complete only, 61.5% coset
  fraction at k = 8), FKW (near-coset only) and E_k (both). The ledger's K_13^(8) data (STABILITY_DATA.md) refutes only
  this ε = 0 version with a single structure. It does not touch C(ε) for ε > 0.
- **The remaining content of C** is unchanged: thin (7,2) families with no near-complete block and no near-coset structure.
  NC only certifies that "near-complete" is not a third outcome the bridge must deliver.

## 8. Claims and tags
- NC0(a), NC0(b), NC1, Theorem NC, Corollary NC, the density relations of §1, E_k (7,2) with τ = 3k/4, two-cell
  completeness: [proved by hand].
- NC1 construction on 2992 instances; E_k at k = 4 (both splits) and k = 8 (dual ILP); controls K_7^(4), K_14^(8), and the
  twist at w = 8: [computed exact].
- Many-cell d = O(r); the profile-family 3ε reach being typical; the fraction-form obstruction; the ε = 0 stability
  statement: [heuristic].
- "Near-complete ⟹ rich" for general V: [dead].
- Below (7/4 − ε)k, and constant ξ below (7k+18)/4: [open].
- Not done: independent verification, and Lean. NC1 and Theorem NC are short on top of Lemma 2 and Lemma A0.
