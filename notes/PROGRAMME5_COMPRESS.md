# Programme 5: the compression lemma (C) — a relative lemma that holds, the routes that are dead, the one left

Tags: [proved by hand] / [computed] / [heuristic] / [open]. Nothing independently verified. Code: `compute/programme5/compress/`.
Units: τ = 3k/4 + e, T = τ − 1, e = εk; a block (W, d) means H[W] = {B ∈ H : B ⊆ W} is (k+d)-covering on W, w = |W|.

## 0. Verdict
- **(C) is not proved.** It is also not refutable unless (G) is false: if (G) holds, (C) holds vacuously for large k.
  So (C) ⟺ "(G) for n ≤ 2k implies (G)", and every obstruction below works at the level of methods.
- **New positive result (§2):** the relative pencil lemma NC-P. A block of excess d ≤ (8e − 22)/3 is fatal at every
  w ≥ (6k + 9d + 3)/4. The block's own τ can be **below 3k/4**, because the excess e is supplied by the ambient family.
  NC-P strengthens Theorem NC whenever w ≲ (7/4 + 13ε/3)k.
- **Dead:** subfamilies or τ-critical subfamilies (§3), subfamilies after stripping (§4, pencil padding), merging
  alone and random restriction (§6).
- **Left:** a (7,2)-preserving deletion of non-dominated points (§5, the deletion core), [open].

## 1. Operation calculus [proved by hand; all one-liners]
| operation | (7,2) | τ | sizes |
|---|---|---|---|
| subfamily | kept | ↓ (any amount) | same |
| enlargement B → B' ⊇ B (incl. padding) | kept | ↓ | ↑ |
| point map φ (merging) | kept (images of 2-covers are 2-covers) | ≥ τ − (n − n') | ↓ |
| deleting a point set D (B → B∖D) | **can fail** | **never ↓** (a cover of H−D covers H) | ↓ |
| deleting a dominated point (star(x) ⊆ star(y)) | kept | same | ↓ |
- **Merging one pair p, q.** τ(φH) = τ(H) − 1 if some minimum transversal contains both p and q, else τ(φH) = τ(H).
  Members containing both points shrink by one.
- **Duality.** Every (7,2)-safe operation can lower τ. Deletion is the reverse: safe for τ and for τ/max|B|, but it can
  create a good seven. Doubly safe: dominated deletions, member removals keeping τ ≥ T + 1, merges of pairs never
  together in a member or a minimum transversal, and the relative use of a sub-block (§2).

## 2. NC-P: relative pencil lemma [proved by hand from VERIFIED Thm pen + Lemma P1; computed checks]
**Statement.** Let H be k-uniform with τ(H) ≥ T + 1, and let (W, d) be a block with **4(w − k − d) ≥ 2k + 5d + 3**,
**3d ≤ 2k − 2** and **d + D(k, d) ≤ 4T − 3k − 6** (D as in Thm pen). Then H has a Fano-type seven. The last condition
holds whenever ⌊3d/2⌋ + 1 ≤ 4T − 3k − 6, i.e. d ≤ (8e − 22)/3.
**Proof.**
- H[W] is k-uniform and (k+d)-covering on the ground set W. Thm pen uses only (k+d)-subsets of the ground set and
  members inside them, so it applies verbatim with n := w, r := d: H[W] ⊆ H has a pencil of weight ≤ d + D.
- Lemma P1 needs only "members of size ≤ k and T < τ(H)", for the ambient H, with no condition on n. ∎
**What is new.** NC-P combines the *ambient* T (from P1) with a *local* pencil (from Thm pen on H[W]). With W = V it is
Theorem 9.1. Theorem NC needs w ≥ (7/4 − ε)k + 2d + 3 (below this is [open] in PROGRAMME2_NC §6); NC-P works down to
w ≈ 3k/2 + 9d/4.
**Variants.** NC-P2 uses the two-stage condition of Thm 2S (PROGRAMME5_BULK §2.1, hand): 4(w − k − d) ≥ 2k + 3d + 3,
3 ≤ d ≤ 2k − 4. NC-FW applies Thm FW to H[W]: fatal when d ≤ min(4e, c0(w/k)k) − o(k).
**Region** [computed, exact integers, `ncp_region.py`, k = 240 and k = 1200]. Least fatal block transversal number,
(τ(H[W]) − 3k/4)/k, at k = 1200; "–" means not covered.
| ε | w/k = 1.6 | 1.667 | 1.75 | 1.833 | 2.0 |
|---|---|---|---|---|---|
| 1/44: NC / NC-P / NC-P2 | – / −0.193 / −0.206 | – / −0.142 / −0.142 | −0.009 / −0.058 / −0.058 | +0.033 / +0.025 / +0.025 | +0.116 / +0.192 / +0.192 |
| 0.05: NC / NC-P / NC-P2 | – / −0.193 / −0.206 | – / −0.156 / −0.177 | −0.022 / −0.110 / −0.129 | +0.019 / −0.046 / −0.046 | +0.102 / +0.121 / +0.121 |
- At ε = 0.05 and w = 7k/4 a sub-block with τ(H[W]) ≥ 0.640k is fatal (NC needs 0.728k).
- NC-P's largest fatal d is ≈ 8εk/3 (k = 1200, ε = 1/44: 71 against 72.7). NC remains better for large w.
**Test** [computed]. `ncp_test.py 3000 7`: random inclusion-minimal block on W (k = 4, 5; w = 7..12; d = 0..2) plus
random k-sets meeting an outside set Z. 2712 instances met the hypotheses (in 1972 of them P1 with the block's own τ
would *not* apply). In all 2712 the minimum pencil of H[W] has weight ≤ d + D and the P1 seven has no 2-cover (brute
force). 0 failures.
**Consequence for (S)** [proved by hand]. Proposition S may additionally assume that H has no NC-P block, on top of NC's
exclusion of blocks with |W| ≥ (7/4 − ε)k + 2d + 3.

## 3. Route (b): τ-critical subfamilies — dead on its own [proved by hand]
- **Edge bound.** Bollobás: a τ-critical family with sizes ≤ k has |H| ≤ C(k + τ − 1, k). Published vertex bounds
  (Gyárfás–Lehel–Tuza, Tuza; not re-read here) are not needed: padding shows no O(k) support bound can hold, even
  for (7,2)-families.
- **Lemma 3.1.** A (7,2)-family F has τ(F) ≤ 2⌈|F|/7⌉ (split into groups of ≤ 7), hence |F| ≥ 7τ(F)/2 − 6.
- **Private padding** (p new points per member) keeps (7,2), τ and τ-criticality. Every subfamily F of the padded
  family has |V(F)| ≥ p|F| ≥ p(7τ(F)/2 − 6). Already p = 1 puts every subfamily with τ ≥ 3k'/4 on ≥ 21k'/8 − 6 > 2k'
  points, with ε' = ε − O(1/k).
- **Conclusion.** If any counterexample exists, one exists in which no subfamily on ≤ 2k' points has τ ≥ k'/2 + O(1).
  So route (b) needs stripping (deleting dominated points) first, which makes members non-uniform.

## 4. Pencil padding: stripping does not rescue sub-blocks [proved by hand; computed]
- **Lemma 4.1.** If τ(H) > (k+1)/2, every member B lies in a pencil (repeats allowed). Otherwise the traces {B ∩ C}
  form an intersecting family on B whose transversals cover H, so τ ≤ min|B ∩ C| ≤ k − τ + 1 (A0 localised at B).
- **Lemma 4.2 (shared padding).** Add new points, each to ≤ 3 members. The result is (7,2) and has τ ≥ τ(H) − 1.
  Proof: for a cover Y with X = Y ∩ new, X meets the members of F with |F| ≤ 3|X|; by 3.1, τ(F) ≤ 2⌈3|X|/7⌉ ≤ |X| + 1,
  so (Y ∖ X) ∪ cover(F) covers H.
- **Lemma 4.3.** Give each new point a distinct pencil star (3 members with empty intersection, or 2 disjoint members).
  If H is undominated with minimum degree ≥ 4, the padded family H# is undominated, so stripping does nothing.
- **Effect (load p per member, each new point in ≤ 3 members).**
  - Every subfamily F has |V(F)| ≥ k + p(7τ(F)/2 − 6)/3. For τ(F) ≥ 3k'/4 this is ≥ 15k'/8 − 2 at p = 1 (beyond
    11k'/6) and ≥ 11k'/4 − 4 at p = 2 (beyond 2k').
  - Every block H#[W] with τ > k'/2 has excess d ≥ (p/3 − 2/7)(7k'/4 − 6) − p − 1, i.e. ≥ 2k'/3 − 6 at p = 2, above
    NC-P's 8e/3 ≤ k/3 + 3. Also w − 2d ≤ k + 6 < (7/4 − ε)k at p = 2, so NC never fires either.
- **Data** [computed, `pencil_pad.py`]. Greedy pencil systems on K^(6)_10, K^(8)_13 and K^(4)_6: loads in {1, 2} (all
  exactly 1 on K^(4)_6), **τ unchanged** (5 → 5, 6 → 6, 3 → 3, CP-SAT optimal), **0 dominated points**.
- **Caveat** [heuristic / open]. Load exactly p is not proved to be achievable in a general counterexample. Loads in
  [p, q] give sizes k + p … k + q, and all bounds hold with k' = k + q.
- **Conclusion.** No proof of (C) can output a sub-block or a subfamily, even after stripping. It must **delete
  non-dominated points**.

## 5. The deletion core — the one remaining route
- **Definitions.** z is *deletable* if H − z (z removed from every member) is still (7,2); by §1, τ never drops.
  The *core* H* comes from alternating, until neither applies: delete a deletable point; delete a member while
  τ ≥ T + 1 stays true.
- **Facts** [proved by hand].
  - Private and pencil padding points are deletable (what remains is an enlargement of H), so the core undoes both
    paddings and §3–4 do not obstruct it.
  - H* is τ-critical with τ = T + 1, so |H*| ≤ C(k + T, k).
  - Every point z of H* is essential: some seven S_z has all its 2-covers through z (co-types on V ∖ z intersecting,
    I_z missing some I_y). A seven witnesses ≤ 2 points, so |V(H*)| ≤ 2·C(C(k+T, k), 7): finite in k but useless.
- **(C-del) [open], the sharp form of (C).** Does every counterexample have a core with n* ≤ (2 + o(1))·min|B| and
  sizes within o(k) of each other? Deletion only raises τ/max|B|, so the ratio is never the problem. The support is,
  and so is near-uniformity: Lemma pair/dump assume |x| = k exactly, and a size defect c should cost O(c) weight
  [heuristic, not checked].
- **Obstruction to (C-del) [open].** It would be a (7,2)-family with τ > 3k/4 on ≫ k essential points. Every
  padding-type construction we know produces deletable points, so none is known.

## 6. Merging (c) and random restriction (d) [proved by hand]
- **Uniform merges** are exactly *strong colourings* (every member rainbow), and τ(φH) = the fewest colour classes
  whose union covers H. So (C) with k' = k ⟸ a strong colouring with ≤ 2k classes in which no (3/4+ε')k classes cover
  H. This needs the 2-shadow to have chromatic number ≤ 2k, impossible if > 2k points pairwise share members.
- **General merges.** The only general guarantee, τ' ≥ τ − (n − n'), gives e' ≥ e − (s − s'): useless once
  n > (2 + ε)k.
- **Random W.** H[W] is a block once fewer than a 1/C(w, k+d) fraction of the (k+d)-sets of V miss H. That density is
  exponentially close to 1, matching the fraction-form obstruction of PROGRAMME2_NC §6. Dead.

## 7. Next targets
- (i) (C-del) on small exact data: compute cores of the stored seven-free families with N ≥ 11/6.
- (ii) NC-P plus density increment: in a counterexample every W with w ≈ 7k/4 has τ(H[W]) < w − k − 8e/3 + O(1).
- (iii) Verify NC-P independently (three lines on top of VERIFIED results). Logs: `logs/ncp_*.log`, `logs/pencil_pad.log`.
