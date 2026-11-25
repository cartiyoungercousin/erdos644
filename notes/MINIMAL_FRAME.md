# The minimal-counterexample frame (direction brief, 2026-11-25)

Status: everything below is **HAND, unverified**. Task 0 verifies it.

## Why a new frame
- **CP alone is not enough.** The core-window statement CP is *necessary* (a counterexample to it is a genuine (7,2)-family with τ > T). But a proof of CP bounds nothing until two further open steps are done: lifting (far replies, G2) and the petal side against general adversaries.
- **The failed routes quantify too broadly.** All 21 failed routes quantify over *all* T-covering families. A real counterexample can be taken *minimal*, which is far more rigid. Minimality has only ever been used to dismiss size-stability (CORE §105.1), never in the other direction.

## Setting
**Lemma 1 (padding).** Let f≤(k,7) be the largest τ over (7,2)-families whose members are nonempty and have *at most* k points. Then f≤(k,7) = f(k,7).
*Proof.* Pad each member B with k − |B| fresh private points. This preserves (7,2). Any transversal of the padded family can be pushed back into the original members without growing, so τ does not decrease.

**Definition.** A *counterexample at (k,T)* is a finite family H of nonempty sets of at most k points with property (7,2) and τ(H) > T. It is *minimal* if it minimises the total size ‖H‖ = Σ|B|. Its ground set is V = ∪H, its co-edges are K = V∖B, and 𝒞 is the family of co-edges.

**Statement (G).** For every ε > 0, every k ≥ k₀(ε) and T = ⌈(3/4 + ε)k⌉: every finite family of nonempty sets of at most k points with τ > T has at most seven members with no transversal of at most two points.
- (G) is equivalent to f(k,7) ≤ (3/4 + o(1))k.
- It has no anchors, no confinement and no bound on N. There are no far replies and no separate petal side.

## Structural facts (H a minimal counterexample)
**Lemma 2.5 (antichain).** No member contains another. If C ⊊ B, then B is redundant (anything hitting C hits B), so removing B keeps τ > T and (7,2) with smaller total size. Lemma 4 uses this to rule out B∖{z} equalling an existing member.

**Provenance.** Lemma 3 is classical: S_B together with B forms a Bollobás set-pair system, the standard tool for τ-critical hypergraphs (Bollobás, Lovász, Frankl, Tuza). It gives |H| ≤ C(k+T, k) in the uniform case. Combined with covering, it only forces N ≥ (1+t)k, with equality for the complete family. So it does not organise the window. **Lemma 4 (saturation) is the new ingredient.** Do not present Lemma 3 as novel.

**Lemma 3 (private sets).** For every B ∈ H there is a set S_B with |S_B| ≤ T, S_B ∩ B = ∅, meeting every other member. Equivalently, S_B ⊆ K_B and S_B ⊄ K for every other co-edge K.
*Proof.* H∖{B} is smaller, so it is not a counterexample, and it has a transversal of at most T points. That transversal misses B.

**Lemma 4 (saturation).** Let B ∈ H with |B| ≥ 2 and let z ∈ B. Then there are B₂, …, B_m ∈ H∖{B}, with m ≤ 7, such that:
- (i) B∖{z}, B₂, …, B_m have no transversal of at most two points;
- (ii) every transversal X of B, B₂, …, B_m with |X| ≤ 2 satisfies X ∩ B = {z}.

*Proof.* Replacing B by B∖{z} keeps τ > T (transversals of the new family are transversals of H) and lowers ‖H‖. So the new family fails (7,2), and the failing subfamily must use B∖{z}.

**Notation.** U(A₁, …, A_r) = {x : I_x ∩ I_y = ∅ for some y} (FABLE_C Def 2.1). A₁, …, A_r, A cover all pairs iff U ⊆ A (FABLE_C Lemma 2.3).

**Corollary 5 (co-edge form).** Let K ∈ 𝒞 and z ∈ V∖K, with |V∖K| ≥ 2. There are at most six K₂, …, K_m ∈ 𝒞∖{K} such that U = U(K₂, …, K_m) satisfies:
- z ∈ U ⊆ K ∪ {z};
- U ⊄ K′ for every K′ ∈ 𝒞;
- |U| ≥ T + 1.

## What it says
- **Every co-edge is saturated.** It is one point away from completing a good seven, in every direction z.
- **No exact pool points.** Every point lies in a member, so the exact pool family is not minimal.
- **New objects.** The sets U_z (with |U_z| ≥ T + 1 and U_z∖{z} ⊆ K) are new, and so is their interaction with the private sets S_K.

**Cautions.**
- A minimal counterexample need not be uniform. The verified tools (slack count, Theorems T, Q, P) are stated for uniform families and must be re-derived before use here. Do not pad back to uniform: padding destroys minimality.
- N is unbounded in this frame.

## Tasks (in order)
- **Task 0.** Verify Lemmas 1–4 and Corollary 5 adversarially; then formalise them in Lean.
- **Task 1** (reading corrected by a reviewer): looseness is defined only for genuine (7,2)-families with τ > T. At ε = 0 (FKW) shrinking always ends saturated, so 1(a) is a TEMPLATE, not a test. For near-pool and hash-like MODELS, test whether saturation's consequences (the U_z sets of Corollary 5 and the private sets) contradict their structure.
- **Task 1 (original wording).** The decisive test: are the surviving candidates saturated? An incidence (z, B) is *loose* if B → B∖{z} keeps (7,2). Test:
  - (a) the FKW parity family at m = 3;
  - (b) pencil-free two-class selectors at k = 8;
  - (c) near-pool models M_{Y,η} at (10,8,21) and (13,10,25).
- **Task 2.** Proof side: do saturation and private sets force a (Σ)-shape?
- **Task 3.** Disproof side: build from the saturated templates.
- **Task 4.** Literature: EFKT92 and Kostochka 2002, when obtained.
- **Task 5.** Correct the reviewer brief.
