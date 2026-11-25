# Programme for a full resolution (second direction brief, 2026-11-25)

Status: everything below is **HAND, unverified** (the brief's author checked Lemma 5 numerically and carried out Prop. 9 in one family). Notation: H is a finite family of nonempty sets, V = ∪H, n = |V|, Π is the Fano plane.

## Programme: (G) follows from three statements
- **A. Rich families:** Theorem 3.
- **B. Coset families:** every T-covering coset family has a good seven. Open; reduced to the constant c*.
- **C. Bridge:** a thin family with no finishing shape is close to a coset family. Speculative; measure first.

**Decision points.**
- **D1 (after Task 2).**
  - If c* > (12/7)(1 + ε/ω): stop everything and verify the counterexample exactly. This would resolve the problem NEGATIVELY.
  - If c* ≤ (4/3)(1 + ε/ω): B is within reach.
  - In between: refine Proposition 9.
- **D2 (after Task 4).** If the stored thin families are close to linear, C is the remaining step. Otherwise report their true structure.

## Fact I: the colouring form
**Definition 1 (Fano colouring).** χ: V → points of Π. Put L_ℓ = χ⁻¹(ℓ), the points coloured with a point of the line ℓ, and R_ℓ = V∖L_ℓ. Members B_ℓ ⊆ R_ℓ, one per line, form a Fano-type good seven.

**Lemma 2 (colouring criterion).** If no L_ℓ is a transversal of H, then H has a Fano-type good seven, which has no 2-point transversal. So H is not (7,2).

**Theorem 3 (weighted static theorem).** Suppose y: V → R≥0 has y(M) ≥ 1 for every transversal M, and
  y(V) + 7·max y < 7/3.
Then H is not (7,2).
*Proof.* Greedy balanced colouring into 7 classes. Each class has mass ≤ y(V)/7 + max y, so each line has mass ≤ 3y(V)/7 + 3 max y < 1. Apply Lemma 2.
- **Consequences:**
  - with y = 1/τ: every (7,2)-family on n vertices has τ ≤ 3(n + 7)/7;
  - pool families lose once τ > 3k/4 + 9/2.
- **τ*_b(H)** is the least y(V); by LP duality it equals the maximum fractional packing of transversals.
- **Rich** means τ*_b ≤ 7/3 − η; otherwise **thin**.
- **Open: the heavy-atom case** (an optimal y with large atoms).

## Fact II: a good seven is linear over F₂
Subsets of V are vectors, + is symmetric difference, wt is size.

**Lemma 5 (pencil-sum identity).** For a Fano colouring χ and any B_ℓ ⊆ R_ℓ, let s_p be the sum of the three B_ℓ with ℓ ∋ p, and j_x the number of B_ℓ containing x. Then
  Σ_p wt(s_p) = Σ_x j_x(4 − j_x) ≤ 3(4|∪B_ℓ| − Σ|B_ℓ|).
- With no slack, every s_p = 0, so the seven sets plus ∅ form a 3-dimensional subspace.
- The pencil shape (Σ)(b) is: three members with empty common intersection and wt(x₁+x₂+x₃) ≤ 4T − 3k.
- For a k-uniform family on n points, a Fano-type good seven has Σ wt(s_p) ≤ 3(4n − 7k) = 12δk.

**Definition 6 (coset family).** H ⊆ a + C, with C ≤ F₂^V linear and a ∉ C. Put ρ = min wt over a + C. Every sum of an odd number of members has weight ≥ ρ.

**Corollary 7 (coset obstruction).** A k-uniform coset family on n points with 7ρ > 3(4n − 7k) has no Fano-type good seven.
- **FKW as an example:** it lies in the coset "odd on X and odd on Y", with ρ = 2.
  - On 7m + 1 points: 12 < 14, so it has no Fano-type good seven.
  - On 7m + 2 points: 24 > 14, so it has one.

**Lemma 8 (near-Schur triple).** Let H be k-uniform with every (k + r)-set of V containing a member, and n ≥ 3k/2 + r + 1. Then some three members have wt(x₁+x₂+x₃) ≤ 2r + 1, so in a coset family ρ ≤ 2r + 1. Also, if C has a codeword of weight w ≥ k + r, then ρ ≤ w − k.

**Proposition 9 (sketch).** Take H = (a + C) ∩ (V choose k). If a + C contains pairwise disjoint Ω₁, Ω₂, Ω₃ with Σ|Ω_i| ≤ 4n − 7k, then H has a Fano-type good seven, SUBJECT TO an adjustment step (making all seven sets lie in a + C with size exactly k). The adjustment step is the named gap.

## The constant c*
c* is the largest ρ/r over T-covering coset families with r = Θ(k). Here r ≈ ωk and n − 7k/4 = δk = (ε + ω)k.
- **If c* ≤ (4/3)(1 + ε/ω):** Proposition 9 applies, so statement B holds.
- **If c* > (12/7)(1 + ε/ω):** Corollary 7 gives a coset family with no Fano-type good seven and τ > (3/4 + ε)k. For N < 11/6 this is a COUNTEREXAMPLE.

**Known values:**
- c* ≤ 2, by Lemma 8;
- FKW has ρ/r = 2 at r = 1;
- q-cell parity families have ρ/r = q/(q − 1).

**Likely c* = 1.** A high-rate code should contain words of weight k + r or k + r + 1, which gives ρ ≤ r + 1. Two literature results to locate:
- Enomoto–Frankl–Ito–Nomura, "Codes with given distances" (1987);
- Ward's theorem on divisible codes.

**CSS dictionary.** Write a + C = C₀∖C with [C₀ : C] = 2. Covering means every word of C^⊥∖C₀^⊥ has weight ≥ T + 1. So a covering coset family is a CSS-type pair with one logical qubit, d_X = ρ and d_Z ≥ T + 1.

## Tasks
- **Task 0. Verify** Lemma 2, Theorem 3, Lemma 5, Corollary 7 and Lemma 8, then do Lean. Also:
  - the heavy-atom case of Theorem 3;
  - an EXACT proof (or refutation) that every good seven is Fano-type for N < 11/6 (CORE 1.3 and 8.3 claim it only by float MILP);
  - (Σ)(a) and (c) in F₂ form.
- **Task 1.** Compute τ*_b for every stored family (LP with separation by minimum-weight transversal ILP), and classify each as rich or thin.
- **Task 2. Determine c* (D1).**
  - literature;
  - small exact tables of achievable (r, ρ): is (2,4) achievable? (3,6)? (7,14)?;
  - asymptotics: prove ρ ≤ r + O(1), or ρ ≤ (4/3)r, or construct ρ > (12/7)δk.
- **Task 3. Statement B:** close the adjustment step of Proposition 9.
- **Task 4. Bridge (D2):** measure C(H) and ρ, minimum triple sums against 4T − 3k, pencil-sum weights against 12δk, and affine-ness of the pencil-free selectors.
- **Task 5.** Finish the t = 43/50 certification; extract the method from the two papers when they arrive.

Report Tasks 0, 1 and 2 first.
