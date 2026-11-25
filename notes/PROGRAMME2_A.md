# Programme 2, piece A: rich families for large k (heavy-atom gap closed)

Status: the theorem below is **[proved by hand]**. The constructions are **[computed exact]**: they were checked in Fractions on random instances, and every claimed seven was brute-force checked to have no 2-point transversal.
Code: `compute/programme2/A/`. Logs: `compute/programme2/A/out/`.

## Result
**Theorem A.** Let η > 0. Let H be a family of nonempty sets of at most k points with τ*_b(H) ≤ 7/3 − η and
  τ(H) > (k+1)/2 + 49/(3η).
Then H is not (7,2).
- This holds for every k. In particular it covers k ≥ k₀(η, ε) with τ > (3/4 + ε)k, which is the goal of piece A.
- No uniformity, minimality or spreading of y is used. The heavy atoms are not spread. They are deleted, and the lines that carry them are closed by members of H rather than by weight.

Notation: Π is the Fano plane with lines {013, 124, 235, 346, 450, 561, 602}. The lines through 0 are 0 + {13}, {45}, {62}. Each of the 4 lines avoiding 0 takes exactly one point from each of these three pairs. For A ⊆ V put H_A = {B ∈ H : B ∩ A = ∅}, Λ = y(V∖A), and a′ = max y on V∖A.

**Lemma A0 (Frankl-type).** Let H be a family of nonempty sets of size ≤ k. If every ≤ 3 members of H (repeats allowed) share a point, then τ(H) ≤ (k+1)/2. [proved by hand; checked on 20000 random 3-wise intersecting families, tight]
*Proof.*
- Fix B₁ ∈ H. For any B₂, the set B₁∩B₂ meets every member, so it is a transversal. Hence |B₁∩B₂| ≥ τ for every B₂.
- So every subset of B₁ with |B₁| − τ + 1 points is a transversal.
- Therefore τ ≤ k − τ + 1. ∎

**Theorem A1 (split colouring).** Suppose some ≤ 3 members B_a, B_b, B_c of H_A have empty common intersection, and Λ + 3a′ < 2. Then H is not (7,2).
*Proof.*
- Colour every point of A with colour 0.
- Put each light point v into a class X_s with v ∉ B_s. This is possible because the triple intersection is empty.
- Split each X_s greedily into two halves whose y-masses differ by ≤ a′. Give the halves the two colours of the s-th pair.
- A line through 0 has L_ℓ = A ∪ X_s. The member B_s avoids it.
- A line avoiding 0 has L_ℓ equal to three halves, one from each pair. Its mass is ≤ (Λ + 3a′)/2 < 1, so L_ℓ is not a transversal.
- Lemma 2 finishes. ∎
[computed exact: 3460 random instances, 26651 applications, 0 failures; the instances include H₁ ⊔ {{b}} and H₁ ∪ star_b]

**Theorem A2 (one heavy colour).** Suppose Λ + 3a′ ≥ 2 and y(V) + 7a′ < 7/3. Then H is not (7,2).
*Proof.* Apply Theorem 3H with π ≡ 0, using c₀ = t := Λ − 6s and c_q = s := (1 − 3a′)/3 − σ for q ≠ 0 (σ > 0 small).
- The hypothesis Λ + 3a′ ≥ 2 gives t ≥ 3a′ + 6σ ≥ 0.
- A line avoiding 0 has mass ≤ 3s + 3a′ = 1 − 3σ < 1.
- A line through 0 has mass ≤ y(A) + t + 2s + 3a′ = y(V) − 4/3 + 7a′ + 4σ < 1. ∎
[computed exact: 3000 random weight vectors, every line < 1. The random families never reach the A2 regime at n ≤ 12, which needs many tiny atoms, so the end-to-end runs exercise A1 only. A2 is a special case of the verified Theorem 3H.]

*Proof of Theorem A.*
- Take an optimal y with y(V) = τ*_b ≤ 7/3 − η. Set θ = η/7 and A = {y ≥ θ}. Then |A| ≤ y(V)/θ < 49/(3η), and a′ < θ, so y(V) + 7a′ < 7/3.
- If Λ + 3a′ ≥ 2, apply A2.
- Otherwise apply A1. A transversal of H_A together with A is a transversal of H, so τ(H_A) ≥ τ(H) − |A| > (k+1)/2. Lemma A0 then gives the three members. ∎

## The three routes in the brief
1. **Spreading y (route 1, and the reviewer's hint): not needed. It is false for general rich families.**
   - Example: H = H₁ ⊔ {{b}}. Every transversal contains b, so τ*_b = 1 and y = δ_b. Any y with max y = o(1) must give weight about 1 to every transversal of H₁, which costs about τ*_b(H₁). That cost can be arbitrarily large.
   - Such an H is (7,2) only if H₁ is 6-wise intersecting, so τ ≤ (k−1)/5 + 2 (Frankl). So the heavy atom is harmless, but it cannot be spread.
   - The deletion half of the hint is exactly what works: delete A, keep τ(H_A) ≥ τ − O(1/η), and use only the weak fact that H_A is not 3-wise intersecting.
   - For minimal counterexamples the spreading claim holds vacuously: by Theorem A no rich counterexample with τ > k/2 + O(1/η) exists.
2. **Placement LPs (route 2):** the single placement π ≡ 0 suffices (A2), once lines through the heavy colour may be closed combinatorially (A1). Example (iii) of the Task 0 verification (best fractional line mass 13/12 > 1) is not a counterexample: it uses only y, and A1 uses H.
3. **K_10^(6)-type families (route 3):** these are not a large-k obstruction. [proved by hand]
   - K_n^(k) with n < 7k/4 has τ = n − k + 1 ≤ 3k/4 + 1 and τ*_b = n/τ.
   - It is rich only when 4n > 7k − 7, and then its margin is 7/3 − n/τ = (4n − 7k + 7)/(3τ) ≤ 7/(3τ) = O(1/k). So for fixed η it is thin once k is large.
   - Its heavy atoms 1/τ make A equal to all of V, so H_A = ∅ and A1 does not apply.
   - Concretely, K_10^(6) has τ = 5 < 3.5 + |A| = 13.5.

## Consequences and caveats
- Piece A of Programme 2 is closed for large k. In fact richness alone suffices once τ > k/2 + 49/(3η); the 3/4 threshold is not used. The remaining content of (G) lies entirely in thin families (pieces B and C).
- With A = ∅, Theorem A1 is itself a new static criterion: H not 3-wise intersecting and y(V) + 3 max y < 2 imply not (7,2). It is incomparable with Theorem 3; on complete families it is weaker.
- Not done: independent verification, and Lean. The Lean statements are short (Lemma A0, A1, A2 on top of Lemma 2 and Theorem 3H).
