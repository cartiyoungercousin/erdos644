import Lean644.Fano
import Lean644.Framework

/-!
# Rich families: Lemma A0, the colouring criterion and Theorem A1

Source: `notes/PROGRAMME2_A.md` (Theorem RA, piece A of Programme 2), verified in
`notes/verify/theorem_RA.md`; the colouring criterion is Lemma 2 of `notes/PROGRAMME_2.md`.

* `lemma_A0`: if every `≤ 3` members (repeats allowed) of a family of sets of size `≤ k` share a
  point, then `τ ≤ (k+1)/2`. Contrapositive form: `exists_triple_of_not_coverable`.
* `coverableBy_of_delete`: `τ(H) ≤ τ(H_A) + |A|`, where `H_A` is the subfamily avoiding `A`.
* `colouring_criterion` (Lemma 2, cover form): colour classes `C c` (indexed by the points of the
  Fano plane) cover every member; if for every line `ℓ` some member avoids the union `L_ℓ` of the
  classes on `ℓ`, then `H` is not (7,2). The colouring form with `χ : α → Fin 7` is
  `colouring_criterion_chi`.
* `theorem_A1` (split colouring): fractional transversal weights `y` (every transversal has
  `y`-mass `≥ 1`) are a hypothesis. If three members avoiding `A` have empty common intersection
  and `y(V∖A) + 3 a' < 2`, where `a'` bounds `y` on `V∖A`, then `H` is not (7,2).

Fano labelling (that of `Lean644/Fano.lean`): lines `ℓ₀ = 012, ℓ₁ = 034, ℓ₂ = 056, ℓ₃ = 135,
ℓ₄ = 146, ℓ₅ = 236, ℓ₆ = 245`. The incidence is symmetric, so `fanoPencil ℓ` lists both the lines
through the point `ℓ` and the points on the line `ℓ`. "(7,2)" is `HasPropertyAtMost H 7 2`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-! ## Lemma A0 -/

/-- **Lemma A0.** If all members have at most `k` points and every three members (not
necessarily distinct) share a point, then `τ(H) ≤ (k+1)/2` (natural-number division, which is
the same as the real bound since `τ` is an integer). -/
theorem lemma_A0 {H : Finset (Finset α)} {k : ℕ} (hk : ∀ B ∈ H, B.card ≤ k)
    (h3 : ∀ B₁ ∈ H, ∀ B₂ ∈ H, ∀ B₃ ∈ H, (B₁ ∩ B₂ ∩ B₃).Nonempty) :
    CoverableBy H ((k + 1) / 2) := by
  rcases H.eq_empty_or_nonempty with rfl | ⟨B₁, hB₁⟩
  · exact ⟨∅, by simp, fun A hA => by simp at hA⟩
  by_contra hτ
  -- every `B₁ ∩ B₂` is a transversal, hence has more than `(k+1)/2` points
  have hpair : ∀ B₂ ∈ H, (k + 1) / 2 < (B₁ ∩ B₂).card := by
    intro B₂ hB₂
    by_contra hle
    refine hτ ⟨B₁ ∩ B₂, Nat.le_of_not_lt hle, fun B₃ hB₃ => ?_⟩
    obtain ⟨v, hv⟩ := h3 B₁ hB₁ B₂ hB₂ B₃ hB₃
    simp only [Finset.mem_inter] at hv
    exact ⟨v, Finset.mem_inter.2 ⟨hv.2, Finset.mem_inter.2 ⟨hv.1.1, hv.1.2⟩⟩⟩
  have hB₁m : (k + 1) / 2 ≤ B₁.card := by
    have h := hpair B₁ hB₁
    rw [Finset.inter_self] at h
    exact h.le
  -- any `(k+1)/2` points of `B₁` form a transversal
  obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq hB₁m
  refine hτ ⟨T, hTc.le, fun B₂ hB₂ => ?_⟩
  by_contra hne
  have hsub : B₁ ∩ B₂ ⊆ B₁ \ T := by
    intro v hv
    rw [Finset.mem_inter] at hv
    refine Finset.mem_sdiff.2 ⟨hv.1, fun hvT => hne ⟨v, Finset.mem_inter.2 ⟨hv.2, hvT⟩⟩⟩
  have h1 : (B₁ ∩ B₂).card ≤ B₁.card - T.card := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_sdiff, Finset.inter_eq_left.2 hTB] at h
  have h2 := hpair B₂ hB₂
  have h3' := hk B₁ hB₁
  clear hsub hpair hTB hne h3 hk hτ
  omega

/-- Contrapositive of Lemma A0: if `τ(H) > (k+1)/2`, some three members (not necessarily
distinct) have empty common intersection. -/
theorem exists_triple_of_not_coverable {H : Finset (Finset α)} {k : ℕ}
    (hk : ∀ B ∈ H, B.card ≤ k) (hτ : ¬ CoverableBy H ((k + 1) / 2)) :
    ∃ B₁ ∈ H, ∃ B₂ ∈ H, ∃ B₃ ∈ H, B₁ ∩ B₂ ∩ B₃ = ∅ := by
  by_contra h
  push_neg at h
  exact hτ (lemma_A0 hk h)

/-- Deleting a set `A`: a transversal of the members avoiding `A`, together with `A`, is a
transversal of `H`. So `τ(H) ≤ τ(H_A) + |A|`. -/
theorem coverableBy_of_delete {H : Finset (Finset α)} (A : Finset α) {t : ℕ}
    (h : CoverableBy (H.filter (fun B => Disjoint B A)) t) : CoverableBy H (t + A.card) := by
  obtain ⟨T, hT, htr⟩ := h
  refine ⟨T ∪ A, (Finset.card_union_le T A).trans (Nat.add_le_add_right hT _), ?_⟩
  intro B hB
  by_cases hd : Disjoint B A
  · obtain ⟨v, hv⟩ := htr B (Finset.mem_filter.2 ⟨hB, hd⟩)
    rw [Finset.mem_inter] at hv
    exact ⟨v, Finset.mem_inter.2 ⟨hv.1, Finset.mem_union_left _ hv.2⟩⟩
  · obtain ⟨v, hv⟩ := Finset.not_disjoint_iff_nonempty_inter.1 hd
    rw [Finset.mem_inter] at hv
    exact ⟨v, Finset.mem_inter.2 ⟨hv.1, Finset.mem_union_right _ hv.2⟩⟩

/-! ## The colouring criterion (Lemma 2) -/

/-- `L_ℓ`: the union of the colour classes `C c` over the three points `c` of the line `ℓ`. -/
def fanoLineSet (C : Fin 7 → Finset α) (ℓ : Fin 7) : Finset α :=
  C (fanoPencil ℓ).1 ∪ C (fanoPencil ℓ).2.1 ∪ C (fanoPencil ℓ).2.2

/-- Any two points of the Fano plane lie on a common line: for every `p` and `c`, the point `c`
lies on one of the three lines through `p`. -/
theorem fano_join : ∀ p c : Fin 7,
    (c = (fanoPencil (fanoPencil p).1).1 ∨ c = (fanoPencil (fanoPencil p).1).2.1 ∨
      c = (fanoPencil (fanoPencil p).1).2.2) ∨
    (c = (fanoPencil (fanoPencil p).2.1).1 ∨ c = (fanoPencil (fanoPencil p).2.1).2.1 ∨
      c = (fanoPencil (fanoPencil p).2.1).2.2) ∨
    (c = (fanoPencil (fanoPencil p).2.2).1 ∨ c = (fanoPencil (fanoPencil p).2.2).2.1 ∨
      c = (fanoPencil (fanoPencil p).2.2).2.2) := by
  decide

theorem mem_fanoLineSet {C : Fin 7 → Finset α} {ℓ c : Fin 7}
    (hc : c = (fanoPencil ℓ).1 ∨ c = (fanoPencil ℓ).2.1 ∨ c = (fanoPencil ℓ).2.2)
    {v : α} (hv : v ∈ C c) : v ∈ fanoLineSet C ℓ := by
  unfold fanoLineSet
  rcases hc with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  · exact Finset.mem_union_right _ hv

/-- **Colouring criterion (Lemma 2), cover form.** The classes `C c` need not be disjoint; they
only have to cover every point of every member. If for each line `ℓ` some member of `H` avoids
`L_ℓ`, these seven members have no 2-point transversal, so `H` is not (7,2). -/
theorem colouring_criterion {H : Finset (Finset α)} (C : Fin 7 → Finset α)
    (hcov : ∀ B ∈ H, ∀ v ∈ B, ∃ c, v ∈ C c)
    (hline : ∀ ℓ, ∃ B ∈ H, Disjoint B (fanoLineSet C ℓ)) :
    ¬ HasPropertyAtMost H 7 2 := by
  intro hprop
  choose B hBH hBd using hline
  have hsub : Finset.univ.image B ⊆ H := by
    intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    exact hBH i
  have hcard : (Finset.univ.image B).card ≤ 7 := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 7))) (f := B)
  refine fano_criterion B ?_ (hprop _ hsub hcard)
  rintro p v ⟨h1, h2, h3⟩
  obtain ⟨c, hc⟩ := hcov _ (hBH _) v h1
  have hmiss : ∀ ℓ : Fin 7,
      (c = (fanoPencil ℓ).1 ∨ c = (fanoPencil ℓ).2.1 ∨ c = (fanoPencil ℓ).2.2) → v ∉ B ℓ :=
    fun ℓ hℓ hvB => Finset.disjoint_left.1 (hBd ℓ) hvB (mem_fanoLineSet hℓ hc)
  rcases fano_join p c with h | h | h
  · exact hmiss _ h h1
  · exact hmiss _ h h2
  · exact hmiss _ h h3

/-- Lemma 2 with "no `L_ℓ` is a transversal". -/
theorem colouring_criterion' {H : Finset (Finset α)} (C : Fin 7 → Finset α)
    (hcov : ∀ B ∈ H, ∀ v ∈ B, ∃ c, v ∈ C c)
    (hline : ∀ ℓ, ¬ IsTransversal H (fanoLineSet C ℓ)) :
    ¬ HasPropertyAtMost H 7 2 := by
  refine colouring_criterion C hcov fun ℓ => ?_
  have h := hline ℓ
  unfold IsTransversal at h
  push_neg at h
  obtain ⟨B, hB, hBe⟩ := h
  exact ⟨B, hB, Finset.disjoint_iff_inter_eq_empty.2 hBe⟩

/-- **Lemma 2, colouring form.** `χ` colours the ground set `V ⊇ ∪H` by the points of the Fano
plane, `L_ℓ = {v ∈ V : χ v ∈ ℓ}`. If no `L_ℓ` is a transversal, `H` is not (7,2). -/
theorem colouring_criterion_chi {H : Finset (Finset α)} (V : Finset α)
    (hV : ∀ B ∈ H, B ⊆ V) (χ : α → Fin 7)
    (hline : ∀ ℓ, ¬ IsTransversal H (fanoLineSet (fun c => V.filter (fun v => χ v = c)) ℓ)) :
    ¬ HasPropertyAtMost H 7 2 :=
  colouring_criterion' _ (fun B hB v hv => ⟨χ v,
    (Finset.mem_filter.2 ⟨hV B hB hv, rfl⟩ : v ∈ V.filter (fun w => χ w = χ v))⟩) hline

/-! ## Theorem A1 (split colouring) -/

/-- Greedy balanced split: points of weight in `[0, b]` split into two parts whose masses differ
by at most `b`. -/
theorem balanced_split (y : α → ℝ) {b : ℝ} (hb : 0 ≤ b) (X : Finset α)
    (hX : ∀ v ∈ X, 0 ≤ y v ∧ y v ≤ b) :
    ∃ P Q : Finset α, Disjoint P Q ∧ P ∪ Q = X ∧
      |∑ v ∈ P, y v - ∑ v ∈ Q, y v| ≤ b := by
  induction X using Finset.induction_on with
  | empty => exact ⟨∅, ∅, by simp, by simp, by simpa using hb⟩
  | insert a X ha ih =>
    obtain ⟨P, Q, hPQ, hU, hd⟩ :=
      ih (fun v hv => hX v (Finset.mem_insert_of_mem hv))
    obtain ⟨hya0, hyab⟩ := hX a (Finset.mem_insert_self a X)
    have haP : a ∉ P := fun h => ha (hU ▸ Finset.mem_union_left _ h)
    have haQ : a ∉ Q := fun h => ha (hU ▸ Finset.mem_union_right _ h)
    obtain ⟨hd1, hd2⟩ := abs_le.1 hd
    by_cases hle : ∑ v ∈ P, y v ≤ ∑ v ∈ Q, y v
    · refine ⟨insert a P, Q, Finset.disjoint_insert_left.2 ⟨haQ, hPQ⟩, ?_, ?_⟩
      · rw [Finset.insert_union, hU]
      · rw [Finset.sum_insert haP, abs_le]
        constructor <;> linarith
    · refine ⟨P, insert a Q, Finset.disjoint_insert_right.2 ⟨haP, hPQ⟩, ?_, ?_⟩
      · rw [Finset.union_insert, hU]
      · rw [Finset.sum_insert haQ, abs_le]
        constructor <;> linarith

theorem sum_union_le_of_nonneg (y : α → ℝ) (S T : Finset α) (hy : ∀ v ∈ S ∩ T, 0 ≤ y v) :
    ∑ v ∈ S ∪ T, y v ≤ ∑ v ∈ S, y v + ∑ v ∈ T, y v := by
  have h := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := y)
  have h0 : 0 ≤ ∑ v ∈ S ∩ T, y v := Finset.sum_nonneg hy
  linarith

/-- **Theorem A1 (split colouring).** `V ⊇ ∪H` is the ground set and `y ≥ 0` a fractional
weighting with `y(M) ≥ 1` for every transversal `M ⊆ V`. Let `a'` bound `y` on the light points
`V ∖ A`. If three members `B_a, B_b, B_c` of `H_A` (the members avoiding `A`; not necessarily
distinct) have empty common intersection and `y(V ∖ A) + 3a' < 2`, then `H` is not (7,2). -/
theorem theorem_A1 {H : Finset (Finset α)} (V A : Finset α) (hV : ∀ B ∈ H, B ⊆ V)
    (y : α → ℝ) (hy0 : ∀ v ∈ V, 0 ≤ y v)
    (hyT : ∀ M ⊆ V, IsTransversal H M → 1 ≤ ∑ v ∈ M, y v)
    (a' : ℝ) (ha' : ∀ v ∈ V \ A, y v ≤ a')
    {Ba Bb Bc : Finset α} (hBa : Ba ∈ H) (hBb : Bb ∈ H) (hBc : Bc ∈ H)
    (hAa : Disjoint Ba A) (hAb : Disjoint Bb A) (hAc : Disjoint Bc A)
    (hempty : Ba ∩ Bb ∩ Bc = ∅)
    (hmass : ∑ v ∈ V \ A, y v + 3 * a' < 2) :
    ¬ HasPropertyAtMost H 7 2 := by
  -- the light points and a nonnegative bound `b` on their weights
  have hWV : V \ A ⊆ V := Finset.sdiff_subset
  have hb0 : 0 ≤ max a' 0 := le_max_right _ _
  have hyb : ∀ v ∈ V \ A, 0 ≤ y v ∧ y v ≤ max a' 0 :=
    fun v hv => ⟨hy0 v (hWV hv), (ha' v hv).trans (le_max_left _ _)⟩
  have hmass' : ∑ v ∈ V \ A, y v + 3 * max a' 0 < 2 := by
    rcases le_total a' 0 with h | h
    · rw [max_eq_right h]
      rcases (V \ A).eq_empty_or_nonempty with hW | ⟨v, hv⟩
      · rw [hW]; norm_num
      · have h1 := hy0 v (hWV hv)
        have h2 := ha' v hv
        linarith
    · rw [max_eq_left h]; exact hmass
  -- the three classes `X₁, X₂, X₃` of light points (`v ∉ B_s`)
  have hsumW : ∑ v ∈ (V \ A).filter (fun v => v ∉ Ba), y v
      + ∑ v ∈ ((V \ A).filter (fun v => v ∈ Ba)).filter (fun v => v ∉ Bb), y v
      + ∑ v ∈ ((V \ A).filter (fun v => v ∈ Ba)).filter (fun v => v ∈ Bb), y v
      = ∑ v ∈ V \ A, y v := by
    have e1 := Finset.sum_filter_add_sum_filter_not (V \ A) (fun v => v ∈ Ba) y
    have e2 := Finset.sum_filter_add_sum_filter_not
      ((V \ A).filter (fun v => v ∈ Ba)) (fun v => v ∈ Bb) y
    linarith
  have hX₁W : (V \ A).filter (fun v => v ∉ Ba) ⊆ V \ A := Finset.filter_subset _ _
  have hX₂W : ((V \ A).filter (fun v => v ∈ Ba)).filter (fun v => v ∉ Bb) ⊆ V \ A :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hX₃W : ((V \ A).filter (fun v => v ∈ Ba)).filter (fun v => v ∈ Bb) ⊆ V \ A :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  obtain ⟨P₁, Q₁, hd₁, hu₁, hb₁⟩ :=
    balanced_split y hb0 _ (fun v hv => hyb v (hX₁W hv))
  obtain ⟨P₂, Q₂, hd₂, hu₂, hb₂⟩ :=
    balanced_split y hb0 _ (fun v hv => hyb v (hX₂W hv))
  obtain ⟨P₃, Q₃, hd₃, hu₃, hb₃⟩ :=
    balanced_split y hb0 _ (fun v hv => hyb v (hX₃W hv))
  have e₁ := Finset.sum_union hd₁ (f := y)
  have e₂ := Finset.sum_union hd₂ (f := y)
  have e₃ := Finset.sum_union hd₃ (f := y)
  rw [hu₁] at e₁
  rw [hu₂] at e₂
  rw [hu₃] at e₃
  obtain ⟨b₁l, b₁r⟩ := abs_le.1 hb₁
  obtain ⟨b₂l, b₂r⟩ := abs_le.1 hb₂
  obtain ⟨b₃l, b₃r⟩ := abs_le.1 hb₃
  have hP₁ : P₁ ⊆ V \ A := (hu₁ ▸ Finset.subset_union_left).trans hX₁W
  have hQ₁ : Q₁ ⊆ V \ A := (hu₁ ▸ Finset.subset_union_right).trans hX₁W
  have hP₂ : P₂ ⊆ V \ A := (hu₂ ▸ Finset.subset_union_left).trans hX₂W
  have hQ₂ : Q₂ ⊆ V \ A := (hu₂ ▸ Finset.subset_union_right).trans hX₂W
  have hP₃ : P₃ ⊆ V \ A := (hu₃ ▸ Finset.subset_union_left).trans hX₃W
  have hQ₃ : Q₃ ⊆ V \ A := (hu₃ ▸ Finset.subset_union_right).trans hX₃W
  -- a union of three light sets of small total mass is not a transversal
  have key : ∀ S₁ S₂ S₃ : Finset α, S₁ ⊆ V \ A → S₂ ⊆ V \ A → S₃ ⊆ V \ A →
      2 * (∑ v ∈ S₁, y v + ∑ v ∈ S₂, y v + ∑ v ∈ S₃, y v)
        ≤ ∑ v ∈ V \ A, y v + 3 * max a' 0 →
      ∃ B ∈ H, Disjoint B (S₁ ∪ S₂ ∪ S₃) := by
    intro S₁ S₂ S₃ h₁ h₂ h₃ hS
    by_contra hno
    push_neg at hno
    have hsub : S₁ ∪ S₂ ∪ S₃ ⊆ V :=
      (Finset.union_subset (Finset.union_subset h₁ h₂) h₃).trans hWV
    have hT : IsTransversal H (S₁ ∪ S₂ ∪ S₃) :=
      fun B hB => Finset.not_disjoint_iff_nonempty_inter.1 (hno B hB)
    have hM := hyT _ hsub hT
    have u1 := sum_union_le_of_nonneg y (S₁ ∪ S₂) S₃
      (fun v hv => hy0 v (hsub (Finset.mem_union_left _ (Finset.inter_subset_left hv))))
    have u2 := sum_union_le_of_nonneg y S₁ S₂
      (fun v hv => hy0 v (hsub (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.inter_subset_left hv)))))
    linarith
  -- the colouring: `A ↦ 0`, halves of `X_s` ↦ the two points of the `s`-th pair
  let C : Fin 7 → Finset α := ![A, P₁, Q₁, P₂, Q₂, P₃, Q₃]
  refine colouring_criterion (H := H) C ?_ ?_
  · intro B hB v hv
    by_cases hvA : v ∈ A
    · exact ⟨0, hvA⟩
    have hvW : v ∈ V \ A := Finset.mem_sdiff.2 ⟨hV B hB hv, hvA⟩
    by_cases hva : v ∈ Ba
    · by_cases hvb : v ∈ Bb
      · have hx : v ∈ P₃ ∪ Q₃ := by
          rw [hu₃]; exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hvW, hva⟩, hvb⟩
        rcases Finset.mem_union.1 hx with h | h
        · exact ⟨5, h⟩
        · exact ⟨6, h⟩
      · have hx : v ∈ P₂ ∪ Q₂ := by
          rw [hu₂]; exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hvW, hva⟩, hvb⟩
        rcases Finset.mem_union.1 hx with h | h
        · exact ⟨3, h⟩
        · exact ⟨4, h⟩
    · have hx : v ∈ P₁ ∪ Q₁ := by
        rw [hu₁]; exact Finset.mem_filter.2 ⟨hvW, hva⟩
      rcases Finset.mem_union.1 hx with h | h
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  · -- the three lines through `0`
    have l0 : ∃ B ∈ H, Disjoint B (A ∪ P₁ ∪ Q₁) := by
      refine ⟨Ba, hBa, ?_⟩
      rw [Finset.union_assoc, hu₁]
      refine Finset.disjoint_union_right.2 ⟨hAa, Finset.disjoint_left.2 fun v hv hvX => ?_⟩
      exact (Finset.mem_filter.1 hvX).2 hv
    have l1 : ∃ B ∈ H, Disjoint B (A ∪ P₂ ∪ Q₂) := by
      refine ⟨Bb, hBb, ?_⟩
      rw [Finset.union_assoc, hu₂]
      refine Finset.disjoint_union_right.2 ⟨hAb, Finset.disjoint_left.2 fun v hv hvX => ?_⟩
      exact (Finset.mem_filter.1 hvX).2 hv
    have l2 : ∃ B ∈ H, Disjoint B (A ∪ P₃ ∪ Q₃) := by
      refine ⟨Bc, hBc, ?_⟩
      rw [Finset.union_assoc, hu₃]
      refine Finset.disjoint_union_right.2 ⟨hAc, Finset.disjoint_left.2 fun v hv hvX => ?_⟩
      obtain ⟨hv1, hvb⟩ := Finset.mem_filter.1 hvX
      have hva := (Finset.mem_filter.1 hv1).2
      have : v ∈ Ba ∩ Bb ∩ Bc := by simp [hva, hvb, hv]
      rw [hempty] at this
      simp at this
    -- the four lines avoiding `0`: one half of each pair
    have l3 : ∃ B ∈ H, Disjoint B (P₁ ∪ P₂ ∪ P₃) := key _ _ _ hP₁ hP₂ hP₃ (by linarith)
    have l4 : ∃ B ∈ H, Disjoint B (P₁ ∪ Q₂ ∪ Q₃) := key _ _ _ hP₁ hQ₂ hQ₃ (by linarith)
    have l5 : ∃ B ∈ H, Disjoint B (Q₁ ∪ P₂ ∪ Q₃) := key _ _ _ hQ₁ hP₂ hQ₃ (by linarith)
    have l6 : ∃ B ∈ H, Disjoint B (Q₁ ∪ Q₂ ∪ P₃) := key _ _ _ hQ₁ hQ₂ hP₃ (by linarith)
    intro ℓ
    fin_cases ℓ
    exacts [l0, l1, l2, l3, l4, l5, l6]

/-! ## Non-vacuity -/

/-- Every hypothesis of Theorem A1 holds for `H = {{0}, {1,2}, {1,3}, {2,3}}` with the heavy set
`A = {0}`, `y = δ₀` (every transversal contains `0`), `a' = 0`, and the triple `12, 13, 23` of
`H_A` (empty common intersection); `y(V∖A) + 3a' = 0 < 2`. -/
example : ¬ HasPropertyAtMost ({{0}, {1, 2}, {1, 3}, {2, 3}} : Finset (Finset ℕ)) 7 2 := by
  refine theorem_A1 (V := {0, 1, 2, 3}) (A := {0}) (y := fun v => if v = 0 then 1 else 0)
    (a' := 0) (Ba := {1, 2}) (Bb := {1, 3}) (Bc := {2, 3}) (by decide) ?_ ?_ ?_
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  · intro v _
    split_ifs <;> norm_num
  · intro M _ hT
    obtain ⟨w, hw⟩ := hT {0} (by simp)
    have h0 : (0 : ℕ) ∈ M := by
      rw [Finset.mem_inter, Finset.mem_singleton] at hw
      exact hw.1 ▸ hw.2
    have h := Finset.single_le_sum (f := fun v : ℕ => if v = 0 then (1 : ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) h0
    simpa using h
  · intro v hv
    have hv0 : v ≠ 0 := fun h => (Finset.mem_sdiff.1 hv).2 (by simp [h])
    simp [hv0]
  · have : ∑ v ∈ ({0, 1, 2, 3} : Finset ℕ) \ {0}, (if v = 0 then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have hv0 : v ≠ 0 := fun h => (Finset.mem_sdiff.1 hv).2 (by simp [h])
      simp [hv0]
    rw [this]
    norm_num

end Erdos644
