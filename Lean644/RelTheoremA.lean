import Lean644.TheoremA

/-!
# Theorem 8.1: Theorem A relative to a set `W`

Source: `notes/NEW_PATHS.md` §8.2 (Fable research lead, 2026-11-23); hand-checked.

Let `A ∈ H`, `A ⊆ W`, and suppose any two distinct edges share at most `ρ` points outside `W`.
Template of Theorem A on `W`: `A = a₁ ⊔ … ⊔ a₄`, `W ∖ A = B₁ ⊔ B₂ ⊔ B₃`.
Group 1: `R₁ = B₁∪a₁∪a₂`, `R₂ = B₁∪a₃∪a₄` (responses `K₁, K₂`).
Group 2: `R₃ = B₂∪a₁∪a₃`, `R₄ = B₂∪a₂∪a₄`, each plus one point of `K₁ ∖ W` and one of `K₂ ∖ W`
(if any), so that `K₃, K₄ ∉ {K₁, K₂}` whenever this matters.
Group 3: `R₅ = B₃∪a₁∪a₄ ∪ (K₁∩K₃∖W) ∪ (K₂∩K₄∖W)`, `R₆ = B₃∪a₂∪a₃ ∪ (K₁∩K₄∖W) ∪ (K₂∩K₃∖W)`.
Then `A, K₁, …, K₄` and the responses to `R₅, R₆` have no 2-point cover.
Outside points cost only through the four pairwise overlaps (`2ρ` per group-3 request).
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Theorem 8.1 (Theorem A relative to `W`).** -/
theorem relTheoremA_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2)
    {T k ρ : ℕ} (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (W : Finset α)
    {A : Finset α} (hA : A ∈ H) (hAW : A ⊆ W)
    (hρ : ∀ P ∈ H, ∀ Q ∈ H, P ≠ Q → ((P ∩ Q) \ W).card ≤ ρ)
    (hρc : 2 * ρ ≤ (W.card - k + 2 * ρ + 2) / 3)
    (hT : (W.card - k + 2 * ρ + 2) / 3 + 2 * ((k + 3) / 4) + 2 ≤ T) : False := by
  have hAk := hunif A hA
  have hs : (W \ A).card = W.card - k := by rw [Finset.card_sdiff_of_subset hAW, hAk]
  set c := (W.card - k + 2 * ρ + 2) / 3 with hc
  obtain ⟨a₁, a₂, a₃, a₄, covA, ca₁, ca₂, ca₃, ca₄⟩ :=
    split_four A (k / 4) ((k + 1) / 4) ((k + 2) / 4) ((k + 3) / 4) (by omega)
  obtain ⟨β₁, β₂, hβ₁, hβ₂, hβ₃⟩ : ∃ β₁ β₂, β₁ ≤ c ∧ β₂ ≤ c ∧ β₁ + β₂ ≤ W.card - k ∧
      W.card - k - β₁ - β₂ + 2 * ρ ≤ c :=
    ⟨min (W.card - k) c, min (W.card - k - min (W.card - k) c) c, min_le_right _ _,
      min_le_right _ _, by omega, by
        rcases min_choice (W.card - k) c with h | h <;>
          rcases min_choice (W.card - k - min (W.card - k) c) c with h' | h' <;> omega⟩
  obtain ⟨B₁, B₂, B₃, -, -, -, covB, cB₁, cB₂, cB₃⟩ :=
    split_three (W \ A) β₁ β₂ (W.card - k - β₁ - β₂) (by omega)
  have q4 : ∀ P Q : Finset α, P.card ≤ (k + 3) / 4 → Q.card ≤ (k + 3) / 4 →
      (P ∪ Q).card ≤ 2 * ((k + 3) / 4) := fun P Q h1 h2 =>
    (Finset.card_union_le _ _).trans (by omega)
  -- group 1
  obtain ⟨K₁, hK₁, d₁⟩ := exists_response hτ (d := B₁ ∪ a₁ ∪ a₂)
    ((Finset.card_union_le _ _).trans (by have := Finset.card_union_le B₁ a₁; omega))
  obtain ⟨K₂, hK₂, d₂⟩ := exists_response hτ (d := B₁ ∪ a₃ ∪ a₄)
    ((Finset.card_union_le _ _).trans (by have := Finset.card_union_le B₁ a₃; omega))
  -- one witness point of K₁ ∖ W and of K₂ ∖ W
  obtain ⟨Z₁, hZ₁, cZ₁⟩ := Finset.exists_subset_card_eq (min_le_right 1 (K₁ \ W).card)
  obtain ⟨Z₂, hZ₂, cZ₂⟩ := Finset.exists_subset_card_eq (min_le_right 1 (K₂ \ W).card)
  have z12 : (Z₁ ∪ Z₂).card ≤ 2 := (Finset.card_union_le _ _).trans (by omega)
  -- group 2
  obtain ⟨K₃, hK₃, d₃⟩ := exists_response hτ (d := B₂ ∪ a₁ ∪ a₃ ∪ (Z₁ ∪ Z₂))
    ((Finset.card_union_le _ _).trans
      (by have := Finset.card_union_le B₂ a₁; have := Finset.card_union_le (B₂ ∪ a₁) a₃; omega))
  obtain ⟨K₄, hK₄, d₄⟩ := exists_response hτ (d := B₂ ∪ a₂ ∪ a₄ ∪ (Z₁ ∪ Z₂))
    ((Finset.card_union_le _ _).trans
      (by have := Finset.card_union_le B₂ a₂; have := Finset.card_union_le (B₂ ∪ a₂) a₄; omega))
  -- outside overlaps are at most ρ
  have ov : ∀ P Q : Finset α, P ∈ H → Q ∈ H → ∀ Z : Finset α, Z ⊆ P \ W →
      Z.card = min 1 (P \ W).card → Disjoint Q Z → ((P ∩ Q) \ W).card ≤ ρ := by
    intro P Q hP hQ Z hZ cZ hd
    by_cases he : (P \ W).card = 0
    · have : (P ∩ Q) \ W ⊆ P \ W := fun v hv => by
        simp only [Finset.mem_sdiff, Finset.mem_inter] at hv ⊢; exact ⟨hv.1.1, hv.2⟩
      have := Finset.card_le_card this; omega
    · refine hρ P hP Q hQ ?_
      rintro rfl
      obtain ⟨z, hz⟩ := Finset.card_pos.1 (show 0 < Z.card by omega)
      exact Finset.disjoint_left.1 hd ((Finset.mem_sdiff.1 (hZ hz)).1) hz
  have dZ : ∀ {K S Z₁ Z₂ : Finset α}, Disjoint K (S ∪ (Z₁ ∪ Z₂)) → Disjoint K Z₁ ∧ Disjoint K Z₂ :=
    fun h => ⟨Finset.disjoint_of_subset_right (fun v hv => by simp [hv]) h,
      Finset.disjoint_of_subset_right (fun v hv => by simp [hv]) h⟩
  have o13 := ov K₁ K₃ hK₁ hK₃ Z₁ hZ₁ cZ₁ (dZ d₃).1
  have o14 := ov K₁ K₄ hK₁ hK₄ Z₁ hZ₁ cZ₁ (dZ d₄).1
  have o23 := ov K₂ K₃ hK₂ hK₃ Z₂ hZ₂ cZ₂ (dZ d₃).2
  have o24 := ov K₂ K₄ hK₂ hK₄ Z₂ hZ₂ cZ₂ (dZ d₄).2
  -- group 3
  set R₅ := B₃ ∪ a₁ ∪ a₄ ∪ (((K₁ ∩ K₃) \ W) ∪ ((K₂ ∩ K₄) \ W))
  set R₆ := B₃ ∪ a₂ ∪ a₃ ∪ (((K₁ ∩ K₄) \ W) ∪ ((K₂ ∩ K₃) \ W))
  have r5 : R₅.card ≤ T := (Finset.card_union_le _ _).trans (by
    have := Finset.card_union_le B₃ a₁; have := Finset.card_union_le (B₃ ∪ a₁) a₄
    have := Finset.card_union_le ((K₁ ∩ K₃) \ W) ((K₂ ∩ K₄) \ W); omega)
  have r6 : R₆.card ≤ T := (Finset.card_union_le _ _).trans (by
    have := Finset.card_union_le B₃ a₂; have := Finset.card_union_le (B₃ ∪ a₂) a₃
    have := Finset.card_union_le ((K₁ ∩ K₄) \ W) ((K₂ ∩ K₃) \ W); omega)
  -- avoidance
  have av : ∀ {K S : Finset α} {v : α}, Disjoint K S → v ∈ S → v ∉ K := fun h hv hK =>
    Finset.disjoint_left.1 h hK hv
  -- the covering step: x ∈ A, y anywhere
  have key : ∀ x y, x ∈ A → (x ∈ K₁ ∨ y ∈ K₁) → (x ∈ K₂ ∨ y ∈ K₂) → (x ∈ K₃ ∨ y ∈ K₃) →
      (x ∈ K₄ ∨ y ∈ K₄) → (x ∈ R₅ ∧ y ∈ R₅) ∨ (x ∈ R₆ ∧ y ∈ R₆) := by
    intro x y hx c1 c2 c3 c4
    -- where y can lie
    have yW : ∀ {P Q : Finset α}, y ∈ P → y ∈ Q →
        y ∈ a₁ ∨ y ∈ a₂ ∨ y ∈ a₃ ∨ y ∈ a₄ ∨ y ∈ B₁ ∨ y ∈ B₂ ∨ y ∈ B₃ ∨ y ∈ (P ∩ Q) \ W := by
      intro P Q hP hQ
      by_cases hyW : y ∈ W
      · by_cases hyA : y ∈ A
        · rcases covA y hyA with h | h | h | h <;> simp [h]
        · rcases covB y (Finset.mem_sdiff.2 ⟨hyW, hyA⟩) with h | h | h <;> simp [h]
      · simp [hP, hQ, hyW]
    rcases covA x hx with p | p | p | p
    · -- x ∈ a₁: misses K₁, K₃; so y ∈ K₁ ∩ K₃
      have y1 := c1.resolve_left (av d₁ (by simp [p]))
      have y3 := c3.resolve_left (av d₃ (by simp [p]))
      rcases yW y1 y3 with h | h | h | h | h | h | h | h
      · exact Or.inl ⟨by simp [R₅, p], by simp [R₅, h]⟩
      · exact absurd y1 (av d₁ (by simp [h]))
      · exact absurd y3 (av d₃ (by simp [h]))
      · exact Or.inl ⟨by simp [R₅, p], by simp [R₅, h]⟩
      · exact absurd y1 (av d₁ (by simp [h]))
      · exact absurd y3 (av d₃ (by simp [h]))
      · exact Or.inl ⟨by simp [R₅, p], by simp [R₅, h]⟩
      · exact Or.inl ⟨by simp [R₅, p], by simp only [R₅, Finset.mem_union]; exact Or.inr (Or.inl h)⟩
    · -- x ∈ a₂: misses K₁, K₄
      have y1 := c1.resolve_left (av d₁ (by simp [p]))
      have y4 := c4.resolve_left (av d₄ (by simp [p]))
      rcases yW y1 y4 with h | h | h | h | h | h | h | h
      · exact absurd y1 (av d₁ (by simp [h]))
      · exact absurd y1 (av d₁ (by simp [h]))
      · exact Or.inr ⟨by simp [R₆, p], by simp [R₆, h]⟩
      · exact absurd y4 (av d₄ (by simp [h]))
      · exact absurd y1 (av d₁ (by simp [h]))
      · exact absurd y4 (av d₄ (by simp [h]))
      · exact Or.inr ⟨by simp [R₆, p], by simp [R₆, h]⟩
      · exact Or.inr ⟨by simp [R₆, p], by simp only [R₆, Finset.mem_union]; exact Or.inr (Or.inl h)⟩
    · -- x ∈ a₃: misses K₂, K₃
      have y2 := c2.resolve_left (av d₂ (by simp [p]))
      have y3 := c3.resolve_left (av d₃ (by simp [p]))
      rcases yW y2 y3 with h | h | h | h | h | h | h | h
      · exact absurd y3 (av d₃ (by simp [h]))
      · exact Or.inr ⟨by simp [R₆, p], by simp [R₆, h]⟩
      · exact absurd y2 (av d₂ (by simp [h]))
      · exact absurd y2 (av d₂ (by simp [h]))
      · exact absurd y2 (av d₂ (by simp [h]))
      · exact absurd y3 (av d₃ (by simp [h]))
      · exact Or.inr ⟨by simp [R₆, p], by simp [R₆, h]⟩
      · exact Or.inr ⟨by simp [R₆, p], by simp only [R₆, Finset.mem_union]; exact Or.inr (Or.inr h)⟩
    · -- x ∈ a₄: misses K₂, K₄
      have y2 := c2.resolve_left (av d₂ (by simp [p]))
      have y4 := c4.resolve_left (av d₄ (by simp [p]))
      rcases yW y2 y4 with h | h | h | h | h | h | h | h
      · exact Or.inl ⟨by simp [R₅, p], by simp [R₅, h]⟩
      · exact absurd y4 (av d₄ (by simp [h]))
      · exact absurd y2 (av d₂ (by simp [h]))
      · exact absurd y2 (av d₂ (by simp [h]))
      · exact absurd y2 (av d₂ (by simp [h]))
      · exact absurd y4 (av d₄ (by simp [h]))
      · exact Or.inl ⟨by simp [R₅, p], by simp [R₅, h]⟩
      · exact Or.inl ⟨by simp [R₅, p], by simp only [R₅, Finset.mem_union]; exact Or.inr (Or.inr h)⟩
  refine request_cover hprop (E := {A, K₁, K₂, K₃, K₄}) (D := {R₅, R₆}) ?_ ⟨A, by simp⟩ ?_ ?_ ?_
  · intro P hP; simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> assumption
  · have a : ({A, K₁, K₂, K₃, K₄} : Finset (Finset α)).card ≤ 5 :=
      (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <| (Finset.card_insert_le _ _).trans
        <| Nat.succ_le_succ <| (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <|
          (Finset.card_insert_le _ _).trans (by simp)
    have b : ({R₅, R₆} : Finset (Finset α)).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega
  · intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    exacts [exists_response hτ r5, exists_response hτ r6]
  · intro x y hxy
    have cA := hxy A (by simp)
    have c1 := hxy K₁ (by simp)
    have c2 := hxy K₂ (by simp)
    have c3 := hxy K₃ (by simp)
    have c4 := hxy K₄ (by simp)
    rcases cA with hx | hy
    · rcases key x y hx c1 c2 c3 c4 with h | h
      · exact ⟨R₅, by simp, h⟩
      · exact ⟨R₆, by simp, h⟩
    · rcases key y x hy c1.symm c2.symm c3.symm c4.symm with h | h
      · exact ⟨R₅, by simp, h.2, h.1⟩
      · exact ⟨R₆, by simp, h.2, h.1⟩

end Erdos644
