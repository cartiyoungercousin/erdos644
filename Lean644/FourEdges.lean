import Lean644.Triple

/-!
# Four edges (manuscript Lemma 2.4) and the 4-edges + 3-requests closure

After a fourth edge `K`, a pair `x, y` meeting `E, F, G, K` (with `E, F, G` good) has, up to
swapping `x` and `y`, one of six shapes:
* `x ∈ E ∩ F ∩ K`, `y ∈ G`;  `x ∈ E ∩ G ∩ K`, `y ∈ F`;  `x ∈ F ∩ G ∩ K`, `y ∈ E`;
* `x ∈ (E ∩ F) \ K`, `y ∈ K ∩ G \ (E ∪ F)`; and the two analogues for `E ∩ G`, `F ∩ G`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- One orientation of Lemma 2.4: `x` in a pair cell, `y` in the third edge, both meeting `K`. -/
theorem four_candidate_core {E F G K : Finset α} {x y : α} (hxE : x ∈ E) (hxF : x ∈ F)
    (_hyG : y ∈ G) (hK : x ∈ K ∨ y ∈ K) :
    (x ∈ K) ∨ (y ∈ K ∧ y ∈ E ∧ x ∈ F) ∨ (y ∈ K ∧ y ∈ F ∧ x ∈ E) ∨
    (x ∉ K ∧ y ∈ K ∧ y ∉ E ∧ y ∉ F) := by
  by_cases hx : x ∈ K
  · exact Or.inl hx
  have hy : y ∈ K := hK.resolve_left hx
  by_cases hyE : y ∈ E
  · exact Or.inr (Or.inl ⟨hy, hyE, hxF⟩)
  by_cases hyF : y ∈ F
  · exact Or.inr (Or.inr (Or.inl ⟨hy, hyF, hxE⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hx, hy, hyE, hyF⟩))

/-- Closure with four edges and three requests: if every pair meeting `E, F, G, K` lies in one
of three requests of size `≤ T`, property (7,2) fails (as `τ(H) > T`). -/
theorem closes_of_three_requests {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2)
    {T : ℕ} (hτ : ¬ CoverableBy H T) {E F G K : Finset α} (hE : E ∈ H) (hF : F ∈ H)
    (hG : G ∈ H) (hK : K ∈ H) (R₁ R₂ R₃ : Finset α) (h₁ : R₁.card ≤ T) (h₂ : R₂.card ≤ T)
    (h₃ : R₃.card ≤ T)
    (hcov : ∀ x y : α, (x ∈ E ∨ y ∈ E) → (x ∈ F ∨ y ∈ F) → (x ∈ G ∨ y ∈ G) →
      (x ∈ K ∨ y ∈ K) → (x ∈ R₁ ∧ y ∈ R₁) ∨ (x ∈ R₂ ∧ y ∈ R₂) ∨ (x ∈ R₃ ∧ y ∈ R₃)) :
    False := by
  refine request_cover (E := {E, F, G, K}) (D := {R₁, R₂, R₃}) hprop ?_ ⟨E, by simp⟩ ?_ ?_ ?_
  · intro A hA; simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl <;> assumption
  · exact (Nat.add_le_add Finset.card_le_four Finset.card_le_three)
  · intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> exact exists_response hτ ‹_›
  · intro x y hxy
    rcases hcov x y (hxy E (by simp)) (hxy F (by simp)) (hxy G (by simp)) (hxy K (by simp))
      with h | h | h
    · exact ⟨R₁, by simp, h⟩
    · exact ⟨R₂, by simp, h⟩
    · exact ⟨R₃, by simp, h⟩

end Erdos644
