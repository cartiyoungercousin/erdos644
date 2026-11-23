import Lean644.Framework

/-!
# Good triples (manuscript §2.3)

A triple `E, F, G` is *good* if `E ∩ F ∩ G = ∅`. A pair `x, y` meeting all three edges
(a *candidate pair*) must have one point in a pair cell (`E ∩ F`, `E ∩ G` or `F ∩ G`) and the
other point in the remaining edge — this is manuscript equation (2.1) in compact form.

`closes_of_four_requests`: a good triple of edges of `H` plus four requests of size `≤ T`
covering all candidate pairs contradicts property (7,2) when `τ(H) > T`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- Good triple: empty common intersection. -/
def IsGoodTriple (E F G : Finset α) : Prop := E ∩ F ∩ G = ∅

/-- Candidate pairs of a good triple (manuscript eq. (2.1)), as a case split. -/
theorem triple_candidate {E F G : Finset α} (hgood : IsGoodTriple E F G) {x y : α}
    (hE : x ∈ E ∨ y ∈ E) (hF : x ∈ F ∨ y ∈ F) (hG : x ∈ G ∨ y ∈ G) :
    (x ∈ E ∧ x ∈ F ∧ y ∈ G) ∨ (x ∈ E ∧ x ∈ G ∧ y ∈ F) ∨ (x ∈ F ∧ x ∈ G ∧ y ∈ E) ∨
    (y ∈ E ∧ y ∈ F ∧ x ∈ G) ∨ (y ∈ E ∧ y ∈ G ∧ x ∈ F) ∨ (y ∈ F ∧ y ∈ G ∧ x ∈ E) := by
  have hx : ¬ (x ∈ E ∧ x ∈ F ∧ x ∈ G) := fun h => by
    have : x ∈ E ∩ F ∩ G := by simp [h.1, h.2.1, h.2.2]
    simp [IsGoodTriple] at hgood; simp_all
  have hy : ¬ (y ∈ E ∧ y ∈ F ∧ y ∈ G) := fun h => by
    have : y ∈ E ∩ F ∩ G := by simp [h.1, h.2.1, h.2.2]
    simp [IsGoodTriple] at hgood; simp_all
  tauto

/-- A good triple closes with four requests (static or adaptive — the requests may have been
chosen after seeing other responses): if every candidate pair lies in one of `R₁,…,R₄`, each of
size at most `T`, and `τ(H) > T`, then property (7,2) fails. -/
theorem closes_of_four_requests {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2)
    {T : ℕ} (hτ : ¬ CoverableBy H T) {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H)
    (R₁ R₂ R₃ R₄ : Finset α) (h₁ : R₁.card ≤ T) (h₂ : R₂.card ≤ T) (h₃ : R₃.card ≤ T)
    (h₄ : R₄.card ≤ T)
    (hcov : ∀ x y : α, (x ∈ E ∨ y ∈ E) → (x ∈ F ∨ y ∈ F) → (x ∈ G ∨ y ∈ G) →
      (x ∈ R₁ ∧ y ∈ R₁) ∨ (x ∈ R₂ ∧ y ∈ R₂) ∨ (x ∈ R₃ ∧ y ∈ R₃) ∨ (x ∈ R₄ ∧ y ∈ R₄)) :
    False := by
  refine request_cover (E := {E, F, G}) (D := {R₁, R₂, R₃, R₄}) hprop ?_ ⟨E, by simp⟩ ?_ ?_ ?_
  · intro A hA; simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl <;> assumption
  · exact (Nat.add_le_add Finset.card_le_three Finset.card_le_four)
  · intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact exists_response hτ ‹_›
  · intro x y hxy
    have := hcov x y (hxy E (by simp)) (hxy F (by simp)) (hxy G (by simp))
    rcases this with h | h | h | h
    · exact ⟨R₁, by simp, h⟩
    · exact ⟨R₂, by simp, h⟩
    · exact ⟨R₃, by simp, h⟩
    · exact ⟨R₄, by simp, h⟩

end Erdos644
