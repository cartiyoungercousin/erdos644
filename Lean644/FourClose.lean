import Lean644.SplitA

/-!
# General four-edge closure (manuscript Lemma 2.4, all six products)

For a good triple `E, F, G` and a fourth edge `K`, every pair meeting all four edges lies (up to
order) in one of
`(X∩K)×G, (Y∩K)×F, (Z∩K)×E, (X∖K)×(K∩P_G), (Y∖K)×(K∩P_F), (Z∖K)×(K∩P_E)`
with `X = E∩F, Y = E∩G, Z = F∩G`. So three requests covering these six products close.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

theorem four_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T : ℕ}
    (hτ : ¬ CoverableBy H T) {E F G K : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H)
    (hK : K ∈ H) (hgood : IsGoodTriple E F G)
    (R₁ R₂ R₃ : Finset α) (h₁ : R₁.card ≤ T) (h₂ : R₂.card ≤ T) (h₃ : R₃.card ≤ T)
    (c1 : ∀ u v, u ∈ E → u ∈ F → u ∈ K → v ∈ G →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃))
    (c2 : ∀ u v, u ∈ E → u ∈ G → u ∈ K → v ∈ F →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃))
    (c3 : ∀ u v, u ∈ F → u ∈ G → u ∈ K → v ∈ E →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃))
    (c4 : ∀ u v, u ∈ E → u ∈ F → u ∉ K → v ∈ G → v ∈ K → v ∉ E → v ∉ F →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃))
    (c5 : ∀ u v, u ∈ E → u ∈ G → u ∉ K → v ∈ F → v ∈ K → v ∉ E → v ∉ G →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃))
    (c6 : ∀ u v, u ∈ F → u ∈ G → u ∉ K → v ∈ E → v ∈ K → v ∉ F → v ∉ G →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃)) : False := by
  refine closes_of_three_requests hprop hτ hE hF hG hK R₁ R₂ R₃ h₁ h₂ h₃ ?_
  intro x y h1 h2 h3 h4
  have sw : ∀ u v, ((u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃)) →
      ((v ∈ R₁ ∧ u ∈ R₁) ∨ (v ∈ R₂ ∧ u ∈ R₂) ∨ (v ∈ R₃ ∧ u ∈ R₃)) := by
    intro u v h; rcases h with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
  -- one orientation: u in a pair cell, v in the third edge; both meet K
  have oX : ∀ u v, u ∈ E → u ∈ F → v ∈ G → (u ∈ K ∨ v ∈ K) →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃) := by
    intro u v uE uF vG hk
    rcases four_candidate_core uE uF vG hk with h | ⟨vK, vE, -⟩ | ⟨vK, vF, -⟩ | ⟨uK, vK, vE, vF⟩
    · exact c1 u v uE uF h vG
    · exact sw _ _ (c2 v u vE vG vK uF)
    · exact sw _ _ (c3 v u vF vG vK uE)
    · exact c4 u v uE uF uK vG vK vE vF
  have oY : ∀ u v, u ∈ E → u ∈ G → v ∈ F → (u ∈ K ∨ v ∈ K) →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃) := by
    intro u v uE uG vF hk
    rcases four_candidate_core (G := F) uE uG vF hk with h | ⟨vK, vE, -⟩ | ⟨vK, vG, -⟩ |
      ⟨uK, vK, vE, vG⟩
    · exact c2 u v uE uG h vF
    · exact sw _ _ (c1 v u vE vF vK uG)
    · exact sw _ _ (c3 v u vF vG vK uE)
    · exact c5 u v uE uG uK vF vK vE vG
  have oZ : ∀ u v, u ∈ F → u ∈ G → v ∈ E → (u ∈ K ∨ v ∈ K) →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃) := by
    intro u v uF uG vE hk
    rcases four_candidate_core (E := F) (F := G) (G := E) uF uG vE hk with h | ⟨vK, vF, -⟩ |
      ⟨vK, vG, -⟩ | ⟨uK, vK, vF, vG⟩
    · exact c3 u v uF uG h vE
    · exact sw _ _ (c1 v u vE vF vK uG)
    · exact sw _ _ (c2 v u vE vG vK uF)
    · exact c6 u v uF uG uK vE vK vF vG
  rcases triple_candidate hgood h1 h2 h3 with
    ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact oX x y a b c h4
  · exact oY x y a b c h4
  · exact oZ x y a b c h4
  · exact sw _ _ (oX y x a b c h4.symm)
  · exact sw _ _ (oY y x a b c h4.symm)
  · exact sw _ _ (oZ y x a b c h4.symm)

end Erdos644
