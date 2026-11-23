import Lean644.FourClose

/-!
# One surviving cell: generic closure with bases (manuscript Appendix A, proof of Lemma 4.1)

Setting: good triple `E, F, G`; fourth edge `K` avoiding `X = E∩F` and `Y = E∩G`. The only
possible triple cell is `Q = F∩G∩K`. Candidate pairs (Lemma 2.4): `Q×E`, `X×B`, `Y×A`, `V×C`
with `B = (G∩K)∖F`, `A = (F∩K)∖G`, `C = E∩K`, `V = (F∩G)∖K`.

Three requests `Rᵢ = Q ∪ Sᵢ ∪ Dᵢ`: the *bases* `Sᵢ` cover `X×B`, `Y×A`, `V×C` and contain every
point of `E` lying in `F ∪ G ∪ K`; the rest `D = E ∖ (F ∪ G ∪ K)` is distributed (`Dᵢ`) into
the residual capacities. `Q` lies in every request, so `Q×E` is covered.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

theorem onecore_bases_close {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T : ℕ}
    (hτ : ¬ CoverableBy H T) {E F G K : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H)
    (hK : K ∈ H) (hgood : IsGoodTriple E F G)
    (hX : Disjoint K (E ∩ F)) (hY : Disjoint K (E ∩ G))
    (S₁ S₂ S₃ : Finset α) (n₁ n₂ n₃ : ℕ)
    (s₁ : (F ∩ G ∩ K ∪ S₁).card ≤ n₁) (s₂ : (F ∩ G ∩ K ∪ S₂).card ≤ n₂)
    (s₃ : (F ∩ G ∩ K ∪ S₃).card ≤ n₃) (t₁ : n₁ ≤ T) (t₂ : n₂ ≤ T) (t₃ : n₃ ≤ T)
    (tot : n₁ + n₂ + n₃ + (E \ (F ∪ G ∪ K)).card ≤ 3 * T)
    (cXB : ∀ u v, u ∈ E → u ∈ F → v ∈ G → v ∈ K → v ∉ F →
      (u ∈ S₁ ∧ v ∈ S₁) ∨ (u ∈ S₂ ∧ v ∈ S₂) ∨ (u ∈ S₃ ∧ v ∈ S₃))
    (cYA : ∀ u v, u ∈ E → u ∈ G → v ∈ F → v ∈ K → v ∉ G →
      (u ∈ S₁ ∧ v ∈ S₁) ∨ (u ∈ S₂ ∧ v ∈ S₂) ∨ (u ∈ S₃ ∧ v ∈ S₃))
    (cVC : ∀ u v, u ∈ F → u ∈ G → u ∉ K → v ∈ E → v ∈ K →
      (u ∈ S₁ ∧ v ∈ S₁) ∨ (u ∈ S₂ ∧ v ∈ S₂) ∨ (u ∈ S₃ ∧ v ∈ S₃))
    (cE : ∀ e, e ∈ E → (e ∈ F ∨ e ∈ G ∨ e ∈ K) → e ∈ S₁ ∨ e ∈ S₂ ∨ e ∈ S₃) : False := by
  set Q := F ∩ G ∩ K
  set D := E \ (F ∪ G ∪ K)
  -- distribute D into the residual capacities
  obtain ⟨d₁, hd11, hd12, hd1⟩ : ∃ d₁, d₁ ≤ D.card ∧ n₁ + d₁ ≤ T ∧ (d₁ = D.card ∨ n₁ + d₁ = T) :=
    ⟨min D.card (T - n₁), min_le_left _ _, by omega, by
      rcases min_choice D.card (T - n₁) with h | h <;> [left; right] <;> omega⟩
  obtain ⟨d₂, hd21, hd22, hd2⟩ : ∃ d₂, d₁ + d₂ ≤ D.card ∧ n₂ + d₂ ≤ T ∧
      (d₁ + d₂ = D.card ∨ n₂ + d₂ = T) :=
    ⟨min (D.card - d₁) (T - n₂), by omega, by omega, by
      rcases min_choice (D.card - d₁) (T - n₂) with h | h <;> [left; right] <;> omega⟩
  obtain ⟨D₁, D₂, D₃, -, -, -, covD, cD₁, cD₂, cD₃⟩ := split_three D d₁ d₂ (D.card - d₁ - d₂) (by omega)
  have b3 : ∀ A B C : Finset α, (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card :=
    fun A B C => Finset.card_union_le _ _
  have sw : ∀ (R₁ R₂ R₃ : Finset α) u v, ((u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃))
      → ((u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃)) := fun _ _ _ _ _ h => h
  have lift : ∀ u v, ((u ∈ S₁ ∧ v ∈ S₁) ∨ (u ∈ S₂ ∧ v ∈ S₂) ∨ (u ∈ S₃ ∧ v ∈ S₃)) →
      ((u ∈ Q ∪ S₁ ∪ D₁ ∧ v ∈ Q ∪ S₁ ∪ D₁) ∨ (u ∈ Q ∪ S₂ ∪ D₂ ∧ v ∈ Q ∪ S₂ ∪ D₂) ∨
        (u ∈ Q ∪ S₃ ∪ D₃ ∧ v ∈ Q ∪ S₃ ∪ D₃)) := by
    intro u v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [h1], by simp [h2]⟩
    · exact Or.inr (Or.inl ⟨by simp [h1], by simp [h2]⟩)
    · exact Or.inr (Or.inr ⟨by simp [h1], by simp [h2]⟩)
  have nX : ∀ v, v ∈ K → v ∈ E → v ∈ F → False := fun v h1 h2 h3 =>
    Finset.disjoint_left.1 hX h1 (Finset.mem_inter.2 ⟨h2, h3⟩)
  have nY : ∀ v, v ∈ K → v ∈ E → v ∈ G → False := fun v h1 h2 h3 =>
    Finset.disjoint_left.1 hY h1 (Finset.mem_inter.2 ⟨h2, h3⟩)
  refine four_closes hprop hτ hE hF hG hK hgood (Q ∪ S₁ ∪ D₁) (Q ∪ S₂ ∪ D₂) (Q ∪ S₃ ∪ D₃)
    ((b3 _ _ _).trans (by omega)) ((b3 _ _ _).trans (by omega)) ((b3 _ _ _).trans (by omega))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v uE uF uK _; exact (nX u uK uE uF).elim
  · intro u v uE uG uK _; exact (nY u uK uE uG).elim
  · -- Q × E: Q is in every request; v ∈ E is in some request
    intro u v uF uG uK vE
    have uQ : u ∈ Q := by simp [Q, uF, uG, uK]
    by_cases hv : v ∈ F ∨ v ∈ G ∨ v ∈ K
    · rcases cE v vE hv with h | h | h
      · exact Or.inl ⟨by simp [uQ], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uQ], by simp [h]⟩)
      · exact Or.inr (Or.inr ⟨by simp [uQ], by simp [h]⟩)
    · have vD : v ∈ D := by
        simp only [D, Finset.mem_sdiff, Finset.mem_union]; simp only [not_or] at hv; tauto
      rcases covD v vD with h | h | h
      · exact Or.inl ⟨by simp [uQ], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uQ], by simp [h]⟩)
      · exact Or.inr (Or.inr ⟨by simp [uQ], by simp [h]⟩)
  · intro u v uE uF _ vG vK _ vF; exact lift u v (cXB u v uE uF vG vK vF)
  · intro u v uE uG _ vF vK _ vG; exact lift u v (cYA u v uE uG vF vK vG)
  · intro u v uF uG uK vE vK _ _; exact lift u v (cVC u v uF uG uK vE vK)

end Erdos644
