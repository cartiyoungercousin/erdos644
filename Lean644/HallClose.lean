import Lean644.Static

/-!
# Hall allocation, set level (manuscript Lemma 3.1 and Corollary 3.2)
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- Split a finite set into two parts of prescribed sizes. -/
theorem split_two (W : Finset α) (m n : ℕ) (h : W.card = m + n) :
    ∃ A B : Finset α, A ⊆ W ∧ B ⊆ W ∧ (∀ x ∈ W, x ∈ A ∨ x ∈ B) ∧ A.card = m ∧ B.card = n := by
  obtain ⟨A, hAW, hA⟩ := Finset.exists_subset_card_eq (show m ≤ W.card by omega)
  refine ⟨A, W \ A, hAW, Finset.sdiff_subset, fun x hx => ?_, hA, ?_⟩
  · by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (Finset.mem_sdiff.2 ⟨hx, hxA⟩)
  · rw [Finset.card_sdiff_of_subset hAW]; omega

/-- Split a finite set into three parts of prescribed sizes. -/
theorem split_three (W : Finset α) (l m n : ℕ) (h : W.card = l + m + n) :
    ∃ A B C : Finset α, A ⊆ W ∧ B ⊆ W ∧ C ⊆ W ∧ (∀ x ∈ W, x ∈ A ∨ x ∈ B ∨ x ∈ C) ∧
      A.card = l ∧ B.card = m ∧ C.card = n := by
  obtain ⟨A, W', hA, hW', hcov, hAc, hW'c⟩ := split_two W l (m + n) (by omega)
  obtain ⟨B, C, hB, hC, hcov', hBc, hCc⟩ := split_two W' m n hW'c
  refine ⟨A, B, C, hA, hB.trans hW', hC.trans hW', fun x hx => ?_, hAc, hBc, hCc⟩
  rcases hcov x hx with h | h
  · exact Or.inl h
  · rcases hcov' x h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

/-- In a good triple, `|E ∩ F| + |E ∩ G| + |E \ (F ∪ G)| = |E|`. -/
theorem card_private {E F G : Finset α} (hgood : IsGoodTriple E F G) :
    (E ∩ F).card + (E ∩ G).card + (E \ (F ∪ G)).card = E.card := by
  have h1 := Finset.card_sdiff_add_card_inter E (F ∪ G)
  have h2 := Finset.card_union_add_card_inter (E ∩ F) (E ∩ G)
  have h3 : E ∩ (F ∪ G) = (E ∩ F) ∪ (E ∩ G) := Finset.inter_union_distrib_left E F G
  have h4 : (E ∩ F) ∩ (E ∩ G) = ∅ := by
    unfold IsGoodTriple at hgood
    ext x; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
    intro h
    have : x ∈ E ∩ F ∩ G := by simp [h.1.1, h.1.2, h.2.2]
    rw [hgood] at this; simp at this
  rw [h3] at h1; rw [h4, Finset.card_empty] at h2
  omega

/-- **Hall allocation** (manuscript Lemma 3.1), set level. -/
theorem hall_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) {E F G : Finset α}
    (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (h1 : (E ∩ F).card ≤ T) (h2 : (E ∩ F).card + (E ∩ G).card ≤ T)
    (h3 : (E ∩ F).card + (F ∩ G).card ≤ T) (h4 : (E ∩ G).card + (F ∩ G).card ≤ T)
    (h5 : k + 2 * (E ∩ G).card ≤ 2 * T) (h6 : k + 2 * (F ∩ G).card ≤ 2 * T)
    (h7 : k + 3 * (E ∩ F).card ≤ 3 * T) (h8 : 2 * k + (E ∩ G).card + (F ∩ G).card ≤ 3 * T)
    (h11 : 3 * k + (E ∩ F).card ≤ 4 * T) : False := by
  -- the three pair cells and three private parts
  set X := E ∩ F
  set Y := E ∩ G
  set Z := F ∩ G
  set PE := E \ (F ∪ G)
  set PF := F \ (E ∪ G)
  set PG := G \ (E ∪ F)
  have gE : IsGoodTriple E F G := hgood
  have gF : IsGoodTriple F E G := by unfold IsGoodTriple at *; rw [Finset.inter_comm F E]; exact hgood
  have gG : IsGoodTriple G E F := by
    unfold IsGoodTriple at *; rw [← hgood]; ext x; simp only [Finset.mem_inter]; tauto
  have cE := card_private gE
  have cF := card_private gF
  have cG := card_private gG
  rw [hunif E hE] at cE; rw [hunif F hF] at cF; rw [hunif G hG] at cG
  rw [Finset.inter_comm F E] at cF
  rw [Finset.inter_comm G E, Finset.inter_comm G F] at cG
  obtain ⟨g₁, g₂, g₃, f₂, f₄, e₃, e₄, sg, sf, se, b1, b2, b3, b4⟩ :=
    hall_sizes k T X.card Y.card Z.card PE.card PF.card PG.card
      (by omega) (by omega) (by omega) h1 h2 h3 h4 h5 h6 h7 h8 h11
  obtain ⟨G₁, G₂, G₃, hG₁, hG₂, hG₃, covG, cG₁, cG₂, cG₃⟩ := split_three PG g₁ g₂ g₃ sg.symm
  obtain ⟨F₂, F₄, hF₂, hF₄, covF, cF₂, cF₄⟩ := split_two PF f₂ f₄ sf.symm
  obtain ⟨E₃, E₄, hE₃, hE₄, covE, cE₃, cE₄⟩ := split_two PE e₃ e₄ se.symm
  refine closes_of_four_requests hprop hτ hE hF hG (X ∪ G₁) (X ∪ Y ∪ F₂ ∪ G₂)
    (X ∪ Z ∪ E₃ ∪ G₃) (Y ∪ Z ∪ E₄ ∪ F₄) ?_ ?_ ?_ ?_ ?_
  · calc (X ∪ G₁).card ≤ X.card + G₁.card := Finset.card_union_le _ _
      _ ≤ T := by omega
  · calc (X ∪ Y ∪ F₂ ∪ G₂).card ≤ X.card + Y.card + F₂.card + G₂.card := by
          refine (Finset.card_union_le _ _).trans ?_
          refine Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) _
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ T := by omega
  · calc (X ∪ Z ∪ E₃ ∪ G₃).card ≤ X.card + Z.card + E₃.card + G₃.card := by
          refine (Finset.card_union_le _ _).trans ?_
          refine Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) _
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ T := by omega
  · calc (Y ∪ Z ∪ E₄ ∪ F₄).card ≤ Y.card + Z.card + E₄.card + F₄.card := by
          refine (Finset.card_union_le _ _).trans ?_
          refine Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) _
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ T := by omega
  · -- every candidate pair lies in one of the four requests (manuscript eq. (2.1))
    intro x y hxE hxF hxG
    have pG : ∀ v, v ∈ G → v ∉ E → v ∉ F → v ∈ G₁ ∨ v ∈ G₂ ∨ v ∈ G₃ := fun v h₁ h₂ h₃ =>
      covG v (by simp [PG, h₁, h₂, h₃])
    have pF : ∀ v, v ∈ F → v ∉ E → v ∉ G → v ∈ F₂ ∨ v ∈ F₄ := fun v h₁ h₂ h₃ =>
      covF v (by simp [PF, h₁, h₂, h₃])
    have pE : ∀ v, v ∈ E → v ∉ F → v ∉ G → v ∈ E₃ ∨ v ∈ E₄ := fun v h₁ h₂ h₃ =>
      covE v (by simp [PE, h₁, h₂, h₃])
    -- the goal, as a predicate on an ordered pair
    let P : α → α → Prop := fun u v =>
      (u ∈ X ∪ G₁ ∧ v ∈ X ∪ G₁) ∨ (u ∈ X ∪ Y ∪ F₂ ∪ G₂ ∧ v ∈ X ∪ Y ∪ F₂ ∪ G₂) ∨
      (u ∈ X ∪ Z ∪ E₃ ∪ G₃ ∧ v ∈ X ∪ Z ∪ E₃ ∪ G₃) ∨ (u ∈ Y ∪ Z ∪ E₄ ∪ F₄ ∧ v ∈ Y ∪ Z ∪ E₄ ∪ F₄)
    have symm : ∀ u v, P u v → P v u := by
      intro u v h
      rcases h with h | h | h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
    -- u in X = E ∩ F, v in G
    have caseX : ∀ u v, u ∈ E → u ∈ F → v ∈ G → P u v := by
      intro u v uE uF vG
      have uX : u ∈ X := Finset.mem_inter.2 ⟨uE, uF⟩
      by_cases vE : v ∈ E
      · have vY : v ∈ Y := Finset.mem_inter.2 ⟨vE, vG⟩
        exact Or.inr (Or.inl ⟨by simp [uX], by simp [vY]⟩)
      by_cases vF : v ∈ F
      · have vZ : v ∈ Z := Finset.mem_inter.2 ⟨vF, vG⟩
        exact Or.inr (Or.inr (Or.inl ⟨by simp [uX], by simp [vZ]⟩))
      rcases pG v vG vE vF with h | h | h
      · exact Or.inl ⟨by simp [uX], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uX], by simp [h]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by simp [uX], by simp [h]⟩))
    -- u in Y = E ∩ G, v in F
    have caseY : ∀ u v, u ∈ E → u ∈ G → v ∈ F → P u v := by
      intro u v uE uG vF
      have uY : u ∈ Y := Finset.mem_inter.2 ⟨uE, uG⟩
      by_cases vE : v ∈ E
      · have vX : v ∈ X := Finset.mem_inter.2 ⟨vE, vF⟩
        exact Or.inr (Or.inl ⟨by simp [uY], by simp [vX]⟩)
      by_cases vG : v ∈ G
      · have vZ : v ∈ Z := Finset.mem_inter.2 ⟨vF, vG⟩
        exact Or.inr (Or.inr (Or.inr ⟨by simp [uY], by simp [vZ]⟩))
      rcases pF v vF vE vG with h | h
      · exact Or.inr (Or.inl ⟨by simp [uY], by simp [h]⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [uY], by simp [h]⟩))
    -- u in Z = F ∩ G, v in E
    have caseZ : ∀ u v, u ∈ F → u ∈ G → v ∈ E → P u v := by
      intro u v uF uG vE
      have uZ : u ∈ Z := Finset.mem_inter.2 ⟨uF, uG⟩
      by_cases vF : v ∈ F
      · have vX : v ∈ X := Finset.mem_inter.2 ⟨vE, vF⟩
        exact Or.inr (Or.inr (Or.inl ⟨by simp [uZ], by simp [vX]⟩))
      by_cases vG : v ∈ G
      · have vY : v ∈ Y := Finset.mem_inter.2 ⟨vE, vG⟩
        exact Or.inr (Or.inr (Or.inr ⟨by simp [uZ], by simp [vY]⟩))
      rcases pE v vE vF vG with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨by simp [uZ], by simp [h]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [uZ], by simp [h]⟩))
    rcases triple_candidate hgood hxE hxF hxG with
      ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · exact caseX x y a1 a2 a3
    · exact caseY x y a1 a2 a3
    · exact caseZ x y a1 a2 a3
    · exact symm _ _ (caseX y x a1 a2 a3)
    · exact symm _ _ (caseY y x a1 a2 a3)
    · exact symm _ _ (caseZ y x a1 a2 a3)

end Erdos644

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Corollary 3.2** (manuscript). With `6k ≤ 7T` and `T ≤ k`: a good triple closes if one pair
cell (`E ∩ F`) has size `a ≤ T/2` and the other two have sizes `b, c ≤ T - k/2` with
`b + c ≤ 3T - 2k`. (Halves are written multiplied out, so no rounding is involved.) -/
theorem hall_cor {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hT : 6 * k ≤ 7 * T) (hTk : T ≤ k)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (ha : 2 * (E ∩ F).card ≤ T) (hb : k + 2 * (E ∩ G).card ≤ 2 * T)
    (hc : k + 2 * (F ∩ G).card ≤ 2 * T) (hbc : 2 * k + (E ∩ G).card + (F ∩ G).card ≤ 3 * T) :
    False :=
  hall_closes hprop hτ hunif hE hF hG hgood (by omega) (by omega) (by omega) (by omega)
    hb hc (by omega) hbc (by omega)

end Erdos644
