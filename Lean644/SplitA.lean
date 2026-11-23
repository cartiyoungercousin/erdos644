import Lean644.Adaptive

/-!
# Lemma 4.2 (first asymmetric split), manuscript Appendix A

Also the shared tools `card_union3_le`, `card_union4_le`, `no_core_closes`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

theorem card_union3_le (A B C : Finset α) : (A ∪ B ∪ C).card ≤ A.card + B.card + C.card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)

theorem card_union4_le (A B C D : Finset α) :
    (A ∪ B ∪ C ∪ D).card ≤ A.card + B.card + C.card + D.card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_right (card_union3_le _ _ _) _)

/-- Closure when the fourth edge `K` avoids all pair cells: it suffices that three requests cover
the three complementary products `(E∩F) × (G∩K)`, `(E∩G) × (F∩K)`, `(F∩G) × (E∩K)`. -/
theorem no_core_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T : ℕ}
    (hτ : ¬ CoverableBy H T) {E F G K : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H)
    (hK : K ∈ H) (hgood : IsGoodTriple E F G)
    (hX : Disjoint K (E ∩ F)) (hY : Disjoint K (E ∩ G)) (hZ : Disjoint K (F ∩ G))
    (R₁ R₂ R₃ : Finset α) (h₁ : R₁.card ≤ T) (h₂ : R₂.card ≤ T) (h₃ : R₃.card ≤ T)
    (cX : ∀ u v, u ∈ E → u ∈ F → v ∈ G → v ∈ K →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃))
    (cY : ∀ u v, u ∈ E → u ∈ G → v ∈ F → v ∈ K →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃))
    (cZ : ∀ u v, u ∈ F → u ∈ G → v ∈ E → v ∈ K →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃)) : False := by
  refine closes_of_three_requests hprop hτ hE hF hG hK R₁ R₂ R₃ h₁ h₂ h₃ ?_
  intro x y h1 h2 h3 h4
  have sw : ∀ u v, ((u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) ∨ (u ∈ R₃ ∧ v ∈ R₃)) →
      ((v ∈ R₁ ∧ u ∈ R₁) ∨ (v ∈ R₂ ∧ u ∈ R₂) ∨ (v ∈ R₃ ∧ u ∈ R₃)) := by
    intro u v h; rcases h with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
  rcases no_core_candidate hgood hX hY hZ h1 h2 h3 h4 with
    ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · exact cX x y a b c d
  · exact cY x y a b c d
  · exact cZ x y a b c d
  · exact sw _ _ (cX y x a b c d)
  · exact sw _ _ (cY y x a b c d)
  · exact sw _ _ (cZ y x a b c d)

/-- **Lemma 4.2 (first asymmetric split).** With `x = |E∩F|`, `y = |E∩G|`, `z = |F∩G|`,
`S = x+y+z`: a good triple closes at budget `T ≤ k` if `T ≥ S`, `2T ≥ k+2y`,
`2T ≥ k+2x-y+z` and `3T ≥ k+2x+y+3z`. -/
theorem splitA_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (c1 : (E ∩ F).card + (E ∩ G).card + (F ∩ G).card ≤ T)
    (c2 : k + 2 * (E ∩ G).card ≤ 2 * T)
    (c3 : k + 2 * (E ∩ F).card + (F ∩ G).card ≤ 2 * T + (E ∩ G).card)
    (c4 : k + 2 * (E ∩ F).card + (E ∩ G).card + 3 * (F ∩ G).card ≤ 3 * T) : False := by
  have gF : IsGoodTriple F E G := by
    unfold IsGoodTriple at *; rw [Finset.inter_comm F E]; exact hgood
  have gG : IsGoodTriple G E F := by
    unfold IsGoodTriple at *; rw [← hgood]; ext v; simp only [Finset.mem_inter]; tauto
  have cF := card_private gF
  have cG := card_private gG
  rw [hunif F hF, Finset.inter_comm F E] at cF
  rw [hunif G hG, Finset.inter_comm G E, Finset.inter_comm G F] at cG
  have g0 : ∀ v, v ∈ E → v ∈ F → v ∈ G → False := fun v h1 h2 h3 => by
    have : v ∈ E ∩ F ∩ G := by simp [h1, h2, h3]
    unfold IsGoodTriple at hgood; rw [hgood] at this; simp at this
  set X := E ∩ F with hXdef
  set Y := E ∩ G with hYdef
  set Z := F ∩ G with hZdef
  -- first request: X ∪ Y ∪ Z ∪ W with W ⊆ P_F of size T - S
  obtain ⟨W, hWP, hW⟩ := Finset.exists_subset_card_eq
    (show T - (X.card + Y.card + Z.card) ≤ (F \ (E ∪ G)).card by omega)
  obtain ⟨K, hK, hKD⟩ := exists_response hτ (d := X ∪ Y ∪ Z ∪ W)
    ((card_union4_le _ _ _ _).trans (by omega))
  have kX : Disjoint K X := hKD.mono_right (by intro v hv; simp [hv])
  have kY : Disjoint K Y := hKD.mono_right (by intro v hv; simp [hv])
  have kZ : Disjoint K Z := hKD.mono_right (by intro v hv; simp [hv])
  have kW : Disjoint K W := hKD.mono_right (by intro v hv; simp [hv])
  have nK : ∀ v, v ∈ K → (v ∈ E → v ∈ F → False) ∧ (v ∈ E → v ∈ G → False) ∧
      (v ∈ F → v ∈ G → False) ∧ v ∉ W := fun v hv =>
    ⟨fun a b => Finset.disjoint_left.1 kX hv (by simp [X, a, b]),
     fun a b => Finset.disjoint_left.1 kY hv (by simp [Y, a, b]),
     fun a b => Finset.disjoint_left.1 kZ hv (by simp [Z, a, b]),
     Finset.disjoint_left.1 kW hv⟩
  set A := F ∩ K
  set B := G ∩ K
  set C := E ∩ K
  -- (iii) a + x + z + w ≤ k : A, X, Z, W are disjoint subsets of F
  have dXZ : Disjoint X Z := Finset.disjoint_left.2 fun v h1 h2 => by
    simp only [X, Z, Finset.mem_inter] at h1 h2; exact g0 v h1.1 h1.2 h2.2
  have dXZW : Disjoint (X ∪ Z) W := Finset.disjoint_left.2 fun v h1 h2 => by
    have := Finset.mem_sdiff.1 (hWP h2)
    simp only [X, Z, Finset.mem_union, Finset.mem_inter] at h1 this
    tauto
  have dA : Disjoint A (X ∪ Z ∪ W) := Finset.disjoint_left.2 fun v h1 h2 => by
    have hvK : v ∈ K := (Finset.mem_inter.1 h1).2
    have := nK v hvK
    simp only [X, Z, Finset.mem_union, Finset.mem_inter] at h2
    rcases h2 with (⟨a, b⟩ | ⟨a, b⟩) | h
    · exact this.1 a b
    · exact this.2.2.1 a b
    · exact this.2.2.2 h
  have sub : A ∪ (X ∪ Z ∪ W) ⊆ F := by
    intro v hv
    simp only [Finset.mem_union] at hv
    rcases hv with h | (h | h) | h
    · exact (Finset.mem_inter.1 h).1
    · exact (Finset.mem_inter.1 h).2
    · exact (Finset.mem_inter.1 h).1
    · exact (Finset.mem_sdiff.1 (hWP h)).1
  have iii := Finset.card_le_card sub
  rw [card_union_disj dA, card_union_disj dXZW, card_union_disj dXZ, hunif F hF] at iii
  -- (iv) b ≤ k - y - z : B ⊆ P_G
  have iv : B.card ≤ (G \ (E ∪ F)).card := Finset.card_le_card fun v hv => by
    have := nK v (Finset.mem_inter.1 hv).2
    have hvG := (Finset.mem_inter.1 hv).1
    simp only [Finset.mem_sdiff, Finset.mem_union]
    exact ⟨hvG, fun h => h.elim (fun h => this.2.1 h hvG) (fun h => this.2.2.1 h hvG)⟩
  -- (v) a + b + c ≤ k : A, B, C are disjoint subsets of K
  have dAB : Disjoint A B := Finset.disjoint_left.2 fun v h1 h2 =>
    (nK v (Finset.mem_inter.1 h1).2).2.2.1 (Finset.mem_inter.1 h1).1 (Finset.mem_inter.1 h2).1
  have dABC : Disjoint (A ∪ B) C := Finset.disjoint_left.2 fun v h1 h2 => by
    have hvE := (Finset.mem_inter.1 h2).1
    have hvK := (Finset.mem_inter.1 h2).2
    rcases Finset.mem_union.1 h1 with h | h
    · exact (nK v hvK).1 hvE (Finset.mem_inter.1 h).1
    · exact (nK v hvK).2.1 hvE (Finset.mem_inter.1 h).1
  have v5 := Finset.card_le_card (show A ∪ B ∪ C ⊆ K by
    intro v hv; simp only [Finset.mem_union] at hv
    rcases hv with (h | h) | h <;> exact (Finset.mem_inter.1 h).2)
  rw [card_union_disj dABC, card_union_disj dAB, hunif K hK] at v5
  by_cases hcase : A.card + Y.card + Z.card ≤ T
  · -- Case 1: split B into B₁, B₂ and C into C₁, C₂, C₃
    obtain ⟨b₁, hb1, hb2, hb⟩ : ∃ b₁, b₁ ≤ B.card ∧ b₁ + X.card + Z.card ≤ T ∧
        (b₁ = B.card ∨ b₁ + X.card + Z.card = T) :=
      ⟨min B.card (T - X.card - Z.card), min_le_left _ _, by omega, by
        rcases min_choice B.card (T - X.card - Z.card) with h | h <;> [left; right] <;> omega⟩
    obtain ⟨B₁, B₂, -, -, covB, cB₁, cB₂⟩ := split_two B b₁ (B.card - b₁) (by omega)
    obtain ⟨c₁, hc11, hc12, hc1⟩ : ∃ c₁, c₁ ≤ C.card ∧ c₁ + b₁ + X.card + Z.card ≤ T ∧
        (c₁ = C.card ∨ c₁ + b₁ + X.card + Z.card = T) :=
      ⟨min C.card (T - b₁ - X.card - Z.card), min_le_left _ _, by omega, by
        rcases min_choice C.card (T - b₁ - X.card - Z.card) with h | h <;> [left; right] <;> omega⟩
    obtain ⟨c₂, hc21, hc22, hc2⟩ : ∃ c₂, c₂ + c₁ ≤ C.card ∧
        c₂ + (B.card - b₁) + X.card + Z.card ≤ T ∧
        (c₂ + c₁ = C.card ∨ c₂ + (B.card - b₁) + X.card + Z.card = T) :=
      ⟨min (C.card - c₁) (T - (B.card - b₁) - X.card - Z.card), by omega, by omega, by
        rcases min_choice (C.card - c₁) (T - (B.card - b₁) - X.card - Z.card) with h | h
          <;> [left; right] <;> omega⟩
    obtain ⟨C₁, C₂, C₃, -, -, -, covC, cC₁, cC₂, cC₃⟩ :=
      split_three C c₁ c₂ (C.card - c₁ - c₂) (by omega)
    refine no_core_closes hprop hτ hE hF hG hK hgood kX kY kZ (X ∪ Z ∪ B₁ ∪ C₁)
      (X ∪ Z ∪ B₂ ∪ C₂) (Y ∪ Z ∪ A ∪ C₃) ((card_union4_le _ _ _ _).trans (by omega))
      ((card_union4_le _ _ _ _).trans (by omega)) ((card_union4_le _ _ _ _).trans (by omega))
      ?_ ?_ ?_
    · intro u v uE uF vG vK
      have uX : u ∈ X := by simp [X, uE, uF]
      rcases covB v (by simp [B, vG, vK]) with h | h
      · exact Or.inl ⟨by simp [uX], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uX], by simp [h]⟩)
    · intro u v uE uG vF vK
      have uY : u ∈ Y := by simp [Y, uE, uG]
      exact Or.inr (Or.inr ⟨by simp [uY], by simp [A, vF, vK]⟩)
    · intro u v uF uG vE vK
      have uZ : u ∈ Z := by simp [Z, uF, uG]
      rcases covC v (by simp [C, vE, vK]) with h | h | h
      · exact Or.inl ⟨by simp [uZ], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uZ], by simp [h]⟩)
      · exact Or.inr (Or.inr ⟨by simp [uZ], by simp [h]⟩)
  · -- Case 2: split B ∪ C into two parts of size ≤ T - x - z
    have hBC : (B ∪ C).card ≤ B.card + C.card := Finset.card_union_le _ _
    obtain ⟨p₁, hp1, hp2, hp⟩ : ∃ p₁, p₁ ≤ (B ∪ C).card ∧ p₁ + X.card + Z.card ≤ T ∧
        (p₁ = (B ∪ C).card ∨ p₁ + X.card + Z.card = T) :=
      ⟨min (B ∪ C).card (T - X.card - Z.card), min_le_left _ _, by omega, by
        rcases min_choice (B ∪ C).card (T - X.card - Z.card) with h | h <;> [left; right] <;> omega⟩
    obtain ⟨P₁, P₂, -, -, covP, cP₁, cP₂⟩ :=
      split_two (B ∪ C) p₁ ((B ∪ C).card - p₁) (by omega)
    refine no_core_closes hprop hτ hE hF hG hK hgood kX kY kZ (X ∪ Z ∪ P₁) (X ∪ Z ∪ P₂) (Y ∪ A)
      ((card_union3_le _ _ _).trans (by omega)) ((card_union3_le _ _ _).trans (by omega))
      ((Finset.card_union_le _ _).trans (by omega)) ?_ ?_ ?_
    · intro u v uE uF vG vK
      have uX : u ∈ X := by simp [X, uE, uF]
      rcases covP v (by simp [B, vG, vK]) with h | h
      · exact Or.inl ⟨by simp [uX], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uX], by simp [h]⟩)
    · intro u v uE uG vF vK
      have uY : u ∈ Y := by simp [Y, uE, uG]
      exact Or.inr (Or.inr ⟨by simp [uY], by simp [A, vF, vK]⟩)
    · intro u v uF uG vE vK
      have uZ : u ∈ Z := by simp [Z, uF, uG]
      rcases covP v (by simp [C, vE, vK]) with h | h
      · exact Or.inl ⟨by simp [uZ], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uZ], by simp [h]⟩)

end Erdos644
