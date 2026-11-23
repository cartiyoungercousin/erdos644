import Lean644.SplitA

/-!
# Lemma 4.3 (second asymmetric split), manuscript Appendix A
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Lemma 4.3 (second asymmetric split).** With `x = |E∩F|`, `y = |E∩G|`, `z = |F∩G|`,
`S = x+y+z`: a good triple closes at budget `T ≤ k` if `T ≥ S`, `3T ≥ k+3x`, `T ≥ k-x+z` and
`3T ≥ k+2x+3y+z`. -/
theorem splitB_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (c1 : (E ∩ F).card + (E ∩ G).card + (F ∩ G).card ≤ T)
    (c2 : k + 3 * (E ∩ F).card ≤ 3 * T)
    (c3 : k + (F ∩ G).card ≤ T + (E ∩ F).card)
    (c4 : k + 2 * (E ∩ F).card + 3 * (E ∩ G).card + (F ∩ G).card ≤ 3 * T) : False := by
  have gG : IsGoodTriple G E F := by
    unfold IsGoodTriple at *; rw [← hgood]; ext v; simp only [Finset.mem_inter]; tauto
  have cE := card_private hgood
  have cG := card_private gG
  rw [hunif E hE] at cE
  rw [hunif G hG, Finset.inter_comm G E, Finset.inter_comm G F] at cG
  have g0 : ∀ v, v ∈ E → v ∈ F → v ∈ G → False := fun v h1 h2 h3 => by
    have : v ∈ E ∩ F ∩ G := by simp [h1, h2, h3]
    unfold IsGoodTriple at hgood; rw [hgood] at this; simp at this
  set X := E ∩ F with hXdef
  set Y := E ∩ G with hYdef
  set Z := F ∩ G with hZdef
  -- first request: X ∪ Y ∪ Z ∪ W with W ⊆ P_G of size p = max(0, k - 2(T-x) - y - z)
  obtain ⟨W, hWP, hW⟩ := Finset.exists_subset_card_eq
    (show k + 2 * X.card - (2 * T + Y.card + Z.card) ≤ (G \ (E ∪ F)).card by omega)
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
  -- b + y + z + p ≤ k : B, Y, Z, W are disjoint subsets of G
  have dYZ : Disjoint Y Z := Finset.disjoint_left.2 fun v h1 h2 => by
    simp only [Y, Z, Finset.mem_inter] at h1 h2; exact g0 v h1.1 h2.1 h1.2
  have dYZW : Disjoint (Y ∪ Z) W := Finset.disjoint_left.2 fun v h1 h2 => by
    have := Finset.mem_sdiff.1 (hWP h2)
    simp only [Y, Z, Finset.mem_union, Finset.mem_inter] at h1 this
    tauto
  have dB : Disjoint B (Y ∪ Z ∪ W) := Finset.disjoint_left.2 fun v h1 h2 => by
    have hvK : v ∈ K := (Finset.mem_inter.1 h1).2
    have := nK v hvK
    simp only [Y, Z, Finset.mem_union, Finset.mem_inter] at h2
    rcases h2 with (⟨a, b⟩ | ⟨a, b⟩) | h
    · exact this.2.1 a b
    · exact this.2.2.1 a b
    · exact this.2.2.2 h
  have sub : B ∪ (Y ∪ Z ∪ W) ⊆ G := by
    intro v hv
    simp only [Finset.mem_union] at hv
    rcases hv with h | (h | h) | h
    · exact (Finset.mem_inter.1 h).1
    · exact (Finset.mem_inter.1 h).2
    · exact (Finset.mem_inter.1 h).2
    · exact (Finset.mem_sdiff.1 (hWP h)).1
  have iii := Finset.card_le_card sub
  rw [card_union_disj dB, card_union_disj dYZW, card_union_disj dYZ, hunif G hG] at iii
  -- c ≤ k - x - y : C ⊆ P_E
  have iv : C.card ≤ (E \ (F ∪ G)).card := Finset.card_le_card fun v hv => by
    have := nK v (Finset.mem_inter.1 hv).2
    have hvE := (Finset.mem_inter.1 hv).1
    simp only [Finset.mem_sdiff, Finset.mem_union]
    exact ⟨hvE, fun h => h.elim (fun h => this.1 hvE h) (fun h => this.2.1 hvE h)⟩
  -- a + b + c ≤ k
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
  by_cases hcase : k + Y.card + Z.card < B.card + T
  · -- Case 1: B split into two parts of size ≤ T - x; third request Y ∪ Z ∪ A ∪ C
    obtain ⟨b₁, hb1, hb2, hb⟩ : ∃ b₁, b₁ ≤ B.card ∧ b₁ + X.card ≤ T ∧
        (b₁ = B.card ∨ b₁ + X.card = T) :=
      ⟨min B.card (T - X.card), min_le_left _ _, by omega, by
        rcases min_choice B.card (T - X.card) with h | h <;> [left; right] <;> omega⟩
    obtain ⟨B₁, B₂, -, -, covB, cB₁, cB₂⟩ := split_two B b₁ (B.card - b₁) (by omega)
    refine no_core_closes hprop hτ hE hF hG hK hgood kX kY kZ (X ∪ B₁) (X ∪ B₂)
      (Y ∪ Z ∪ A ∪ C) ((Finset.card_union_le _ _).trans (by omega))
      ((Finset.card_union_le _ _).trans (by omega)) ((card_union4_le _ _ _ _).trans (by omega))
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
      exact Or.inr (Or.inr ⟨by simp [uZ], by simp [C, vE, vK]⟩)
  · -- Case 2: B split into two parts of size ≤ T - x - y; A distributed; all contain Y
    obtain ⟨b₁, hb1, hb2, hb⟩ : ∃ b₁, b₁ ≤ B.card ∧ b₁ + X.card + Y.card ≤ T ∧
        (b₁ = B.card ∨ b₁ + X.card + Y.card = T) :=
      ⟨min B.card (T - X.card - Y.card), min_le_left _ _, by omega, by
        rcases min_choice B.card (T - X.card - Y.card) with h | h <;> [left; right] <;> omega⟩
    obtain ⟨B₁, B₂, -, -, covB, cB₁, cB₂⟩ := split_two B b₁ (B.card - b₁) (by omega)
    obtain ⟨a₁, ha11, ha12, ha1⟩ : ∃ a₁, a₁ ≤ A.card ∧ a₁ + b₁ + X.card + Y.card ≤ T ∧
        (a₁ = A.card ∨ a₁ + b₁ + X.card + Y.card = T) :=
      ⟨min A.card (T - b₁ - X.card - Y.card), min_le_left _ _, by omega, by
        rcases min_choice A.card (T - b₁ - X.card - Y.card) with h | h <;> [left; right] <;> omega⟩
    obtain ⟨a₂, ha21, ha22, ha2⟩ : ∃ a₂, a₂ + a₁ ≤ A.card ∧
        a₂ + (B.card - b₁) + X.card + Y.card ≤ T ∧
        (a₂ + a₁ = A.card ∨ a₂ + (B.card - b₁) + X.card + Y.card = T) :=
      ⟨min (A.card - a₁) (T - (B.card - b₁) - X.card - Y.card), by omega, by omega, by
        rcases min_choice (A.card - a₁) (T - (B.card - b₁) - X.card - Y.card) with h | h
          <;> [left; right] <;> omega⟩
    obtain ⟨A₁, A₂, A₃, -, -, -, covA, cA₁, cA₂, cA₃⟩ :=
      split_three A a₁ a₂ (A.card - a₁ - a₂) (by omega)
    refine no_core_closes hprop hτ hE hF hG hK hgood kX kY kZ (X ∪ Y ∪ B₁ ∪ A₁)
      (X ∪ Y ∪ B₂ ∪ A₂) (Y ∪ Z ∪ C ∪ A₃) ((card_union4_le _ _ _ _).trans (by omega))
      ((card_union4_le _ _ _ _).trans (by omega)) ((card_union4_le _ _ _ _).trans (by omega))
      ?_ ?_ ?_
    · intro u v uE uF vG vK
      have uX : u ∈ X := by simp [X, uE, uF]
      rcases covB v (by simp [B, vG, vK]) with h | h
      · exact Or.inl ⟨by simp [uX], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uX], by simp [h]⟩)
    · intro u v uE uG vF vK
      have uY : u ∈ Y := by simp [Y, uE, uG]
      rcases covA v (by simp [A, vF, vK]) with h | h | h
      · exact Or.inl ⟨by simp [uY], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [uY], by simp [h]⟩)
      · exact Or.inr (Or.inr ⟨by simp [uY], by simp [h]⟩)
    · intro u v uF uG vE vK
      have uZ : u ∈ Z := by simp [Z, uF, uG]
      exact Or.inr (Or.inr ⟨by simp [uZ], by simp [C, vE, vK]⟩)

end Erdos644
