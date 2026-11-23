import Lean644.OneCore

/-!
# Lemma 4.1 (one surviving cell), manuscript Appendix A

Integer arithmetic of all four cases audited exhaustively in `compute/audit_onecore.py`
(k ≤ 26, 56M response configurations, 0 failures).
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Lemma 4.1 (one surviving cell).** With `x = |E∩F|, y = |E∩G|, z = |F∩G|`, `S = x+y+z`,
a good triple closes at budget `T ≤ k` under the nine inequalities of the manuscript. -/
theorem onecore_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (h1 : (E ∩ F).card + (E ∩ G).card ≤ T)
    (h2 : k + 2 * (E ∩ F).card ≤ 2 * T) (h3 : k + 2 * (E ∩ G).card ≤ 2 * T)
    (h4 : k + (E ∩ F).card ≤ T + (E ∩ G).card + (F ∩ G).card)
    (h5 : k + (E ∩ G).card ≤ T + (E ∩ F).card + (F ∩ G).card)
    (h6 : 3 * k ≤ 3 * T + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card))
    (h7 : 3 * k + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card) ≤ 5 * T)
    (h8 : k + (E ∩ F).card + (E ∩ G).card + 2 * (F ∩ G).card ≤ 3 * T)
    (h9 : 2 * k + 3 * (F ∩ G).card ≤ 4 * T) : False := by
  have gF : IsGoodTriple F E G := by
    unfold IsGoodTriple at *; rw [Finset.inter_comm F E]; exact hgood
  have gG : IsGoodTriple G E F := by
    unfold IsGoodTriple at *; rw [← hgood]; ext v; simp only [Finset.mem_inter]; tauto
  have g0 : ∀ v, v ∈ E → v ∈ F → v ∈ G → False := fun v h1 h2 h3 => by
    have : v ∈ E ∩ F ∩ G := by simp [h1, h2, h3]
    unfold IsGoodTriple at hgood; rw [hgood] at this; simp at this
  set X := E ∩ F with hXdef
  set Y := E ∩ G with hYdef
  set Z := F ∩ G with hZdef
  -- first request: X ∪ Y ∪ Z₀ with |Z₀| = min(z, T - x - y)
  obtain ⟨z₀, hz01, hz02, hz0⟩ : ∃ z₀, z₀ ≤ Z.card ∧ z₀ + X.card + Y.card ≤ T ∧
      (z₀ = Z.card ∨ z₀ + X.card + Y.card = T) :=
    ⟨min Z.card (T - X.card - Y.card), min_le_left _ _, by omega, by
      rcases min_choice Z.card (T - X.card - Y.card) with h | h <;> [left; right] <;> omega⟩
  obtain ⟨Z₀, hZ₀, cZ₀⟩ := Finset.exists_subset_card_eq hz01
  obtain ⟨K, hK, hKD⟩ := exists_response hτ (d := X ∪ Y ∪ Z₀)
    ((card_union3_le _ _ _).trans (by omega))
  have nK : ∀ v, v ∈ K → (v ∈ E → v ∈ F → False) ∧ (v ∈ E → v ∈ G → False) ∧ v ∉ Z₀ :=
    fun v hv => by
      have h := Finset.disjoint_left.1 hKD hv
      simp only [X, Y, Finset.mem_union, Finset.mem_inter, not_or, not_and] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
  have kX : Disjoint K X := Finset.disjoint_left.2 fun v hv h =>
    (nK v hv).1 (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2
  have kY : Disjoint K Y := Finset.disjoint_left.2 fun v hv h =>
    (nK v hv).2.1 (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2
  set Q := F ∩ G ∩ K
  have hQc : (F ∩ G ∩ K).card = Q.card := rfl
  set A := (F ∩ K) \ G
  set B := (G ∩ K) \ F
  set C := E ∩ K
  set V := Z \ K
  set D := E \ (F ∪ G ∪ K)
  have hDc : (E \ (F ∪ G ∪ K)).card = D.card := rfl
  -- disjointness facts
  have mZ : ∀ v, v ∈ Z ↔ v ∈ F ∧ v ∈ G := fun v => Finset.mem_inter
  -- |F ∩ K| = q + a, |G ∩ K| = q + b
  have eFK : (F ∩ K).card = Q.card + A.card := by
    have e : (F ∩ K) ∩ G = Q := by ext v; simp [Q]; tauto
    have h := Finset.card_sdiff_add_card_inter (F ∩ K) G
    rw [e] at h
    change A.card + Q.card = (F ∩ K).card at h
    omega
  have eGK : (G ∩ K).card = Q.card + B.card := by
    have e : (G ∩ K) ∩ F = Q := by ext v; simp [Q]; tauto
    have h := Finset.card_sdiff_add_card_inter (G ∩ K) F
    rw [e] at h
    change B.card + Q.card = (G ∩ K).card at h
    omega
  -- |V| = z - q
  have eV : V.card + Q.card = Z.card := Finset.card_sdiff_add_card_inter Z K
  -- (q) Q ⊆ Z \ Z₀
  have bq : Q.card + z₀ ≤ Z.card := by
    have sub : Q ∪ Z₀ ⊆ Z := by
      intro v hv; rcases Finset.mem_union.1 hv with h | h
      · simp [Q, Z] at h ⊢; tauto
      · exact hZ₀ h
    have d : Disjoint Q Z₀ := Finset.disjoint_left.2 fun v h1 h2 =>
      (nK v (by simp [Q] at h1; tauto)).2.2 h2
    have := Finset.card_le_card sub
    rw [card_union_disj d] at this; omega
  -- generic: three disjoint subsets of an edge P
  have three : ∀ P S₁ S₂ S₃ : Finset α, P ∈ H → S₁ ⊆ P → S₂ ⊆ P → S₃ ⊆ P → Disjoint S₁ S₂ →
      Disjoint (S₁ ∪ S₂) S₃ → S₁.card + S₂.card + S₃.card ≤ k := by
    intro P S₁ S₂ S₃ hP a b c d12 d3
    have := Finset.card_le_card (show S₁ ∪ S₂ ∪ S₃ ⊆ P by
      intro v hv; simp only [Finset.mem_union] at hv; rcases hv with (h | h) | h
      exacts [a h, b h, c h])
    rw [card_union_disj d3, card_union_disj d12, hunif P hP] at this; exact this
  have dXZ0 : Disjoint X Z₀ := Finset.disjoint_left.2 fun v h1 h2 => by
    have := hZ₀ h2; simp [X, Z] at h1 this; exact g0 v h1.1 h1.2 this.2
  have dYZ0 : Disjoint Y Z₀ := Finset.disjoint_left.2 fun v h1 h2 => by
    have := hZ₀ h2; simp [Y, Z] at h1 this; exact g0 v h1.1 this.1 h1.2
  have dXY : Disjoint X Y := Finset.disjoint_left.2 fun v h1 h2 => by
    simp [X, Y] at h1 h2; exact g0 v h1.1 h1.2 h2.2
  -- (f) |F∩K| + x + z₀ ≤ k
  have bf := three F (F ∩ K) X Z₀ hF Finset.inter_subset_left Finset.inter_subset_right
    (fun v h => (Finset.mem_inter.1 (hZ₀ h)).1)
    (Finset.disjoint_left.2 fun v h1 h2 => (nK v (Finset.mem_inter.1 h1).2).1
      (Finset.mem_inter.1 h2).1 (Finset.mem_inter.1 h2).2)
    (Finset.disjoint_left.2 fun v h1 h2 => by
      rcases Finset.mem_union.1 h1 with h | h
      · exact (nK v (Finset.mem_inter.1 h).2).2.2 h2
      · exact Finset.disjoint_left.1 dXZ0 h h2)
  -- (g) |G∩K| + y + z₀ ≤ k
  have bg := three G (G ∩ K) Y Z₀ hG Finset.inter_subset_left Finset.inter_subset_right
    (fun v h => (Finset.mem_inter.1 (hZ₀ h)).2)
    (Finset.disjoint_left.2 fun v h1 h2 => (nK v (Finset.mem_inter.1 h1).2).2.1
      (Finset.mem_inter.1 h2).1 (Finset.mem_inter.1 h2).2)
    (Finset.disjoint_left.2 fun v h1 h2 => by
      rcases Finset.mem_union.1 h1 with h | h
      · exact (nK v (Finset.mem_inter.1 h).2).2.2 h2
      · exact Finset.disjoint_left.1 dYZ0 h h2)
  -- (d) |D| + |C| + x + y ≤ k   (D, C, X, Y disjoint in E)
  have bd : D.card + C.card + X.card + Y.card ≤ k := by
    have sub : D ∪ C ∪ (X ∪ Y) ⊆ E := by
      intro v hv; simp only [Finset.mem_union] at hv
      rcases hv with (h | h) | (h | h)
      · exact (Finset.mem_sdiff.1 h).1
      · exact (Finset.mem_inter.1 h).1
      · exact (Finset.mem_inter.1 h).1
      · exact (Finset.mem_inter.1 h).1
    have d1 : Disjoint D C := Finset.disjoint_left.2 fun v h1 h2 => by
      simp [D, C] at h1 h2; tauto
    have d2 : Disjoint (D ∪ C) (X ∪ Y) := Finset.disjoint_left.2 fun v h1 h2 => by
      simp only [D, C, X, Y, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at h1 h2
      rcases h1 with h | h
      · tauto
      · rcases h2 with h' | h'
        · exact (nK v h.2).1 h'.1 h'.2
        · exact (nK v h.2).2.1 h'.1 h'.2
    have := Finset.card_le_card sub
    rw [card_union_disj d2, card_union_disj d1, card_union_disj dXY, hunif E hE] at this
    omega
  -- (k) q + a + b + c ≤ k (disjoint in K)
  have bk : Q.card + A.card + B.card + C.card ≤ k := by
    have sub : Q ∪ A ∪ B ∪ C ⊆ K := by
      intro v hv; simp only [Q, A, B, C, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hv
      tauto
    have d1 : Disjoint Q A := Finset.disjoint_left.2 fun v h1 h2 => by
      simp [Q, A] at h1 h2; tauto
    have d2 : Disjoint (Q ∪ A) B := Finset.disjoint_left.2 fun v h1 h2 => by
      simp [Q, A, B] at h1 h2; tauto
    have d3 : Disjoint (Q ∪ A ∪ B) C := Finset.disjoint_left.2 fun v h1 h2 => by
      simp only [Q, A, B, C, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at h1 h2
      rcases h1 with (h | h) | h
      · exact g0 v h2.1 h.1.1 h.1.2
      · exact (nK v h2.2).1 h2.1 h.1.1
      · exact (nK v h2.2).2.1 h2.1 h.1.1
    have := Finset.card_le_card sub
    rw [card_union_disj d3, card_union_disj d2, card_union_disj d1, hunif K hK] at this
    exact this
  -- common coverage facts
  have memB : ∀ v, v ∈ G → v ∈ K → v ∉ F → v ∈ B := fun v a b c => by simp [B, a, b, c]
  have memA : ∀ v, v ∈ F → v ∈ K → v ∉ G → v ∈ A := fun v a b c => by simp [A, a, b, c]
  have memC : ∀ v, v ∈ E → v ∈ K → v ∈ C := fun v a b => by simp [C, a, b]
  have memX : ∀ v, v ∈ E → v ∈ F → v ∈ X := fun v a b => by simp [X, a, b]
  have memY : ∀ v, v ∈ E → v ∈ G → v ∈ Y := fun v a b => by simp [Y, a, b]
  have memZ : ∀ v, v ∈ F → v ∈ G → v ∈ Z := fun v a b => by simp [Z, a, b]
  have QZ : ∀ S : Finset α, Z ⊆ S → (Q ∪ S).card ≤ S.card := fun S h =>
    Finset.card_le_card (Finset.union_subset (fun v hv => h (by simp [Q, Z] at hv ⊢; tauto))
      subset_rfl)
  have u2 : ∀ P R : Finset α, (Q ∪ (P ∪ R)).card ≤ Q.card + P.card + R.card := fun P R =>
    (Finset.card_union_le _ _).trans (by have := Finset.card_union_le P R; omega)
  by_cases c0 : C.card + Z.card ≤ T
  · -- Case 0: bases X ∪ B, Y ∪ A, Z ∪ C
    refine onecore_bases_close hprop hτ hE hF hG hK hgood kX kY (X ∪ B) (Y ∪ A) (Z ∪ C)
      (Q.card + X.card + B.card) (Q.card + Y.card + A.card) (Z.card + C.card)
      (u2 _ _) (u2 _ _) ((QZ _ Finset.subset_union_left).trans (Finset.card_union_le _ _))
      (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_
    · intro u v uE uF vG vK vF
      exact Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memX u uE uF], by simp only [Finset.mem_union, true_or, or_true, memB v vG vK vF]⟩
    · intro u v uE uG vF vK vG
      exact Or.inr (Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memY u uE uG], by simp only [Finset.mem_union, true_or, or_true, memA v vF vK vG]⟩)
    · intro u v uF uG _ vE vK
      exact Or.inr (Or.inr ⟨by simp only [Finset.mem_union, true_or, or_true, memZ u uF uG], by simp only [Finset.mem_union, true_or, or_true, memC v vE vK]⟩)
    · intro e eE he
      rcases he with h | h | h
      · exact Or.inl (by simp only [Finset.mem_union, true_or, or_true, memX e eE h])
      · exact Or.inr (Or.inl (by simp only [Finset.mem_union, true_or, or_true, memY e eE h]))
      · exact Or.inr (Or.inr (by simp only [Finset.mem_union, true_or, or_true, memC e eE h]))
  by_cases c1 : A.card + 2 * T < k + X.card + Z.card
  · -- Case 1: split C = C₂ ⊔ C₃; bases X ∪ B, Y ∪ A ∪ Z ∪ C₂, Z ∪ C₃
    obtain ⟨c₂, hc1, hc2, hc⟩ : ∃ c₂, c₂ ≤ C.card ∧ c₂ + Y.card + A.card + Z.card ≤ T ∧
        (c₂ = C.card ∨ c₂ + Y.card + A.card + Z.card = T) :=
      ⟨min C.card (T - Y.card - A.card - Z.card), min_le_left _ _, by omega, by
        rcases min_choice C.card (T - Y.card - A.card - Z.card) with h | h <;> [left; right]
          <;> omega⟩
    obtain ⟨C₂, C₃, -, -, covC, cC₂, cC₃⟩ := split_two C c₂ (C.card - c₂) (by omega)
    refine onecore_bases_close hprop hτ hE hF hG hK hgood kX kY (X ∪ B) (Y ∪ A ∪ Z ∪ C₂)
      (Z ∪ C₃) (Q.card + X.card + B.card) (Y.card + A.card + Z.card + c₂) (Z.card + C.card - c₂)
      (u2 _ _) ((QZ _ (by intro v hv; simp [hv])).trans
        ((card_union4_le _ _ _ _).trans (by omega)))
      ((QZ _ Finset.subset_union_left).trans ((Finset.card_union_le _ _).trans (by omega)))
      (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_
    · intro u v uE uF vG vK vF
      exact Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memX u uE uF], by simp only [Finset.mem_union, true_or, or_true, memB v vG vK vF]⟩
    · intro u v uE uG vF vK vG
      exact Or.inr (Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memY u uE uG], by simp only [Finset.mem_union, true_or, or_true, memA v vF vK vG]⟩)
    · intro u v uF uG _ vE vK
      rcases covC v (memC v vE vK) with h | h
      · exact Or.inr (Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memZ u uF uG], by simp only [Finset.mem_union, true_or, or_true, h]⟩)
      · exact Or.inr (Or.inr ⟨by simp only [Finset.mem_union, true_or, or_true, memZ u uF uG], by simp only [Finset.mem_union, true_or, or_true, h]⟩)
    · intro e eE he
      rcases he with h | h | h
      · exact Or.inl (by simp only [Finset.mem_union, true_or, or_true, memX e eE h])
      · exact Or.inr (Or.inl (by simp only [Finset.mem_union, true_or, or_true, memY e eE h]))
      · rcases covC e (memC e eE h) with h' | h'
        · exact Or.inr (Or.inl (by simp only [Finset.mem_union, true_or, or_true, h']))
        · exact Or.inr (Or.inr (by simp only [Finset.mem_union, true_or, or_true, h']))
  by_cases c2 : B.card + 2 * T < k + Y.card + Z.card
  · -- Case 2 (mirror of Case 1): bases Y ∪ A, X ∪ B ∪ Z ∪ C₂, Z ∪ C₃
    obtain ⟨c₂, hc1, hc2, hc⟩ : ∃ c₂, c₂ ≤ C.card ∧ c₂ + X.card + B.card + Z.card ≤ T ∧
        (c₂ = C.card ∨ c₂ + X.card + B.card + Z.card = T) :=
      ⟨min C.card (T - X.card - B.card - Z.card), min_le_left _ _, by omega, by
        rcases min_choice C.card (T - X.card - B.card - Z.card) with h | h <;> [left; right]
          <;> omega⟩
    obtain ⟨C₂, C₃, -, -, covC, cC₂, cC₃⟩ := split_two C c₂ (C.card - c₂) (by omega)
    refine onecore_bases_close hprop hτ hE hF hG hK hgood kX kY (Y ∪ A) (X ∪ B ∪ Z ∪ C₂)
      (Z ∪ C₃) (Q.card + Y.card + A.card) (X.card + B.card + Z.card + c₂) (Z.card + C.card - c₂)
      (u2 _ _) ((QZ _ (by intro v hv; simp [hv])).trans
        ((card_union4_le _ _ _ _).trans (by omega)))
      ((QZ _ Finset.subset_union_left).trans ((Finset.card_union_le _ _).trans (by omega)))
      (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_
    · intro u v uE uF vG vK vF
      exact Or.inr (Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memX u uE uF], by simp only [Finset.mem_union, true_or, or_true, memB v vG vK vF]⟩)
    · intro u v uE uG vF vK vG
      exact Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memY u uE uG], by simp only [Finset.mem_union, true_or, or_true, memA v vF vK vG]⟩
    · intro u v uF uG _ vE vK
      rcases covC v (memC v vE vK) with h | h
      · exact Or.inr (Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memZ u uF uG], by simp only [Finset.mem_union, true_or, or_true, h]⟩)
      · exact Or.inr (Or.inr ⟨by simp only [Finset.mem_union, true_or, or_true, memZ u uF uG], by simp only [Finset.mem_union, true_or, or_true, h]⟩)
    · intro e eE he
      rcases he with h | h | h
      · exact Or.inr (Or.inl (by simp only [Finset.mem_union, true_or, or_true, memX e eE h]))
      · exact Or.inl (by simp only [Finset.mem_union, true_or, or_true, memY e eE h])
      · rcases covC e (memC e eE h) with h' | h'
        · exact Or.inr (Or.inl (by simp only [Finset.mem_union, true_or, or_true, h']))
        · exact Or.inr (Or.inr (by simp only [Finset.mem_union, true_or, or_true, h']))
  · -- Case 3: u = c + z - T; C = C₁₂ ⊔ C₃ with |C₁₂| = u; V = V₁₃ ⊔ V₂₃ with |V₁₃| = θ
    obtain ⟨u, hu⟩ : ∃ u, C.card + Z.card = T + u := ⟨C.card + Z.card - T, by omega⟩
    obtain ⟨θ, hθ1, hθ⟩ : ∃ θ, Y.card + A.card + Z.card + u ≤ θ + T ∧
        (θ = 0 ∨ θ + T = Y.card + A.card + Z.card + u) :=
      ⟨Y.card + A.card + Z.card + u - T, by omega, by omega⟩
    have hθv : θ ≤ V.card := by omega
    have hθb : Q.card + X.card + B.card + u + θ ≤ T := by omega
    obtain ⟨C₁₂, C₃, -, -, covC, cC₁₂, cC₃⟩ := split_two C u (T - Z.card) (by omega)
    obtain ⟨V₁₃, V₂₃, -, -, covV, cV₁₃, cV₂₃⟩ := split_two V θ (V.card - θ) (by omega)
    refine onecore_bases_close hprop hτ hE hF hG hK hgood kX kY (X ∪ B ∪ C₁₂ ∪ V₁₃)
      (Y ∪ A ∪ C₁₂ ∪ V₂₃) (Z ∪ C₃)
      (Q.card + X.card + B.card + C₁₂.card + V₁₃.card)
      (Q.card + Y.card + A.card + C₁₂.card + V₂₃.card) (Z.card + C₃.card)
      ((Finset.card_union_le _ _).trans (by have := card_union4_le X B C₁₂ V₁₃; omega))
      ((Finset.card_union_le _ _).trans (by have := card_union4_le Y A C₁₂ V₂₃; omega))
      ((QZ _ Finset.subset_union_left).trans (Finset.card_union_le _ _))
      (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_
    · intro u v uE uF vG vK vF
      exact Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memX u uE uF], by simp only [Finset.mem_union, true_or, or_true, memB v vG vK vF]⟩
    · intro u v uE uG vF vK vG
      exact Or.inr (Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, memY u uE uG], by simp only [Finset.mem_union, true_or, or_true, memA v vF vK vG]⟩)
    · intro u v uF uG uK vE vK
      have uV : u ∈ V := by simp [V, Z, uF, uG, uK]
      rcases covC v (memC v vE vK) with h | h
      · rcases covV u uV with h' | h'
        · exact Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, h'], by simp only [Finset.mem_union, true_or, or_true, h]⟩
        · exact Or.inr (Or.inl ⟨by simp only [Finset.mem_union, true_or, or_true, h'], by simp only [Finset.mem_union, true_or, or_true, h]⟩)
      · exact Or.inr (Or.inr ⟨by simp only [Finset.mem_union, true_or, or_true, memZ u uF uG], by simp only [Finset.mem_union, true_or, or_true, h]⟩)
    · intro e eE he
      rcases he with h | h | h
      · exact Or.inl (by simp only [Finset.mem_union, true_or, or_true, memX e eE h])
      · exact Or.inr (Or.inl (by simp only [Finset.mem_union, true_or, or_true, memY e eE h]))
      · rcases covC e (memC e eE h) with h' | h'
        · exact Or.inl (by simp only [Finset.mem_union, true_or, or_true, h'])
        · exact Or.inr (Or.inr (by simp only [Finset.mem_union, true_or, or_true, h']))

end Erdos644
