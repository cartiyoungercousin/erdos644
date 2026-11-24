import Lean644.TwoCores

/-!
# Lemma 4.7 (near core), manuscript Appendix A

Dichotomy with threshold `m` = `IntersectionGap H m (k/2)` (two distinct edges meet in `≤ m` or
`> k/2` points; `k/2` is floor division). `Δ = (S-T)₊` (truncated subtraction).
Request `K` avoiding `Y ∪ Z` and `min(x, T-y-z)` points of `X`. Cells: `P = X∩K`,
`A = (E∩K)∖F`, `B = (F∩K)∖E`, `C = G∩K`, `W = G∖(E∪F∪K)`.
Case 1 (`|E∩K| ≤ m`): requests `X∪Y∪B ∪ C₁ ∪ W₁`, `P∪Z∪A ∪ W₂`, `X ∪ C₃ ∪ W₃`.
Case 2 (`|E∩K| > m`, so `|G∩K| ≤ m`): requests `P∪Y∪Z∪B ∪ A₁ ∪ W₁`, `X∪C ∪ W₂`, `Z ∪ A₃`
(in the branch `S ≤ T` of the hypothesis, `P = ∅` and `W` is not needed).
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Lemma 4.7 (near core).** -/
theorem nearCore_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k m : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k) (hk : 0 < k)
    (hdich : IntersectionGap H m (k / 2))
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (hyz : (E ∩ G).card + (F ∩ G).card ≤ T) (hmz : m + (F ∩ G).card ≤ T)
    (hxm : (E ∩ F).card + m ≤ T) (h4 : k + (E ∩ G).card - (F ∩ G).card ≤ T)
    (h5 : 2 * k + (E ∩ F).card - 2 * (F ∩ G).card ≤ 2 * T)
    (h6 : 2 * k + (E ∩ F).card + m - (F ∩ G).card ≤ 3 * T)
    (hor : (k - (E ∩ F).card + (E ∩ G).card
          + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card - T) ≤ T ∧
        2 * k - 2 * (E ∩ F).card + (F ∩ G).card
          + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card - T) ≤ 2 * T ∧
        2 * k - (F ∩ G).card + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card - T) ≤ 2 * T ∧
        3 * k - (E ∩ F).card - (E ∩ G).card
          + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card - T) ≤ 3 * T) ∨
      ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card ≤ T ∧
        k - (E ∩ F).card + (E ∩ G).card ≤ T ∧
        2 * k - 2 * (E ∩ F).card + (F ∩ G).card ≤ 2 * T)) : False := by
  have g0 : ∀ v, v ∈ E → v ∈ F → v ∈ G → False := fun v h1 h2 h3 => by
    have : v ∈ E ∩ F ∩ G := by simp [h1, h2, h3]
    unfold IsGoodTriple at hgood; rw [hgood] at this; simp at this
  have kE := hunif E hE
  have kF := hunif F hF
  have kG := hunif G hG
  set X := E ∩ F with hXdef
  set Y := E ∩ G with hYdef
  set Z := F ∩ G with hZdef
  -- subtraction-free forms
  obtain ⟨Δ, hΔ1, hΔ2⟩ : ∃ Δ, X.card + Y.card + Z.card ≤ T + Δ ∧
      (Δ = 0 ∨ X.card + Y.card + Z.card = T + Δ) :=
    ⟨X.card + Y.card + Z.card - T, by omega, by omega⟩
  have d4 : k + Y.card ≤ T + Z.card := by clear * - h4; omega
  have d5 : 2 * k + X.card ≤ 2 * T + 2 * Z.card := by clear * - h5; omega
  have d6 : 2 * k + X.card + m ≤ 3 * T + Z.card := by clear * - h6; omega
  have e1 : k + Y.card + Δ ≤ T + X.card := by clear * - hor hΔ1 hΔ2; omega
  have e2 : 2 * k + Z.card + Δ ≤ 2 * T + 2 * X.card := by clear * - hor hΔ1 hΔ2; omega
  have hbr : (2 * k + Δ ≤ 2 * T + Z.card ∧ 3 * k + Δ ≤ 3 * T + X.card + Y.card) ∨
      X.card + Y.card + Z.card ≤ T := by clear * - hor hΔ1 hΔ2; omega
  clear h4 h5 h6 hor
  -- the request: Y ∪ Z ∪ X₀
  obtain ⟨x₀, hx01, hx02, hx0⟩ : ∃ x₀, x₀ ≤ X.card ∧ x₀ + Y.card + Z.card ≤ T ∧
      (x₀ = X.card ∨ x₀ + Y.card + Z.card = T) :=
    ⟨min X.card (T - Y.card - Z.card), min_le_left _ _, by omega, by
      rcases min_choice X.card (T - Y.card - Z.card) with h | h <;> [left; right] <;> omega⟩
  obtain ⟨X₀, hX₀, cX₀⟩ := Finset.exists_subset_card_eq hx01
  obtain ⟨K, hK, hKd⟩ := exists_response hτ (d := Y ∪ Z ∪ X₀)
    ((card_union3_le _ _ _).trans (by omega))
  have nKY : ∀ v ∈ K, v ∉ Y := fun v hv h => Finset.disjoint_left.1 hKd hv (by simp [h])
  have nKZ : ∀ v ∈ K, v ∉ Z := fun v hv h => Finset.disjoint_left.1 hKd hv (by simp [h])
  have nKX₀ : ∀ v ∈ K, v ∉ X₀ := fun v hv h => Finset.disjoint_left.1 hKd hv (by simp [h])
  -- cell sizes
  have hP : (X ∩ K).card ≤ Δ := by
    have s : X ∩ K ⊆ X \ X₀ := fun v hv => Finset.mem_sdiff.2
      ⟨(Finset.mem_inter.1 hv).1, nKX₀ v (Finset.mem_inter.1 hv).2⟩
    have e := Finset.card_sdiff_add_card_eq_card hX₀
    have := Finset.card_le_card s
    clear * - e this cX₀ hx0 hΔ1; omega
  have hPA : (E ∩ K).card = (X ∩ K).card + ((E ∩ K) \ F).card := by
    have e : (E ∩ K) ∩ F = X ∩ K := by ext v; simp [X]; tauto
    have h := Finset.card_sdiff_add_card_inter (E ∩ K) F
    rw [e] at h; omega
  have hA : ((E ∩ K) \ F).card + X.card + Y.card ≤ k := by
    rw [← kE]
    refine three_le (fun v h => (Finset.mem_inter.1 (Finset.mem_sdiff.1 h).1).1)
      Finset.inter_subset_left Finset.inter_subset_left ?_ ?_
    · exact Finset.disjoint_left.2 fun v h1 h2 =>
        (Finset.mem_sdiff.1 h1).2 (Finset.mem_inter.1 h2).2
    · refine Finset.disjoint_left.2 fun v h1 h2 => ?_
      rcases Finset.mem_union.1 h1 with h | h
      · exact nKY v (Finset.mem_inter.1 (Finset.mem_sdiff.1 h).1).2 h2
      · exact g0 v (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2 (Finset.mem_inter.1 h2).2
  have hB : ((F ∩ K) \ E).card + X.card + Z.card ≤ k := by
    rw [← kF]
    refine three_le (fun v h => (Finset.mem_inter.1 (Finset.mem_sdiff.1 h).1).1)
      Finset.inter_subset_right Finset.inter_subset_left ?_ ?_
    · exact Finset.disjoint_left.2 fun v h1 h2 =>
        (Finset.mem_sdiff.1 h1).2 (Finset.mem_inter.1 h2).1
    · refine Finset.disjoint_left.2 fun v h1 h2 => ?_
      rcases Finset.mem_union.1 h1 with h | h
      · exact nKZ v (Finset.mem_inter.1 (Finset.mem_sdiff.1 h).1).2 h2
      · exact g0 v (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2 (Finset.mem_inter.1 h2).2
  have hCW : (G ∩ K).card + (G \ (E ∪ F ∪ K)).card + Y.card + Z.card ≤ k := by
    have dCW : Disjoint (G ∩ K) (G \ (E ∪ F ∪ K)) := Finset.disjoint_left.2 fun v h1 h2 => by
      simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h2
      exact h2.2.2 (Finset.mem_inter.1 h1).2
    have := three_le (P := G) (S₁ := (G ∩ K) ∪ (G \ (E ∪ F ∪ K))) (S₂ := Y) (S₃ := Z)
      (Finset.union_subset Finset.inter_subset_left Finset.sdiff_subset)
      Finset.inter_subset_right Finset.inter_subset_right
      (Finset.disjoint_left.2 fun v h1 h2 => by
        rcases Finset.mem_union.1 h1 with h | h
        · exact nKY v (Finset.mem_inter.1 h).2 h2
        · simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h
          exact h.2.1.1 (Finset.mem_inter.1 h2).1)
      (Finset.disjoint_left.2 fun v h1 h2 => by
        simp only [Finset.mem_union] at h1
        rcases h1 with (h | h) | h
        · exact nKZ v (Finset.mem_inter.1 h).2 h2
        · simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h
          exact h.2.1.2 (Finset.mem_inter.1 h2).1
        · exact g0 v (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h2).1
            (Finset.mem_inter.1 h).2)
    rw [card_union_disj dCW, kG] at this; omega
  -- membership facts
  have mX : ∀ v, v ∈ E → v ∈ F → v ∈ X := fun v a b => Finset.mem_inter.2 ⟨a, b⟩
  have mY : ∀ v, v ∈ E → v ∈ G → v ∈ Y := fun v a b => Finset.mem_inter.2 ⟨a, b⟩
  have mZ : ∀ v, v ∈ F → v ∈ G → v ∈ Z := fun v a b => Finset.mem_inter.2 ⟨a, b⟩
  have mA : ∀ v, v ∈ E → v ∈ K → v ∉ F → v ∈ (E ∩ K) \ F := fun v a b c =>
    Finset.mem_sdiff.2 ⟨Finset.mem_inter.2 ⟨a, b⟩, c⟩
  have mB : ∀ v, v ∈ F → v ∈ K → v ∉ E → v ∈ (F ∩ K) \ E := fun v a b c =>
    Finset.mem_sdiff.2 ⟨Finset.mem_inter.2 ⟨a, b⟩, c⟩
  have mC : ∀ v, v ∈ G → v ∈ K → v ∈ G ∩ K := fun v a b => Finset.mem_inter.2 ⟨a, b⟩
  have mW : ∀ v, v ∈ G → v ∉ E → v ∉ F → v ∉ K → v ∈ G \ (E ∪ F ∪ K) := fun v a b c d =>
    Finset.mem_sdiff.2 ⟨a, by simp only [Finset.mem_union, not_or]; exact ⟨⟨b, c⟩, d⟩⟩
  have nEGK : ∀ v, v ∈ E → v ∈ G → v ∈ K → False := fun v a b c => nKY v c (mY v a b)
  have nFGK : ∀ v, v ∈ F → v ∈ G → v ∈ K → False := fun v a b c => nKZ v c (mZ v a b)
  by_cases hc : (E ∩ K).card ≤ m
  · -- Case 1
    set L₁ := X.card + Y.card + ((F ∩ K) \ E).card
    set L₂ := (X ∩ K).card + Z.card + ((E ∩ K) \ F).card
    have tL1 : L₁ ≤ T := by clear * - hB d4; omega
    have tL2 : L₂ ≤ T := by clear * - hc hPA hmz; omega
    have tL3 : X.card ≤ T := by clear * - hxm; omega
    obtain ⟨c₁, hc11, hc12, hc1⟩ : ∃ c₁, c₁ ≤ (G ∩ K).card ∧ L₁ + c₁ ≤ T ∧
        (c₁ = (G ∩ K).card ∨ L₁ + c₁ = T) :=
      ⟨min (G ∩ K).card (T - L₁), min_le_left _ _, by omega, by
        rcases min_choice (G ∩ K).card (T - L₁) with h | h <;> [left; right] <;> omega⟩
    have tC3 : X.card + ((G ∩ K).card - c₁) ≤ T := by clear * - hc1 hc11 hc12 hB hCW d5; omega
    obtain ⟨C₁, C₃, -, -, covC, cC₁, cC₃⟩ :=
      split_two (G ∩ K) c₁ ((G ∩ K).card - c₁) (by omega)
    set W := G \ (E ∪ F ∪ K)
    have tot : L₁ + c₁ + L₂ + (X.card + ((G ∩ K).card - c₁)) + W.card ≤ 3 * T := by
      clear * - hc11 hc hPA hB hCW d6; omega
    obtain ⟨w₁, hw11, hw12, hw1⟩ : ∃ w₁, w₁ ≤ W.card ∧ L₁ + c₁ + w₁ ≤ T ∧
        (w₁ = W.card ∨ L₁ + c₁ + w₁ = T) :=
      ⟨min W.card (T - (L₁ + c₁)), min_le_left _ _, by omega, by
        rcases min_choice W.card (T - (L₁ + c₁)) with h | h <;> [left; right] <;> omega⟩
    obtain ⟨w₂, hw21, hw22, hw2⟩ : ∃ w₂, w₁ + w₂ ≤ W.card ∧ L₂ + w₂ ≤ T ∧
        (w₁ + w₂ = W.card ∨ L₂ + w₂ = T) :=
      ⟨min (W.card - w₁) (T - L₂), by omega, by omega, by
        rcases min_choice (W.card - w₁) (T - L₂) with h | h <;> [left; right] <;> omega⟩
    obtain ⟨W₁, W₂, W₃, -, -, -, covW, cW₁, cW₂, cW₃⟩ :=
      split_three W w₁ w₂ (W.card - w₁ - w₂) (by omega)
    have r1 : (X ∪ Y ∪ ((F ∩ K) \ E) ∪ C₁ ∪ W₁).card ≤ T := by
      have a := card_union4_le (X ∪ Y) ((F ∩ K) \ E) C₁ W₁
      have b := Finset.card_union_le X Y
      clear * - a b cC₁ cW₁ hw12; omega
    have r2 : ((X ∩ K) ∪ Z ∪ ((E ∩ K) \ F) ∪ W₂).card ≤ T := by
      have a := card_union4_le (X ∩ K) Z ((E ∩ K) \ F) W₂
      clear * - a cW₂ hw22; omega
    have r3 : (X ∪ C₃ ∪ W₃).card ≤ T := by
      have a := card_union3_le X C₃ W₃
      clear * - a cC₃ cW₃ tot tC3 hw11 hw1 hw21 hw2 hw12 hw22; omega
    refine four_closes hprop hτ hE hF hG hK hgood
      (X ∪ Y ∪ ((F ∩ K) \ E) ∪ C₁ ∪ W₁) ((X ∩ K) ∪ Z ∪ ((E ∩ K) \ F) ∪ W₂) (X ∪ C₃ ∪ W₃)
      r1 r2 r3 ?_ ?_ ?_ ?_ ?_ ?_
    · intro p q pE pF pK qG
      by_cases qE : q ∈ E
      · exact Or.inl ⟨by simp [mX p pE pF], by simp [mY q qE qG]⟩
      by_cases qF : q ∈ F
      · exact Or.inr (Or.inl ⟨by simp [Finset.mem_inter.2 ⟨mX p pE pF, pK⟩],
          by simp [mZ q qF qG]⟩)
      by_cases qK : q ∈ K
      · rcases covC q (mC q qG qK) with h | h
        · exact Or.inl ⟨by simp [mX p pE pF], by simp [h]⟩
        · exact Or.inr (Or.inr ⟨by simp [mX p pE pF], by simp [h]⟩)
      rcases covW q (mW q qG qE qF qK) with h | h | h
      · exact Or.inl ⟨by simp [mX p pE pF], by simp [h]⟩
      · exact Or.inr (Or.inl ⟨by simp [Finset.mem_inter.2 ⟨mX p pE pF, pK⟩], by simp [h]⟩)
      · exact Or.inr (Or.inr ⟨by simp [mX p pE pF], by simp [h]⟩)
    · intro p q pE pG pK _; exact (nEGK p pE pG pK).elim
    · intro p q pF pG pK _; exact (nFGK p pF pG pK).elim
    · intro p q pE pF _ qG qK _ _
      rcases covC q (mC q qG qK) with h | h
      · exact Or.inl ⟨by simp [mX p pE pF], by simp [h]⟩
      · exact Or.inr (Or.inr ⟨by simp [mX p pE pF], by simp [h]⟩)
    · intro p q pE pG _ qF qK qE _
      exact Or.inl ⟨by simp [mY p pE pG], by simp [mB q qF qK qE]⟩
    · intro p q pF pG _ qE qK qF _
      exact Or.inr (Or.inl ⟨by simp [mZ p pF pG], by simp [mA q qE qK qF]⟩)
  · -- Case 2: |E ∩ K| > m, so |E ∩ K| > k/2 and |G ∩ K| ≤ m
    have hEK : k / 2 < (E ∩ K).card := by
      by_contra h
      push Not at h
      exact hc (hdich.apply hunif (by omega) hE hK h)
    have hGKu : (G ∩ K).card ≤ k / 2 := by
      have d : Disjoint (E ∩ K) (G ∩ K) := Finset.disjoint_left.2 fun v h1 h2 =>
        nEGK v (Finset.mem_inter.1 h1).1 (Finset.mem_inter.1 h2).1 (Finset.mem_inter.1 h1).2
      have := Finset.card_le_card (show (E ∩ K) ∪ (G ∩ K) ⊆ K from
        Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
      rw [card_union_disj d, hunif K hK] at this
      omega
    have hGK : (G ∩ K).card ≤ m := hdich.apply hunif (by omega) hG hK hGKu
    set L₁ := (X ∩ K).card + Y.card + Z.card + ((F ∩ K) \ E).card
    set L₂ := X.card + (G ∩ K).card
    have tL1 : L₁ ≤ T := by clear * - hP hB e1; omega
    have tL2 : L₂ ≤ T := by clear * - hGK hxm; omega
    -- which part of W must be covered
    obtain ⟨W', hW'W, hW'cov, f3, f4⟩ : ∃ W' : Finset α, W' ⊆ G \ (E ∪ F ∪ K) ∧
        ((X ∩ K).Nonempty → W' = G \ (E ∪ F ∪ K)) ∧ L₁ + L₂ + W'.card ≤ 2 * T ∧
        L₁ + L₂ + Z.card + ((E ∩ K) \ F).card + W'.card ≤ 3 * T := by
      rcases hbr with ⟨b3, b4⟩ | hS
      · exact ⟨_, subset_rfl, fun _ => rfl, by clear * - hP hB hCW b3; omega,
          by clear * - hP hB hCW hA b4; omega⟩
      · have hp0 : (X ∩ K).card = 0 := by clear * - hP hS hΔ2 hΔ1; omega
        refine ⟨∅, Finset.empty_subset _, fun h => ?_, by simp; omega, ?_⟩
        · rw [Finset.card_eq_zero] at hp0; rw [hp0] at h; exact absurd h (by simp)
        · simp; clear * - tL1 tL2 hP hA hB e2; omega
    obtain ⟨a₃, ha31, ha32, ha3⟩ : ∃ a₃, a₃ ≤ ((E ∩ K) \ F).card ∧ Z.card + a₃ ≤ T ∧
        (a₃ = ((E ∩ K) \ F).card ∨ Z.card + a₃ = T) :=
      ⟨min ((E ∩ K) \ F).card (T - Z.card), min_le_left _ _, by omega, by
        rcases min_choice ((E ∩ K) \ F).card (T - Z.card) with h | h <;> [left; right]
          <;> omega⟩
    obtain ⟨w₂, hw21, hw22, hw2⟩ : ∃ w₂, w₂ ≤ W'.card ∧ L₂ + w₂ ≤ T ∧
        (w₂ = W'.card ∨ L₂ + w₂ = T) :=
      ⟨min W'.card (T - L₂), min_le_left _ _, by omega, by
        rcases min_choice W'.card (T - L₂) with h | h <;> [left; right] <;> omega⟩
    have t1 : L₁ + (((E ∩ K) \ F).card - a₃) + (W'.card - w₂) ≤ T := by
      clear * - ha31 ha32 ha3 hw21 hw22 hw2 f3 f4 tL1 tL2 hP hA hB e2; omega
    obtain ⟨A₃, A₁, -, -, covA, cA₃, cA₁⟩ :=
      split_two ((E ∩ K) \ F) a₃ (((E ∩ K) \ F).card - a₃) (by omega)
    obtain ⟨W₂, W₁, -, -, covW, cW₂, cW₁⟩ := split_two W' w₂ (W'.card - w₂) (by omega)
    have r1 : ((X ∩ K) ∪ Y ∪ Z ∪ ((F ∩ K) \ E) ∪ A₁ ∪ W₁).card ≤ T := by
      have a := card_union4_le (X ∩ K) Y Z ((F ∩ K) \ E)
      have b := card_union3_le ((X ∩ K) ∪ Y ∪ Z ∪ ((F ∩ K) \ E)) A₁ W₁
      clear * - a b cA₁ cW₁ t1; omega
    have r2 : (X ∪ (G ∩ K) ∪ W₂).card ≤ T := by
      have a := card_union3_le X (G ∩ K) W₂
      clear * - a cW₂ hw22; omega
    have r3 : (Z ∪ A₃).card ≤ T := by
      have a := Finset.card_union_le Z A₃
      clear * - a cA₃ ha32; omega
    refine four_closes hprop hτ hE hF hG hK hgood
      ((X ∩ K) ∪ Y ∪ Z ∪ ((F ∩ K) \ E) ∪ A₁ ∪ W₁) (X ∪ (G ∩ K) ∪ W₂) (Z ∪ A₃)
      r1 r2 r3 ?_ ?_ ?_ ?_ ?_ ?_
    · intro p q pE pF pK qG
      have pP : p ∈ X ∩ K := Finset.mem_inter.2 ⟨mX p pE pF, pK⟩
      by_cases qE : q ∈ E
      · exact Or.inl ⟨by simp [pP], by simp [mY q qE qG]⟩
      by_cases qF : q ∈ F
      · exact Or.inl ⟨by simp [pP], by simp [mZ q qF qG]⟩
      by_cases qK : q ∈ K
      · exact Or.inr (Or.inl ⟨by simp [mX p pE pF], by simp [mC q qG qK]⟩)
      have qW' : q ∈ W' := by rw [hW'cov ⟨p, pP⟩]; exact mW q qG qE qF qK
      rcases covW q qW' with h | h
      · exact Or.inr (Or.inl ⟨by simp [mX p pE pF], by simp [h]⟩)
      · exact Or.inl ⟨by simp [pP], by simp [h]⟩
    · intro p q pE pG pK _; exact (nEGK p pE pG pK).elim
    · intro p q pF pG pK _; exact (nFGK p pF pG pK).elim
    · intro p q pE pF _ qG qK _ _
      exact Or.inr (Or.inl ⟨by simp [mX p pE pF], by simp [mC q qG qK]⟩)
    · intro p q pE pG _ qF qK qE _
      exact Or.inl ⟨by simp [mY p pE pG], by simp [mB q qF qK qE]⟩
    · intro p q pF pG _ qE qK qF _
      rcases covA q (mA q qE qK qF) with h | h
      · exact Or.inr (Or.inr ⟨by simp [mZ p pF pG], by simp [h]⟩)
      · exact Or.inl ⟨by simp [mZ p pF pG], by simp [h]⟩

end Erdos644
