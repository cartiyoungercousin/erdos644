import Lean644.GapTraces
import Lean644.FourClose

/-!
# Lemma 4.6 (two cores), manuscript Appendix A

Request `Y ∪ R₀` with `R₀ ⊆ F`, `|R₀| = T - y`, containing `g` points of `X` and `g` of `Z`
and as much of `X ∪ Z` as possible (`g = (k-y-u)₊`, truncated subtraction). The traces of the
response `K` on `E` and `G` are then `≤ u`, hence `≤ ℓ` by the gap. Bases `X ∪ (G∩K)`,
`Z ∪ (E∩K)`, `Y ∪ (F∩K)`; the private parts `E ∖ (F∪G∪K)` and `G ∖ (E∪F∪K)` are distributed.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

section mem3
variable {A B C : Finset α} {x : α}
private theorem m3_1 (h : x ∈ A) : x ∈ A ∪ B ∪ C :=
  Finset.mem_union_left _ (Finset.mem_union_left _ h)
private theorem m3_2 (h : x ∈ B) : x ∈ A ∪ B ∪ C :=
  Finset.mem_union_left _ (Finset.mem_union_right _ h)
private theorem m3_3 (h : x ∈ C) : x ∈ A ∪ B ∪ C := Finset.mem_union_right _ h
end mem3

/-- Three pairwise disjoint subsets of `P`. -/
theorem three_le {P S₁ S₂ S₃ : Finset α} (a : S₁ ⊆ P) (b : S₂ ⊆ P) (c : S₃ ⊆ P)
    (d12 : Disjoint S₁ S₂) (d3 : Disjoint (S₁ ∪ S₂) S₃) :
    S₁.card + S₂.card + S₃.card ≤ P.card := by
  have := Finset.card_le_card (show S₁ ∪ S₂ ∪ S₃ ⊆ P from
    Finset.union_subset (Finset.union_subset a b) c)
  rwa [card_union_disj d3, card_union_disj d12] at this

/-- **Lemma 4.6 (two cores).** Assume `Gap(ℓ,u)`, `u < k`, `T ≤ k`, `g = (k-y-u)₊`. -/
theorem twoCores_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k l u : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k) (hu : u < k)
    (hgap : IntersectionGap H l u)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (hg1 : k - (E ∩ G).card - u ≤ (E ∩ F).card) (hg2 : k - (E ∩ G).card - u ≤ (F ∩ G).card)
    (hg3 : (E ∩ G).card + 2 * (k - (E ∩ G).card - u) ≤ T)
    (h4 : (E ∩ F).card + l ≤ T) (h5 : (F ∩ G).card + l ≤ T)
    (h6 : k + 2 * (E ∩ G).card ≤ 2 * T) (h7 : 3 * k ≤ 4 * T)
    (h8 : 3 * k + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card) ≤ 5 * T) : False := by
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
  obtain ⟨g, e1, gX, gZ, gY⟩ : ∃ g, k ≤ u + Y.card + g ∧ g ≤ X.card ∧ g ≤ Z.card ∧
      Y.card + 2 * g ≤ T :=
    ⟨k - Y.card - u, by omega, hg1, hg2, hg3⟩
  obtain ⟨Δ, hΔ1, hΔ2⟩ : ∃ Δ, X.card + Y.card + Z.card ≤ T + Δ ∧
      (Δ = 0 ∨ X.card + Y.card + Z.card = T + Δ) :=
    ⟨X.card + Y.card + Z.card - T, by omega, by omega⟩
  have hYT : Y.card ≤ T := by omega
  clear hg1 hg2 hg3
  -- disjointness of the cells
  have dXZ : Disjoint X Z := Finset.disjoint_left.2 fun v h1 h2 =>
    g0 v (Finset.mem_inter.1 h1).1 (Finset.mem_inter.1 h1).2 (Finset.mem_inter.1 h2).2
  have dXY : Disjoint X Y := Finset.disjoint_left.2 fun v h1 h2 =>
    g0 v (Finset.mem_inter.1 h1).1 (Finset.mem_inter.1 h1).2 (Finset.mem_inter.1 h2).2
  have dYZ : Disjoint Y Z := Finset.disjoint_left.2 fun v h1 h2 =>
    g0 v (Finset.mem_inter.1 h1).1 (Finset.mem_inter.1 h2).1 (Finset.mem_inter.1 h1).2
  have XF : X ⊆ F := Finset.inter_subset_right
  have ZF : Z ⊆ F := Finset.inter_subset_left
  have cXZ : (X ∪ Z).card = X.card + Z.card := card_union_disj dXZ
  -- the request inside F
  obtain ⟨X₀, hX₀, cX₀⟩ := Finset.exists_subset_card_eq gX
  obtain ⟨Z₀, hZ₀, cZ₀⟩ := Finset.exists_subset_card_eq gZ
  obtain ⟨R₀, hR₀F, cR₀, hX₀R, hZ₀R, hrest⟩ : ∃ R₀ : Finset α, R₀ ⊆ F ∧ R₀.card + Y.card = T ∧
      X₀ ⊆ R₀ ∧ Z₀ ⊆ R₀ ∧ ((X ∪ Z) \ R₀).card ≤ Δ := by
    by_cases hM : X.card + Z.card + Y.card ≤ T
    · -- all of X ∪ Z, plus private points of F
      have hpriv : T - Y.card - X.card - Z.card ≤ (F \ (X ∪ Z)).card := by
        have := Finset.card_sdiff_add_card_eq_card (Finset.union_subset XF ZF)
        omega
      obtain ⟨R₁, hR₁, cR₁⟩ := Finset.exists_subset_card_eq hpriv
      refine ⟨X ∪ Z ∪ R₁, Finset.union_subset (Finset.union_subset XF ZF)
        (hR₁.trans Finset.sdiff_subset), ?_, fun v hv => m3_1 (hX₀ hv),
        fun v hv => m3_2 (hZ₀ hv), ?_⟩
      · have d : Disjoint (X ∪ Z) R₁ := Finset.disjoint_left.2 fun v h1 h2 =>
          (Finset.mem_sdiff.1 (hR₁ h2)).2 h1
        rw [card_union_disj d, cXZ, cR₁]; omega
      · have : (X ∪ Z) \ (X ∪ Z ∪ R₁) = ∅ := by
          ext v; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.notMem_empty,
            iff_false, not_and, not_or]; tauto
        rw [this]; simp
    · -- g points of X, g of Z, then other points of X ∪ Z
      have hsub : X₀ ∪ Z₀ ⊆ X ∪ Z := Finset.union_subset_union hX₀ hZ₀
      have d0 : Disjoint X₀ Z₀ := Finset.disjoint_of_subset_left hX₀
        (Finset.disjoint_of_subset_right hZ₀ dXZ)
      have c0 : (X₀ ∪ Z₀).card = 2 * g := by rw [card_union_disj d0, cX₀, cZ₀]; omega
      have e0 := Finset.card_sdiff_add_card_eq_card hsub
      obtain ⟨R₁, hR₁, cR₁⟩ := Finset.exists_subset_card_eq
        (show T - Y.card - 2 * g ≤ ((X ∪ Z) \ (X₀ ∪ Z₀)).card by omega)
      have d1 : Disjoint (X₀ ∪ Z₀) R₁ := Finset.disjoint_left.2 fun v h1 h2 =>
        (Finset.mem_sdiff.1 (hR₁ h2)).2 h1
      refine ⟨X₀ ∪ Z₀ ∪ R₁, Finset.union_subset (hsub.trans (Finset.union_subset XF ZF))
        (hR₁.trans (Finset.sdiff_subset.trans (Finset.union_subset XF ZF))), ?_,
        fun v hv => m3_1 hv, fun v hv => m3_2 hv, ?_⟩
      · rw [card_union_disj d1, c0, cR₁]; omega
      · have s1 : (X ∪ Z) \ (X₀ ∪ Z₀ ∪ R₁) ⊆ ((X ∪ Z) \ (X₀ ∪ Z₀)) \ R₁ := by
          intro v hv
          simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hv ⊢
          exact ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩
        have e1' := Finset.card_sdiff_add_card_eq_card hR₁
        have := Finset.card_le_card s1
        omega
  -- the response
  obtain ⟨K, hK, hKd⟩ := exists_response hτ (d := Y ∪ R₀)
    ((Finset.card_union_le _ _).trans (by omega))
  have nKY : ∀ v ∈ K, v ∉ Y := fun v hv h =>
    Finset.disjoint_left.1 hKd hv (Finset.mem_union_left _ h)
  have nKR : ∀ v ∈ K, v ∉ R₀ := fun v hv h =>
    Finset.disjoint_left.1 hKd hv (Finset.mem_union_right _ h)
  -- (i), (ii): traces on E and G
  have bE : (E ∩ K).card + Y.card + X₀.card ≤ k := by
    rw [← kE]
    refine three_le Finset.inter_subset_left Finset.inter_subset_left
      (hX₀.trans Finset.inter_subset_left) ?_ ?_
    · exact Finset.disjoint_left.2 fun v h1 h2 => nKY v (Finset.mem_inter.1 h1).2 h2
    · refine Finset.disjoint_left.2 fun v h1 h2 => ?_
      rcases Finset.mem_union.1 h1 with h | h
      · exact nKR v (Finset.mem_inter.1 h).2 (hX₀R h2)
      · exact Finset.disjoint_left.1 dXY (hX₀ h2) h
  have bG : (G ∩ K).card + Y.card + Z₀.card ≤ k := by
    rw [← kG]
    refine three_le Finset.inter_subset_left Finset.inter_subset_right
      (hZ₀.trans Finset.inter_subset_right) ?_ ?_
    · exact Finset.disjoint_left.2 fun v h1 h2 => nKY v (Finset.mem_inter.1 h1).2 h2
    · refine Finset.disjoint_left.2 fun v h1 h2 => ?_
      rcases Finset.mem_union.1 h1 with h | h
      · exact nKR v (Finset.mem_inter.1 h).2 (hZ₀R h2)
      · exact Finset.disjoint_left.1 dYZ h (hZ₀ h2)
  have lE : (E ∩ K).card ≤ l := hgap.apply hunif hu hE hK (by clear * - bE e1 cX₀; omega)
  have lG : (G ∩ K).card ≤ l := hgap.apply hunif hu hG hK (by clear * - bG e1 cZ₀; omega)
  -- (iii): trace on F
  have bF : (F ∩ K).card + R₀.card ≤ k := by
    have := Finset.card_le_card (show (F ∩ K) ∪ R₀ ⊆ F from
      Finset.union_subset Finset.inter_subset_left hR₀F)
    rw [card_union_disj (Finset.disjoint_left.2 fun v h1 h2 =>
      nKR v (Finset.mem_inter.1 h1).2 h2), kF] at this
    exact this
  -- (iv): the two cores
  have bPR : (X ∩ K).card + (Z ∩ K).card ≤ Δ := by
    have d : Disjoint (X ∩ K) (Z ∩ K) := Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left dXZ)
    have s : (X ∩ K) ∪ (Z ∩ K) ⊆ (X ∪ Z) \ R₀ := by
      intro v hv
      rcases Finset.mem_union.1 hv with h | h
      · exact Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ (Finset.mem_inter.1 h).1,
          nKR v (Finset.mem_inter.1 h).2⟩
      · exact Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ (Finset.mem_inter.1 h).1,
          nKR v (Finset.mem_inter.1 h).2⟩
    have := Finset.card_le_card s
    rw [card_union_disj d] at this
    omega
  -- (v), (vi): private parts
  have bD : (E \ (F ∪ G ∪ K)).card + (E ∩ K).card + X.card + Y.card ≤ k + (X ∩ K).card := by
    have hA := Finset.card_union_add_card_inter X (E ∩ K)
    have hXK : (X ∩ (E ∩ K)).card ≤ (X ∩ K).card :=
      Finset.card_le_card fun v hv => Finset.mem_inter.2
        ⟨(Finset.mem_inter.1 hv).1, (Finset.mem_inter.1 (Finset.mem_inter.1 hv).2).2⟩
    have := three_le (P := E) (S₁ := E \ (F ∪ G ∪ K)) (S₂ := Y) (S₃ := X ∪ (E ∩ K))
      Finset.sdiff_subset Finset.inter_subset_left
      (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
      (Finset.disjoint_left.2 fun v h1 h2 => by
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h1
        exact h1.2.1.2 (Finset.mem_inter.1 h2).2)
      (Finset.disjoint_left.2 fun v h1 h2 => by
        rcases Finset.mem_union.1 h1 with h | h <;> rcases Finset.mem_union.1 h2 with h' | h'
        · simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h
          exact h.2.1.1 (Finset.mem_inter.1 h').2
        · simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h
          exact h.2.2 (Finset.mem_inter.1 h').2
        · exact Finset.disjoint_left.1 dXY h' h
        · exact nKY v (Finset.mem_inter.1 h').2 h)
    omega
  have bW : (G \ (E ∪ F ∪ K)).card + (G ∩ K).card + Y.card + Z.card ≤ k + (Z ∩ K).card := by
    have hA := Finset.card_union_add_card_inter Z (G ∩ K)
    have hZK : (Z ∩ (G ∩ K)).card ≤ (Z ∩ K).card :=
      Finset.card_le_card fun v hv => Finset.mem_inter.2
        ⟨(Finset.mem_inter.1 hv).1, (Finset.mem_inter.1 (Finset.mem_inter.1 hv).2).2⟩
    have := three_le (P := G) (S₁ := G \ (E ∪ F ∪ K)) (S₂ := Y) (S₃ := Z ∪ (G ∩ K))
      Finset.sdiff_subset Finset.inter_subset_right
      (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_left)
      (Finset.disjoint_left.2 fun v h1 h2 => by
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h1
        exact h1.2.1.1 (Finset.mem_inter.1 h2).1)
      (Finset.disjoint_left.2 fun v h1 h2 => by
        rcases Finset.mem_union.1 h1 with h | h <;> rcases Finset.mem_union.1 h2 with h' | h'
        · simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h
          exact h.2.1.2 (Finset.mem_inter.1 h').1
        · simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h
          exact h.2.2 (Finset.mem_inter.1 h').2
        · exact Finset.disjoint_left.1 dYZ h h'
        · exact nKY v (Finset.mem_inter.1 h').2 h)
    omega
  -- distribute the private parts
  set Dist := (E \ (F ∪ G ∪ K)) ∪ (G \ (E ∪ F ∪ K)) with hDist
  have cDist : Dist.card ≤ (E \ (F ∪ G ∪ K)).card + (G \ (E ∪ F ∪ K)).card :=
    Finset.card_union_le _ _
  have n1 : (X ∪ (G ∩ K)).card ≤ X.card + (G ∩ K).card := Finset.card_union_le _ _
  have n2 : (Z ∪ (E ∩ K)).card ≤ Z.card + (E ∩ K).card := Finset.card_union_le _ _
  have n3 : (Y ∪ (F ∩ K)).card ≤ Y.card + (F ∩ K).card := Finset.card_union_le _ _
  have tot : X.card + (G ∩ K).card + (Z.card + (E ∩ K).card) + (Y.card + (F ∩ K).card)
      + Dist.card ≤ 3 * T := by
    clear * - cDist bD bW bPR bF cR₀ hΔ1 hΔ2 h7 h8; omega
  have t1 : X.card + (G ∩ K).card ≤ T := by clear * - lG h4; omega
  have t2 : Z.card + (E ∩ K).card ≤ T := by clear * - lE h5; omega
  have t3 : Y.card + (F ∩ K).card ≤ T := by clear * - bF cR₀ h6 hTk; omega
  obtain ⟨d₁, hd11, hd12, hd1⟩ : ∃ d₁, d₁ ≤ Dist.card ∧ X.card + (G ∩ K).card + d₁ ≤ T ∧
      (d₁ = Dist.card ∨ X.card + (G ∩ K).card + d₁ = T) :=
    ⟨min Dist.card (T - (X.card + (G ∩ K).card)), min_le_left _ _, by omega, by
      rcases min_choice Dist.card (T - (X.card + (G ∩ K).card)) with h | h <;> [left; right]
        <;> omega⟩
  obtain ⟨d₂, hd21, hd22, hd2⟩ : ∃ d₂, d₁ + d₂ ≤ Dist.card ∧ Z.card + (E ∩ K).card + d₂ ≤ T ∧
      (d₁ + d₂ = Dist.card ∨ Z.card + (E ∩ K).card + d₂ = T) :=
    ⟨min (Dist.card - d₁) (T - (Z.card + (E ∩ K).card)), by omega, by omega, by
      rcases min_choice (Dist.card - d₁) (T - (Z.card + (E ∩ K).card)) with h | h
        <;> [left; right] <;> omega⟩
  obtain ⟨D₁, D₂, D₃, -, -, -, covD, cD₁, cD₂, cD₃⟩ :=
    split_three Dist d₁ d₂ (Dist.card - d₁ - d₂) (by omega)
  have inDist : ∀ v, v ∈ Dist → v ∈ X ∪ (G ∩ K) ∪ D₁ ∨ v ∈ Z ∪ (E ∩ K) ∪ D₂ ∨
      v ∈ Y ∪ (F ∩ K) ∪ D₃ := fun v hv => by
    rcases covD v hv with h | h | h
    exacts [Or.inl (m3_3 h), Or.inr (Or.inl (m3_3 h)), Or.inr (Or.inr (m3_3 h))]
  -- membership in the three requests
  have allP : ∀ v, v ∈ E → v ∈ F → v ∈ K →
      v ∈ X ∪ (G ∩ K) ∪ D₁ ∧ v ∈ Z ∪ (E ∩ K) ∪ D₂ ∧ v ∈ Y ∪ (F ∩ K) ∪ D₃ :=
    fun v a b c => ⟨m3_1 (Finset.mem_inter.2 ⟨a, b⟩), m3_2 (Finset.mem_inter.2 ⟨a, c⟩),
      m3_2 (Finset.mem_inter.2 ⟨b, c⟩)⟩
  have allR : ∀ v, v ∈ F → v ∈ G → v ∈ K →
      v ∈ X ∪ (G ∩ K) ∪ D₁ ∧ v ∈ Z ∪ (E ∩ K) ∪ D₂ ∧ v ∈ Y ∪ (F ∩ K) ∪ D₃ :=
    fun v a b c => ⟨m3_2 (Finset.mem_inter.2 ⟨b, c⟩), m3_1 (Finset.mem_inter.2 ⟨a, b⟩),
      m3_2 (Finset.mem_inter.2 ⟨a, c⟩)⟩
  have someE : ∀ v, v ∈ E → v ∈ X ∪ (G ∩ K) ∪ D₁ ∨ v ∈ Z ∪ (E ∩ K) ∪ D₂ ∨
      v ∈ Y ∪ (F ∩ K) ∪ D₃ := fun v hv => by
    by_cases hF' : v ∈ F
    · exact Or.inl (m3_1 (Finset.mem_inter.2 ⟨hv, hF'⟩))
    by_cases hG' : v ∈ G
    · exact Or.inr (Or.inr (m3_1 (Finset.mem_inter.2 ⟨hv, hG'⟩)))
    by_cases hK' : v ∈ K
    · exact Or.inr (Or.inl (m3_2 (Finset.mem_inter.2 ⟨hv, hK'⟩)))
    exact inDist v (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hv, by
      simp only [Finset.mem_union, not_or]; exact ⟨⟨hF', hG'⟩, hK'⟩⟩))
  have someG : ∀ v, v ∈ G → v ∈ X ∪ (G ∩ K) ∪ D₁ ∨ v ∈ Z ∪ (E ∩ K) ∪ D₂ ∨
      v ∈ Y ∪ (F ∩ K) ∪ D₃ := fun v hv => by
    by_cases hE' : v ∈ E
    · exact Or.inr (Or.inr (m3_1 (Finset.mem_inter.2 ⟨hE', hv⟩)))
    by_cases hF' : v ∈ F
    · exact Or.inr (Or.inl (m3_1 (Finset.mem_inter.2 ⟨hF', hv⟩)))
    by_cases hK' : v ∈ K
    · exact Or.inl (m3_2 (Finset.mem_inter.2 ⟨hv, hK'⟩))
    exact inDist v (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hv, by
      simp only [Finset.mem_union, not_or]; exact ⟨⟨hE', hF'⟩, hK'⟩⟩))
  have pick : ∀ u v : α, (u ∈ X ∪ (G ∩ K) ∪ D₁ ∧ u ∈ Z ∪ (E ∩ K) ∪ D₂ ∧ u ∈ Y ∪ (F ∩ K) ∪ D₃) →
      (v ∈ X ∪ (G ∩ K) ∪ D₁ ∨ v ∈ Z ∪ (E ∩ K) ∪ D₂ ∨ v ∈ Y ∪ (F ∩ K) ∪ D₃) →
      (u ∈ X ∪ (G ∩ K) ∪ D₁ ∧ v ∈ X ∪ (G ∩ K) ∪ D₁) ∨
      (u ∈ Z ∪ (E ∩ K) ∪ D₂ ∧ v ∈ Z ∪ (E ∩ K) ∪ D₂) ∨
      (u ∈ Y ∪ (F ∩ K) ∪ D₃ ∧ v ∈ Y ∪ (F ∩ K) ∪ D₃) := by
    intro u v hu hv
    rcases hv with h | h | h
    exacts [Or.inl ⟨hu.1, h⟩, Or.inr (Or.inl ⟨hu.2.1, h⟩), Or.inr (Or.inr ⟨hu.2.2, h⟩)]
  refine four_closes hprop hτ hE hF hG hK hgood (X ∪ (G ∩ K) ∪ D₁) (Z ∪ (E ∩ K) ∪ D₂)
    (Y ∪ (F ∩ K) ∪ D₃)
    ((Finset.card_union_le _ _).trans (by clear * - n1 cD₁ hd12; omega))
    ((Finset.card_union_le _ _).trans (by clear * - n2 cD₂ hd22; omega))
    ((Finset.card_union_le _ _).trans
      (by clear * - n3 cD₃ tot hd11 hd1 hd21 hd2 hd12 hd22 t3; omega)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro p q pE pF pK qG; exact pick p q (allP p pE pF pK) (someG q qG)
  · intro p q pE pG pK _; exact (nKY p pK (Finset.mem_inter.2 ⟨pE, pG⟩)).elim
  · intro p q pF pG pK qE; exact pick p q (allR p pF pG pK) (someE q qE)
  · intro p q pE pF _ qG qK _ _
    exact Or.inl ⟨m3_1 (Finset.mem_inter.2 ⟨pE, pF⟩), m3_2 (Finset.mem_inter.2 ⟨qG, qK⟩)⟩
  · intro p q pE pG _ qF qK _ _
    exact Or.inr (Or.inr ⟨m3_1 (Finset.mem_inter.2 ⟨pE, pG⟩),
      m3_2 (Finset.mem_inter.2 ⟨qF, qK⟩)⟩)
  · intro p q pF pG _ qE qK _ _
    exact Or.inr (Or.inl ⟨m3_1 (Finset.mem_inter.2 ⟨pF, pG⟩),
      m3_2 (Finset.mem_inter.2 ⟨qE, qK⟩)⟩)

end Erdos644
