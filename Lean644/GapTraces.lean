import Lean644.SplitA

/-!
# Intersection gaps and Lemma 4.4 (two forced traces), manuscript §2.4 and Appendix A
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- `Gap(ℓ,u)` (manuscript §2.4): no two *distinct* edges of `H` meet in a number of points in
`{ℓ+1, …, u}`; equivalently `|A ∩ B| ≤ u → |A ∩ B| ≤ ℓ` for distinct edges `A, B`. -/
def IntersectionGap (H : Finset (Finset α)) (l u : ℕ) : Prop :=
  ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ u → (A ∩ B).card ≤ l

/-- Applying the gap to a trace bounded by `u < k` (the edges are then automatically distinct). -/
theorem IntersectionGap.apply {H : Finset (Finset α)} {l u k : ℕ} (hgap : IntersectionGap H l u)
    (hunif : IsUniform H k) (hu : u < k) {A B : Finset α} (hA : A ∈ H) (hB : B ∈ H)
    (h : (A ∩ B).card ≤ u) : (A ∩ B).card ≤ l := by
  refine hgap A hA B hB ?_ h
  rintro rfl
  rw [Finset.inter_self, hunif A hA] at h
  omega

/-- **Lemma 4.4 (two forced traces).** Assume `Gap(ℓ,u)` with `u < k`, and put
`p = (k-x-y-u)₊`, `t = (k-x-z-u)₊` (truncated subtraction in `ℕ`). A good triple closes at
budget `T ≤ k` if `S+p+t ≤ T`, `k+3x+p+t ≤ 3T` and `y+z+2ℓ ≤ T`. -/
theorem gapTraces_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k l u : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k) (hu : u < k)
    (hgap : IntersectionGap H l u)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (c1 : (E ∩ F).card + (E ∩ G).card + (F ∩ G).card + (k - (E ∩ F).card - (E ∩ G).card - u)
      + (k - (E ∩ F).card - (F ∩ G).card - u) ≤ T)
    (c2 : k + 3 * (E ∩ F).card + (k - (E ∩ F).card - (E ∩ G).card - u)
      + (k - (E ∩ F).card - (F ∩ G).card - u) ≤ 3 * T)
    (c3 : (E ∩ G).card + (F ∩ G).card + 2 * l ≤ T) : False := by
  have gF : IsGoodTriple F E G := by
    unfold IsGoodTriple at *; rw [Finset.inter_comm F E]; exact hgood
  have gG : IsGoodTriple G E F := by
    unfold IsGoodTriple at *; rw [← hgood]; ext v; simp only [Finset.mem_inter]; tauto
  have cE := card_private hgood
  have cF := card_private gF
  have cG := card_private gG
  rw [hunif E hE] at cE
  rw [hunif F hF, Finset.inter_comm F E] at cF
  rw [hunif G hG, Finset.inter_comm G E, Finset.inter_comm G F] at cG
  have g0 : ∀ v, v ∈ E → v ∈ F → v ∈ G → False := fun v h1 h2 h3 => by
    have : v ∈ E ∩ F ∩ G := by simp [h1, h2, h3]
    unfold IsGoodTriple at hgood; rw [hgood] at this; simp at this
  set X := E ∩ F with hXdef
  set Y := E ∩ G with hYdef
  set Z := F ∩ G with hZdef
  set p := k - X.card - Y.card - u
  set t := k - X.card - Z.card - u
  -- the first request
  obtain ⟨WE, hWE, cWE⟩ := Finset.exists_subset_card_eq
    (show p ≤ (E \ (F ∪ G)).card by omega)
  obtain ⟨WF, hWF, cWF⟩ := Finset.exists_subset_card_eq
    (show t ≤ (F \ (E ∪ G)).card by omega)
  obtain ⟨WG, hWG, cWG⟩ := Finset.exists_subset_card_eq
    (show T - (X.card + Y.card + Z.card) - p - t ≤ (G \ (E ∪ F)).card by omega)
  have hD : (X ∪ Y ∪ Z ∪ (WE ∪ WF ∪ WG)).card ≤ T :=
    (card_union4_le _ _ _ _).trans (by have := card_union3_le WE WF WG; omega)
  obtain ⟨K, hK, hKD⟩ := exists_response hτ hD
  have nK : ∀ v, v ∈ K → (v ∈ E → v ∈ F → False) ∧ (v ∈ E → v ∈ G → False) ∧
      (v ∈ F → v ∈ G → False) ∧ v ∉ WE ∧ v ∉ WF ∧ v ∉ WG := fun v hv => by
    have h := Finset.disjoint_left.1 hKD hv
    simp only [X, Y, Z, Finset.mem_union, Finset.mem_inter, not_or, not_and] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩
  have kX : Disjoint K X := Finset.disjoint_left.2 fun v hv h =>
    (nK v hv).1 (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2
  have kY : Disjoint K Y := Finset.disjoint_left.2 fun v hv h =>
    (nK v hv).2.1 (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2
  have kZ : Disjoint K Z := Finset.disjoint_left.2 fun v hv h =>
    (nK v hv).2.2.1 (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2
  -- trace bounds: for an edge P with two pair cells C₁ C₂ and a requested private piece W
  have trace : ∀ P C₁ C₂ W : Finset α, P ∈ H → C₁ ⊆ P → C₂ ⊆ P → W ⊆ P → Disjoint C₁ C₂ →
      Disjoint (C₁ ∪ C₂) W → Disjoint K (C₁ ∪ C₂ ∪ W) →
      (P ∩ K).card + C₁.card + C₂.card + W.card ≤ k := by
    intro P C₁ C₂ W hP h1 h2 h3 d12 d3 dK
    have dPK : Disjoint (P ∩ K) (C₁ ∪ C₂ ∪ W) :=
      Finset.disjoint_left.2 fun v hv h => Finset.disjoint_left.1 dK (Finset.mem_inter.1 hv).2 h
    have sub : (P ∩ K) ∪ (C₁ ∪ C₂ ∪ W) ⊆ P := by
      intro v hv; simp only [Finset.mem_union] at hv
      rcases hv with h | (h | h) | h
      · exact (Finset.mem_inter.1 h).1
      · exact h1 h
      · exact h2 h
      · exact h3 h
    have := Finset.card_le_card sub
    rw [card_union_disj dPK, card_union_disj d3, card_union_disj d12, hunif P hP] at this
    omega
  have dKall : ∀ S' : Finset α, S' ⊆ X ∪ Y ∪ Z ∪ (WE ∪ WF ∪ WG) → Disjoint K S' :=
    fun S' h => hKD.mono_right h
  have dXY : Disjoint X Y := Finset.disjoint_left.2 fun v h1 h2 => by
    simp only [X, Y, Finset.mem_inter] at h1 h2; exact g0 v h1.1 h1.2 h2.2
  have dXZ : Disjoint X Z := Finset.disjoint_left.2 fun v h1 h2 => by
    simp only [X, Z, Finset.mem_inter] at h1 h2; exact g0 v h1.1 h1.2 h2.2
  have dYZ : Disjoint Y Z := Finset.disjoint_left.2 fun v h1 h2 => by
    simp only [Y, Z, Finset.mem_inter] at h1 h2; exact g0 v h1.1 h2.1 h1.2
  have tE := trace E X Y WE hE Finset.inter_subset_left Finset.inter_subset_left
    (fun v h => (Finset.mem_sdiff.1 (hWE h)).1) dXY
    (Finset.disjoint_left.2 fun v h1 h2 => by
      have := Finset.mem_sdiff.1 (hWE h2)
      simp only [X, Y, Finset.mem_union, Finset.mem_inter] at h1 this; tauto)
    (dKall _ (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto))
  have tF := trace F X Z WF hF Finset.inter_subset_right Finset.inter_subset_left
    (fun v h => (Finset.mem_sdiff.1 (hWF h)).1) dXZ
    (Finset.disjoint_left.2 fun v h1 h2 => by
      have := Finset.mem_sdiff.1 (hWF h2)
      simp only [X, Z, Finset.mem_union, Finset.mem_inter] at h1 this; tauto)
    (dKall _ (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto))
  have tG := trace G Y Z WG hG Finset.inter_subset_right Finset.inter_subset_right
    (fun v h => (Finset.mem_sdiff.1 (hWG h)).1) dYZ
    (Finset.disjoint_left.2 fun v h1 h2 => by
      have := Finset.mem_sdiff.1 (hWG h2)
      simp only [Y, Z, Finset.mem_union, Finset.mem_inter] at h1 this; tauto)
    (dKall _ (by intro v hv; simp only [Finset.mem_union] at hv ⊢; tauto))
  -- the gap forces the traces on E and F down to ℓ
  have gE : (E ∩ K).card ≤ l := hgap.apply hunif hu hE hK (by omega)
  have gF' : (F ∩ K).card ≤ l := hgap.apply hunif hu hF hK (by omega)
  -- split B = G ∩ K into two nearly equal halves
  set B := G ∩ K
  obtain ⟨B₁, B₂, -, -, covB, cB₁, cB₂⟩ := split_two B (B.card / 2) (B.card - B.card / 2) (by omega)
  refine no_core_closes hprop hτ hE hF hG hK hgood kX kY kZ (X ∪ B₁) (X ∪ B₂)
    (Y ∪ Z ∪ (F ∩ K) ∪ (E ∩ K)) ((Finset.card_union_le _ _).trans (by omega))
    ((Finset.card_union_le _ _).trans (by omega)) ((card_union4_le _ _ _ _).trans (by omega))
    ?_ ?_ ?_
  · intro u' v uE uF vG vK
    have uX : u' ∈ X := by simp [X, uE, uF]
    rcases covB v (by simp [B, vG, vK]) with h | h
    · exact Or.inl ⟨by simp [uX], by simp [h]⟩
    · exact Or.inr (Or.inl ⟨by simp [uX], by simp [h]⟩)
  · intro u' v uE uG vF vK
    have uY : u' ∈ Y := by simp [Y, uE, uG]
    exact Or.inr (Or.inr ⟨by simp [uY], by simp [vF, vK]⟩)
  · intro u' v uF uG vE vK
    have uZ : u' ∈ Z := by simp [Z, uF, uG]
    exact Or.inr (Or.inr ⟨by simp [uZ], by simp [vE, vK]⟩)

end Erdos644
