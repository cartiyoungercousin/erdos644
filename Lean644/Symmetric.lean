import Lean644.HallClose

/-!
# Symmetric allocation (manuscript Lemmas 3.3 and 3.4)

Cells `X = E ∩ F`, `Y = E ∩ G`, `Z = F ∩ G` of sizes `m, y, z`, opposite private parts
`P_X = G \ (E ∪ F)`, `P_Y = F \ (E ∪ G)`, `P_Z = E \ (F ∪ G)`. Split `X = X₁ ⊔ X₂`,
`Y = Y₁ ⊔ Y₂`, `Z = Z₁ ⊔ Z₂` and request
```
R₀ = X₁ ∪ Y₁ ∪ Z₁,  R_X = X ∪ P_X ∪ Y₂ ∪ Z₂,  R_Y = Y ∪ P_Y ∪ X₂ ∪ Z₂,  R_Z = Z ∪ P_Z ∪ X₂ ∪ Y₂.
```
The manuscript's Lemma 3.3 (boxed triangle) is replaced by an explicit witness for the split
sizes (`symmetric_sizes`), validated in `compute/symmetric_formula_check.py`.
-/

namespace Erdos644

/-- Integer core of Lemma 3.4 (via Lemma 3.3): split sizes `a₁ ≤ m, a₂ ≤ y, a₃ ≤ z`. -/
theorem symmetric_sizes (k T m y z : ℕ) (hTk : T ≤ k) (hmy : m ≥ y) (hyz : y ≥ z)
    (c1 : T + y + z ≥ k + m) (c2 : 2 * T ≥ k + m) (c3 : 3 * T + z ≥ 2 * k + m + y)
    (c4 : 5 * T ≥ 3 * k + (m + y + z)) :
    ∃ a₁ a₂ a₃ : ℕ, a₁ ≤ m ∧ a₂ ≤ y ∧ a₃ ≤ z ∧ a₂ + a₃ + T ≥ k + m ∧ a₁ + a₃ + T ≥ k + y ∧
      a₁ + a₂ + T ≥ k + z ∧ a₁ + a₂ + a₃ ≤ T := by
  obtain ⟨t, ht1, ht2, ht⟩ : ∃ t, t ≤ T ∧ t ≤ m + y + z ∧ (t = T ∨ t = m + y + z) :=
    ⟨min T (m + y + z), min_le_left _ _, min_le_right _ _, min_choice _ _⟩
  obtain ⟨a₁, h11, h12, h1⟩ : ∃ a₁, a₁ ≤ m ∧ a₁ + (k + m - T) ≤ t ∧ (a₁ = m ∨ a₁ + (k + m - T) = t) :=
    ⟨min m (t - (k + m - T)), min_le_left _ _, by omega, by
      rcases min_choice m (t - (k + m - T)) with h | h <;> [left; right] <;> omega⟩
  obtain ⟨a₂, h21, h22, h23, h2⟩ : ∃ a₂, a₂ ≤ y ∧ a₂ + (k + y - T) ≤ t ∧ a₂ + a₁ ≤ t ∧
      (a₂ = y ∨ a₂ + (k + y - T) = t ∨ a₂ + a₁ = t) :=
    ⟨min y (min (t - (k + y - T)) (t - a₁)), by omega, by omega, by omega, by
      rcases min_choice y (min (t - (k + y - T)) (t - a₁)) with h | h
      · left; exact h
      · rcases min_choice (t - (k + y - T)) (t - a₁) with h' | h' <;> [right; right] <;> omega⟩
  refine ⟨a₁, a₂, t - a₁ - a₂, h11, h21, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

variable {α : Type*} [DecidableEq α]

/-- **Symmetric allocation** (manuscript Lemma 3.4), with `X = E ∩ F` the largest cell. -/
theorem symmetric_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (hmy : (E ∩ F).card ≥ (E ∩ G).card) (hyz : (E ∩ G).card ≥ (F ∩ G).card)
    (c1 : T + (E ∩ G).card + (F ∩ G).card ≥ k + (E ∩ F).card)
    (c2 : 2 * T ≥ k + (E ∩ F).card)
    (c3 : 3 * T + (F ∩ G).card ≥ 2 * k + (E ∩ F).card + (E ∩ G).card)
    (c4 : 5 * T ≥ 3 * k + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card)) : False := by
  have gF : IsGoodTriple F E G := by
    unfold IsGoodTriple at *; rw [Finset.inter_comm F E]; exact hgood
  have gG : IsGoodTriple G E F := by
    unfold IsGoodTriple at *; rw [← hgood]; ext x; simp only [Finset.mem_inter]; tauto
  have cE := card_private hgood
  have cF := card_private gF
  have cG := card_private gG
  rw [hunif E hE] at cE; rw [hunif F hF] at cF; rw [hunif G hG] at cG
  rw [Finset.inter_comm F E] at cF
  rw [Finset.inter_comm G E, Finset.inter_comm G F] at cG
  set X := E ∩ F
  set Y := E ∩ G
  set Z := F ∩ G
  set PZ := E \ (F ∪ G)
  set PY := F \ (E ∪ G)
  set PX := G \ (E ∪ F)
  obtain ⟨a₁, a₂, a₃, ha1, ha2, ha3, s1, s2, s3, s0⟩ :=
    symmetric_sizes k T X.card Y.card Z.card hTk hmy hyz c1 c2 c3 c4
  obtain ⟨X₁, X₂, hX₁, hX₂, covX, cX₁, cX₂⟩ := split_two X a₁ (X.card - a₁) (by omega)
  obtain ⟨Y₁, Y₂, hY₁, hY₂, covY, cY₁, cY₂⟩ := split_two Y a₂ (Y.card - a₂) (by omega)
  obtain ⟨Z₁, Z₂, hZ₁, hZ₂, covZ, cZ₁, cZ₂⟩ := split_two Z a₃ (Z.card - a₃) (by omega)
  have u4 : ∀ A B C D : Finset α, (A ∪ B ∪ C ∪ D).card ≤ A.card + B.card + C.card + D.card :=
    fun A B C D => by
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) _
      exact Nat.add_le_add_right (Finset.card_union_le _ _) _
  have u3 : ∀ A B C : Finset α, (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := fun A B C =>
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  refine closes_of_four_requests hprop hτ hE hF hG (X₁ ∪ Y₁ ∪ Z₁) (X ∪ PX ∪ Y₂ ∪ Z₂)
    (Y ∪ PY ∪ X₂ ∪ Z₂) (Z ∪ PZ ∪ X₂ ∪ Y₂) ?_ ?_ ?_ ?_ ?_
  · exact (u3 _ _ _).trans (by omega)
  · exact (u4 _ _ _ _).trans (by omega)
  · exact (u4 _ _ _ _).trans (by omega)
  · exact (u4 _ _ _ _).trans (by omega)
  · intro x y hxE hxF hxG
    let P : α → α → Prop := fun u v =>
      (u ∈ X₁ ∪ Y₁ ∪ Z₁ ∧ v ∈ X₁ ∪ Y₁ ∪ Z₁) ∨ (u ∈ X ∪ PX ∪ Y₂ ∪ Z₂ ∧ v ∈ X ∪ PX ∪ Y₂ ∪ Z₂) ∨
      (u ∈ Y ∪ PY ∪ X₂ ∪ Z₂ ∧ v ∈ Y ∪ PY ∪ X₂ ∪ Z₂) ∨ (u ∈ Z ∪ PZ ∪ X₂ ∪ Y₂ ∧ v ∈ Z ∪ PZ ∪ X₂ ∪ Y₂)
    have symm : ∀ u v, P u v → P v u := by
      intro u v h
      rcases h with h | h | h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
    -- pairs of points in two different cells
    have XY : ∀ u v, u ∈ X → v ∈ Y → P u v := by
      intro u v hu hv
      rcases covX u hu with h1 | h1 <;> rcases covY v hv with h2 | h2
      · exact Or.inl ⟨by simp [h1], by simp [h2]⟩
      · exact Or.inr (Or.inl ⟨by simp [hu], by simp [h2]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by simp [h1], by simp [hv]⟩))
      · exact Or.inr (Or.inl ⟨by simp [hu], by simp [h2]⟩)
    have XZ : ∀ u v, u ∈ X → v ∈ Z → P u v := by
      intro u v hu hv
      rcases covX u hu with h1 | h1 <;> rcases covZ v hv with h2 | h2
      · exact Or.inl ⟨by simp [h1], by simp [h2]⟩
      · exact Or.inr (Or.inl ⟨by simp [hu], by simp [h2]⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [h1], by simp [hv]⟩))
      · exact Or.inr (Or.inl ⟨by simp [hu], by simp [h2]⟩)
    have YZ : ∀ u v, u ∈ Y → v ∈ Z → P u v := by
      intro u v hu hv
      rcases covY u hu with h1 | h1 <;> rcases covZ v hv with h2 | h2
      · exact Or.inl ⟨by simp [h1], by simp [h2]⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by simp [hu], by simp [h2]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [h1], by simp [hv]⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨by simp [hu], by simp [h2]⟩))
    -- the three candidate-pair shapes of a good triple
    have caseX : ∀ u v, u ∈ E → u ∈ F → v ∈ G → P u v := by
      intro u v uE uF vG
      have uX : u ∈ X := Finset.mem_inter.2 ⟨uE, uF⟩
      by_cases vE : v ∈ E
      · exact XY u v uX (Finset.mem_inter.2 ⟨vE, vG⟩)
      by_cases vF : v ∈ F
      · exact XZ u v uX (Finset.mem_inter.2 ⟨vF, vG⟩)
      have vP : v ∈ PX := by simp [PX, vG, vE, vF]
      exact Or.inr (Or.inl ⟨by simp [uX], by simp [vP]⟩)
    have caseY : ∀ u v, u ∈ E → u ∈ G → v ∈ F → P u v := by
      intro u v uE uG vF
      have uY : u ∈ Y := Finset.mem_inter.2 ⟨uE, uG⟩
      by_cases vE : v ∈ E
      · exact symm _ _ (XY v u (Finset.mem_inter.2 ⟨vE, vF⟩) uY)
      by_cases vG : v ∈ G
      · exact YZ u v uY (Finset.mem_inter.2 ⟨vF, vG⟩)
      have vP : v ∈ PY := by simp [PY, vF, vE, vG]
      exact Or.inr (Or.inr (Or.inl ⟨by simp [uY], by simp [vP]⟩))
    have caseZ : ∀ u v, u ∈ F → u ∈ G → v ∈ E → P u v := by
      intro u v uF uG vE
      have uZ : u ∈ Z := Finset.mem_inter.2 ⟨uF, uG⟩
      by_cases vF : v ∈ F
      · exact symm _ _ (XZ v u (Finset.mem_inter.2 ⟨vE, vF⟩) uZ)
      by_cases vG : v ∈ G
      · exact symm _ _ (YZ v u (Finset.mem_inter.2 ⟨vE, vG⟩) uZ)
      have vP : v ∈ PZ := by simp [PZ, vE, vF, vG]
      exact Or.inr (Or.inr (Or.inr ⟨by simp [uZ], by simp [vP]⟩))
    rcases triple_candidate hgood hxE hxF hxG with
      ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · exact caseX x y a1 a2 a3
    · exact caseY x y a1 a2 a3
    · exact caseZ x y a1 a2 a3
    · exact symm _ _ (caseX y x a1 a2 a3)
    · exact symm _ _ (caseY y x a1 a2 a3)
    · exact symm _ _ (caseZ y x a1 a2 a3)

end Erdos644
