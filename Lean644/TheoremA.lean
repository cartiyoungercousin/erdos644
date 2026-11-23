import Lean644.HallClose

/-!
# Theorem A (one-anchor Fano template)

Source: `notes/ROADMAP_3_4.md` §3(a) (research agent, 2026-11-23); hand-checked.

Let every edge of `H` lie in a ground set `V` with `|V| = n`, and `A ∈ H`. Split `A` into four
quarters `a₁..a₄` and `V ∖ A` into three thirds `B₁, B₂, B₃`. The six requests
`B₁∪a₁∪a₂, B₁∪a₃∪a₄, B₂∪a₁∪a₃, B₂∪a₂∪a₄, B₃∪a₁∪a₄, B₃∪a₂∪a₃` (third `j` paired with the
`j`-th perfect matching of the quarters) together with `A` force a bad subfamily of 7 edges.
Hence `τ(H) ≤ ⌈(n-k)/3⌉ + 2⌈k/4⌉`; this is tight for the complete family `K_{7m-1}^{(4m)}` and
for the FKW parity family.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- Request-cover principle relative to a ground set `V` containing every edge: only pairs of
points of `V` need to be covered. -/
theorem request_cover_V {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2)
    (V : Finset α) (hV : ∀ A ∈ H, A ⊆ V) {E D : Finset (Finset α)} (hEH : E ⊆ H)
    (hEne : E.Nonempty) (hcard : E.card + D.card ≤ 7) (hresp : ∀ d ∈ D, ∃ B ∈ H, Disjoint B d)
    (hcov : ∀ x ∈ V, ∀ y ∈ V, (∀ A ∈ E, x ∈ A ∨ y ∈ A) → ∃ d ∈ D, x ∈ d ∧ y ∈ d) : False := by
  classical
  choose! resp hrespH hrespD using hresp
  set G := E ∪ D.image resp
  have hGH : G ⊆ H := by
    intro B hB
    rcases Finset.mem_union.1 hB with hB | hB
    · exact hEH hB
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hB
      exact hrespH d hd
  have hGcard : G.card ≤ 7 :=
    (Finset.card_union_le _ _).trans ((Nat.add_le_add_left Finset.card_image_le _).trans hcard)
  have hGne : G.Nonempty := hEne.mono Finset.subset_union_left
  obtain ⟨x, y, hxy⟩ := (coverableBy_two_iff hGne).1 (hprop G hGH hGcard)
  obtain ⟨A₀, hA₀⟩ := hEne
  have inV : ∀ B ∈ G, ∀ v, v ∈ B → v ∈ V := fun B hB v hv => hV B (hGH hB) hv
  -- a single point lying in every member of G is impossible
  have single : ∀ w, (∀ B ∈ G, w ∈ B) → False := by
    intro w hw
    have wV : w ∈ V := inV A₀ (Finset.mem_union_left _ hA₀) w (hw A₀ (Finset.mem_union_left _ hA₀))
    obtain ⟨d, hd, hwd, -⟩ := hcov w wV w wV (fun A hA => Or.inl (hw A (Finset.mem_union_left _ hA)))
    exact Finset.disjoint_left.1 (hrespD d hd)
      (hw _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hd))) hwd
  by_cases hx : x ∈ V
  · by_cases hy : y ∈ V
    · obtain ⟨d, hd, hxd, hyd⟩ := hcov x hx y hy (fun A hA => hxy A (Finset.mem_union_left _ hA))
      have hB : resp d ∈ G := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hd)
      rcases hxy (resp d) hB with h | h
      · exact Finset.disjoint_left.1 (hrespD d hd) h hxd
      · exact Finset.disjoint_left.1 (hrespD d hd) h hyd
    · exact single x fun B hB => (hxy B hB).resolve_right fun h => hy (inV B hB y h)
  · exact single y fun B hB => (hxy B hB).resolve_left fun h => hx (inV B hB x h)

/-- Split a finite set into four parts of prescribed sizes. -/
theorem split_four (W : Finset α) (a b c d : ℕ) (h : W.card = a + b + c + d) :
    ∃ P₁ P₂ P₃ P₄ : Finset α, (∀ x ∈ W, x ∈ P₁ ∨ x ∈ P₂ ∨ x ∈ P₃ ∨ x ∈ P₄) ∧
      P₁.card = a ∧ P₂.card = b ∧ P₃.card = c ∧ P₄.card = d := by
  obtain ⟨U, U', -, -, cov, cU, cU'⟩ := split_two W (a + b) (c + d) (by omega)
  obtain ⟨P₁, P₂, -, -, cov1, c1, c2⟩ := split_two U a b cU
  obtain ⟨P₃, P₄, -, -, cov2, c3, c4⟩ := split_two U' c d cU'
  refine ⟨P₁, P₂, P₃, P₄, fun x hx => ?_, c1, c2, c3, c4⟩
  rcases cov x hx with h | h
  · rcases cov1 x h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases cov2 x h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

/-- **Theorem A.** If every edge lies in `V` and `⌈(|V|-k)/3⌉ + 2⌈k/4⌉ ≤ T`, then a nonempty
`k`-uniform family with property (7,2) has `τ ≤ T`. -/
theorem theoremA_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (V : Finset α) (hV : ∀ A ∈ H, A ⊆ V)
    {A : Finset α} (hA : A ∈ H) (hT : (V.card - k + 2) / 3 + 2 * ((k + 3) / 4) ≤ T) : False := by
  have hAk := hunif A hA
  have hAV := hV A hA
  have hm : (V \ A).card = V.card - k := by rw [Finset.card_sdiff_of_subset hAV, hAk]
  obtain ⟨a₁, a₂, a₃, a₄, covA, ca₁, ca₂, ca₃, ca₄⟩ :=
    split_four A (k / 4) ((k + 1) / 4) ((k + 2) / 4) ((k + 3) / 4) (by omega)
  obtain ⟨B₁, B₂, B₃, -, -, -, covB, cB₁, cB₂, cB₃⟩ :=
    split_three (V \ A) ((V.card - k) / 3) ((V.card - k + 1) / 3) ((V.card - k + 2) / 3) (by omega)
  have sz : ∀ (B P Q : Finset α), B.card ≤ (V.card - k + 2) / 3 → P.card ≤ (k + 3) / 4 →
      Q.card ≤ (k + 3) / 4 → (B ∪ P ∪ Q).card ≤ T := fun B P Q h1 h2 h3 =>
    (Finset.card_union_le _ _).trans (by have := Finset.card_union_le B P; omega)
  have bB₁ : B₁.card ≤ (V.card - k + 2) / 3 := by omega
  have bB₂ : B₂.card ≤ (V.card - k + 2) / 3 := by omega
  have bB₃ : B₃.card ≤ (V.card - k + 2) / 3 := by omega
  have ba₁ : a₁.card ≤ (k + 3) / 4 := by omega
  have ba₂ : a₂.card ≤ (k + 3) / 4 := by omega
  have ba₃ : a₃.card ≤ (k + 3) / 4 := by omega
  have ba₄ : a₄.card ≤ (k + 3) / 4 := by omega
  set R₁ := B₁ ∪ a₁ ∪ a₂
  set R₂ := B₁ ∪ a₃ ∪ a₄
  set R₃ := B₂ ∪ a₁ ∪ a₃
  set R₄ := B₂ ∪ a₂ ∪ a₄
  set R₅ := B₃ ∪ a₁ ∪ a₄
  set R₆ := B₃ ∪ a₂ ∪ a₃
  set D : Finset (Finset α) := {R₁, R₂, R₃, R₄, R₅, R₆}
  have hD : D.card ≤ 6 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  -- every request has size ≤ T, hence a response
  have hresp : ∀ d ∈ D, ∃ B ∈ H, Disjoint B d := by
    intro d hd
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact exists_response hτ (sz _ _ _ bB₁ ba₁ ba₂)
    · exact exists_response hτ (sz _ _ _ bB₁ ba₃ ba₄)
    · exact exists_response hτ (sz _ _ _ bB₂ ba₁ ba₃)
    · exact exists_response hτ (sz _ _ _ bB₂ ba₂ ba₄)
    · exact exists_response hτ (sz _ _ _ bB₃ ba₁ ba₄)
    · exact exists_response hτ (sz _ _ _ bB₃ ba₂ ba₃)
  -- which request contains a given quarter/quarter or quarter/third pair
  have mem : ∀ (R : Finset α), R ∈ D → ∀ x y, x ∈ R → y ∈ R → ∃ d ∈ D, x ∈ d ∧ y ∈ d :=
    fun R hR x y hx hy => ⟨R, hR, hx, hy⟩
  have i1 : R₁ ∈ D := by simp [D]
  have i2 : R₂ ∈ D := by simp [D]
  have i3 : R₃ ∈ D := by simp [D]
  have i4 : R₄ ∈ D := by simp [D]
  have i5 : R₅ ∈ D := by simp [D]
  have i6 : R₆ ∈ D := by simp [D]
  -- x in A (some quarter), y anywhere in V
  have key : ∀ x y, x ∈ A → y ∈ V → ∃ d ∈ D, x ∈ d ∧ y ∈ d := by
    intro x y hx hy
    have hyq : y ∈ a₁ ∨ y ∈ a₂ ∨ y ∈ a₃ ∨ y ∈ a₄ ∨ y ∈ B₁ ∨ y ∈ B₂ ∨ y ∈ B₃ := by
      by_cases hyA : y ∈ A
      · rcases covA y hyA with h | h | h | h <;> simp [h]
      · rcases covB y (Finset.mem_sdiff.2 ⟨hy, hyA⟩) with h | h | h <;> simp [h]
    rcases covA x hx with p | p | p | p <;>
      rcases hyq with q | q | q | q | q | q | q
    -- x ∈ a₁
    · exact mem R₁ i1 x y (by simp [R₁, p]) (by simp [R₁, q])
    · exact mem R₁ i1 x y (by simp [R₁, p]) (by simp [R₁, q])
    · exact mem R₃ i3 x y (by simp [R₃, p]) (by simp [R₃, q])
    · exact mem R₅ i5 x y (by simp [R₅, p]) (by simp [R₅, q])
    · exact mem R₁ i1 x y (by simp [R₁, p]) (by simp [R₁, q])
    · exact mem R₃ i3 x y (by simp [R₃, p]) (by simp [R₃, q])
    · exact mem R₅ i5 x y (by simp [R₅, p]) (by simp [R₅, q])
    -- x ∈ a₂
    · exact mem R₁ i1 x y (by simp [R₁, p]) (by simp [R₁, q])
    · exact mem R₁ i1 x y (by simp [R₁, p]) (by simp [R₁, q])
    · exact mem R₆ i6 x y (by simp [R₆, p]) (by simp [R₆, q])
    · exact mem R₄ i4 x y (by simp [R₄, p]) (by simp [R₄, q])
    · exact mem R₁ i1 x y (by simp [R₁, p]) (by simp [R₁, q])
    · exact mem R₄ i4 x y (by simp [R₄, p]) (by simp [R₄, q])
    · exact mem R₆ i6 x y (by simp [R₆, p]) (by simp [R₆, q])
    -- x ∈ a₃
    · exact mem R₃ i3 x y (by simp [R₃, p]) (by simp [R₃, q])
    · exact mem R₆ i6 x y (by simp [R₆, p]) (by simp [R₆, q])
    · exact mem R₂ i2 x y (by simp [R₂, p]) (by simp [R₂, q])
    · exact mem R₂ i2 x y (by simp [R₂, p]) (by simp [R₂, q])
    · exact mem R₂ i2 x y (by simp [R₂, p]) (by simp [R₂, q])
    · exact mem R₃ i3 x y (by simp [R₃, p]) (by simp [R₃, q])
    · exact mem R₆ i6 x y (by simp [R₆, p]) (by simp [R₆, q])
    -- x ∈ a₄
    · exact mem R₅ i5 x y (by simp [R₅, p]) (by simp [R₅, q])
    · exact mem R₄ i4 x y (by simp [R₄, p]) (by simp [R₄, q])
    · exact mem R₂ i2 x y (by simp [R₂, p]) (by simp [R₂, q])
    · exact mem R₂ i2 x y (by simp [R₂, p]) (by simp [R₂, q])
    · exact mem R₂ i2 x y (by simp [R₂, p]) (by simp [R₂, q])
    · exact mem R₄ i4 x y (by simp [R₄, p]) (by simp [R₄, q])
    · exact mem R₅ i5 x y (by simp [R₅, p]) (by simp [R₅, q])
  refine request_cover_V hprop V hV (E := {A}) (D := D) (by simpa using hA) ⟨A, by simp⟩
    (by simp; omega) hresp ?_
  intro x hx y hy hxy
  rcases hxy A (by simp) with h | h
  · exact key x y h hy
  · obtain ⟨d, hd, h1, h2⟩ := key y x h hx
    exact ⟨d, hd, h2, h1⟩

/-- **Theorem A, transversal form.** A `k`-uniform family with property (7,2) whose edges lie in
`V` has `τ ≤ ⌈(|V|-k)/3⌉ + 2⌈k/4⌉`. -/
theorem theoremA {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {k : ℕ}
    (hunif : IsUniform H k) (V : Finset α) (hV : ∀ A ∈ H, A ⊆ V) :
    CoverableBy H ((V.card - k + 2) / 3 + 2 * ((k + 3) / 4)) := by
  by_contra hτ
  rcases H.eq_empty_or_nonempty with rfl | ⟨A, hA⟩
  · exact hτ ⟨∅, by simp, fun A hA => by simp at hA⟩
  · exact theoremA_closes hprop hτ hunif V hV hA le_rfl

end Erdos644
