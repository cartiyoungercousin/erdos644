import Lean644.Adaptive

/-!
# The rectangle lemma and the waste adversary (TWIN.md §5, FRESH_C.md §8)

* `rect_cover_iff` (TWIN Lemma 5.1): if `A`, `A'` are disjoint, a pair covers `A`, `A'` and the
  sets `E t` iff (up to order) it is a pair `(x, y) ∈ A × A'` lying in no rectangle
  `(A \ E t) × (A' \ E t)`.
* `rect_count`: rectangles covering `X × Y` have total area at least `|X| |Y|`.
* `waste_core` (counting core of FRESH_C Theorem 8): `n` rectangles of semi-perimeter `≤ T` in a
  `T × k` grid with `(n + 1) T < 4k` leave uncovered pairs whose two projections have more than
  `T` points in total.
* `waste_adversary` (FRESH_C Theorem 8, six-edge form): `A₁ ⊇ X`, `|X| = T`, `Y` a `k`-set
  disjoint from `X`, four `k`-sets `B t ⊆ X ∪ Y`, `0 < T`, `5T < 4k`. Then for every request `S`
  with `|S| ≤ T` there is a point `x ∉ S`, `x ∈ X ∪ Y`, and a partner `y` such that `{x, y}` meets
  `A₁`, `Y` and all `B t`; so every 7th reply containing `x` completes a 2-coverable 7-tuple.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Rectangle lemma** (TWIN Lemma 5.1). -/
theorem rect_cover_iff {ι : Type*} {A A' : Finset α} (hdisj : Disjoint A A') (E : ι → Finset α) :
    (∃ x y : α, (x ∈ A ∨ y ∈ A) ∧ (x ∈ A' ∨ y ∈ A') ∧ ∀ t, x ∈ E t ∨ y ∈ E t) ↔
      ∃ x ∈ A, ∃ y ∈ A', ∀ t, ¬ (x ∈ A \ E t ∧ y ∈ A' \ E t) := by
  constructor
  · rintro ⟨x, y, hA, hA', hE⟩
    have key : ∀ {u v : α}, u ∈ A → v ∈ A' → (∀ t, u ∈ E t ∨ v ∈ E t) →
        ∃ x ∈ A, ∃ y ∈ A', ∀ t, ¬ (x ∈ A \ E t ∧ y ∈ A' \ E t) := by
      intro u v hu hv h
      refine ⟨u, hu, v, hv, fun t ht => ?_⟩
      rcases h t with h | h
      · exact (Finset.mem_sdiff.1 ht.1).2 h
      · exact (Finset.mem_sdiff.1 ht.2).2 h
    rcases hA with hxA | hyA
    · rcases hA' with hxA' | hyA'
      · exact absurd hxA' (Finset.disjoint_left.1 hdisj hxA)
      · exact key hxA hyA' hE
    · rcases hA' with hxA' | hyA'
      · exact key hyA hxA' (fun t => (hE t).symm)
      · exact absurd hyA' (Finset.disjoint_left.1 hdisj hyA)
  · rintro ⟨x, hx, y, hy, h⟩
    refine ⟨x, y, Or.inl hx, Or.inr hy, fun t => ?_⟩
    by_contra hcon
    push_neg at hcon
    exact h t ⟨Finset.mem_sdiff.2 ⟨hx, hcon.1⟩, Finset.mem_sdiff.2 ⟨hy, hcon.2⟩⟩

/-- Rectangles covering a grid have total area at least the area of the grid. -/
theorem rect_count {ι : Type*} [Fintype ι] (X Y : Finset α) (P Q : ι → Finset α)
    (h : ∀ x ∈ X, ∀ y ∈ Y, ∃ t, x ∈ P t ∧ y ∈ Q t) :
    X.card * Y.card ≤ ∑ t, (P t).card * (Q t).card := by
  classical
  have hsub : X ×ˢ Y ⊆ Finset.univ.biUnion (fun t => P t ×ˢ Q t) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.1 hxy
    obtain ⟨t, hxt, hyt⟩ := h x hx y hy
    exact Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, Finset.mem_product.2 ⟨hxt, hyt⟩⟩
  calc X.card * Y.card = (X ×ˢ Y).card := (Finset.card_product _ _).symm
    _ ≤ (Finset.univ.biUnion (fun t => P t ×ˢ Q t)).card := Finset.card_le_card hsub
    _ ≤ ∑ t, (P t ×ˢ Q t).card := Finset.card_biUnion_le
    _ = ∑ t, (P t).card * (Q t).card := by simp [Finset.card_product]

/-- AM–GM in the form used below. -/
theorem four_mul_le_sq {a b T : ℕ} (h : a + b ≤ T) : 4 * (a * b) ≤ T * T := by
  have h1 : (a + b) * (a + b) ≤ T * T := Nat.mul_le_mul h h
  have h2 : 4 * (a * b) ≤ (a + b) * (a + b) := by
    rcases le_total a b with hab | hab
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      nlinarith [Nat.zero_le (d * d)]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      nlinarith [Nat.zero_le (d * d)]
  exact h2.trans h1

/-- **Counting core of Theorem 8.** -/
theorem waste_core {ι : Type*} [Fintype ι] {X Y EX EY : Finset α} {T k : ℕ}
    (hX : X.card = T) (hY : Y.card = k) (P Q : ι → Finset α)
    (hPQ : ∀ t, (P t).card + (Q t).card ≤ T) (hT0 : 0 < T)
    (hT : (Fintype.card ι + 1) * T < 4 * k)
    (hE : ∀ x ∈ X, ∀ y ∈ Y, (∀ t, ¬ (x ∈ P t ∧ y ∈ Q t)) → x ∈ EX ∧ y ∈ EY) :
    T < EX.card + EY.card := by
  classical
  by_contra hcon
  have hcon : EX.card + EY.card ≤ T := Nat.le_of_not_lt hcon
  -- the rectangles together with `EX × EY` cover the grid
  have hcov : ∀ x ∈ X, ∀ y ∈ Y, ∃ t : Option ι, x ∈ t.elim EX P ∧ y ∈ t.elim EY Q := by
    intro x hx y hy
    by_cases hgood : ∀ t, ¬ (x ∈ P t ∧ y ∈ Q t)
    · exact ⟨none, hE x hx y hy hgood⟩
    · push_neg at hgood
      obtain ⟨t, ht⟩ := hgood
      exact ⟨some t, ht⟩
  have hcount := rect_count X Y (fun o : Option ι => o.elim EX P)
    (fun o : Option ι => o.elim EY Q) hcov
  rw [Fintype.sum_option] at hcount
  simp only [Option.elim_none, Option.elim_some] at hcount
  have h1 : 4 * (EX.card * EY.card) ≤ T * T := four_mul_le_sq hcon
  have h2 : 4 * ∑ t, (P t).card * (Q t).card ≤ Fintype.card ι * (T * T) := by
    rw [Finset.mul_sum]
    calc ∑ t, 4 * ((P t).card * (Q t).card) ≤ ∑ _t : ι, T * T :=
          Finset.sum_le_sum (fun t _ => four_mul_le_sq (hPQ t))
      _ = Fintype.card ι * (T * T) := by simp [Finset.card_univ]
  rw [hX, hY] at hcount
  have h3 : 4 * (T * k) ≤ (Fintype.card ι + 1) * T * T := by nlinarith
  have h4 : (Fintype.card ι + 1) * T * T < 4 * k * T := mul_lt_mul_of_pos_right hT hT0
  nlinarith

/-- **Theorem 8 (waste adversary), six-edge form.** -/
theorem waste_adversary {A₁ X Y : Finset α} {T k : ℕ} (hXA : X ⊆ A₁) (hX : X.card = T)
    (hY : Y.card = k) (hXY : Disjoint X Y) (B : Fin 4 → Finset α)
    (hBsub : ∀ t, B t ⊆ X ∪ Y) (hBcard : ∀ t, (B t).card = k)
    (hT0 : 0 < T) (hT : 5 * T < 4 * k) {S : Finset α} (hS : S.card ≤ T) :
    ∃ x, x ∉ S ∧ x ∈ X ∪ Y ∧ ∃ y, (x ∈ A₁ ∨ y ∈ A₁) ∧ (x ∈ Y ∨ y ∈ Y) ∧
      ∀ t, x ∈ B t ∨ y ∈ B t := by
  classical
  have hPQ : ∀ t, (X \ B t).card + (Y \ B t).card ≤ T := by
    intro t
    have hd : Disjoint (X \ B t) (Y \ B t) :=
      Finset.disjoint_left.2 (fun a ha ha' => Finset.disjoint_left.1 hXY
        (Finset.mem_sdiff.1 ha).1 (Finset.mem_sdiff.1 ha').1)
    have h1 := card_union_disj hd
    have h2 : X \ B t ∪ Y \ B t = (X ∪ Y) \ B t := (Finset.union_sdiff_distrib _ _ _).symm
    have h3 : ((X ∪ Y) \ B t).card = (X ∪ Y).card - (B t).card :=
      Finset.card_sdiff_of_subset (hBsub t)
    have h4 : (X ∪ Y).card = T + k := by
      rw [card_union_disj hXY, hX, hY]
    rw [h2, h3, h4, hBcard t] at h1
    omega
  have hcore : T < (X.filter (fun x => ∃ y ∈ Y, ∀ t, x ∈ B t ∨ y ∈ B t)).card +
      (Y.filter (fun y => ∃ x ∈ X, ∀ t, x ∈ B t ∨ y ∈ B t)).card := by
    refine waste_core (ι := Fin 4) hX hY (fun t => X \ B t) (fun t => Y \ B t) hPQ hT0
      (by simpa using hT) ?_
    intro x hx y hy hgood
    have hcov : ∀ t, x ∈ B t ∨ y ∈ B t := by
      intro t
      by_contra hcon
      push_neg at hcon
      exact hgood t ⟨Finset.mem_sdiff.2 ⟨hx, hcon.1⟩, Finset.mem_sdiff.2 ⟨hy, hcon.2⟩⟩
    exact ⟨Finset.mem_filter.2 ⟨hx, y, hy, hcov⟩, Finset.mem_filter.2 ⟨hy, x, hx, hcov⟩⟩
  have hdisjE : Disjoint (X.filter (fun x => ∃ y ∈ Y, ∀ t, x ∈ B t ∨ y ∈ B t))
      (Y.filter (fun y => ∃ x ∈ X, ∀ t, x ∈ B t ∨ y ∈ B t)) :=
    Finset.disjoint_left.2 (fun a ha ha' => Finset.disjoint_left.1 hXY
      (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 ha').1)
  have hcardE := card_union_disj hdisjE
  have hnot : ¬ (X.filter (fun x => ∃ y ∈ Y, ∀ t, x ∈ B t ∨ y ∈ B t)) ∪
      (Y.filter (fun y => ∃ x ∈ X, ∀ t, x ∈ B t ∨ y ∈ B t)) ⊆ S := fun hsub => by
    have := Finset.card_le_card hsub
    omega
  obtain ⟨x, hxE, hxS⟩ := Finset.not_subset.1 hnot
  rcases Finset.mem_union.1 hxE with hx | hx
  · obtain ⟨hxX, y, hy, hcov⟩ := Finset.mem_filter.1 hx
    exact ⟨x, hxS, Finset.mem_union_left _ hxX, y, Or.inl (hXA hxX), Or.inr hy, hcov⟩
  · obtain ⟨hxY, y, hy, hcov⟩ := Finset.mem_filter.1 hx
    exact ⟨x, hxS, Finset.mem_union_right _ hxY, y, Or.inr (hXA hy), Or.inl hxY,
      fun t => (hcov t).symm⟩

end Erdos644
