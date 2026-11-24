import Lean644.Defs

/-!
# Anchors (TWIN.md §13.1–13.2)

Three sets `Ba, Bb, Bc` with empty common intersection are *anchors*; `V = Ba ∪ Bb ∪ Bc`.

* `anchor_cover_mem` (anchor lemma): a pair `{x, y}` meeting the three anchors lies in `V`.
* `anchor_trace_iff` (trace equivalence): for such a pair, meeting `E` is the same as meeting
  the trace `E ∩ V`.
* `anchor_mono` (monotonicity): if `E i ∩ V ⊆ E' i` for all `i`, every 2-cover of the anchors and
  the `E i` is a 2-cover of the anchors and the `E' i`.
* `anchor_coverable_mono`: the same for `CoverableBy · 2` of the finite families
  `{Ba, Bb, Bc} ∪ {E i}` and `{Ba, Bb, Bc} ∪ {E' i}`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Anchor lemma.** -/
theorem anchor_cover_mem {Ba Bb Bc : Finset α} (h : Ba ∩ Bb ∩ Bc = ∅) {x y : α}
    (ha : x ∈ Ba ∨ y ∈ Ba) (hb : x ∈ Bb ∨ y ∈ Bb) (hc : x ∈ Bc ∨ y ∈ Bc) :
    x ∈ Ba ∪ Bb ∪ Bc ∧ y ∈ Ba ∪ Bb ∪ Bc := by
  have key : ∀ z, z ∈ Ba → z ∈ Bb → z ∈ Bc → False := by
    intro z h1 h2 h3
    have hz : z ∈ Ba ∩ Bb ∩ Bc := Finset.mem_inter.2 ⟨Finset.mem_inter.2 ⟨h1, h2⟩, h3⟩
    rw [h] at hz
    exact Finset.notMem_empty z hz
  constructor
  · by_contra hx
    simp only [Finset.mem_union, not_or] at hx
    obtain ⟨⟨hxa, hxb⟩, hxc⟩ := hx
    exact key y (ha.resolve_left hxa) (hb.resolve_left hxb) (hc.resolve_left hxc)
  · by_contra hy
    simp only [Finset.mem_union, not_or] at hy
    obtain ⟨⟨hya, hyb⟩, hyc⟩ := hy
    exact key x (ha.resolve_right hya) (hb.resolve_right hyb) (hc.resolve_right hyc)

/-- **Trace equivalence.** -/
theorem anchor_trace_iff {V E : Finset α} {x y : α} (hx : x ∈ V) (hy : y ∈ V) :
    (x ∈ E ∨ y ∈ E) ↔ (x ∈ E ∩ V ∨ y ∈ E ∩ V) := by
  simp only [Finset.mem_inter]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨h, hy⟩
  · rintro (h | h)
    · exact Or.inl h.1
    · exact Or.inr h.1

/-- **Monotonicity in the traces.** -/
theorem anchor_mono {ι : Type*} {Ba Bb Bc : Finset α} (h : Ba ∩ Bb ∩ Bc = ∅)
    (E E' : ι → Finset α) (hmono : ∀ i, E i ∩ (Ba ∪ Bb ∪ Bc) ⊆ E' i) {x y : α}
    (ha : x ∈ Ba ∨ y ∈ Ba) (hb : x ∈ Bb ∨ y ∈ Bb) (hc : x ∈ Bc ∨ y ∈ Bc)
    (hE : ∀ i, x ∈ E i ∨ y ∈ E i) : ∀ i, x ∈ E' i ∨ y ∈ E' i := by
  obtain ⟨hx, hy⟩ := anchor_cover_mem h ha hb hc
  intro i
  rcases (anchor_trace_iff hx hy).1 (hE i) with h' | h'
  · exact Or.inl (hmono i h')
  · exact Or.inr (hmono i h')

/-- Monotonicity for `CoverableBy · 2`. -/
theorem anchor_coverable_mono {ι : Type*} [Fintype ι] {Ba Bb Bc : Finset α}
    (h : Ba ∩ Bb ∩ Bc = ∅) (E E' : ι → Finset α)
    (hmono : ∀ i, E i ∩ (Ba ∪ Bb ∪ Bc) ⊆ E' i)
    (hcov : CoverableBy (insert Ba (insert Bb (insert Bc (Finset.univ.image E)))) 2) :
    CoverableBy (insert Ba (insert Bb (insert Bc (Finset.univ.image E')))) 2 := by
  classical
  rw [coverableBy_two_iff ⟨Ba, Finset.mem_insert_self _ _⟩] at hcov ⊢
  obtain ⟨x, y, hxy⟩ := hcov
  have ha := hxy Ba (Finset.mem_insert_self _ _)
  have hb := hxy Bb (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hc := hxy Bc
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hE : ∀ i, x ∈ E i ∨ y ∈ E i := fun i =>
    hxy (E i) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))
  have hE' := anchor_mono h E E' hmono ha hb hc hE
  refine ⟨x, y, fun A hA => ?_⟩
  rcases Finset.mem_insert.1 hA with rfl | hA
  · exact ha
  rcases Finset.mem_insert.1 hA with rfl | hA
  · exact hb
  rcases Finset.mem_insert.1 hA with rfl | hA
  · exact hc
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
  exact hE' i

end Erdos644
