import Lean644.Defs

/-!
# Petal reduction (PETAL.md §1, P1–P4), analogous to `Anchor.lean`

Petals: an indexed family `P : ι → Finset α` with empty common intersection
(`∀ x, ∃ a, x ∉ P a`). The *dangerous graph* `Γ(P)` has the edges `{x, y}` with
`∀ a, x ∈ P a ∨ y ∈ P a` (`PetalEdge`); a point is *active* if it lies on an edge
(`PetalActive`).

* `petalEdge_ne`, `petalEdge_mem_union` (P1): the two points of an edge are distinct and lie in
  petals; by definition both are active, and every 2-cover of a family containing the petals is
  an edge.
* `petalActive_iff`: `x` is active iff the petals missing `x` have a common point.
* `petal_trace_iff`, `petal_mono` (P3(i)): for a set `W` containing all active points,
  a 2-cover meets `E` iff it meets `E ∩ W`; coverability is monotone in the traces on `W`.
* `petal_one_centre` (P4(a)): a centre containing no active point destroys all 2-covers.
* `petal_three_centres` (P4(c)): three centres with pairwise disjoint traces on `W` destroy all
  2-covers.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α] {ι : Type*}

/-- `{x, y}` meets every petal. -/
def PetalEdge (P : ι → Finset α) (x y : α) : Prop := ∀ a, x ∈ P a ∨ y ∈ P a

/-- `x` is a non-isolated vertex of the dangerous graph. -/
def PetalActive (P : ι → Finset α) (x : α) : Prop := ∃ y, PetalEdge P x y

theorem PetalEdge.symm {P : ι → Finset α} {x y : α} (h : PetalEdge P x y) : PetalEdge P y x :=
  fun a => (h a).symm

theorem PetalEdge.active_left {P : ι → Finset α} {x y : α} (h : PetalEdge P x y) :
    PetalActive P x := ⟨y, h⟩

theorem PetalEdge.active_right {P : ι → Finset α} {x y : α} (h : PetalEdge P x y) :
    PetalActive P y := ⟨x, h.symm⟩

/-- P1: the endpoints of an edge are distinct (petals have empty common intersection). -/
theorem petalEdge_ne {P : ι → Finset α} (hempty : ∀ x, ∃ a, x ∉ P a) {x y : α}
    (h : PetalEdge P x y) : x ≠ y := by
  rintro rfl
  obtain ⟨a, ha⟩ := hempty x
  rcases h a with h' | h' <;> exact ha h'

/-- P1: both endpoints of an edge lie in some petal. -/
theorem petalEdge_mem_union {P : ι → Finset α} (hempty : ∀ x, ∃ a, x ∉ P a) {x y : α}
    (h : PetalEdge P x y) : (∃ a, x ∈ P a) ∧ (∃ a, y ∈ P a) := by
  obtain ⟨a, ha⟩ := hempty y
  obtain ⟨b, hb⟩ := hempty x
  exact ⟨⟨a, (h a).resolve_right ha⟩, ⟨b, (h b).resolve_left hb⟩⟩

/-- Activity formula: `x` is active iff the petals missing `x` have a common point. -/
theorem petalActive_iff (P : ι → Finset α) (x : α) :
    PetalActive P x ↔ ∃ y, ∀ a, x ∉ P a → y ∈ P a := by
  constructor
  · rintro ⟨y, h⟩
    exact ⟨y, fun a ha => (h a).resolve_left ha⟩
  · rintro ⟨y, h⟩
    refine ⟨y, fun a => ?_⟩
    by_cases hx : x ∈ P a
    · exact Or.inl hx
    · exact Or.inr (h a hx)

/-- Trace equivalence on a set `W` containing the active points. -/
theorem petal_trace_iff {P : ι → Finset α} {W E : Finset α} (hW : ∀ x, PetalActive P x → x ∈ W)
    {x y : α} (h : PetalEdge P x y) : (x ∈ E ∨ y ∈ E) ↔ (x ∈ E ∩ W ∨ y ∈ E ∩ W) := by
  have hx := hW x h.active_left
  have hy := hW y h.active_right
  simp only [Finset.mem_inter]
  constructor
  · rintro (h' | h')
    · exact Or.inl ⟨h', hx⟩
    · exact Or.inr ⟨h', hy⟩
  · rintro (h' | h')
    · exact Or.inl h'.1
    · exact Or.inr h'.1

/-- **P3(i), monotonicity.** If `E i ∩ W ⊆ E' i` for all `i`, every 2-cover of the petals and the
`E i` is a 2-cover of the petals and the `E' i`. -/
theorem petal_mono {κ : Type*} {P : ι → Finset α} {W : Finset α}
    (hW : ∀ x, PetalActive P x → x ∈ W) (E E' : κ → Finset α)
    (hmono : ∀ i, E i ∩ W ⊆ E' i) {x y : α} (h : PetalEdge P x y)
    (hE : ∀ i, x ∈ E i ∨ y ∈ E i) : ∀ i, x ∈ E' i ∨ y ∈ E' i := by
  intro i
  rcases (petal_trace_iff hW h).1 (hE i) with h' | h'
  · exact Or.inl (hmono i h')
  · exact Or.inr (hmono i h')

/-- **P4(a), one centre.** A set containing no active point is met by no 2-cover of the
petals. -/
theorem petal_one_centre {P : ι → Finset α} {C : Finset α}
    (hC : ∀ x ∈ C, ¬ PetalActive P x) {x y : α} (h : PetalEdge P x y) :
    ¬ (x ∈ C ∨ y ∈ C) := by
  rintro (h' | h')
  · exact hC x h' h.active_left
  · exact hC y h' h.active_right

/-- **P4(c), three centres.** Three sets whose traces on `W` are pairwise disjoint are not all
met by a 2-cover of the petals. -/
theorem petal_three_centres {P : ι → Finset α} (hempty : ∀ x, ∃ a, x ∉ P a) {W : Finset α}
    (hW : ∀ x, PetalActive P x → x ∈ W) {C₁ C₂ C₃ : Finset α}
    (h12 : C₁ ∩ C₂ ∩ W = ∅) (h13 : C₁ ∩ C₃ ∩ W = ∅) (h23 : C₂ ∩ C₃ ∩ W = ∅)
    {x y : α} (h : PetalEdge P x y) :
    ¬ ((x ∈ C₁ ∨ y ∈ C₁) ∧ (x ∈ C₂ ∨ y ∈ C₂) ∧ (x ∈ C₃ ∨ y ∈ C₃)) := by
  have hx := hW x h.active_left
  have hy := hW y h.active_right
  have key : ∀ {A B : Finset α}, A ∩ B ∩ W = ∅ → ∀ z, z ∈ W → z ∈ A → z ∈ B → False := by
    intro A B hAB z hz hA hB
    have : z ∈ A ∩ B ∩ W := Finset.mem_inter.2 ⟨Finset.mem_inter.2 ⟨hA, hB⟩, hz⟩
    rw [hAB] at this
    exact Finset.notMem_empty z this
  rintro ⟨h1, h2, h3⟩
  rcases h1 with a1 | a1 <;> rcases h2 with a2 | a2 <;> rcases h3 with a3 | a3
  · exact key h12 x hx a1 a2
  · exact key h12 x hx a1 a2
  · exact key h13 x hx a1 a3
  · exact key h23 y hy a2 a3
  · exact key h23 x hx a2 a3
  · exact key h13 y hy a1 a3
  · exact key h12 y hy a1 a2
  · exact key h12 y hy a1 a2

end Erdos644
