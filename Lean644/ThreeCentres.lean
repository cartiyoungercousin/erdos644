import Lean644.Framework

/-!
# Lemma 6.1 (three centres) and Corollary 6.2 (trace pairs)

Source: `notes/NEW_PATHS.md` §6.1 (Fable research lead, 2026-11-23); hand-checked.

**Lemma 6.1.** Let `P` be a family of edges ("petals") with empty common intersection, `U` their
union, and `C₁, C₂, C₃` edges ("centres") with `Cᵢ ∩ Cⱼ ∩ U = ∅` for `i ≠ j`. Then `P` together
with the three centres has no 2-point transversal. (A point in two centres is outside `U`, so it
meets no petal; the other point would have to lie in every petal.)

**Corollary 6.2.** If `τ(H) > T`, `H` has property (7,2), and `P ⊆ H` has at most 4 members with
empty common intersection and union `U`, then any two edges `B₁, B₂` with `B₁ ∩ B₂ ∩ U = ∅`
satisfy `|B₁ ∩ U| + |B₂ ∩ U| > T`. (Otherwise request `(B₁ ∩ U) ∪ (B₂ ∩ U)`; the response is a
third centre.)
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Lemma 6.1 (three centres).** `P.sup id` is the union of the petals. -/
theorem three_centres (P : Finset (Finset α)) (hP : ∀ x, ∃ A ∈ P, x ∉ A)
    (C₁ C₂ C₃ : Finset α)
    (h12 : ∀ x ∈ C₁, x ∈ C₂ → x ∉ P.sup id) (h13 : ∀ x ∈ C₁, x ∈ C₃ → x ∉ P.sup id)
    (h23 : ∀ x ∈ C₂, x ∈ C₃ → x ∉ P.sup id) :
    ¬ CoverableBy (insert C₁ (insert C₂ (insert C₃ P))) 2 := by
  rw [coverableBy_two_iff ⟨C₁, Finset.mem_insert_self _ _⟩]
  rintro ⟨x, y, hxy⟩
  have hPxy : ∀ A ∈ P, x ∈ A ∨ y ∈ A := fun A hA =>
    hxy A (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hA)))
  have hPyx : ∀ A ∈ P, y ∈ A ∨ x ∈ A := fun A hA => (hPxy A hA).symm
  -- a point outside the union meets no petal, so the other point is in every petal
  have fin : ∀ z w, z ∉ P.sup id → (∀ A ∈ P, z ∈ A ∨ w ∈ A) → False := by
    intro z w hz h
    obtain ⟨A, hA, hwA⟩ := hP w
    rcases h A hA with h1 | h1
    · exact hz (Finset.mem_sup.2 ⟨A, hA, h1⟩)
    · exact hwA h1
  have c1 := hxy C₁ (Finset.mem_insert_self _ _)
  have c2 := hxy C₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have c3 := hxy C₃ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_self _ _)))
  -- pigeonhole: one of the two points lies in two centres
  rcases c1 with a | a <;> rcases c2 with b | b <;> rcases c3 with c | c
  · exact fin x y (h12 x a b) hPxy
  · exact fin x y (h12 x a b) hPxy
  · exact fin x y (h13 x a c) hPxy
  · exact fin y x (h23 y b c) hPyx
  · exact fin x y (h23 x b c) hPxy
  · exact fin y x (h13 y a c) hPyx
  · exact fin y x (h12 y a b) hPyx
  · exact fin y x (h12 y a b) hPyx

/-- **Corollary 6.2 (trace pairs).** -/
theorem trace_pairs {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T : ℕ}
    (hτ : ¬ CoverableBy H T) {P : Finset (Finset α)} (hPH : P ⊆ H) (hPc : P.card ≤ 4)
    (hP : ∀ x, ∃ A ∈ P, x ∉ A) {B₁ B₂ : Finset α} (hB₁ : B₁ ∈ H) (hB₂ : B₂ ∈ H)
    (h12 : ∀ x ∈ B₁, x ∈ B₂ → x ∉ P.sup id) :
    T < (B₁ ∩ P.sup id).card + (B₂ ∩ P.sup id).card := by
  by_contra hle
  have hD : ((B₁ ∩ P.sup id) ∪ (B₂ ∩ P.sup id)).card ≤ T :=
    (Finset.card_union_le _ _).trans (by omega)
  obtain ⟨C₃, hC₃, hdisj⟩ := exists_response hτ hD
  have miss : ∀ x ∈ C₃, x ∉ (B₁ ∩ P.sup id) ∪ (B₂ ∩ P.sup id) := fun x hx =>
    Finset.disjoint_left.1 hdisj hx
  have h13 : ∀ x ∈ B₁, x ∈ C₃ → x ∉ P.sup id := fun x h1 h3 hU =>
    miss x h3 (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h1, hU⟩))
  have h23 : ∀ x ∈ B₂, x ∈ C₃ → x ∉ P.sup id := fun x h2 h3 hU =>
    miss x h3 (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h2, hU⟩))
  have hsub : insert B₁ (insert B₂ (insert C₃ P)) ⊆ H := by
    intro A hA
    simp only [Finset.mem_insert] at hA
    rcases hA with rfl | rfl | rfl | hA
    · exact hB₁
    · exact hB₂
    · exact hC₃
    · exact hPH hA
  have hcard : (insert B₁ (insert B₂ (insert C₃ P))).card ≤ 7 :=
    (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <|
      (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <|
        (Finset.card_insert_le _ _).trans (by omega)
  exact three_centres P hP B₁ B₂ C₃ h12 h13 h23 (hprop _ hsub hcard)

end Erdos644
