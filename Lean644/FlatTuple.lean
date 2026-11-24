import Lean644.Framework

/-!
# Flat 7-tuples (FRESH_C.md §1, Lemma 3 and Corollary 4)

* `exists_flat_tuple` (Lemma 3, "top-degree requests"): if `H` is `k`-uniform, `τ(H) > T` and
  `3k ≤ 4T`, then there are seven edges `A 0, …, A 6` of `H` (not necessarily distinct) such that
  every point lies in at most four of them.
* `flat_cover_shape` (Corollary 4): if every point lies in at most four of seven sets and `{x, y}`
  meets all seven, then one of `x, y` lies in exactly four of them (and the other one in all of the
  remaining three, which is just the covering hypothesis).
* `flat_tuple_cover`: both combined with property (7,2) (in the "at most" convention).

The proof of Lemma 3 follows the notes: requests alternate between "a `T`-subset of the points of
degree `≥ j`" (`flat_even_step`) and "all points of degree `≥ j`" (`flat_odd_step`).
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- Indicator of membership, as a natural number. -/
def ind (A : Finset α) (x : α) : ℕ := if x ∈ A then 1 else 0

theorem ind_le_one (A : Finset α) (x : α) : ind A x ≤ 1 := by
  unfold ind; split_ifs <;> omega

theorem ind_pos_iff (A : Finset α) (x : α) : 1 ≤ ind A x ↔ x ∈ A := by
  unfold ind; split_ifs with h <;> simp [h]

/-- Even step: all degrees are `≤ j`, the points of degree `≥ j` lie in `Q` with `|Q| ≤ m`.
Requesting `min T |Q|` points of `Q` gives an edge after which the points of degree `≥ j+1`
lie in a set of size `≤ m - T`. -/
theorem flat_even_step {H : Finset (Finset α)} {T : ℕ} (hτ : ¬ CoverableBy H T)
    {d : α → ℕ} {j m : ℕ} {Q : Finset α}
    (hQ : ∀ x, j ≤ d x → x ∈ Q) (hQc : Q.card ≤ m) (hd : ∀ x, d x ≤ j) :
    ∃ A ∈ H, ∃ P : Finset α, P.card ≤ m - T ∧
      (∀ x, j + 1 ≤ d x + ind A x → x ∈ P) ∧ ∀ x, d x + ind A x ≤ j + 1 := by
  obtain ⟨S, hSQ, hSc⟩ := Finset.exists_subset_card_eq (min_le_right T Q.card)
  obtain ⟨A, hA, hAS⟩ := exists_response hτ (d := S) (by rw [hSc]; exact min_le_left _ _)
  refine ⟨A, hA, Q \ S, ?_, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hSQ, hSc]
    rcases le_total T Q.card with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  · intro x hx
    have h1 := ind_le_one A x
    have h2 := hd x
    have hxQ : x ∈ Q := hQ x (by omega)
    have hxA : x ∈ A := (ind_pos_iff A x).1 (by omega)
    exact Finset.mem_sdiff.2 ⟨hxQ, fun hxS => Finset.disjoint_left.1 hAS hxA hxS⟩
  · intro x
    have h1 := ind_le_one A x
    have h2 := hd x
    omega

/-- Odd step: all degrees are `≤ j`, the points of degree `≥ j` lie in `P` with `|P| ≤ p ≤ T`.
Requesting `P` gives an edge after which all degrees are still `≤ j`, and the points of degree
`≥ j` lie in a set of size `≤ p + k`. -/
theorem flat_odd_step {H : Finset (Finset α)} {T k : ℕ} (hunif : IsUniform H k)
    (hτ : ¬ CoverableBy H T) {d : α → ℕ} {j p : ℕ} {P : Finset α}
    (hP : ∀ x, j ≤ d x → x ∈ P) (hPc : P.card ≤ p) (hpT : p ≤ T) (hd : ∀ x, d x ≤ j) :
    ∃ A ∈ H, ∃ Q : Finset α, Q.card ≤ p + k ∧
      (∀ x, j ≤ d x + ind A x → x ∈ Q) ∧ ∀ x, d x + ind A x ≤ j := by
  obtain ⟨A, hA, hAP⟩ := exists_response hτ (d := P) (hPc.trans hpT)
  refine ⟨A, hA, P ∪ A, ?_, ?_, ?_⟩
  · have := Finset.card_union_le P A
    have := hunif A hA
    omega
  · intro x hx
    by_cases hxA : x ∈ A
    · exact Finset.mem_union_right _ hxA
    · have : ind A x = 0 := by simp [ind, hxA]
      exact Finset.mem_union_left _ (hP x (by omega))
  · intro x
    by_cases hxA : x ∈ A
    · have hxP : ¬ j ≤ d x := fun h => Finset.disjoint_left.1 hAP hxA (hP x h)
      have := ind_le_one A x
      omega
    · have : ind A x = 0 := by simp [ind, hxA]
      have := hd x
      omega

/-- Lemma 3 in indicator form. -/
theorem exists_flat_tuple_ind {H : Finset (Finset α)} {T k : ℕ} (hunif : IsUniform H k)
    (hτ : ¬ CoverableBy H T) (hT : 3 * k ≤ 4 * T) :
    ∃ A₁ ∈ H, ∃ A₂ ∈ H, ∃ A₃ ∈ H, ∃ A₄ ∈ H, ∃ A₅ ∈ H, ∃ A₆ ∈ H, ∃ A₇ ∈ H,
      ∀ x, ind A₁ x + ind A₂ x + ind A₃ x + ind A₄ x + ind A₅ x + ind A₆ x + ind A₇ x ≤ 4 := by
  -- step 1 (odd step with j = 1 from the empty configuration)
  obtain ⟨A₁, hA₁, Q₁, hQ₁c, hQ₁, hd₁⟩ :=
    flat_odd_step (d := fun _ => 0) (j := 1) (p := 0) (P := ∅) hunif hτ
      (by intro x hx; omega) (by simp) (Nat.zero_le _) (by intro x; omega)
  obtain ⟨A₂, hA₂, P₂, hP₂c, hP₂, hd₂⟩ := flat_even_step hτ hQ₁ hQ₁c hd₁
  obtain ⟨A₃, hA₃, Q₃, hQ₃c, hQ₃, hd₃⟩ :=
    flat_odd_step hunif hτ hP₂ hP₂c (by omega) hd₂
  obtain ⟨A₄, hA₄, P₄, hP₄c, hP₄, hd₄⟩ := flat_even_step hτ hQ₃ hQ₃c hd₃
  obtain ⟨A₅, hA₅, Q₅, hQ₅c, hQ₅, hd₅⟩ :=
    flat_odd_step hunif hτ hP₄ hP₄c (by omega) hd₄
  obtain ⟨A₆, hA₆, P₆, hP₆c, hP₆, hd₆⟩ := flat_even_step hτ hQ₅ hQ₅c hd₅
  obtain ⟨A₇, hA₇, Q₇, -, -, hd₇⟩ :=
    flat_odd_step hunif hτ hP₆ hP₆c (by omega) hd₆
  refine ⟨A₁, hA₁, A₂, hA₂, A₃, hA₃, A₄, hA₄, A₅, hA₅, A₆, hA₆, A₇, hA₇, fun x => ?_⟩
  have := hd₇ x
  simpa using this

/-- **Lemma 3 (top-degree requests).** If `H` is `k`-uniform, `τ(H) > T` and `3k ≤ 4T`, then
`H` contains seven edges (repetitions allowed) such that every point lies in at most four of
them. -/
theorem exists_flat_tuple {H : Finset (Finset α)} {T k : ℕ} (hunif : IsUniform H k)
    (hτ : ¬ CoverableBy H T) (hT : 3 * k ≤ 4 * T) :
    ∃ A : Fin 7 → Finset α, (∀ i, A i ∈ H) ∧
      ∀ x, (Finset.univ.filter (fun i => x ∈ A i)).card ≤ 4 := by
  obtain ⟨A₁, hA₁, A₂, hA₂, A₃, hA₃, A₄, hA₄, A₅, hA₅, A₆, hA₆, A₇, hA₇, h⟩ :=
    exists_flat_tuple_ind hunif hτ hT
  refine ⟨![A₁, A₂, A₃, A₄, A₅, A₆, A₇], ?_, fun x => ?_⟩
  · intro i
    fin_cases i <;> simpa
  · have key : (Finset.univ.filter (fun i => x ∈ ![A₁, A₂, A₃, A₄, A₅, A₆, A₇] i)).card =
        ∑ i, ind (![A₁, A₂, A₃, A₄, A₅, A₆, A₇] i) x := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      unfold ind
      split_ifs <;> rfl
    rw [key, Fin.sum_univ_seven]
    exact h x

/-- **Corollary 4.** If every point lies in at most four of the seven sets `A i` and the pair
`{x, y}` meets all of them, then `x` or `y` lies in exactly four of them (the other point then
lies in each of the three remaining sets, by the covering hypothesis). Both lie in at least
three. -/
theorem flat_cover_shape {A : Fin 7 → Finset α}
    (hflat : ∀ x, (Finset.univ.filter (fun i => x ∈ A i)).card ≤ 4)
    {x y : α} (hxy : ∀ i, x ∈ A i ∨ y ∈ A i) :
    ((Finset.univ.filter (fun i => x ∈ A i)).card = 4 ∨
      (Finset.univ.filter (fun i => y ∈ A i)).card = 4) ∧
    3 ≤ (Finset.univ.filter (fun i => x ∈ A i)).card ∧
    3 ≤ (Finset.univ.filter (fun i => y ∈ A i)).card := by
  have hunion : (Finset.univ : Finset (Fin 7)) ⊆
      Finset.univ.filter (fun i => x ∈ A i) ∪ Finset.univ.filter (fun i => y ∈ A i) := by
    intro i _
    rcases hxy i with h | h
    · exact Finset.mem_union_left _ (by simp [h])
    · exact Finset.mem_union_right _ (by simp [h])
  have h7 := Finset.card_le_card hunion
  have hu := Finset.card_union_le (Finset.univ.filter (fun i => x ∈ A i))
    (Finset.univ.filter (fun i => y ∈ A i))
  have hx := hflat x
  have hy := hflat y
  simp only [Finset.card_univ, Fintype.card_fin] at h7
  omega

/-- Lemma 3 + Corollary 4 for a (7,2)-family: if `H` is `k`-uniform with property (7,2),
`τ(H) > T` and `3k ≤ 4T`, there are seven edges with all degrees `≤ 4`, covered by a pair
`{x, y}` in which `x` lies in exactly four of the edges and `y` in the other three. -/
theorem flat_tuple_cover {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hunif : IsUniform H k) (hτ : ¬ CoverableBy H T) (hT : 3 * k ≤ 4 * T) :
    ∃ A : Fin 7 → Finset α, (∀ i, A i ∈ H) ∧
      (∀ z, (Finset.univ.filter (fun i => z ∈ A i)).card ≤ 4) ∧
      ∃ x y : α, (Finset.univ.filter (fun i => x ∈ A i)).card = 4 ∧
        ∀ i, x ∈ A i ∨ y ∈ A i := by
  classical
  obtain ⟨A, hA, hflat⟩ := exists_flat_tuple hunif hτ hT
  refine ⟨A, hA, hflat, ?_⟩
  have hG : (Finset.univ.image A) ⊆ H := by
    intro B hB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
    exact hA i
  have hGc : (Finset.univ.image A).card ≤ 7 := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin 7))) (f := A))
  have hGne : (Finset.univ.image A).Nonempty := ⟨A 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  obtain ⟨x, y, hxy⟩ := (coverableBy_two_iff hGne).1 (hprop _ hG hGc)
  have hxy' : ∀ i, x ∈ A i ∨ y ∈ A i := fun i =>
    hxy (A i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  rcases (flat_cover_shape hflat hxy').1 with h | h
  · exact ⟨x, y, h, hxy'⟩
  · exact ⟨y, x, h, fun i => (hxy' i).symm⟩

end Erdos644
