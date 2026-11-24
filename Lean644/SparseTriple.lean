import Lean644.TheoremA
import Lean644.SplitA

/-!
# Sparse-triple lemma

Source: `notes/FRESH_A.md` (fresh Fable agent A, 2026-11-24); hand-checked.

Let `(E, F, G)` be a good triple, `P = (E∩F) ∪ (E∩G) ∪ (F∩G)`, `S = |E∩F| + |E∩G| + |F∩G|`.
If `τ(H) > T` and `k + 3S ≤ 3T`: request `P` (response `A₁`), then three times `P` plus
`T - |P|` points of the running intersection (or all of it). Then `A₁ ∩ A₂ ∩ A₃ ∩ A₄ = ∅`; a
2-cover of `E, F, G` has a point in `P`, which misses every `Aᵢ`, so the other point lies in all
four: impossible. Hence every good triple satisfies `3T < k + 3S`, i.e. `S > T - k/3`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- One shrinking request: the response avoids `P` and meets `C` in at most
`|C| - (T - |P|)` points (truncated). -/
theorem shrink_step {H : Finset (Finset α)} {T : ℕ} (hτ : ¬ CoverableBy H T)
    (P C : Finset α) (hP : P.card ≤ T) :
    ∃ A ∈ H, Disjoint A P ∧ (A ∩ C).card ≤ C.card - (T - P.card) := by
  by_cases hc : T - P.card ≤ C.card
  · obtain ⟨D, hD, cD⟩ := Finset.exists_subset_card_eq hc
    obtain ⟨A, hA, dA⟩ := exists_response hτ (d := P ∪ D)
      ((Finset.card_union_le _ _).trans (by omega))
    refine ⟨A, hA, Finset.disjoint_of_subset_right Finset.subset_union_left dA, ?_⟩
    have d : Disjoint (A ∩ C) D := Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.subset_union_right dA)
    have := Finset.card_le_card (Finset.union_subset (Finset.inter_subset_right : A ∩ C ⊆ C) hD)
    rw [card_union_disj d, cD] at this; omega
  · obtain ⟨A, hA, dA⟩ := exists_response hτ (d := P ∪ C)
      ((Finset.card_union_le _ _).trans (by omega))
    refine ⟨A, hA, Finset.disjoint_of_subset_right Finset.subset_union_left dA, ?_⟩
    have : A ∩ C = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty]
      exact Finset.disjoint_of_subset_right Finset.subset_union_right dA
    rw [this, Finset.card_empty]; exact Nat.zero_le _

/-- **Sparse-triple lemma.** -/
theorem sparse_triple {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (hS : k + 3 * ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card) ≤ 3 * T) : False := by
  set P := (E ∩ F) ∪ (E ∩ G) ∪ (F ∩ G) with hPdef
  have cP : P.card ≤ (E ∩ F).card + (E ∩ G).card + (F ∩ G).card := card_union3_le _ _ _
  have hP : P.card ≤ T := by omega
  obtain ⟨A₁, h₁, d₁⟩ := exists_response hτ hP
  have k₁ := hunif A₁ h₁
  obtain ⟨A₂, h₂, d₂, c₂⟩ := shrink_step hτ P A₁ hP
  obtain ⟨A₃, h₃, d₃, c₃⟩ := shrink_step hτ P (A₁ ∩ A₂) hP
  obtain ⟨A₄, h₄, d₄, c₄⟩ := shrink_step hτ P (A₁ ∩ A₂ ∩ A₃) hP
  have e2 : A₂ ∩ A₁ = A₁ ∩ A₂ := Finset.inter_comm _ _
  have e3 : A₃ ∩ (A₁ ∩ A₂) = A₁ ∩ A₂ ∩ A₃ := by rw [Finset.inter_comm]
  have e4 : A₄ ∩ (A₁ ∩ A₂ ∩ A₃) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ := by rw [Finset.inter_comm]
  rw [e2, k₁] at c₂; rw [e3] at c₃; rw [e4] at c₄
  have empty : (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card = 0 := by omega
  rw [Finset.card_eq_zero] at empty
  -- the seven edges
  set G7 : Finset (Finset α) := {E, F, G, A₁, A₂, A₃, A₄} with hG7
  have hsub : G7 ⊆ H := by
    intro B hB; simp only [hG7, Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard : G7.card ≤ 7 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  obtain ⟨x, y, hxy⟩ := (coverableBy_two_iff ⟨E, by simp [hG7]⟩).1 (hprop G7 hsub hcard)
  have cE := hxy E (by simp [hG7])
  have cF := hxy F (by simp [hG7])
  have cG := hxy G (by simp [hG7])
  have c1 := hxy A₁ (by simp [hG7])
  have c2 := hxy A₂ (by simp [hG7])
  have c3 := hxy A₃ (by simp [hG7])
  have c4 := hxy A₄ (by simp [hG7])
  -- the point in P misses every Aᵢ, so the other point is in all four
  have finish : ∀ p q, p ∈ P → (p ∈ A₁ ∨ q ∈ A₁) → (p ∈ A₂ ∨ q ∈ A₂) → (p ∈ A₃ ∨ q ∈ A₃) →
      (p ∈ A₄ ∨ q ∈ A₄) → False := by
    intro p q hp a1 a2 a3 a4
    have n1 : p ∉ A₁ := fun h => Finset.disjoint_left.1 d₁ h hp
    have n2 : p ∉ A₂ := fun h => Finset.disjoint_left.1 d₂ h hp
    have n3 : p ∉ A₃ := fun h => Finset.disjoint_left.1 d₃ h hp
    have n4 : p ∉ A₄ := fun h => Finset.disjoint_left.1 d₄ h hp
    have hq : q ∈ A₁ ∩ A₂ ∩ A₃ ∩ A₄ := by
      simp only [Finset.mem_inter]
      exact ⟨⟨⟨a1.resolve_left n1, a2.resolve_left n2⟩, a3.resolve_left n3⟩, a4.resolve_left n4⟩
    rw [empty] at hq; simp at hq
  rcases triple_candidate hgood cE cF cG with
    ⟨a, b, -⟩ | ⟨a, b, -⟩ | ⟨a, b, -⟩ | ⟨a, b, -⟩ | ⟨a, b, -⟩ | ⟨a, b, -⟩
  · exact finish x y (by simp [P, a, b]) c1 c2 c3 c4
  · exact finish x y (by simp [P, a, b]) c1 c2 c3 c4
  · exact finish x y (by simp [P, a, b]) c1 c2 c3 c4
  · exact finish y x (by simp [P, a, b]) c1.symm c2.symm c3.symm c4.symm
  · exact finish y x (by simp [P, a, b]) c1.symm c2.symm c3.symm c4.symm
  · exact finish y x (by simp [P, a, b]) c1.symm c2.symm c3.symm c4.symm

end Erdos644
