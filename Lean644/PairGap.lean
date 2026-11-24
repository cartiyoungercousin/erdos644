import Lean644.TwoCores

/-!
# The pair gap (lex-min anchors)

Source: `notes/NEW_PATHS.md` §1.2 (Fable research lead); the gap itself is condition (9) of the
11/13 repository. Hand-checked.

Let `u` be such that every good triple has a pair cell of size `≥ u` (true for the largest cell
of a lex-min anchor). If two edges `A, B` meet in `t₀ < u` points, request
`(A∩B) ∪ D_A ∪ D_B` with `D_A ⊆ A ∖ B`, `D_B ⊆ B ∖ A`, `|D_A| = |D_B| = (k + 1 - t₀ - u)₊`;
the response `K` forms a good triple `(A, B, K)` with all three cells `< u`, a contradiction,
as long as the request has at most `T` points. Hence no pair intersection lies in
`[2k - 2u - T + 2, u)`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Pair gap.** -/
theorem pair_gap {H : Finset (Finset α)} {T k u : ℕ} (hτ : ¬ CoverableBy H T)
    (hunif : IsUniform H k)
    (hlex : ∀ E ∈ H, ∀ F ∈ H, ∀ G ∈ H, IsGoodTriple E F G →
      u ≤ (E ∩ F).card ∨ u ≤ (E ∩ G).card ∨ u ≤ (F ∩ G).card)
    {A B : Finset α} (hA : A ∈ H) (hB : B ∈ H) (hlt : (A ∩ B).card < u)
    (hge : 2 * k + 2 ≤ (A ∩ B).card + 2 * u + T) (hu : u ≤ k) (huT : u ≤ T) : False := by
  set t₀ := (A ∩ B).card with ht₀
  have kA := hunif A hA
  have kB := hunif B hB
  have eA : (A \ B).card + t₀ = k := by rw [← kA]; exact Finset.card_sdiff_add_card_inter A B
  have eB : (B \ A).card + t₀ = k := by
    rw [← kB, ht₀, Finset.inter_comm]; exact Finset.card_sdiff_add_card_inter B A
  obtain ⟨DA, hDA, cDA⟩ := Finset.exists_subset_card_eq
    (show k + 1 - t₀ - u ≤ (A \ B).card by omega)
  obtain ⟨DB, hDB, cDB⟩ := Finset.exists_subset_card_eq
    (show k + 1 - t₀ - u ≤ (B \ A).card by omega)
  obtain ⟨K, hK, dK⟩ := exists_response hτ (d := (A ∩ B) ∪ DA ∪ DB)
    ((card_union3_le _ _ _).trans (by omega))
  have nK : ∀ v ∈ K, v ∉ (A ∩ B) ∪ DA ∪ DB := fun v hv h => Finset.disjoint_left.1 dK hv h
  have hgood : IsGoodTriple A B K := by
    unfold IsGoodTriple; ext v
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    rintro ⟨a, b⟩ k'
    exact nK v k' (by simp [a, b])
  -- the traces of K on A and B are below u
  have tA : (A ∩ K).card < u := by
    have s : (A ∩ K) ∪ DA ∪ (A ∩ B) ⊆ A :=
      Finset.union_subset (Finset.union_subset Finset.inter_subset_left
        (hDA.trans Finset.sdiff_subset)) Finset.inter_subset_left
    have d1 : Disjoint (A ∩ K) DA := Finset.disjoint_left.2 fun v h1 h2 =>
      nK v (Finset.mem_inter.1 h1).2 (by simp [h2])
    have d2 : Disjoint ((A ∩ K) ∪ DA) (A ∩ B) := Finset.disjoint_left.2 fun v h1 h2 => by
      rcases Finset.mem_union.1 h1 with h | h
      · exact nK v (Finset.mem_inter.1 h).2 (by simp [h2])
      · exact (Finset.mem_sdiff.1 (hDA h)).2 (Finset.mem_inter.1 h2).2
    have := Finset.card_le_card s
    rw [card_union_disj d2, card_union_disj d1, kA] at this
    omega
  have tB : (B ∩ K).card < u := by
    have s : (B ∩ K) ∪ DB ∪ (A ∩ B) ⊆ B :=
      Finset.union_subset (Finset.union_subset Finset.inter_subset_left
        (hDB.trans Finset.sdiff_subset)) Finset.inter_subset_right
    have d1 : Disjoint (B ∩ K) DB := Finset.disjoint_left.2 fun v h1 h2 =>
      nK v (Finset.mem_inter.1 h1).2 (by simp [h2])
    have d2 : Disjoint ((B ∩ K) ∪ DB) (A ∩ B) := Finset.disjoint_left.2 fun v h1 h2 => by
      rcases Finset.mem_union.1 h1 with h | h
      · exact nK v (Finset.mem_inter.1 h).2 (by simp [h2])
      · exact (Finset.mem_sdiff.1 (hDB h)).2 (Finset.mem_inter.1 h2).1
    have := Finset.card_le_card s
    rw [card_union_disj d2, card_union_disj d1, kB] at this
    omega
  rcases hlex A hA B hB K hK hgood with h | h | h <;> omega

end Erdos644
