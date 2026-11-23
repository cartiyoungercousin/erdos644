import Lean644.Framework
import Lean644.Triple

/-!
# Lemma A (sparser triple), from the R1 game

Source: `notes/R1_RESULTS.md` §4.4 (R1 research agent, 2026-11-23); hand-checked 2026-11-23.

Let `τ(H) > T`, and let `E, G ∈ H` with `Y = E ∩ G`, `y = |Y|`. Request
`D = Y ∪ D_E ∪ D_G` with `D_E ⊆ E ∖ G`, `D_G ⊆ G ∖ E` of sizes `⌊(T-y)/2⌋`, `⌈(T-y)/2⌉`.
The response `K` misses `Y`, so `(E, G, K)` is a good triple, and its two new pair cells
`E ∩ K`, `G ∩ K` are small.

**Lemma A.** If moreover `E ∩ F` (size `x`) is a pair cell with `y ≤ x ≤ k/2`, `k/2 ≤ T ≤ k`
and `x + 2y + T ≥ 2k + 2`, then `(E, G, K)` has all pair cells `≤ k/2` and every two of its pair
cells sum to less than `x + y`. So a good triple minimizing the sum of its two largest pair cells
(among those with all cells `≤ k/2`) satisfies `x + 2y + T ≤ 2k + 1`.

Note: only `τ(H) > T` is used (one request), not property (7,2).
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- The response to `D = (E ∩ G) ∪ D_E ∪ D_G` forms a good triple with `E, G` whose new pair
cells are small. -/
theorem sparser_response {H : Finset (Finset α)} {T k : ℕ} (hτ : ¬ CoverableBy H T)
    (hunif : IsUniform H k) {E G : Finset α} (hE : E ∈ H) (hG : G ∈ H)
    (hyT : (E ∩ G).card ≤ T) (hTk : T ≤ k) :
    ∃ K ∈ H, IsGoodTriple E G K ∧
      2 * (E ∩ K).card + (E ∩ G).card + T ≤ 2 * k + 1 ∧
      2 * (G ∩ K).card + (E ∩ G).card + T ≤ 2 * k + 1 ∧
      (E ∩ K).card + (G ∩ K).card + (E ∩ G).card + T ≤ 2 * k := by
  have sE : (E \ G).card + (E ∩ G).card = k := by
    rw [← hunif E hE]; exact Finset.card_sdiff_add_card_inter E G
  have sG : (G \ E).card + (E ∩ G).card = k := by
    rw [← hunif G hG, Finset.inter_comm E G]; exact Finset.card_sdiff_add_card_inter G E
  obtain ⟨DE, hDE, cDE⟩ := Finset.exists_subset_card_eq
    (show (T - (E ∩ G).card) / 2 ≤ (E \ G).card by omega)
  obtain ⟨DG, hDG, cDG⟩ := Finset.exists_subset_card_eq
    (show (T - (E ∩ G).card) - (T - (E ∩ G).card) / 2 ≤ (G \ E).card by omega)
  have cD : ((E ∩ G) ∪ DE ∪ DG).card ≤ T :=
    (Finset.card_union_le _ _).trans <|
      (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans (by omega)
  obtain ⟨K, hK, hdisj⟩ := exists_response hτ cD
  have miss : ∀ v ∈ K, v ∉ (E ∩ G) ∪ DE ∪ DG := fun v hv => Finset.disjoint_left.1 hdisj hv
  -- E ∩ K lies in (E \ G) \ DE
  have subE : E ∩ K ⊆ (E \ G) \ DE := by
    intro v hv
    rw [Finset.mem_inter] at hv
    have h := miss v hv.2
    simp only [Finset.mem_union, Finset.mem_inter, not_or, not_and] at h
    exact Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hv.1, h.1.1 hv.1⟩, h.1.2⟩
  have subG : G ∩ K ⊆ (G \ E) \ DG := by
    intro v hv
    rw [Finset.mem_inter] at hv
    have h := miss v hv.2
    simp only [Finset.mem_union, Finset.mem_inter, not_or, not_and] at h
    exact Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hv.1, fun hE' => h.1.1 hE' hv.1⟩, h.2⟩
  have bE := (Finset.card_le_card subE).trans_eq rfl
  have bG := (Finset.card_le_card subG).trans_eq rfl
  have eE := Finset.card_sdiff_add_card_eq_card hDE
  have eG := Finset.card_sdiff_add_card_eq_card hDG
  refine ⟨K, hK, ?_, by omega, by omega, by omega⟩
  -- good triple: K misses E ∩ G
  unfold IsGoodTriple
  ext v
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
  rintro ⟨hvE, hvG⟩ hvK
  exact miss v hvK (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_inter.2 ⟨hvE, hvG⟩)))

/-- **Lemma A (sparser triple).** With `x = |E ∩ F|`, `y = |E ∩ G|`, `y ≤ x ≤ k/2`,
`k/2 ≤ T ≤ k` and `x + 2y + T ≥ 2k + 2`, there is a good triple `(E, G, K)` with all three
pair cells `≤ k/2` and each two of them summing to less than `x + y`. -/
theorem lemmaA {H : Finset (Finset α)} {T k : ℕ} (hτ : ¬ CoverableBy H T)
    (hunif : IsUniform H k) {E F G : Finset α} (hE : E ∈ H) (hG : G ∈ H)
    (hTk : T ≤ k) (hkT : k ≤ 2 * T) (hyx : (E ∩ G).card ≤ (E ∩ F).card)
    (hx : 2 * (E ∩ F).card ≤ k)
    (hbig : 2 * k + 2 ≤ (E ∩ F).card + 2 * (E ∩ G).card + T) :
    ∃ K ∈ H, IsGoodTriple E G K ∧
      2 * (E ∩ G).card ≤ k ∧ 2 * (E ∩ K).card ≤ k ∧ 2 * (G ∩ K).card ≤ k ∧
      (E ∩ G).card + (E ∩ K).card < (E ∩ F).card + (E ∩ G).card ∧
      (E ∩ G).card + (G ∩ K).card < (E ∩ F).card + (E ∩ G).card ∧
      (E ∩ K).card + (G ∩ K).card < (E ∩ F).card + (E ∩ G).card := by
  obtain ⟨K, hK, hgood, h1, h2, h3⟩ :=
    sparser_response hτ hunif hE hG (by omega) hTk
  exact ⟨K, hK, hgood, by omega, by omega, by omega, by omega, by omega, by omega⟩

end Erdos644
