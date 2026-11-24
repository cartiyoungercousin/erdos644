import Lean644.Framework

/-!
# Gap lemma (TWIN.md §14.2, S1), with a general cap `c`

`H` is `k`-uniform with `τ(H) > T`. Let `Bi, Bj ∈ H`, `p = |Bi ∩ Bj|`. If `p ≤ c`, `p ≤ T` and
`2k ≤ p + 2c + T` (in scaled units with `c = t²`: `λ_t = 2 - 2t² - t ≤ p ≤ t²`), then one more
request gives an edge `Bl` with `Bi ∩ Bj ∩ Bl = ∅`, `|Bi ∩ Bl| ≤ c` and `|Bj ∩ Bl| ≤ c`:
an anchor triple all of whose pair-intersections are at most `c`.
The request is `Bi ∩ Bj` together with `k - c - p` points of each of `Bi \ Bj`, `Bj \ Bi`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- One side of the gap lemma: if `S ⊆ Bi \ Bj` and `Bl` avoids `Bi ∩ Bj` and `S`, then
`Bi ∩ Bl ⊆ (Bi \ Bj) \ S`. -/
theorem gap_side {Bi Bj Bl S : Finset α} (h1 : Disjoint Bl (Bi ∩ Bj)) (h2 : Disjoint Bl S) :
    Bi ∩ Bl ⊆ (Bi \ Bj) \ S := by
  intro x hx
  obtain ⟨hxi, hxl⟩ := Finset.mem_inter.1 hx
  refine Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hxi, fun hxj => ?_⟩, fun hxS => ?_⟩
  · exact Finset.disjoint_left.1 h1 hxl (Finset.mem_inter.2 ⟨hxi, hxj⟩)
  · exact Finset.disjoint_left.1 h2 hxl hxS

/-- **Gap lemma (S1).** -/
theorem gap_anchor {H : Finset (Finset α)} {T k c : ℕ} (hunif : IsUniform H k)
    (hτ : ¬ CoverableBy H T) {Bi Bj : Finset α} (hi : Bi ∈ H) (hj : Bj ∈ H)
    (hpc : (Bi ∩ Bj).card ≤ c) (hpT : (Bi ∩ Bj).card ≤ T)
    (hgap : 2 * k ≤ (Bi ∩ Bj).card + 2 * c + T) :
    ∃ Bl ∈ H, Bi ∩ Bj ∩ Bl = ∅ ∧ (Bi ∩ Bl).card ≤ c ∧ (Bj ∩ Bl).card ≤ c := by
  have hci : (Bi \ Bj).card = k - (Bi ∩ Bj).card := by
    have h := Finset.card_sdiff_add_card_inter Bi Bj
    have := hunif Bi hi
    omega
  have hcj : (Bj \ Bi).card = k - (Bi ∩ Bj).card := by
    have h := Finset.card_sdiff_add_card_inter Bj Bi
    have := hunif Bj hj
    rw [Finset.inter_comm Bj Bi] at h
    omega
  obtain ⟨Si, hSi, hSic⟩ := Finset.exists_subset_card_eq
    (show k - c - (Bi ∩ Bj).card ≤ (Bi \ Bj).card by omega)
  obtain ⟨Sj, hSj, hSjc⟩ := Finset.exists_subset_card_eq
    (show k - c - (Bi ∩ Bj).card ≤ (Bj \ Bi).card by omega)
  have hScard : (Bi ∩ Bj ∪ Si ∪ Sj).card ≤ T := by
    have h1 := Finset.card_union_le (Bi ∩ Bj ∪ Si) Sj
    have h2 := Finset.card_union_le (Bi ∩ Bj) Si
    omega
  obtain ⟨Bl, hl, hdisj⟩ := exists_response hτ hScard
  have hd0 : Disjoint Bl (Bi ∩ Bj) :=
    hdisj.mono_right (Finset.subset_union_left.trans Finset.subset_union_left)
  have hdi : Disjoint Bl Si :=
    hdisj.mono_right (Finset.subset_union_right.trans Finset.subset_union_left)
  have hdj : Disjoint Bl Sj := hdisj.mono_right Finset.subset_union_right
  have hd0' : Disjoint Bl (Bj ∩ Bi) := by rwa [Finset.inter_comm]
  refine ⟨Bl, hl, ?_, ?_, ?_⟩
  · exact Finset.disjoint_iff_inter_eq_empty.1 hd0.symm
  · have h := Finset.card_le_card (gap_side hd0 hdi)
    rw [Finset.card_sdiff_of_subset hSi, hci, hSic] at h
    omega
  · have h := Finset.card_le_card (gap_side hd0' hdj)
    rw [Finset.card_sdiff_of_subset hSj, hcj, hSjc] at h
    omega

end Erdos644
