import Lean644.Statements

/-!
# Bridge between the two conventions

`six_sevenths_erdos_wording_of`: the "at most seven" statement (the manuscript's) implies the
"exactly seven" statement (Erdős's). For `k ≥ 7`:
* a family with fewer than 7 members is hit by one point per member, i.e. `≤ 6 ≤ ⌈6k/7⌉` points;
* a family with at least 7 members has the "exactly 7" property iff the "at most 7" one, since
  every small subfamily sits inside a 7-member subfamily and covering is monotone.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- Covering a bigger family covers a smaller one. -/
theorem CoverableBy.mono {F G : Finset (Finset α)} {t : ℕ} (hGF : G ⊆ F)
    (h : CoverableBy F t) : CoverableBy G t := by
  obtain ⟨T, hT, htr⟩ := h
  exact ⟨T, hT, fun A hA => htr A (hGF hA)⟩

/-- With at least `p` members, the "exactly p" property gives the "at most p" property. -/
theorem HasProperty.atMost {F : Finset (Finset α)} {p t : ℕ} (h : HasProperty F p t)
    (hF : p ≤ F.card) : HasPropertyAtMost F p t := by
  intro G hGF hG
  obtain ⟨U, hGU, hUF, hU⟩ := Finset.exists_subsuperset_card_eq hGF hG hF
  exact (h U hUF hU).mono hGU

/-- A family of nonempty sets can be hit by at most `|F|` points (one per member). -/
theorem coverableBy_card {F : Finset (Finset α)} (hne : ∀ A ∈ F, A.Nonempty) :
    CoverableBy F F.card := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨A₀, hA₀⟩
  · exact ⟨∅, by simp, fun A hA => by simp at hA⟩
  obtain ⟨a₀, -⟩ := hne A₀ hA₀
  haveI : Nonempty α := ⟨a₀⟩
  choose! f hf using hne
  refine ⟨F.image f, Finset.card_image_le, fun A hA => ⟨f A, ?_⟩⟩
  exact Finset.mem_inter.2 ⟨hf A hA, Finset.mem_image_of_mem f hA⟩

theorem six_le_ceil {k : ℕ} (hk : 7 ≤ k) : 6 ≤ ⌈(6 * k : ℚ) / 7⌉₊ := by
  have : (5 : ℚ) < (6 * k : ℚ) / 7 := by
    have : (7 : ℚ) ≤ k := by exact_mod_cast hk
    rw [lt_div_iff₀ (by norm_num)]; linarith
  exact Nat.lt_ceil.2 (by exact_mod_cast this)

theorem CoverableBy.weaken {F : Finset (Finset α)} {s t : ℕ} (hst : s ≤ t)
    (h : CoverableBy F s) : CoverableBy F t := by
  obtain ⟨T, hT, htr⟩ := h
  exact ⟨T, hT.trans hst, htr⟩

/-- **Bridge.** The manuscript's statement implies the statement in Erdős's wording. -/
theorem six_sevenths_erdos_wording_of (h : SixSeventhsStatement) : SixSeventhsErdosWording := by
  intro α _ k hk H hunif hprop
  by_cases hcard : 7 ≤ H.card
  · exact h α k hk H hunif (hprop.atMost hcard)
  · have hne : ∀ A ∈ H, A.Nonempty := fun A hA =>
      Finset.card_pos.1 (by rw [hunif A hA]; omega)
    exact (coverableBy_card hne).weaken (by have := six_le_ceil hk; omega)

end Erdos644
