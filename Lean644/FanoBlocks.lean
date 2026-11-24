import Lean644.Fano
import Lean644.Framework

/-!
# Mandatory blocks (Fano-nerve criterion in sequential form; TWIN.md §7.5)

Seven sets `B 0, …, B 6` are labelled so that the triples
`012, 034, 056, 135, 146, 236, 245` are the lines of a Fano plane (these are exactly the triples
`fanoPencil p` of `Lean644/Fano.lean`). If every line has empty common intersection there is no
2-point transversal (`fano_criterion`). Reading the lines by their largest index gives the
*mandatory blocks*

  `M₂ = B₀ ∩ B₁`, `M₄ = B₀ ∩ B₃`, `M₅ = (B₁ ∩ B₃) ∪ (B₂ ∩ B₄)`,
  `M₆ = (B₀ ∩ B₅) ∪ (B₁ ∩ B₄) ∪ (B₂ ∩ B₃)`  (`M₀ = M₁ = M₃ = ∅`),

and the criterion says: if each `B c` is disjoint from `M_c` (i.e. `M_c` was requested when `B c`
was the reply), the seven sets have no 2-point transversal (`fano_blocks`).
Consequently, in a (7,2)-family with `τ > T`, six edges that respect the blocks `M₂, M₄, M₅` have
`|M₆| > T` (`mandatory_block_large`): the last block cannot be requested.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Mandatory-block criterion.** -/
theorem fano_blocks (B : Fin 7 → Finset α)
    (h2 : Disjoint (B 2) (B 0 ∩ B 1)) (h4 : Disjoint (B 4) (B 0 ∩ B 3))
    (h5 : Disjoint (B 5) (B 1 ∩ B 3 ∪ B 2 ∩ B 4))
    (h6 : Disjoint (B 6) (B 0 ∩ B 5 ∪ B 1 ∩ B 4 ∪ B 2 ∩ B 3)) :
    ¬ CoverableBy (Finset.univ.image B) 2 := by
  apply fano_criterion
  intro p v
  fin_cases p
  · rintro ⟨ha, hb, hc⟩
    have ha : v ∈ B 0 := ha
    have hb : v ∈ B 1 := hb
    have hc : v ∈ B 2 := hc
    exact Finset.disjoint_left.1 h2 hc (Finset.mem_inter.2 ⟨ha, hb⟩)
  · rintro ⟨ha, hb, hc⟩
    have ha : v ∈ B 0 := ha
    have hb : v ∈ B 3 := hb
    have hc : v ∈ B 4 := hc
    exact Finset.disjoint_left.1 h4 hc (Finset.mem_inter.2 ⟨ha, hb⟩)
  · rintro ⟨ha, hb, hc⟩
    have ha : v ∈ B 0 := ha
    have hb : v ∈ B 5 := hb
    have hc : v ∈ B 6 := hc
    exact Finset.disjoint_left.1 h6 hc (by simp [ha, hb])
  · rintro ⟨ha, hb, hc⟩
    have ha : v ∈ B 1 := ha
    have hb : v ∈ B 3 := hb
    have hc : v ∈ B 5 := hc
    exact Finset.disjoint_left.1 h5 hc (by simp [ha, hb])
  · rintro ⟨ha, hb, hc⟩
    have ha : v ∈ B 1 := ha
    have hb : v ∈ B 4 := hb
    have hc : v ∈ B 6 := hc
    exact Finset.disjoint_left.1 h6 hc (by simp [ha, hb])
  · rintro ⟨ha, hb, hc⟩
    have ha : v ∈ B 2 := ha
    have hb : v ∈ B 3 := hb
    have hc : v ∈ B 6 := hc
    exact Finset.disjoint_left.1 h6 hc (by simp [ha, hb])
  · rintro ⟨ha, hb, hc⟩
    have ha : v ∈ B 2 := ha
    have hb : v ∈ B 4 := hb
    have hc : v ∈ B 5 := hc
    exact Finset.disjoint_left.1 h5 hc (by simp [ha, hb])

/-- In a (7,2)-family with `τ > T`: if six edges respect the mandatory blocks `M₂, M₄, M₅`, the
last block `M₆` has more than `T` points (otherwise it could be requested, and the response would
complete a 7-tuple without 2-point transversal). -/
theorem mandatory_block_large {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T : ℕ}
    (hτ : ¬ CoverableBy H T) {B₀ B₁ B₂ B₃ B₄ B₅ : Finset α}
    (h₀ : B₀ ∈ H) (h₁ : B₁ ∈ H) (h₂ : B₂ ∈ H) (h₃ : B₃ ∈ H) (h₄ : B₄ ∈ H) (h₅ : B₅ ∈ H)
    (hM2 : Disjoint B₂ (B₀ ∩ B₁)) (hM4 : Disjoint B₄ (B₀ ∩ B₃))
    (hM5 : Disjoint B₅ (B₁ ∩ B₃ ∪ B₂ ∩ B₄)) :
    T < (B₀ ∩ B₅ ∪ B₁ ∩ B₄ ∪ B₂ ∩ B₃).card := by
  classical
  by_contra hcard
  obtain ⟨B₆, h₆, hM6⟩ := exists_response hτ (Nat.le_of_not_lt hcard)
  have hBH : ∀ i, ![B₀, B₁, B₂, B₃, B₄, B₅, B₆] i ∈ H := by
    intro i
    fin_cases i
    exacts [h₀, h₁, h₂, h₃, h₄, h₅, h₆]
  have hG : (Finset.univ.image ![B₀, B₁, B₂, B₃, B₄, B₅, B₆]) ⊆ H := by
    intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    exact hBH i
  have hGc : (Finset.univ.image ![B₀, B₁, B₂, B₃, B₄, B₅, B₆]).card ≤ 7 := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin 7)))
      (f := ![B₀, B₁, B₂, B₃, B₄, B₅, B₆]))
  exact fano_blocks ![B₀, B₁, B₂, B₃, B₄, B₅, B₆] hM2 hM4 hM5 hM6 (hprop _ hG hGc)

end Erdos644
