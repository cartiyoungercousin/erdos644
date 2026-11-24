import Lean644.Defs

/-!
# The Fano criterion

Source: `notes/NEW_PATHS.md` §8.1 (Fable research lead); hand-checked.

Seven edges indexed by the lines of the Fano plane have no 2-point transversal as soon as, for
every point `p` of the plane, the three edges on the lines through `p` have empty common
intersection. Lines (points `0..6`): `ℓ₀ = 012, ℓ₁ = 034, ℓ₂ = 056, ℓ₃ = 135, ℓ₄ = 146,
ℓ₅ = 236, ℓ₆ = 245`; the pencil of point `p` is the set of lines through `p`.
The combinatorial core is a statement about two Boolean vectors, checked by `decide`.
-/

namespace Erdos644

/-- The pencils of the Fano plane: the three lines through each point. -/
def fanoPencil : Fin 7 → Fin 7 × Fin 7 × Fin 7
  | 0 => (0, 1, 2) | 1 => (0, 3, 4) | 2 => (0, 5, 6) | 3 => (1, 3, 5)
  | 4 => (1, 4, 6) | 5 => (2, 3, 6) | 6 => (2, 4, 5)

set_option maxRecDepth 100000 in
/-- Boolean core: no two "membership vectors" that each miss a line of every pencil can
together cover all seven lines. -/
theorem fano_bool : ∀ a b : Fin 7 → Bool,
    (∀ p : Fin 7, ¬ (a (fanoPencil p).1 = true ∧ a (fanoPencil p).2.1 = true ∧
      a (fanoPencil p).2.2 = true)) →
    (∀ p : Fin 7, ¬ (b (fanoPencil p).1 = true ∧ b (fanoPencil p).2.1 = true ∧
      b (fanoPencil p).2.2 = true)) →
    ¬ (∀ i : Fin 7, a i = true ∨ b i = true) := by
  decide

variable {α : Type*} [DecidableEq α]

/-- **Fano criterion.** -/
theorem fano_criterion (L : Fin 7 → Finset α)
    (hconc : ∀ p : Fin 7, ∀ v, ¬ (v ∈ L (fanoPencil p).1 ∧ v ∈ L (fanoPencil p).2.1 ∧
      v ∈ L (fanoPencil p).2.2)) :
    ¬ CoverableBy (Finset.univ.image L) 2 := by
  rw [coverableBy_two_iff ⟨L 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩]
  rintro ⟨x, y, hxy⟩
  refine fano_bool (fun i => decide (x ∈ L i)) (fun i => decide (y ∈ L i)) ?_ ?_ ?_
  · intro p h; simp only [decide_eq_true_eq] at h; exact hconc p x h
  · intro p h; simp only [decide_eq_true_eq] at h; exact hconc p y h
  · intro i
    simpa only [decide_eq_true_eq] using hxy (L i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))

end Erdos644
