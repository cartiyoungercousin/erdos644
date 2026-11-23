import Lean644.Defs

/-!
# Frozen headline statements

Trust policy (notes/LEAN_POLICY.md): every statement here is approved by a human before any
proof work, and CI checks that this file's hash does not change afterwards. Proofs live in
other files and must prove these `Prop`s *exactly*.

## Six-sevenths bound (target of the current verification project)

Source being verified: cubres/erdos-644-research, manuscript `six_sevenths_v3.tex`
(commit e8e5f9347800214af49b9e363d8ea258bb1e5fb2), Theorem 1.1, range `k ≥ 7`.

Plain English: let `k ≥ 7`. Let `H` be a finite family of sets, each with exactly `k`
elements, such that every subfamily of **at most seven** members can be hit by some set of
at most two points. Then some set of at most `⌈6k/7⌉` points meets every member of `H`.

Notes on fidelity:
* "at most seven" (`HasPropertyAtMost`), not "exactly seven" — see `DefsTests.lean` for why
  the latter would make small cases false.
* `k ≥ 7`: for `2 ≤ k ≤ 6` the manuscript cites the 1992 result `f(k,6) = k`, which we have not
  obtained or verified; those cases are deliberately left out of this statement.
* `⌈6k/7⌉` is written with `Nat.ceil` over `ℚ` to match the paper's notation literally.
* The ground type `α` is arbitrary (any type with decidable equality).
-/

namespace Erdos644

/-- **Erdős #644, six-sevenths bound (k ≥ 7).** -/
def SixSeventhsStatement : Prop :=
  ∀ (α : Type) [DecidableEq α] (k : ℕ), 7 ≤ k →
    ∀ H : Finset (Finset α), IsUniform H k → HasPropertyAtMost H 7 2 →
      CoverableBy H ⌈(6 * k : ℚ) / 7⌉₊

end Erdos644
