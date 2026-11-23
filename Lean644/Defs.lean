import Mathlib

/-!
# Basic definitions for Erdős Problem #644

Following Fon-Der-Flaass–Kostochka–Woodall (1999):
* a *transversal* of a family `F` of sets is a set meeting every member of `F`;
* `F` has *property (p,t)* if every subfamily of `F` with exactly `p` members has a
  transversal of size at most `t`.

Erdős #644 asks about the largest transversal number of an `r`-uniform family with
property `(7,2)`. Instead of defining `τ` as a number we use `CoverableBy F t`
("τ(F) ≤ t"), which keeps statements free of `sSup`/`Nat.find` subtleties.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- `T` meets every member of `F`. -/
def IsTransversal (F : Finset (Finset α)) (T : Finset α) : Prop :=
  ∀ A ∈ F, (A ∩ T).Nonempty

/-- `τ(F) ≤ t`: some set of at most `t` points meets every member of `F`. -/
def CoverableBy (F : Finset (Finset α)) (t : ℕ) : Prop :=
  ∃ T : Finset α, T.card ≤ t ∧ IsTransversal F T

/-- Property `(p,t)` of FKW99: every subfamily with exactly `p` members has `τ ≤ t`. -/
def HasProperty (F : Finset (Finset α)) (p t : ℕ) : Prop :=
  ∀ G ⊆ F, G.card = p → CoverableBy G t

/-- Property `(p,t)` in the **"at most"** convention (Erdős–Hajnal–Tuza; used by the 6/7
manuscript and by Bucić–Korándi–Sudakov): every subfamily with *at most* `p` members has
`τ ≤ t`. Unlike `HasProperty`, this is not vacuous for families with fewer than `p` members.
See `DefsTests.lean` for an example separating the two conventions. -/
def HasPropertyAtMost (F : Finset (Finset α)) (p t : ℕ) : Prop :=
  ∀ G ⊆ F, G.card ≤ p → CoverableBy G t

/-- All members of `F` have exactly `r` elements. -/
def IsUniform (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∀ A ∈ F, A.card = r

/-! ## Decidability (so small examples can be checked by `decide`) -/

instance [Fintype α] (F : Finset (Finset α)) (T : Finset α) : Decidable (IsTransversal F T) := by
  unfold IsTransversal; infer_instance

instance [Fintype α] (F : Finset (Finset α)) (t : ℕ) : Decidable (CoverableBy F t) := by
  unfold CoverableBy; infer_instance

instance (F : Finset (Finset α)) (r : ℕ) : Decidable (IsUniform F r) := by
  unfold IsUniform; infer_instance

/-! ## Two-point covers

`τ(F) ≤ 2` for a nonempty family is the same as: some two (not necessarily distinct) points
`x, y` such that every member contains `x` or `y`. This is the "signature/miss-pattern"
reformulation used throughout the notes. -/

theorem coverableBy_two_iff {F : Finset (Finset α)} (hF : F.Nonempty) :
    CoverableBy F 2 ↔ ∃ x y : α, ∀ A ∈ F, x ∈ A ∨ y ∈ A := by
  constructor
  · rintro ⟨T, hT, htr⟩
    obtain ⟨A₀, hA₀⟩ := hF
    obtain ⟨z, hz⟩ := htr A₀ hA₀
    have hzT : z ∈ T := (Finset.mem_inter.1 hz).2
    have hpos : 0 < T.card := Finset.card_pos.2 ⟨z, hzT⟩
    interval_cases h : T.card
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
      refine ⟨a, a, fun A hA => ?_⟩
      obtain ⟨w, hw⟩ := htr A hA
      simp only [Finset.mem_inter, Finset.mem_singleton] at hw
      exact Or.inl (hw.2 ▸ hw.1)
    · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.1 h
      refine ⟨a, b, fun A hA => ?_⟩
      obtain ⟨w, hw⟩ := htr A hA
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with ⟨hwA, rfl | rfl⟩
      · exact Or.inl hwA
      · exact Or.inr hwA
  · rintro ⟨x, y, h⟩
    refine ⟨{x, y}, Finset.card_le_two, fun A hA => ?_⟩
    rcases h A hA with hx | hy
    · exact ⟨x, by simp [hx]⟩
    · exact ⟨y, by simp [hy]⟩

end Erdos644
