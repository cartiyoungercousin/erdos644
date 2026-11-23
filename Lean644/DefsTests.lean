import Lean644.Defs

/-!
# Unit tests for the definitions (trust policy rule 3)

Each test is a fact we already know on paper. A mis-stated definition should break at least
one of them. Tests are checked by the kernel (`decide`), never by compiler-trusting tactics.
-/

namespace Erdos644

/-- Complements of the 7 lines `{i, i+1, i+3} (mod 7)` of the Fano plane on `Fin 7`.
These are the FKW obstruction for `k = 1`: seven 4-sets with no 2-point transversal. -/
def fanoComplements : Finset (Finset (Fin 7)) :=
  { {2, 4, 5, 6},   -- complement of {0,1,3}
    {0, 3, 5, 6},   -- complement of {1,2,4}
    {0, 1, 4, 6},   -- complement of {2,3,5}
    {0, 1, 2, 5},   -- complement of {3,4,6}
    {1, 2, 3, 6},   -- complement of {4,5,0}
    {0, 2, 3, 4},   -- complement of {5,6,1}
    {1, 3, 4, 5} }  -- complement of {6,0,2}

/-- Sanity: 7 distinct sets, each of size 4. -/
example : fanoComplements.card = 7 := by decide
example : IsUniform fanoComplements 4 := by decide

set_option maxRecDepth 8000 in
/-- NEGATIVE test: the Fano complements cannot be hit by 2 points (τ ≥ 3). -/
theorem fano_not_coverable_two : ¬ CoverableBy fanoComplements 2 := by
  rw [coverableBy_two_iff ⟨{2, 4, 5, 6}, by decide⟩]
  decide

set_option maxRecDepth 8000 in
/-- POSITIVE test: three points do suffice ({0,1,2} is not a Fano line), so τ = 3. -/
example : CoverableBy fanoComplements 3 :=
  ⟨{0, 1, 2}, by decide, by decide⟩

/-- Hence the complete 4-uniform family on 7 points fails property (7,2). -/
example : ¬ HasProperty ((Finset.univ : Finset (Fin 7)).powersetCard 4) 7 2 := by
  intro h
  refine fano_not_coverable_two (h fanoComplements ?_ (by decide))
  intro A hA
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, (by decide : IsUniform fanoComplements 4) A hA⟩

/-! ### The two conventions for property (p,t) differ on small families

Three pairwise disjoint 2-sets: the "exactly 7" property holds vacuously (there is no
7-member subfamily), but the "at most 7" property fails (the family itself needs 3 points).
With `k = 2` this family has τ = 3 > ⌈6·2/7⌉ = 2, so stating the 6/7 theorem with the
"exactly" convention would be FALSE. -/

def threeDisjointPairs : Finset (Finset (Fin 6)) := {{0, 1}, {2, 3}, {4, 5}}

example : HasProperty threeDisjointPairs 7 2 := by
  intro G hG hcard
  have h1 := Finset.card_le_card hG
  have h2 : threeDisjointPairs.card = 3 := by decide
  omega

set_option maxRecDepth 8000 in
example : ¬ HasPropertyAtMost threeDisjointPairs 7 2 := by
  intro h
  have h3 := h threeDisjointPairs subset_rfl (by decide)
  rw [coverableBy_two_iff ⟨{0, 1}, by decide⟩] at h3
  revert h3
  decide

/-- POSITIVE test of `HasProperty`: a star (all 3-sets through point 0) has property (7,1). -/
example : HasProperty (((Finset.univ : Finset (Fin 5)).powersetCard 3).filter (0 ∈ ·)) 7 1 := by
  intro G hG _
  refine ⟨{0}, by simp, fun A hA => ⟨0, ?_⟩⟩
  have := (Finset.mem_filter.1 (hG hA)).2
  simp [this]

end Erdos644
