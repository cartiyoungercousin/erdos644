import Lean644.FourEdges
import Lean644.HallClose

/-!
# Adaptive closures (manuscript §4, proofs in Appendix A)

General helpers, then the lemmas one by one.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

theorem card_union_disj {s t : Finset α} (h : Disjoint s t) : (s ∪ t).card = s.card + t.card := by
  have := Finset.card_union_add_card_inter s t
  rw [Finset.disjoint_iff_inter_eq_empty.1 h] at this
  simpa using this

/-- If `K` avoids all three pair cells of a good triple, then (up to swapping) a pair meeting
`E, F, G, K` lies in `(E∩F) × (G∩K)`, `(E∩G) × (F∩K)` or `(F∩G) × (E∩K)`
(manuscript, "complementary products" at the start of Appendix A). -/
theorem no_core_candidate {E F G K : Finset α} (hgood : IsGoodTriple E F G)
    (hX : Disjoint K (E ∩ F)) (hY : Disjoint K (E ∩ G)) (hZ : Disjoint K (F ∩ G)) {x y : α}
    (hE : x ∈ E ∨ y ∈ E) (hF : x ∈ F ∨ y ∈ F) (hG : x ∈ G ∨ y ∈ G) (hK : x ∈ K ∨ y ∈ K) :
    (x ∈ E ∧ x ∈ F ∧ y ∈ G ∧ y ∈ K) ∨ (x ∈ E ∧ x ∈ G ∧ y ∈ F ∧ y ∈ K) ∨
    (x ∈ F ∧ x ∈ G ∧ y ∈ E ∧ y ∈ K) ∨
    (y ∈ E ∧ y ∈ F ∧ x ∈ G ∧ x ∈ K) ∨ (y ∈ E ∧ y ∈ G ∧ x ∈ F ∧ x ∈ K) ∨
    (y ∈ F ∧ y ∈ G ∧ x ∈ E ∧ x ∈ K) := by
  have nX : ∀ v, v ∈ K → v ∈ E → v ∈ F → False := fun v h1 h2 h3 =>
    Finset.disjoint_left.1 hX h1 (Finset.mem_inter.2 ⟨h2, h3⟩)
  have nY : ∀ v, v ∈ K → v ∈ E → v ∈ G → False := fun v h1 h2 h3 =>
    Finset.disjoint_left.1 hY h1 (Finset.mem_inter.2 ⟨h2, h3⟩)
  have nZ : ∀ v, v ∈ K → v ∈ F → v ∈ G → False := fun v h1 h2 h3 =>
    Finset.disjoint_left.1 hZ h1 (Finset.mem_inter.2 ⟨h2, h3⟩)
  rcases triple_candidate hgood hE hF hG with
    ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · rcases four_candidate_core a1 a2 a3 hK with h | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨_, h1, _, _⟩
    · exact (nX x h a1 a2).elim
    · exact (nY y h1 h2 a3).elim
    · exact (nZ y h1 h2 a3).elim
    · exact Or.inl ⟨a1, a2, a3, h1⟩
  · rcases four_candidate_core a1 a2 a3 hK with h | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨_, h1, _, _⟩
    · exact (nY x h a1 a2).elim
    · exact (nX y h1 h2 a3).elim
    · exact (nZ y h1 a3 h2).elim
    · exact Or.inr (Or.inl ⟨a1, a2, a3, h1⟩)
  · rcases four_candidate_core a1 a2 a3 hK with h | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨_, h1, _, _⟩
    · exact (nZ x h a1 a2).elim
    · exact (nX y h1 a3 h2).elim
    · exact (nY y h1 a3 h2).elim
    · exact Or.inr (Or.inr (Or.inl ⟨a1, a2, a3, h1⟩))
  · rcases four_candidate_core a1 a2 a3 hK.symm with h | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨_, h1, _, _⟩
    · exact (nX y h a1 a2).elim
    · exact (nY x h1 h2 a3).elim
    · exact (nZ x h1 h2 a3).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, a3, h1⟩)))
  · rcases four_candidate_core a1 a2 a3 hK.symm with h | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨_, h1, _, _⟩
    · exact (nY y h a1 a2).elim
    · exact (nX x h1 h2 a3).elim
    · exact (nZ x h1 a3 h2).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, a3, h1⟩))))
  · rcases four_candidate_core a1 a2 a3 hK.symm with h | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨_, h1, _, _⟩
    · exact (nZ y h a1 a2).elim
    · exact (nX x h1 a3 h2).elim
    · exact (nY x h1 a3 h2).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2, a3, h1⟩))))

end Erdos644
