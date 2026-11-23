import Lean644.HallClose

/-!
# Tight-triple lemma (Fano template, three concurrent anchors)

Source: `notes/ROADMAP_3_4.md` §3(c) (research agent, 2026-11-23); hand-checked and size formula
validated exhaustively in Python (865,364 triples, 0 violations).

For a good triple `E, F, G` put the points of `F ∖ E` in classes `e₀, e₁`, of `G ∖ F` in `f₀, f₁`,
of `E ∖ G` in `g₀, g₁` (halves), and request the four "Fano lines not through p":
`e_a ∪ f_b ∪ g_c` with `a + b + c` even. Any candidate pair uses two different letters, and any
two classes with different letters lie on exactly one of these lines.
Each request has about `|E ∪ F ∪ G| / 2 = (3k - S)/2` points.

**Consequence.** If `τ(H) > T` then every good triple has `S ≤ 3k - 2T + 1`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Tight-triple lemma.** A good triple with `3k + 2 ≤ 2T + S` (where `S = x + y + z` is the
sum of the pair-cell sizes) closes: property (7,2) and `τ(H) > T` are incompatible. -/
theorem tightTriple_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (hT : 3 * k + 2 ≤ 2 * T + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card)) : False := by
  have g0 : ∀ v, v ∈ E → v ∈ F → v ∈ G → False := fun v h1 h2 h3 => by
    have : v ∈ E ∩ F ∩ G := by simp [h1, h2, h3]
    unfold IsGoodTriple at hgood; rw [hgood] at this; simp at this
  -- sizes of the three groups
  have sE : (F \ E).card + (E ∩ F).card = k := by
    rw [← hunif F hF, Finset.inter_comm E F]; exact Finset.card_sdiff_add_card_inter F E
  have sF : (G \ F).card + (F ∩ G).card = k := by
    rw [← hunif G hG, Finset.inter_comm F G]; exact Finset.card_sdiff_add_card_inter G F
  have sG : (E \ G).card + (E ∩ G).card = k := by
    rw [← hunif E hE]; exact Finset.card_sdiff_add_card_inter E G
  -- halves: the larger half goes to e₁, f₀, g₀ (odd parity, so no request gets three)
  obtain ⟨e₀, e₁, -, -, ce, ce₀, ce₁⟩ :=
    split_two (F \ E) ((F \ E).card / 2) ((F \ E).card - (F \ E).card / 2) (by omega)
  obtain ⟨f₀, f₁, -, -, cf, cf₀, cf₁⟩ :=
    split_two (G \ F) ((G \ F).card - (G \ F).card / 2) ((G \ F).card / 2) (by omega)
  obtain ⟨g₀, g₁, -, -, cg, cg₀, cg₁⟩ :=
    split_two (E \ G) ((E \ G).card - (E \ G).card / 2) ((E \ G).card / 2) (by omega)
  have u3 : ∀ A B C : Finset α, (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := fun A B C =>
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  -- the goal predicate for an (unordered) pair, as four requests
  let P : α → α → Prop := fun u v =>
    (u ∈ e₀ ∪ f₀ ∪ g₀ ∧ v ∈ e₀ ∪ f₀ ∪ g₀) ∨ (u ∈ e₀ ∪ f₁ ∪ g₁ ∧ v ∈ e₀ ∪ f₁ ∪ g₁) ∨
    (u ∈ e₁ ∪ f₀ ∪ g₁ ∧ v ∈ e₁ ∪ f₀ ∪ g₁) ∨ (u ∈ e₁ ∪ f₁ ∪ g₀ ∧ v ∈ e₁ ∪ f₁ ∪ g₀)
  have symm : ∀ u v, P u v → P v u := by
    intro u v h
    rcases h with h | h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
  -- two classes with different letters share exactly one request
  have EF : ∀ u v, u ∈ F \ E → v ∈ G \ F → P u v := by
    intro u v hu hv
    rcases ce u hu with a | a <;> rcases cf v hv with b | b
    · exact Or.inl ⟨by simp [a], by simp [b]⟩
    · exact Or.inr (Or.inl ⟨by simp [a], by simp [b]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by simp [a], by simp [b]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [a], by simp [b]⟩))
  have EG : ∀ u v, u ∈ F \ E → v ∈ E \ G → P u v := by
    intro u v hu hv
    rcases ce u hu with a | a <;> rcases cg v hv with c | c
    · exact Or.inl ⟨by simp [a], by simp [c]⟩
    · exact Or.inr (Or.inl ⟨by simp [a], by simp [c]⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [a], by simp [c]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by simp [a], by simp [c]⟩))
  have FG : ∀ u v, u ∈ G \ F → v ∈ E \ G → P u v := by
    intro u v hu hv
    rcases cf u hu with b | b <;> rcases cg v hv with c | c
    · exact Or.inl ⟨by simp [b], by simp [c]⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by simp [b], by simp [c]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [b], by simp [c]⟩))
    · exact Or.inr (Or.inl ⟨by simp [b], by simp [c]⟩)
  refine closes_of_four_requests hprop hτ hE hF hG (e₀ ∪ f₀ ∪ g₀) (e₀ ∪ f₁ ∪ g₁)
    (e₁ ∪ f₀ ∪ g₁) (e₁ ∪ f₁ ∪ g₀) ((u3 _ _ _).trans (by omega)) ((u3 _ _ _).trans (by omega))
    ((u3 _ _ _).trans (by omega)) ((u3 _ _ _).trans (by omega)) ?_
  intro x y hxE hxF hxG
  -- membership in the three groups
  have inE : ∀ v, v ∈ F → v ∉ E → v ∈ F \ E := fun v a b => Finset.mem_sdiff.2 ⟨a, b⟩
  have inF : ∀ v, v ∈ G → v ∉ F → v ∈ G \ F := fun v a b => Finset.mem_sdiff.2 ⟨a, b⟩
  have inG : ∀ v, v ∈ E → v ∉ G → v ∈ E \ G := fun v a b => Finset.mem_sdiff.2 ⟨a, b⟩
  -- u in a pair cell, v in the third edge
  have cX : ∀ u v, u ∈ E → u ∈ F → v ∈ G → P u v := by
    intro u v uE uF vG
    have ug := inG u uE (fun h => g0 u uE uF h)
    by_cases vF : v ∈ F
    · exact symm _ _ (EG v u (inE v vF (fun h => g0 v h vF vG)) ug)
    · exact symm _ _ (FG v u (inF v vG vF) ug)
  have cY : ∀ u v, u ∈ E → u ∈ G → v ∈ F → P u v := by
    intro u v uE uG vF
    have uf := inF u uG (fun h => g0 u uE h uG)
    by_cases vE : v ∈ E
    · exact FG u v uf (inG v vE (fun h => g0 v vE vF h))
    · exact symm _ _ (EF v u (inE v vF vE) uf)
  have cZ : ∀ u v, u ∈ F → u ∈ G → v ∈ E → P u v := by
    intro u v uF uG vE
    have ue := inE u uF (fun h => g0 u h uF uG)
    by_cases vG : v ∈ G
    · exact EF u v ue (inF v vG (fun h => g0 v vE h vG))
    · exact EG u v ue (inG v vE vG)
  rcases triple_candidate hgood hxE hxF hxG with
    ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · exact cX x y a1 a2 a3
  · exact cY x y a1 a2 a3
  · exact cZ x y a1 a2 a3
  · exact symm _ _ (cX y x a1 a2 a3)
  · exact symm _ _ (cY y x a1 a2 a3)
  · exact symm _ _ (cZ y x a1 a2 a3)

/-- **Corollary.** If `τ(H) > T`, every good triple has `S ≤ 3k - 2T + 1`. -/
theorem goodTriple_S_le {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G) :
    2 * T + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card) ≤ 3 * k + 1 := by
  by_contra h
  exact tightTriple_closes hprop hτ hunif hE hF hG hgood (by omega)

end Erdos644
