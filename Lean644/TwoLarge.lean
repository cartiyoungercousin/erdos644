import Lean644.TwoCores

/-!
# Lemma 4.8 (two large opposite cells), manuscript Appendix A

Edges `E, F, G, J` (the manuscript's `E, F, G, H`; `H` is the family here) with all four triple
intersections empty, `X = E∩F` and `B = G∩J` of size `> k/2`, the other four pair cells of size
`≤ m`; dichotomy with threshold `m` (`IntersectionGap H m (k/2)`), `4m ≤ k`.
With `σ = |E∩G| + |F∩G|`, `ρ = |F∩J| + |E∩J|`, `p = ⌈k/2⌉ - σ`, `q = T - ⌈k/2⌉ - ρ`, request
`I` avoiding `U ∪ B₀ ∪ X₀` (`U` = the four small cells, `|B₀| = p`, `|X₀| = q`). Then
`|G∩I| ≤ ⌊k/2⌋`, hence `≤ m`. With `B∩I ⊆ B₁ ⊆ B`, `|B₁| = min(b, T-x)`, the requests
`X ∪ B₁` and `(X∩I) ∪ (B∖B₁)` and the edges `E,F,G,J,I` give a bad 7-subfamily.
(The manuscript uses `min(σ,ρ)`/`max(σ,ρ)` in `p, q`; only the trace on `G` is needed, and the
choice here satisfies the same bounds.)
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- Candidate pairs of four edges with empty triple intersections (propositional core). -/
theorem four_pairs {xE xF xG xJ yE yF yG yJ : Prop}
    (a1 : ¬(xE ∧ xF ∧ xG)) (a2 : ¬(xE ∧ xF ∧ xJ)) (a3 : ¬(xE ∧ xG ∧ xJ)) (a4 : ¬(xF ∧ xG ∧ xJ))
    (b1 : ¬(yE ∧ yF ∧ yG)) (b2 : ¬(yE ∧ yF ∧ yJ)) (b3 : ¬(yE ∧ yG ∧ yJ)) (b4 : ¬(yF ∧ yG ∧ yJ))
    (cE : xE ∨ yE) (cF : xF ∨ yF) (cG : xG ∨ yG) (cJ : xJ ∨ yJ) :
    (xE ∧ xF ∧ yG ∧ yJ) ∨ (yE ∧ yF ∧ xG ∧ xJ) ∨
      (((xE ∧ xG) ∨ (xF ∧ xG) ∨ (xF ∧ xJ) ∨ (xE ∧ xJ)) ∧
        ((yE ∧ yG) ∨ (yF ∧ yG) ∨ (yF ∧ yJ) ∨ (yE ∧ yJ))) := by
  rcases cE with e | e <;> rcases cF with f | f <;> rcases cG with g | g <;>
    rcases cJ with j | j
  all_goals first
    | exact absurd ⟨‹xE›, ‹xF›, ‹xG›⟩ a1 | exact absurd ⟨‹xE›, ‹xF›, ‹xJ›⟩ a2
    | exact absurd ⟨‹xE›, ‹xG›, ‹xJ›⟩ a3 | exact absurd ⟨‹xF›, ‹xG›, ‹xJ›⟩ a4
    | exact absurd ⟨‹yE›, ‹yF›, ‹yG›⟩ b1 | exact absurd ⟨‹yE›, ‹yF›, ‹yJ›⟩ b2
    | exact absurd ⟨‹yE›, ‹yG›, ‹yJ›⟩ b3 | exact absurd ⟨‹yF›, ‹yG›, ‹yJ›⟩ b4
    | exact Or.inl ⟨‹xE›, ‹xF›, ‹yG›, ‹yJ›⟩
    | exact Or.inr (Or.inl ⟨‹yE›, ‹yF›, ‹xG›, ‹xJ›⟩)
    | exact Or.inr (Or.inr ⟨Or.inl ⟨‹xE›, ‹xG›⟩, Or.inr (Or.inr (Or.inl ⟨‹yF›, ‹yJ›⟩))⟩)
    | exact Or.inr (Or.inr ⟨Or.inr (Or.inl ⟨‹xF›, ‹xG›⟩), Or.inr (Or.inr (Or.inr ⟨‹yE›, ‹yJ›⟩))⟩)
    | exact Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inl ⟨‹xF›, ‹xJ›⟩)), Or.inl ⟨‹yE›, ‹yG›⟩⟩)
    | exact Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inr ⟨‹xE›, ‹xJ›⟩)), Or.inr (Or.inl ⟨‹yF›, ‹yG›⟩)⟩)

/-- **Lemma 4.8 (two large opposite cells).** -/
theorem twoLarge_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k m : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k)
    (hdich : IntersectionGap H m (k / 2)) (hm : 4 * m ≤ k)
    {E F G J : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hJ : J ∈ H)
    (t1 : E ∩ F ∩ G = ∅) (t2 : E ∩ F ∩ J = ∅) (t3 : E ∩ G ∩ J = ∅) (t4 : F ∩ G ∩ J = ∅)
    (hx : k < 2 * (E ∩ F).card) (hb : k < 2 * (G ∩ J).card)
    (hY : (E ∩ G).card ≤ m) (hZ : (F ∩ G).card ≤ m) (hY' : (F ∩ J).card ≤ m)
    (hZ' : (E ∩ J).card ≤ m)
    (c1 : (k + 1) / 2 + 2 * m ≤ T) (c2 : (E ∩ F).card + m ≤ T)
    (c3 : 2 * (E ∩ F).card + (G ∩ J).card + (k + 1) / 2 + 2 * m ≤ 3 * T) : False := by
  have no3 : ∀ (A B C : Finset α), A ∩ B ∩ C = ∅ → ∀ v, ¬(v ∈ A ∧ v ∈ B ∧ v ∈ C) :=
    fun A B C h v hv => by
      have : v ∈ A ∩ B ∩ C := Finset.mem_inter.2 ⟨Finset.mem_inter.2 ⟨hv.1, hv.2.1⟩, hv.2.2⟩
      rw [h] at this; simp at this
  set X := E ∩ F with hXdef
  set B := G ∩ J with hBdef
  have kG := hunif G hG
  -- the request
  obtain ⟨B₀, hB₀, cB₀⟩ := Finset.exists_subset_card_eq
    (show (k + 1) / 2 - ((E ∩ G).card + (F ∩ G).card) ≤ B.card by omega)
  obtain ⟨X₀, hX₀, cX₀⟩ := Finset.exists_subset_card_eq
    (show T - (k + 1) / 2 - ((F ∩ J).card + (E ∩ J).card) ≤ X.card by omega)
  set U := (E ∩ G) ∪ (F ∩ G) ∪ (F ∩ J) ∪ (E ∩ J) with hU
  have cU : U.card ≤ (E ∩ G).card + (F ∩ G).card + (F ∩ J).card + (E ∩ J).card :=
    card_union4_le _ _ _ _
  obtain ⟨I, hI, hId⟩ := exists_response hτ (d := U ∪ B₀ ∪ X₀)
    ((card_union3_le _ _ _).trans (by omega))
  have nIU : ∀ v ∈ I, v ∉ U := fun v hv h => Finset.disjoint_left.1 hId hv (by simp [h])
  have nIB₀ : ∀ v ∈ I, v ∉ B₀ := fun v hv h => Finset.disjoint_left.1 hId hv (by simp [h])
  have nIX₀ : ∀ v ∈ I, v ∉ X₀ := fun v hv h => Finset.disjoint_left.1 hId hv (by simp [h])
  -- the trace of I on G
  have hGIu : (G ∩ I).card ≤ k / 2 := by
    have dYZ : Disjoint (E ∩ G) (F ∩ G) := Finset.disjoint_left.2 fun v h1 h2 =>
      no3 _ _ _ t1 v ⟨(Finset.mem_inter.1 h1).1, (Finset.mem_inter.1 h2).1, (Finset.mem_inter.1 h1).2⟩
    have dI : Disjoint (G ∩ I) ((E ∩ G) ∪ (F ∩ G)) := Finset.disjoint_left.2 fun v h1 h2 =>
      nIU v (Finset.mem_inter.1 h1).2 (by
        rcases Finset.mem_union.1 h2 with h | h <;> simp [U, h])
    have := three_le (P := G) (S₁ := G ∩ I) (S₂ := (E ∩ G) ∪ (F ∩ G)) (S₃ := B₀)
      Finset.inter_subset_left
      (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
      (hB₀.trans Finset.inter_subset_left) dI
      (Finset.disjoint_left.2 fun v h1 h2 => by
        have vB := hB₀ h2
        rcases Finset.mem_union.1 h1 with h | h
        · exact nIB₀ v (Finset.mem_inter.1 h).2 h2
        · rcases Finset.mem_union.1 h with h' | h'
          · exact no3 _ _ _ t3 v ⟨(Finset.mem_inter.1 h').1, (Finset.mem_inter.1 h').2,
              (Finset.mem_inter.1 vB).2⟩
          · exact no3 _ _ _ t4 v ⟨(Finset.mem_inter.1 h').1, (Finset.mem_inter.1 h').2,
              (Finset.mem_inter.1 vB).2⟩)
    rw [card_union_disj dYZ, kG] at this
    omega
  have hGI : (G ∩ I).card ≤ m := hdich.apply hunif (by omega) hG hI hGIu
  have hBI : (B ∩ I).card ≤ m :=
    (Finset.card_le_card fun v hv => Finset.mem_inter.2
      ⟨(Finset.mem_inter.1 (Finset.mem_inter.1 hv).1).1, (Finset.mem_inter.1 hv).2⟩).trans hGI
  have hXI : (X ∩ I).card + X₀.card ≤ X.card := by
    have s : X ∩ I ⊆ X \ X₀ := fun v hv => Finset.mem_sdiff.2
      ⟨(Finset.mem_inter.1 hv).1, nIX₀ v (Finset.mem_inter.1 hv).2⟩
    have e := Finset.card_sdiff_add_card_eq_card hX₀
    have := Finset.card_le_card s
    omega
  -- B₁ ⊇ B ∩ I
  obtain ⟨E₁, hE₁, cE₁⟩ := Finset.exists_subset_card_eq
    (show min B.card (T - X.card) - (B ∩ I).card ≤ (B \ (B ∩ I)).card by
      have := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := B) (s₂ := I))
      omega)
  set B₁ := (B ∩ I) ∪ E₁ with hB₁
  have hB₁B : B₁ ⊆ B := Finset.union_subset Finset.inter_subset_left
    (hE₁.trans Finset.sdiff_subset)
  have cB₁ : B₁.card = min B.card (T - X.card) := by
    have d : Disjoint (B ∩ I) E₁ := Finset.disjoint_left.2 fun v h1 h2 =>
      (Finset.mem_sdiff.1 (hE₁ h2)).2 h1
    have : (B ∩ I).card ≤ min B.card (T - X.card) :=
      le_min (Finset.card_le_card Finset.inter_subset_left) (by omega)
    rw [hB₁, card_union_disj d, cE₁]; omega
  have cBB₁ := Finset.card_sdiff_add_card_eq_card hB₁B
  -- the two requests
  have r1 : (X ∪ B₁).card ≤ T := (Finset.card_union_le _ _).trans (by omega)
  have r2 : ((X ∩ I) ∪ (B \ B₁)).card ≤ T := (Finset.card_union_le _ _).trans (by omega)
  obtain ⟨R₁, hR₁, dR₁⟩ := exists_response hτ r1
  obtain ⟨R₂, hR₂, dR₂⟩ := exists_response hτ r2
  refine request_cover hprop (E := {E, F, G, J, I}) (D := {X ∪ B₁, (X ∩ I) ∪ (B \ B₁)}) ?_
    ⟨E, by simp⟩ ?_ ?_ ?_
  · intro A hA; simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl <;> assumption
  · have a : ({E, F, G, J, I} : Finset (Finset α)).card ≤ 5 :=
      (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <| (Finset.card_insert_le _ _).trans
        <| Nat.succ_le_succ <| (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <|
          (Finset.card_insert_le _ _).trans (by simp)
    have b : ({X ∪ B₁, (X ∩ I) ∪ (B \ B₁)} : Finset (Finset α)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  · intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    exacts [⟨R₁, hR₁, dR₁⟩, ⟨R₂, hR₂, dR₂⟩]
  · intro x y hxy
    have cE := hxy E (by simp)
    have cF := hxy F (by simp)
    have cG := hxy G (by simp)
    have cJ := hxy J (by simp)
    have cI := hxy I (by simp)
    have inU : ∀ v, ((v ∈ E ∧ v ∈ G) ∨ (v ∈ F ∧ v ∈ G) ∨ (v ∈ F ∧ v ∈ J) ∨ (v ∈ E ∧ v ∈ J)) →
        v ∉ I := fun v h hv => nIU v hv (by
          rcases h with h | h | h | h <;> simp [U, h.1, h.2])
    have XB : ∀ u v, u ∈ E → u ∈ F → v ∈ G → v ∈ J → (u ∈ I ∨ v ∈ I) →
        ∃ d ∈ ({X ∪ B₁, (X ∩ I) ∪ (B \ B₁)} : Finset (Finset α)), u ∈ d ∧ v ∈ d := by
      intro u v uE uF vG vJ huv
      have uX : u ∈ X := Finset.mem_inter.2 ⟨uE, uF⟩
      have vB : v ∈ B := Finset.mem_inter.2 ⟨vG, vJ⟩
      by_cases h1 : v ∈ B₁
      · exact ⟨X ∪ B₁, by simp, by simp [uX], by simp [h1]⟩
      · have vI : v ∉ I := fun h => h1 (by simp [hB₁, vB, h])
        have uI : u ∈ I := huv.resolve_right vI
        exact ⟨(X ∩ I) ∪ (B \ B₁), by simp, by simp [uX, uI], by simp [vB, h1]⟩
    rcases four_pairs (no3 _ _ _ t1 x) (no3 _ _ _ t2 x) (no3 _ _ _ t3 x) (no3 _ _ _ t4 x) (no3 _ _ _ t1 y) (no3 _ _ _ t2 y)
      (no3 _ _ _ t3 y) (no3 _ _ _ t4 y) cE cF cG cJ with h | h | ⟨hx', hy'⟩
    · exact XB x y h.1 h.2.1 h.2.2.1 h.2.2.2 cI
    · obtain ⟨d, hd, h1, h2⟩ := XB y x h.1 h.2.1 h.2.2.1 h.2.2.2 cI.symm
      exact ⟨d, hd, h2, h1⟩
    · rcases cI with h | h
      · exact (inU x hx' h).elim
      · exact (inU y hy' h).elim

end Erdos644
