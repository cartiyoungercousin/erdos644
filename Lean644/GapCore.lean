import Lean644.OneCoreLemma
import Lean644.GapTraces

/-!
# Lemma 4.5 (forced traces and one core), manuscript Appendix A

Same first request as Lemma 4.1 (`X ∪ Y ∪ Z₀`, `|Z₀| = min(z, T-x-y)`); the gap `Gap(ℓ,u)`
forces `|E∩K| ≤ ℓ` and `|F∩K| ≤ ℓ`. Bases `X ∪ B₁`, `X ∪ B₂`, `Y ∪ Z ∪ A ∪ C`.
`Δ = (S-T)₊` is truncated subtraction in `ℕ`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

section mem
variable {A B C D : Finset α} {x : α}
private theorem m4_1 (h : x ∈ A) : x ∈ A ∪ B ∪ C ∪ D :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
private theorem m4_2 (h : x ∈ B) : x ∈ A ∪ B ∪ C ∪ D :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
private theorem m4_3 (h : x ∈ C) : x ∈ A ∪ B ∪ C ∪ D :=
  Finset.mem_union_left _ (Finset.mem_union_right _ h)
private theorem m4_4 (h : x ∈ D) : x ∈ A ∪ B ∪ C ∪ D := Finset.mem_union_right _ h
private theorem m2_1 (h : x ∈ A) : x ∈ A ∪ B := Finset.mem_union_left _ h
private theorem m2_2 (h : x ∈ B) : x ∈ A ∪ B := Finset.mem_union_right _ h
end mem

/-- **Lemma 4.5 (forced traces and one core).** -/
theorem gapCore_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k l u : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k) (hu : u < k)
    (hgap : IntersectionGap H l u)
    {E F G : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H) (hgood : IsGoodTriple E F G)
    (h1 : (E ∩ F).card + (E ∩ G).card ≤ T)
    (c2 : k - (E ∩ F).card - (E ∩ G).card ≤ u)
    (c3 : k - (E ∩ F).card - (F ∩ G).card
      + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card - T) ≤ u)
    (c4 : 2 * (E ∩ F).card + 2 * ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card - T) + k
      - (E ∩ G).card - (F ∩ G).card ≤ 2 * T)
    (c5 : (E ∩ G).card + (F ∩ G).card + 2 * l ≤ T)
    (c6 : 2 * k + (E ∩ F).card - (E ∩ G).card + l
      + ((E ∩ F).card + (E ∩ G).card + (F ∩ G).card - T) ≤ 3 * T) : False := by
  have gF : IsGoodTriple F E G := by
    unfold IsGoodTriple at *; rw [Finset.inter_comm F E]; exact hgood
  have gG : IsGoodTriple G E F := by
    unfold IsGoodTriple at *; rw [← hgood]; ext v; simp only [Finset.mem_inter]; tauto
  have g0 : ∀ v, v ∈ E → v ∈ F → v ∈ G → False := fun v h1 h2 h3 => by
    have : v ∈ E ∩ F ∩ G := by simp [h1, h2, h3]
    unfold IsGoodTriple at hgood; rw [hgood] at this; simp at this
  set X := E ∩ F with hXdef
  set Y := E ∩ G with hYdef
  set Z := F ∩ G with hZdef
  -- subtraction-free forms of the hypotheses (Δ = (S-T)₊)
  obtain ⟨Δ, hΔ1, hΔ2⟩ : ∃ Δ, X.card + Y.card + Z.card ≤ T + Δ ∧
      (Δ = 0 ∨ X.card + Y.card + Z.card = T + Δ) :=
    ⟨X.card + Y.card + Z.card - T, by omega, by omega⟩
  have d2 : k ≤ u + X.card + Y.card := by clear * - c2; omega
  have d3 : k + Δ ≤ u + X.card + Z.card := by clear * - c3 hΔ1 hΔ2; omega
  have d4 : 2 * X.card + 2 * Δ + k ≤ 2 * T + Y.card + Z.card := by clear * - c4 hΔ1 hΔ2; omega
  have d6 : 2 * k + X.card + l + Δ ≤ 3 * T + Y.card := by clear * - c6 hΔ1 hΔ2; omega
  clear c2 c3 c4 c6
  -- first request: X ∪ Y ∪ Z₀ with |Z₀| = min(z, T - x - y)
  obtain ⟨z₀, hz01, hz02, hz0⟩ : ∃ z₀, z₀ ≤ Z.card ∧ z₀ + X.card + Y.card ≤ T ∧
      (z₀ = Z.card ∨ z₀ + X.card + Y.card = T) :=
    ⟨min Z.card (T - X.card - Y.card), min_le_left _ _, by omega, by
      rcases min_choice Z.card (T - X.card - Y.card) with h | h <;> [left; right] <;> omega⟩
  obtain ⟨Z₀, hZ₀, cZ₀⟩ := Finset.exists_subset_card_eq hz01
  obtain ⟨K, hK, hKD⟩ := exists_response hτ (d := X ∪ Y ∪ Z₀)
    ((card_union3_le _ _ _).trans (by omega))
  have nK : ∀ v, v ∈ K → (v ∈ E → v ∈ F → False) ∧ (v ∈ E → v ∈ G → False) ∧ v ∉ Z₀ :=
    fun v hv => by
      have h := Finset.disjoint_left.1 hKD hv
      simp only [X, Y, Finset.mem_union, Finset.mem_inter, not_or, not_and] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
  have kX : Disjoint K X := Finset.disjoint_left.2 fun v hv h =>
    (nK v hv).1 (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2
  have kY : Disjoint K Y := Finset.disjoint_left.2 fun v hv h =>
    (nK v hv).2.1 (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h).2
  set Q := F ∩ G ∩ K
  have hQc : (F ∩ G ∩ K).card = Q.card := rfl
  set A := (F ∩ K) \ G
  set B := (G ∩ K) \ F
  set C := E ∩ K
  set V := Z \ K
  set D := E \ (F ∪ G ∪ K)
  have hDc : (E \ (F ∪ G ∪ K)).card = D.card := rfl
  -- disjointness facts
  have mZ : ∀ v, v ∈ Z ↔ v ∈ F ∧ v ∈ G := fun v => Finset.mem_inter
  -- |F ∩ K| = q + a, |G ∩ K| = q + b
  have eFK : (F ∩ K).card = Q.card + A.card := by
    have e : (F ∩ K) ∩ G = Q := by ext v; simp [Q]; tauto
    have h := Finset.card_sdiff_add_card_inter (F ∩ K) G
    rw [e] at h
    change A.card + Q.card = (F ∩ K).card at h
    omega
  have eGK : (G ∩ K).card = Q.card + B.card := by
    have e : (G ∩ K) ∩ F = Q := by ext v; simp [Q]; tauto
    have h := Finset.card_sdiff_add_card_inter (G ∩ K) F
    rw [e] at h
    change B.card + Q.card = (G ∩ K).card at h
    omega
  -- |V| = z - q
  have eV : V.card + Q.card = Z.card := Finset.card_sdiff_add_card_inter Z K
  -- (q) Q ⊆ Z \ Z₀
  have bq : Q.card + z₀ ≤ Z.card := by
    have sub : Q ∪ Z₀ ⊆ Z := by
      intro v hv; rcases Finset.mem_union.1 hv with h | h
      · simp [Q, Z] at h ⊢; tauto
      · exact hZ₀ h
    have d : Disjoint Q Z₀ := Finset.disjoint_left.2 fun v h1 h2 =>
      (nK v (by simp [Q] at h1; tauto)).2.2 h2
    have := Finset.card_le_card sub
    rw [card_union_disj d] at this; omega
  -- generic: three disjoint subsets of an edge P
  have three : ∀ P S₁ S₂ S₃ : Finset α, P ∈ H → S₁ ⊆ P → S₂ ⊆ P → S₃ ⊆ P → Disjoint S₁ S₂ →
      Disjoint (S₁ ∪ S₂) S₃ → S₁.card + S₂.card + S₃.card ≤ k := by
    intro P S₁ S₂ S₃ hP a b c d12 d3
    have := Finset.card_le_card (show S₁ ∪ S₂ ∪ S₃ ⊆ P by
      intro v hv; simp only [Finset.mem_union] at hv; rcases hv with (h | h) | h
      exacts [a h, b h, c h])
    rw [card_union_disj d3, card_union_disj d12, hunif P hP] at this; exact this
  have dXZ0 : Disjoint X Z₀ := Finset.disjoint_left.2 fun v h1 h2 => by
    have := hZ₀ h2; simp [X, Z] at h1 this; exact g0 v h1.1 h1.2 this.2
  have dYZ0 : Disjoint Y Z₀ := Finset.disjoint_left.2 fun v h1 h2 => by
    have := hZ₀ h2; simp [Y, Z] at h1 this; exact g0 v h1.1 this.1 h1.2
  have dXY : Disjoint X Y := Finset.disjoint_left.2 fun v h1 h2 => by
    simp [X, Y] at h1 h2; exact g0 v h1.1 h1.2 h2.2
  -- (f) |F∩K| + x + z₀ ≤ k
  have bf := three F (F ∩ K) X Z₀ hF Finset.inter_subset_left Finset.inter_subset_right
    (fun v h => (Finset.mem_inter.1 (hZ₀ h)).1)
    (Finset.disjoint_left.2 fun v h1 h2 => (nK v (Finset.mem_inter.1 h1).2).1
      (Finset.mem_inter.1 h2).1 (Finset.mem_inter.1 h2).2)
    (Finset.disjoint_left.2 fun v h1 h2 => by
      rcases Finset.mem_union.1 h1 with h | h
      · exact (nK v (Finset.mem_inter.1 h).2).2.2 h2
      · exact Finset.disjoint_left.1 dXZ0 h h2)
  -- (g) |G∩K| + y + z₀ ≤ k
  have bg := three G (G ∩ K) Y Z₀ hG Finset.inter_subset_left Finset.inter_subset_right
    (fun v h => (Finset.mem_inter.1 (hZ₀ h)).2)
    (Finset.disjoint_left.2 fun v h1 h2 => (nK v (Finset.mem_inter.1 h1).2).2.1
      (Finset.mem_inter.1 h2).1 (Finset.mem_inter.1 h2).2)
    (Finset.disjoint_left.2 fun v h1 h2 => by
      rcases Finset.mem_union.1 h1 with h | h
      · exact (nK v (Finset.mem_inter.1 h).2).2.2 h2
      · exact Finset.disjoint_left.1 dYZ0 h h2)
  -- (d) |D| + |C| + x + y ≤ k   (D, C, X, Y disjoint in E)
  have bd : D.card + C.card + X.card + Y.card ≤ k := by
    have sub : D ∪ C ∪ (X ∪ Y) ⊆ E := by
      intro v hv; simp only [Finset.mem_union] at hv
      rcases hv with (h | h) | (h | h)
      · exact (Finset.mem_sdiff.1 h).1
      · exact (Finset.mem_inter.1 h).1
      · exact (Finset.mem_inter.1 h).1
      · exact (Finset.mem_inter.1 h).1
    have d1 : Disjoint D C := Finset.disjoint_left.2 fun v h1 h2 => by
      simp [D, C] at h1 h2; tauto
    have d2 : Disjoint (D ∪ C) (X ∪ Y) := Finset.disjoint_left.2 fun v h1 h2 => by
      simp only [D, C, X, Y, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at h1 h2
      rcases h1 with h | h
      · tauto
      · rcases h2 with h' | h'
        · exact (nK v h.2).1 h'.1 h'.2
        · exact (nK v h.2).2.1 h'.1 h'.2
    have := Finset.card_le_card sub
    rw [card_union_disj d2, card_union_disj d1, card_union_disj dXY, hunif E hE] at this
    omega
  -- (k) q + a + b + c ≤ k (disjoint in K)
  have bk : Q.card + A.card + B.card + C.card ≤ k := by
    have sub : Q ∪ A ∪ B ∪ C ⊆ K := by
      intro v hv; simp only [Q, A, B, C, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hv
      tauto
    have d1 : Disjoint Q A := Finset.disjoint_left.2 fun v h1 h2 => by
      simp [Q, A] at h1 h2; tauto
    have d2 : Disjoint (Q ∪ A) B := Finset.disjoint_left.2 fun v h1 h2 => by
      simp [Q, A, B] at h1 h2; tauto
    have d3 : Disjoint (Q ∪ A ∪ B) C := Finset.disjoint_left.2 fun v h1 h2 => by
      simp only [Q, A, B, C, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at h1 h2
      rcases h1 with (h | h) | h
      · exact g0 v h2.1 h.1.1 h.1.2
      · exact (nK v h2.2).1 h2.1 h.1.1
      · exact (nK v h2.2).2.1 h2.1 h.1.1
    have := Finset.card_le_card sub
    rw [card_union_disj d3, card_union_disj d2, card_union_disj d1, hunif K hK] at this
    exact this
  -- common coverage facts
  have memB : ∀ v, v ∈ G → v ∈ K → v ∉ F → v ∈ B := fun v a b c => by simp [B, a, b, c]
  have memA : ∀ v, v ∈ F → v ∈ K → v ∉ G → v ∈ A := fun v a b c => by simp [A, a, b, c]
  have memC : ∀ v, v ∈ E → v ∈ K → v ∈ C := fun v a b => by simp [C, a, b]
  have memX : ∀ v, v ∈ E → v ∈ F → v ∈ X := fun v a b => by simp [X, a, b]
  have memY : ∀ v, v ∈ E → v ∈ G → v ∈ Y := fun v a b => by simp [Y, a, b]
  have memZ : ∀ v, v ∈ F → v ∈ G → v ∈ Z := fun v a b => by simp [Z, a, b]
  have QZ : ∀ S : Finset α, Z ⊆ S → (Q ∪ S).card ≤ S.card := fun S h =>
    Finset.card_le_card (Finset.union_subset (fun v hv => h (by simp [Q, Z] at hv ⊢; tauto))
      subset_rfl)
  have u2 : ∀ P R : Finset α, (Q ∪ (P ∪ R)).card ≤ Q.card + P.card + R.card := fun P R =>
    (Finset.card_union_le _ _).trans (by have := Finset.card_union_le P R; omega)
  -- B, Y, Z are disjoint in G
  have hbB : B.card + Y.card + Z.card ≤ k := by
    refine three G B Y Z hG (fun v h => (Finset.mem_inter.1 (Finset.mem_sdiff.1 h).1).1)
      Finset.inter_subset_right Finset.inter_subset_right ?_ ?_
    · exact Finset.disjoint_left.2 fun v h1 h2 =>
        (nK v (Finset.mem_inter.1 (Finset.mem_sdiff.1 h1).1).2).2.1
          (Finset.mem_inter.1 h2).1 (Finset.mem_inter.1 h2).2
    · refine Finset.disjoint_left.2 fun v h1 h2 => ?_
      rcases Finset.mem_union.1 h1 with h | h
      · exact (Finset.mem_sdiff.1 h).2 (Finset.mem_inter.1 h2).1
      · exact g0 v (Finset.mem_inter.1 h).1 (Finset.mem_inter.1 h2).1 (Finset.mem_inter.1 h).2
  -- the triple cell Q has at most Δ points
  have hQΔ : Q.card ≤ Δ := by
    clear * - bq hz0 hz02 hΔ1; omega
  -- gap: |E ∩ K| ≤ ℓ and |F ∩ K| ≤ ℓ
  have hcu : C.card ≤ u := by clear * - bd d2; omega
  have hcl : C.card ≤ l := hgap.apply hunif hu hE hK hcu
  have hfu : (F ∩ K).card ≤ u := by
    have h0 : Z₀.card = z₀ := cZ₀
    clear * - bf h0 hz0 d3 hΔ1 hz01; omega
  have hfl : (F ∩ K).card ≤ l := hgap.apply hunif hu hF hK hfu
  obtain ⟨B₁, B₂, -, -, covB, cB₁, cB₂⟩ := split_two B (B.card / 2) (B.card - B.card / 2) (by omega)
  refine onecore_bases_close hprop hτ hE hF hG hK hgood kX kY (X ∪ B₁) (X ∪ B₂)
    (Y ∪ Z ∪ A ∪ C) (Q.card + X.card + B₁.card) (Q.card + X.card + B₂.card)
    (Y.card + Z.card + A.card + C.card)
    (u2 _ _) (u2 _ _) ((QZ _ (by intro v hv; simp [hv])).trans (card_union4_le _ _ _ _))
    (by clear * - cB₁ hQΔ hbB d4; omega) (by clear * - cB₂ hQΔ hbB d4; omega)
    (by clear * - eFK hfl hcl c5; omega)
    (by clear * - cB₁ cB₂ hQΔ hbB eFK hfl bd hDc d6; omega) ?_ ?_ ?_ ?_
  · intro p q pE pF qG qK qF
    rcases covB q (memB q qG qK qF) with h | h
    · exact Or.inl ⟨m2_1 (memX p pE pF), m2_2 h⟩
    · exact Or.inr (Or.inl ⟨m2_1 (memX p pE pF), m2_2 h⟩)
  · intro p q pE pG qF qK qG
    exact Or.inr (Or.inr ⟨m4_1 (memY p pE pG), m4_3 (memA q qF qK qG)⟩)
  · intro p q pF pG _ qE qK
    exact Or.inr (Or.inr ⟨m4_2 (memZ p pF pG), m4_4 (memC q qE qK)⟩)
  · intro e eE he
    rcases he with h | h | h
    · exact Or.inl (m2_1 (memX e eE h))
    · exact Or.inr (Or.inr (m4_1 (memY e eE h)))
    · exact Or.inr (Or.inr (m4_4 (memC e eE h)))

end Erdos644
