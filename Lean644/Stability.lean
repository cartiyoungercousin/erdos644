import Lean644.TightTriple
import Lean644.SplitA

/-!
# Theorem 11.1 (stability inequality)

Source: `notes/NEW_PATHS.md` §11 (Fable research lead, 2026-11-23); hand-checked.

Let `σ` be a lower bound for `S = |E∩F| + |E∩G| + |F∩G|` over all good triples. If `τ(H) > T`
then `11T + 7σ < 17k + 5`; equivalently `τ ≤ (17k - 7σ + 16)/11`. Tight (up to `O(1)`) at the
complete family on `7k/4` points.

Proof. Request `T` points of an edge `A`; the response `B` meets `A` in `m ≤ k - T` points.
*Rigidity:* for `Q ⊆ (A∪B) ∖ (A∩B)`, a response `K` to `(A∪B) ∖ Q` (plus any extra set) forms a
good triple with `A, B`, so `σ ≤ m + |K ∩ (A∪B)|`; hence `K ∩ (A∪B) ⊆ Q` and
`|K ∖ (A∪B)| ≤ k + m - σ =: η`. Take disjoint `M₁, M₂, M₃` in `(A∪B) ∖ (A∩B)` and
`Q₁ = M₂ ∪ M₃`, `Q₂ = M₁ ∪ M₃`, `Q₃ = M₁ ∪ M₂` (so `Q₁ ∩ Q₂ ∩ Q₃ = ∅`); the third request also
contains `(K₁ ∩ K₂) ∖ (A∪B)`. Then `K₁, K₂, K₃` is a good triple whose union is at most
`|M| + 3η`, and the tight-triple lemma (`goodTriple_S_le`) gives the inequality.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- Inclusion–exclusion for a good triple: `|K₁ ∪ K₂ ∪ K₃| + S = 3k`. -/
theorem card_union_goodTriple {K₁ K₂ K₃ : Finset α} (h : K₁ ∩ K₂ ∩ K₃ = ∅) :
    (K₁ ∪ K₂ ∪ K₃).card + ((K₁ ∩ K₂).card + (K₁ ∩ K₃).card + (K₂ ∩ K₃).card) =
      K₁.card + K₂.card + K₃.card := by
  have h1 := Finset.card_union_add_card_inter (K₁ ∪ K₂) K₃
  have h2 := Finset.card_union_add_card_inter K₁ K₂
  have e : (K₁ ∪ K₂) ∩ K₃ = (K₁ ∩ K₃) ∪ (K₂ ∩ K₃) := Finset.union_inter_distrib_right _ _ _
  have h3 := Finset.card_union_add_card_inter (K₁ ∩ K₃) (K₂ ∩ K₃)
  have e2 : (K₁ ∩ K₃) ∩ (K₂ ∩ K₃) = ∅ := by
    ext v; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
    intro hv
    have : v ∈ K₁ ∩ K₂ ∩ K₃ := by simp [hv.1.1, hv.2.1, hv.1.2]
    rw [h] at this; simp at this
  rw [e2, Finset.card_empty] at h3
  rw [e] at h1
  omega

/-- **Theorem 11.1 (stability inequality).** -/
theorem stability_closes {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2)
    {T k σ : ℕ} (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k)
    (hT2 : k ≤ 2 * T)
    (hσ : ∀ E ∈ H, ∀ F ∈ H, ∀ G ∈ H, IsGoodTriple E F G →
      σ ≤ (E ∩ F).card + (E ∩ G).card + (F ∩ G).card)
    (hbound : 17 * k + 5 ≤ 11 * T + 7 * σ) : False := by
  -- an edge
  obtain ⟨A, hA⟩ : H.Nonempty := by
    rcases H.eq_empty_or_nonempty with rfl | h
    · exact absurd ⟨∅, by simp, fun B hB => by simp at hB⟩ hτ
    · exact h
  have kA := hunif A hA
  -- request T points of A
  obtain ⟨D₀, hD₀, cD₀⟩ := Finset.exists_subset_card_eq (show T ≤ A.card by omega)
  obtain ⟨B, hB, dB⟩ := exists_response hτ (le_of_eq cD₀)
  have kB := hunif B hB
  set m := (A ∩ B).card with hmdef
  have hm : m + T ≤ k := by
    have s : A ∩ B ⊆ A \ D₀ := fun v hv => Finset.mem_sdiff.2
      ⟨(Finset.mem_inter.1 hv).1, fun h => Finset.disjoint_left.1 dB (Finset.mem_inter.1 hv).2 h⟩
    have h1 : m ≤ (A \ D₀).card := Finset.card_le_card s
    have e := Finset.card_sdiff_add_card_eq_card hD₀
    omega
  set U := A ∪ B with hU
  set S₀ := U \ (A ∩ B) with hS₀
  have cU : U.card + m = 2 * k := by
    have := Finset.card_union_add_card_inter A B
    rw [kA, kB] at this; exact this.trans (two_mul k).symm
  have cS₀ : S₀.card + m = U.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left.trans Finset.subset_union_left)
  -- rigidity
  have rig : ∀ Q X : Finset α, Q ⊆ S₀ → ((U \ Q) ∪ X).card ≤ T →
      ∃ K ∈ H, K ∩ U ⊆ Q ∧ Disjoint K X ∧ σ ≤ m + (K ∩ U).card ∧ (K \ U).card + (K ∩ U).card = k := by
    intro Q X hQ hD
    obtain ⟨K, hK, dK⟩ := exists_response hτ hD
    have nK : ∀ v ∈ K, v ∉ (U \ Q) ∪ X := fun v hv h => Finset.disjoint_left.1 dK hv h
    have hKQ : K ∩ U ⊆ Q := fun v hv => by
      by_contra h
      exact nK v (Finset.mem_inter.1 hv).1 (Finset.mem_union_left _
        (Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hv).2, h⟩))
    have nAB : ∀ v ∈ K, v ∈ A → v ∈ B → False := fun v hv a b => by
      have vU : v ∈ U := Finset.mem_union_left _ a
      have vQ := hKQ (Finset.mem_inter.2 ⟨hv, vU⟩)
      exact (Finset.mem_sdiff.1 (hQ vQ)).2 (Finset.mem_inter.2 ⟨a, b⟩)
    have hgood : IsGoodTriple A B K := by
      unfold IsGoodTriple; ext v
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      rintro ⟨a, b⟩ k'; exact nAB v k' a b
    have hS := hσ A hA B hB K hK hgood
    -- |A ∩ K| + |B ∩ K| = |K ∩ U|
    have e1 := Finset.card_union_add_card_inter (A ∩ K) (B ∩ K)
    have e2 : (A ∩ K) ∪ (B ∩ K) = K ∩ U := by ext v; simp [U]; tauto
    have e3 : (A ∩ K) ∩ (B ∩ K) = ∅ := by
      ext v; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      intro h; exact nAB v h.1.2 h.1.1 h.2.1
    rw [e2, e3, Finset.card_empty] at e1
    have e4 : (K \ U).card + (K ∩ U).card = k := by
      rw [Finset.card_sdiff_add_card_inter]; exact hunif K hK
    have hm' : (A ∩ B).card = m := rfl
    refine ⟨K, hK, hKQ, Finset.disjoint_of_subset_right Finset.subset_union_right dK, ?_, e4⟩
    omega
  -- (a) σ ≤ 2k - T and (b) σ ≤ k + m
  have hmT : m ≤ T := by omega
  obtain ⟨Q₀, hQ₀, cQ₀⟩ := Finset.exists_subset_card_eq (show 2 * k - m - T ≤ S₀.card by omega)
  have dQ₀ : ((U \ Q₀) ∪ ∅).card ≤ T := by
    rw [Finset.union_empty]
    have := Finset.card_sdiff_add_card_eq_card (hQ₀.trans Finset.sdiff_subset)
    omega
  obtain ⟨K₀, -, hK₀Q, -, hσ₀, hk₀⟩ := rig Q₀ ∅ hQ₀ dQ₀
  have ha : σ + T ≤ 2 * k := by
    have := Finset.card_le_card hK₀Q; omega
  have hb : σ ≤ k + m := by omega
  -- sizes of the three blocks
  set η := k + m - σ with hη
  set q := 2 * k - m - T with hq
  set h := (q + η + 1) / 2 with hh
  by_cases fit : 2 * h + (q - h) ≤ S₀.card
  swap
  · clear rig; omega
  obtain ⟨M₁, hM₁, cM₁⟩ := Finset.exists_subset_card_eq (show h ≤ S₀.card by omega)
  have c1 := Finset.card_sdiff_add_card_eq_card hM₁
  obtain ⟨M₂, hM₂, cM₂⟩ := Finset.exists_subset_card_eq (show h ≤ (S₀ \ M₁).card by omega)
  have hM₁₂ : M₁ ∪ M₂ ⊆ S₀ := Finset.union_subset hM₁ (hM₂.trans Finset.sdiff_subset)
  have d12 : Disjoint M₁ M₂ := Finset.disjoint_left.2 fun v h1 h2 =>
    (Finset.mem_sdiff.1 (hM₂ h2)).2 h1
  have c12 : (M₁ ∪ M₂).card = 2 * h := by rw [card_union_disj d12, cM₁, cM₂]; omega
  have c2 := Finset.card_sdiff_add_card_eq_card hM₁₂
  obtain ⟨M₃, hM₃, cM₃⟩ := Finset.exists_subset_card_eq
    (show q - h ≤ (S₀ \ (M₁ ∪ M₂)).card by omega)
  have d13 : Disjoint M₁ M₃ := Finset.disjoint_left.2 fun v h1 h3 =>
    (Finset.mem_sdiff.1 (hM₃ h3)).2 (Finset.mem_union_left _ h1)
  have d23 : Disjoint M₂ M₃ := Finset.disjoint_left.2 fun v h2 h3 =>
    (Finset.mem_sdiff.1 (hM₃ h3)).2 (Finset.mem_union_right _ h2)
  have sM₃ : M₃ ⊆ S₀ := hM₃.trans Finset.sdiff_subset
  have sM₂ : M₂ ⊆ S₀ := hM₂.trans Finset.sdiff_subset
  have sU : S₀ ⊆ U := Finset.sdiff_subset
  -- request sizes
  have dsz : ∀ Q : Finset α, Q ⊆ S₀ → (U \ Q).card + Q.card = U.card := fun Q hQ =>
    Finset.card_sdiff_add_card_eq_card (hQ.trans sU)
  have cQ₁ : (M₂ ∪ M₃).card = h + (q - h) := by rw [card_union_disj d23, cM₂, cM₃]
  have cQ₂ : (M₁ ∪ M₃).card = h + (q - h) := by rw [card_union_disj d13, cM₁, cM₃]
  have r1 : ((U \ (M₂ ∪ M₃)) ∪ ∅).card ≤ T := by
    rw [Finset.union_empty]; have := dsz _ (Finset.union_subset sM₂ sM₃); omega
  have r2 : ((U \ (M₁ ∪ M₃)) ∪ ∅).card ≤ T := by
    rw [Finset.union_empty]; have := dsz _ (Finset.union_subset hM₁ sM₃); omega
  obtain ⟨K₁, hK₁, s₁, -, σ₁, k₁⟩ := rig _ ∅ (Finset.union_subset sM₂ sM₃) r1
  obtain ⟨K₂, hK₂, s₂, -, σ₂, k₂⟩ := rig _ ∅ (Finset.union_subset hM₁ sM₃) r2
  have o12 : ((K₁ ∩ K₂) \ U).card ≤ η := by
    have := Finset.card_le_card (show (K₁ ∩ K₂) \ U ⊆ K₁ \ U from fun v hv => by
      simp only [Finset.mem_sdiff, Finset.mem_inter] at hv ⊢; exact ⟨hv.1.1, hv.2⟩)
    omega
  have r3 : ((U \ (M₁ ∪ M₂)) ∪ ((K₁ ∩ K₂) \ U)).card ≤ T := by
    have := dsz _ hM₁₂
    have := Finset.card_union_le (U \ (M₁ ∪ M₂)) ((K₁ ∩ K₂) \ U)
    omega
  obtain ⟨K₃, hK₃, s₃, dK₃, σ₃, k₃⟩ := rig _ _ hM₁₂ r3
  -- the three responses form a good triple
  have hgood : IsGoodTriple K₁ K₂ K₃ := by
    unfold IsGoodTriple; ext v
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    rintro ⟨v1, v2⟩ v3
    by_cases vU : v ∈ U
    · have a1 := s₁ (Finset.mem_inter.2 ⟨v1, vU⟩)
      have a2 := s₂ (Finset.mem_inter.2 ⟨v2, vU⟩)
      have a3 := s₃ (Finset.mem_inter.2 ⟨v3, vU⟩)
      simp only [Finset.mem_union] at a1 a2 a3
      rcases a3 with h1 | h2
      · rcases a1 with h2 | h3
        · exact Finset.disjoint_left.1 d12 h1 h2
        · exact Finset.disjoint_left.1 d13 h1 h3
      · rcases a2 with h1 | h3
        · exact Finset.disjoint_left.1 d12 h1 h2
        · exact Finset.disjoint_left.1 d23 h2 h3
    · exact Finset.disjoint_left.1 dK₃ v3
        (Finset.mem_sdiff.2 ⟨Finset.mem_inter.2 ⟨v1, v2⟩, vU⟩)
  -- union bound
  have hunion : (K₁ ∪ K₂ ∪ K₃).card ≤ 2 * h + (q - h) + 3 * η := by
    have sub : K₁ ∪ K₂ ∪ K₃ ⊆ (M₁ ∪ M₂ ∪ M₃) ∪ ((K₁ \ U) ∪ (K₂ \ U) ∪ (K₃ \ U)) := by
      intro v hv
      by_cases vU : v ∈ U
      · refine Finset.mem_union_left _ ?_
        simp only [Finset.mem_union] at hv
        rcases hv with (h1 | h2) | h3
        · have := s₁ (Finset.mem_inter.2 ⟨h1, vU⟩); simp only [Finset.mem_union] at this ⊢; tauto
        · have := s₂ (Finset.mem_inter.2 ⟨h2, vU⟩); simp only [Finset.mem_union] at this ⊢; tauto
        · have := s₃ (Finset.mem_inter.2 ⟨h3, vU⟩); simp only [Finset.mem_union] at this ⊢; tauto
      · refine Finset.mem_union_right _ ?_
        simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢
        rcases hv with (h1 | h2) | h3
        · exact Or.inl (Or.inl ⟨h1, vU⟩)
        · exact Or.inl (Or.inr ⟨h2, vU⟩)
        · exact Or.inr ⟨h3, vU⟩
    have a := Finset.card_le_card sub
    have b := Finset.card_union_le (M₁ ∪ M₂ ∪ M₃) ((K₁ \ U) ∪ (K₂ \ U) ∪ (K₃ \ U))
    have c := card_union3_le M₁ M₂ M₃
    have d := card_union3_le (K₁ \ U) (K₂ \ U) (K₃ \ U)
    omega
  have hS := goodTriple_S_le hprop hτ hunif hK₁ hK₂ hK₃ hgood
  have ie := card_union_goodTriple (show K₁ ∩ K₂ ∩ K₃ = ∅ from hgood)
  rw [hunif K₁ hK₁, hunif K₂ hK₂, hunif K₃ hK₃] at ie
  clear rig
  omega

end Erdos644
