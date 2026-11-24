import Lean644.TheoremA

/-!
# Lemma B (trace lemma)

Source: `notes/NEW_PATHS.md` §1.3 (Fable research lead, 2026-11-23); hand-checked.

Let `τ(H) > T`, `(E, F, G)` a good triple with union `W`, and `K` any edge. Then
`2|K ∩ W| > 3T - |W|`. Proof: if not, split `W ∖ K` into three parts `Pᵢ` of size at most
`T - |K∩W|` and request `(K ∩ W) ∪ Pᵢ`. Any two points covering `E, F, G` lie in `W` (one in a
pair cell, the other in the third edge), one of them lies in `K ∩ W` (to cover `K`), hence both
lie in one request. So `E, F, G, K` and the three responses have no 2-point cover.
No uniformity is needed.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Lemma B (trace lemma).** -/
theorem trace_lemma {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T : ℕ}
    (hτ : ¬ CoverableBy H T) {E F G K : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hG : G ∈ H)
    (hK : K ∈ H) (hgood : IsGoodTriple E F G)
    (h : 2 * (K ∩ (E ∪ F ∪ G)).card + (E ∪ F ∪ G).card ≤ 3 * T) : False := by
  set W := E ∪ F ∪ G with hW
  set c := (K ∩ W).card with hc
  have e := Finset.card_sdiff_add_card_inter W K
  have hcK : (W ∩ K).card = c := by rw [Finset.inter_comm]
  obtain ⟨s₁, hs11, hs12, hs1⟩ : ∃ s₁, s₁ ≤ (W \ K).card ∧ c + s₁ ≤ T ∧
      (s₁ = (W \ K).card ∨ c + s₁ = T) :=
    ⟨min (W \ K).card (T - c), min_le_left _ _, by omega, by
      rcases min_choice (W \ K).card (T - c) with h' | h' <;> [left; right] <;> omega⟩
  obtain ⟨s₂, hs21, hs22, hs2⟩ : ∃ s₂, s₁ + s₂ ≤ (W \ K).card ∧ c + s₂ ≤ T ∧
      (s₁ + s₂ = (W \ K).card ∨ c + s₂ = T) :=
    ⟨min ((W \ K).card - s₁) (T - c), by omega, by omega, by
      rcases min_choice ((W \ K).card - s₁) (T - c) with h' | h' <;> [left; right] <;> omega⟩
  obtain ⟨P₁, P₂, P₃, -, -, -, covP, cP₁, cP₂, cP₃⟩ :=
    split_three (W \ K) s₁ s₂ ((W \ K).card - s₁ - s₂) (by omega)
  have sz : ∀ P : Finset α, c + P.card ≤ T → ((K ∩ W) ∪ P).card ≤ T := fun P hP =>
    (Finset.card_union_le _ _).trans hP
  refine request_cover hprop (E := {E, F, G, K})
    (D := {(K ∩ W) ∪ P₁, (K ∩ W) ∪ P₂, (K ∩ W) ∪ P₃}) ?_ ⟨E, by simp⟩ ?_ ?_ ?_
  · intro A hA; simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl <;> assumption
  · have a : ({E, F, G, K} : Finset (Finset α)).card ≤ 4 :=
      (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <| (Finset.card_insert_le _ _).trans
        <| Nat.succ_le_succ <| (Finset.card_insert_le _ _).trans (by simp)
    have b : ({(K ∩ W) ∪ P₁, (K ∩ W) ∪ P₂, (K ∩ W) ∪ P₃} : Finset (Finset α)).card ≤ 3 :=
      (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <|
        (Finset.card_insert_le _ _).trans (by simp)
    omega
  · intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact exists_response hτ (sz _ (by omega))
    · exact exists_response hτ (sz _ (by omega))
    · exact exists_response hτ (sz _ (by omega))
  · intro x y hxy
    have cE := hxy E (by simp)
    have cF := hxy F (by simp)
    have cG := hxy G (by simp)
    have cK := hxy K (by simp)
    -- both points lie in W
    have xyW : x ∈ W ∧ y ∈ W := by
      rcases triple_candidate hgood cE cF cG with
        ⟨a, b, c'⟩ | ⟨a, b, c'⟩ | ⟨a, b, c'⟩ | ⟨a, b, c'⟩ | ⟨a, b, c'⟩ | ⟨a, b, c'⟩ <;>
        exact ⟨by simp [W, a, b, c'], by simp [W, a, b, c']⟩
    -- the point of K lies in every request; the other lies in some request
    have other : ∀ u v, u ∈ K → u ∈ W → v ∈ W →
        ∃ d ∈ ({(K ∩ W) ∪ P₁, (K ∩ W) ∪ P₂, (K ∩ W) ∪ P₃} : Finset (Finset α)),
          u ∈ d ∧ v ∈ d := by
      intro u v uK uW vW
      have uKW : u ∈ K ∩ W := Finset.mem_inter.2 ⟨uK, uW⟩
      by_cases vK : v ∈ K
      · exact ⟨(K ∩ W) ∪ P₁, by simp, by simp [uKW], by simp [Finset.mem_inter.2 ⟨vK, vW⟩]⟩
      · rcases covP v (Finset.mem_sdiff.2 ⟨vW, vK⟩) with h1 | h1 | h1
        · exact ⟨(K ∩ W) ∪ P₁, by simp, by simp [uKW], by simp [h1]⟩
        · exact ⟨(K ∩ W) ∪ P₂, by simp, by simp [uKW], by simp [h1]⟩
        · exact ⟨(K ∩ W) ∪ P₃, by simp, by simp [uKW], by simp [h1]⟩
    rcases cK with hx | hy
    · exact other x y hx xyW.1 xyW.2
    · obtain ⟨d, hd, h1, h2⟩ := other y x hy xyW.2 xyW.1
      exact ⟨d, hd, h2, h1⟩

end Erdos644
