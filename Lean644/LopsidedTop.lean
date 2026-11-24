import Lean644.PairGap
import Lean644.ThreeCentres

/-!
# Theorem 6.4 (top of the lopsided regime), improved constant

Source: `notes/NEW_PATHS.md` §6.3 (Fable research lead), simplified here: the fourth request
does not need `G ∩ P₃`, which improves the hand constant from 30 to 26 (the LP-sharp value of §7).

Let `u` be such that every good triple has a pair cell `≥ u` (lex-min anchor), and `E, F` edges
with `|E ∩ F| = u`. Far pairs (`< u`) meet in at most `2k + 1 - 2u - T` points (pair gap).
1. Request `k - u + 1` points of `E ∩ F`; the response `G` is far from `E` and `F`.
2. `S ⊆ G`, `|S| = k - u + 1`, `S ⊇ G ∩ (E ∪ F)`. Request `S ∪ Q₃` (`Q₃ ⊆ E∩F`,
   `|Q₃| = T - (k - u + 1)`): the response `P₃` is far from `G`, hence close to `E` and `F`.
3. Request `S ∪ Q₄` (`Q₄ ⊆ E∩F`, `Q₄ ⊇ E ∩ F ∩ P₃`, `|Q₄| = |Q₃|`): the response `P₄` is far
   from `G`, close to `E, F`, and `E ∩ F ∩ P₃ ∩ P₄ = ∅`.
4. `U = E ∪ F ∪ P₃ ∪ P₄` has `|U| ≤ 6k - 5u - 2T + 2`, and `|G ∩ U| ≤ 4(2k + 1 - 2u - T)`.
5. Request `(G ∩ U) ∪ X` with `X ⊆ U ∖ G` of size `T - |G∩U|`: by `trace_pairs`,
   `|U| + |G ∩ U| > 2T`, contradicting 4 when `28k + 12 ≤ 16T + 26u`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- **Theorem 6.4 (top of the lopsided regime).** -/
theorem lopsided_top {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2) {T k u : ℕ}
    (hτ : ¬ CoverableBy H T) (hunif : IsUniform H k) (hTk : T ≤ k)
    (hlex : ∀ E ∈ H, ∀ F ∈ H, ∀ G ∈ H, IsGoodTriple E F G →
      u ≤ (E ∩ F).card ∨ u ≤ (E ∩ G).card ∨ u ≤ (F ∩ G).card)
    {E F : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hEF : (E ∩ F).card = u)
    (h2u : k + 1 ≤ 2 * u) (huT : u ≤ T) (h3 : 2 * k + 2 ≤ 2 * T + u)
    (hmain : 28 * k + 12 ≤ 16 * T + 26 * u) : False := by
  have hu : u ≤ k := by rw [← hEF, ← hunif E hE]; exact Finset.card_le_card Finset.inter_subset_left
  -- far pairs
  have far : ∀ A ∈ H, ∀ B ∈ H, (A ∩ B).card < u → (A ∩ B).card + 2 * u + T ≤ 2 * k + 1 :=
    fun A hA B hB h => by
      by_contra hc
      exact pair_gap hτ hunif hlex hA hB h (by omega) hu huT
  -- close from a good triple with two far pairs
  have close : ∀ A ∈ H, ∀ B ∈ H, ∀ C ∈ H, IsGoodTriple A B C → (A ∩ B).card < u →
      (B ∩ C).card < u → u ≤ (A ∩ C).card := fun A hA B hB C hC hg h1 h2 => by
    rcases hlex A hA B hB C hC hg with h | h | h <;> omega
  have kE := hunif E hE
  have kF := hunif F hF
  -- subtraction-free sizes: sa = k - u + 1, sb = T - sa
  obtain ⟨sa, ha⟩ : ∃ sa, sa + u = k + 1 := ⟨k + 1 - u, by omega⟩
  obtain ⟨sb, hb⟩ : ∃ sb, sb + sa = T := ⟨T - sa, by omega⟩
  -- step 1: G
  obtain ⟨Q₀, hQ₀, cQ₀⟩ := Finset.exists_subset_card_eq (show sa ≤ (E ∩ F).card by omega)
  obtain ⟨G, hG, dG⟩ := exists_response hτ (show Q₀.card ≤ T by omega)
  have kG := hunif G hG
  have trace_le : ∀ (A B D : Finset α), A ∈ H → D ⊆ A → Disjoint B D →
      (A ∩ B).card + D.card ≤ k := fun A B D hA hD hBD => by
    have d : Disjoint (A ∩ B) D := Finset.disjoint_of_subset_left Finset.inter_subset_right hBD
    have := Finset.card_le_card (Finset.union_subset (Finset.inter_subset_left : A ∩ B ⊆ A) hD)
    rw [card_union_disj d, hunif A hA] at this; exact this
  have gE := trace_le E G Q₀ hE (hQ₀.trans Finset.inter_subset_left) dG
  have gF := trace_le F G Q₀ hF (hQ₀.trans Finset.inter_subset_right) dG
  have fGE := far E hE G hG (by omega)
  have fGF := far F hF G hG (by omega)
  -- step 2: S and P₃
  have cGEF : (G ∩ (E ∪ F)).card ≤ (E ∩ G).card + (F ∩ G).card := by
    rw [Finset.inter_union_distrib_left, Finset.inter_comm G E, Finset.inter_comm G F]
    exact Finset.card_union_le _ _
  have eGo := Finset.card_sdiff_add_card_inter G (E ∪ F)
  have hGa : (G ∩ (E ∪ F)).card ≤ sa := by clear * - cGEF fGE fGF ha hmain hTk huT h3; omega
  obtain ⟨sc, hc⟩ : ∃ sc, sc + (G ∩ (E ∪ F)).card = sa := ⟨sa - (G ∩ (E ∪ F)).card, by omega⟩
  obtain ⟨S', hS', cS'⟩ := Finset.exists_subset_card_eq
    (show sc ≤ (G \ (E ∪ F)).card by clear * - hc eGo kG ha hu h2u; omega)
  set S := (G ∩ (E ∪ F)) ∪ S' with hS
  have dS : Disjoint (G ∩ (E ∪ F)) S' := Finset.disjoint_left.2 fun v h1 h2 =>
    (Finset.mem_sdiff.1 (hS' h2)).2 (Finset.mem_inter.1 h1).2
  have cS : S.card = sa := by rw [hS, card_union_disj dS, cS']; omega
  have SG : S ⊆ G := Finset.union_subset Finset.inter_subset_left (hS'.trans Finset.sdiff_subset)
  have SEG : E ∩ G ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_inter.2
    ⟨(Finset.mem_inter.1 hv).2, Finset.mem_union_left _ (Finset.mem_inter.1 hv).1⟩)
  have SFG : F ∩ G ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_inter.2
    ⟨(Finset.mem_inter.1 hv).2, Finset.mem_union_right _ (Finset.mem_inter.1 hv).1⟩)
  obtain ⟨Q₃, hQ₃, cQ₃⟩ := Finset.exists_subset_card_eq
    (show sb ≤ (E ∩ F).card by omega)
  obtain ⟨P₃, hP₃, dP₃⟩ := exists_response hτ (d := S ∪ Q₃)
    ((Finset.card_union_le _ _).trans (by omega))
  have nP₃S : Disjoint P₃ S := Finset.disjoint_of_subset_right Finset.subset_union_left dP₃
  have nP₃Q : Disjoint P₃ Q₃ := Finset.disjoint_of_subset_right Finset.subset_union_right dP₃
  have gP₃ := trace_le G P₃ S hG SG nP₃S
  have fGP₃ := far G hG P₃ hP₃ (by omega)
  have goodT : ∀ A ∈ H, ∀ P ∈ H, A ∩ G ⊆ S → Disjoint P S → IsGoodTriple A G P :=
    fun A _ P _ hAG hPS => by
      unfold IsGoodTriple; ext v
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      rintro ⟨a, g⟩ p
      exact Finset.disjoint_left.1 hPS p (hAG (Finset.mem_inter.2 ⟨a, g⟩))
  have cEP₃ := close E hE G hG P₃ hP₃ (goodT E hE P₃ hP₃ SEG nP₃S) (by omega)
    (by omega)
  have cFP₃ := close F hF G hG P₃ hP₃ (goodT F hF P₃ hP₃ SFG nP₃S) (by omega)
    (by omega)
  -- step 3: Q₄ ⊇ E ∩ F ∩ P₃, P₄
  have cEFP₃ : (E ∩ F ∩ P₃).card + Q₃.card ≤ u := by
    have d : Disjoint (E ∩ F ∩ P₃) Q₃ :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right nP₃Q
    have := Finset.card_le_card (Finset.union_subset (Finset.inter_subset_left : E ∩ F ∩ P₃ ⊆ E ∩ F) hQ₃)
    rw [card_union_disj d, hEF] at this; exact this
  have e4 := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left : E ∩ F ∩ P₃ ⊆ E ∩ F)
  obtain ⟨sd, hd⟩ : ∃ sd, sd + (E ∩ F ∩ P₃).card = sb :=
    ⟨sb - (E ∩ F ∩ P₃).card, by clear * - cEFP₃ cQ₃ ha hb h3; omega⟩
  obtain ⟨Q', hQ', cQ'⟩ := Finset.exists_subset_card_eq
    (show sd ≤ ((E ∩ F) \ (E ∩ F ∩ P₃)).card by clear * - hd e4 hEF cEFP₃ cQ₃; omega)
  set Q₄ := (E ∩ F ∩ P₃) ∪ Q' with hQ₄
  have dQ : Disjoint (E ∩ F ∩ P₃) Q' := Finset.disjoint_left.2 fun v h1 h2 =>
    (Finset.mem_sdiff.1 (hQ' h2)).2 h1
  have cQ₄ : Q₄.card = sb := by rw [hQ₄, card_union_disj dQ, cQ']; omega
  have Q₄EF : Q₄ ⊆ E ∩ F := Finset.union_subset Finset.inter_subset_left
    (hQ'.trans Finset.sdiff_subset)
  obtain ⟨P₄, hP₄, dP₄⟩ := exists_response hτ (d := S ∪ Q₄)
    ((Finset.card_union_le _ _).trans (by omega))
  have nP₄S : Disjoint P₄ S := Finset.disjoint_of_subset_right Finset.subset_union_left dP₄
  have nP₄Q : Disjoint P₄ Q₄ := Finset.disjoint_of_subset_right Finset.subset_union_right dP₄
  have gP₄ := trace_le G P₄ S hG SG nP₄S
  have fGP₄ := far G hG P₄ hP₄ (by omega)
  have cEP₄ := close E hE G hG P₄ hP₄ (goodT E hE P₄ hP₄ SEG nP₄S) (by omega)
    (by omega)
  have cFP₄ := close F hF G hG P₄ hP₄ (goodT F hF P₄ hP₄ SFG nP₄S) (by omega)
    (by omega)
  have quad : ∀ v, v ∈ E → v ∈ F → v ∈ P₃ → v ∈ P₄ → False := fun v a b c d =>
    Finset.disjoint_left.1 nP₄Q d (Finset.mem_union_left _ (by simp [a, b, c]))
  have cEFP₄ : (E ∩ F ∩ P₄).card + Q₄.card ≤ u := by
    have d : Disjoint (E ∩ F ∩ P₄) Q₄ :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right nP₄Q
    have := Finset.card_le_card (Finset.union_subset (Finset.inter_subset_left : E ∩ F ∩ P₄ ⊆ E ∩ F) Q₄EF)
    rw [card_union_disj d, hEF] at this; exact this
  -- step 4: the union U
  set P : Finset (Finset α) := {E, F, P₃, P₄} with hP
  have memU : ∀ v, v ∈ P.sup id ↔ v ∈ E ∨ v ∈ F ∨ v ∈ P₃ ∨ v ∈ P₄ := fun v => by
    simp [hP, Finset.sup_insert]
  -- |P₃ ∖ (E∪F)| and |P₄ ∖ (E∪F)|
  have outside : ∀ Pi : Finset α, Pi ∈ H → u ≤ (E ∩ Pi).card → u ≤ (F ∩ Pi).card →
      (Pi \ (E ∪ F)).card + 2 * u ≤ k + (E ∩ F ∩ Pi).card := fun Pi hPi h1 h2 => by
    have a := Finset.card_sdiff_add_card_inter Pi (E ∪ F)
    have b := Finset.card_union_add_card_inter (Pi ∩ E) (Pi ∩ F)
    have e1 : Pi ∩ (E ∪ F) = (Pi ∩ E) ∪ (Pi ∩ F) := Finset.inter_union_distrib_left _ _ _
    have e2 : (Pi ∩ E) ∩ (Pi ∩ F) = E ∩ F ∩ Pi := by ext v; simp; tauto
    rw [Finset.inter_comm E Pi] at h1; rw [Finset.inter_comm F Pi] at h2
    rw [e1, hunif Pi hPi] at a; rw [e2] at b
    omega
  have o3 := outside P₃ hP₃ cEP₃ cFP₃
  have o4 := outside P₄ hP₄ cEP₄ cFP₄
  have cUle : (P.sup id).card ≤ 6 * k - 5 * u - 2 * T + 2 := by
    have sub : P.sup id ⊆ (E ∪ F) ∪ (P₃ \ (E ∪ F)) ∪ (P₄ \ (E ∪ F)) := fun v hv => by
      rw [memU] at hv
      simp only [Finset.mem_union, Finset.mem_sdiff]
      by_cases a : v ∈ E
      · exact Or.inl (Or.inl (Or.inl a))
      by_cases b : v ∈ F
      · exact Or.inl (Or.inl (Or.inr b))
      rcases hv with h | h | h | h
      · exact absurd h a
      · exact absurd h b
      · exact Or.inl (Or.inr ⟨h, fun h' => h'.elim a b⟩)
      · exact Or.inr ⟨h, fun h' => h'.elim a b⟩
    have a := Finset.card_le_card sub
    have b := card_union3_le (E ∪ F) (P₃ \ (E ∪ F)) (P₄ \ (E ∪ F))
    have c := Finset.card_union_add_card_inter E F
    rw [hEF, kE, kF] at c
    clear * - a b c o3 o4 cEFP₃ cEFP₄ cQ₃ cQ₄ ha hb hTk huT h2u h3
    omega
  -- trace of G on U
  have cGU : (G ∩ P.sup id).card ≤ 4 * (2 * k + 1 - 2 * u - T) := by
    have sub : G ∩ P.sup id ⊆ (E ∩ G) ∪ (F ∩ G) ∪ (G ∩ P₃) ∪ (G ∩ P₄) := fun v hv => by
      rw [Finset.mem_inter, memU] at hv
      obtain ⟨g, h⟩ := hv
      rcases h with h | h | h | h <;> simp [g, h]
    have a := Finset.card_le_card sub
    have b := card_union4_le (E ∩ G) (F ∩ G) (G ∩ P₃) (G ∩ P₄)
    clear * - a b fGE fGF fGP₃ fGP₄
    omega
  -- step 5: the last request and trace_pairs
  have eU := Finset.card_sdiff_add_card_inter (P.sup id) G
  obtain ⟨X, hX, cX⟩ := Finset.exists_subset_card_eq
    (show min (T - (G ∩ P.sup id).card) ((P.sup id) \ G).card ≤ ((P.sup id) \ G).card from
      min_le_right _ _)
  have cXD : ((G ∩ P.sup id) ∪ X).card ≤ T := (Finset.card_union_le _ _).trans
    (by clear * - cX cGU hmain hTk huT h2u h3; omega)
  obtain ⟨C, hC, dC⟩ := exists_response hτ cXD
  have hPH : P ⊆ H := by
    intro A hA; simp only [hP, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl <;> assumption
  have hPc : P.card ≤ 4 := (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <|
    (Finset.card_insert_le _ _).trans <| Nat.succ_le_succ <|
      (Finset.card_insert_le _ _).trans (by simp)
  have hPe : ∀ x, ∃ A ∈ P, x ∉ A := fun x => by
    by_cases a : x ∈ E
    · by_cases b : x ∈ F
      · by_cases c : x ∈ P₃
        · exact ⟨P₄, by simp [hP], fun d => quad x a b c d⟩
        · exact ⟨P₃, by simp [hP], c⟩
      · exact ⟨F, by simp [hP], b⟩
    · exact ⟨E, by simp [hP], a⟩
  have hGC : ∀ x ∈ G, x ∈ C → x ∉ P.sup id := fun x hg hc hu' =>
    Finset.disjoint_left.1 dC hc (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hg, hu'⟩))
  have tp := trace_pairs hprop hτ hPH hPc hPe hG hC hGC
  -- C ∩ U avoids G ∩ U and X
  have cCU : (C ∩ P.sup id).card + (G ∩ P.sup id).card + X.card ≤ (P.sup id).card := by
    have d1 : Disjoint (C ∩ P.sup id) (G ∩ P.sup id) := Finset.disjoint_left.2 fun v h1 h2 =>
      Finset.disjoint_left.1 dC (Finset.mem_inter.1 h1).1 (Finset.mem_union_left _ h2)
    have d2 : Disjoint ((C ∩ P.sup id) ∪ (G ∩ P.sup id)) X := Finset.disjoint_left.2
      fun v h1 h2 => by
        rcases Finset.mem_union.1 h1 with h | h
        · exact Finset.disjoint_left.1 dC (Finset.mem_inter.1 h).1 (Finset.mem_union_right _ h2)
        · exact (Finset.mem_sdiff.1 (hX h2)).2 (Finset.mem_inter.1 h).1
    have := Finset.card_le_card (show (C ∩ P.sup id) ∪ (G ∩ P.sup id) ∪ X ⊆ P.sup id from
      Finset.union_subset (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
        (hX.trans Finset.sdiff_subset))
    rwa [card_union_disj d2, card_union_disj d1] at this
  rw [Finset.inter_comm (P.sup id) G] at eU
  clear * - tp cCU cX eU cUle cGU hmain hTk huT h2u h3 ha hb
  omega

end Erdos644
