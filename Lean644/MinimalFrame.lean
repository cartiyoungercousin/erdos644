import Lean644.Defs

/-!
# The minimal-counterexample frame (notes/MINIMAL_FRAME.md, Lemmas 1, 3, 4)

Hand verification: notes/verify/minimal_frame.md (including the proof-text fixes, remarks B, C).
Minimality of a counterexample is never formalised as "minimal total size"; instead each lemma
takes, as an explicit hypothesis, exactly the consequence of minimality its proof uses.

* `private_set` (Lemma 3): if `τ(H) > T` and `τ(H ∖ {B}) ≤ T`, some `S` with `|S| ≤ T` and
  `S ∩ B = ∅` meets every other member.
* `shrink H B z`: the family with `B` replaced by `B ∖ {z}`;
  `not_coverableBy_shrink`: replacing keeps `τ > T`.
* `saturation_core` (Lemma 4, clean core): if `H` has `(7,2)` and the shrunk family fails
  `(7,2)`, then `B ∖ {z}` together with at most six members of `H ∖ {B}` has no 2-transversal.
* `saturation_ii` (Lemma 4 (ii)): for such members, every 2-transversal of `B, B₂, …, B_m`
  meets `B` exactly in `{z}`.
* `saturation` (Lemma 4, (i) and (ii)): with minimality as the hypothesis "if the shrunk family
  keeps `τ > T` then it fails `(7,2)`".
* `antichain` (remark A): under the minimality hypothesis "removing a member never leaves a
  counterexample", no member contains another; `saturation_of_minimal` uses it to show
  `B ∖ {z}` is not an existing member, alongside (i), (ii).
* `padding_coverable`, `padding_iff` (Lemma 1): padding to a `k`-uniform family over
  `α ⊕ (Finset α × ℕ)` preserves `(7,2)` and does not decrease `τ`; hence `f≤(k,7) = f(k,7)`.

`(7,2)` is `HasPropertyAtMost · 7 2` throughout (the "at most seven" convention of the note).
-/

namespace Erdos644
namespace MinimalFrame

variable {α : Type*} [DecidableEq α]

/-! ## Lemma 3 (private sets) -/

/-- **Lemma 3 (private sets).** Minimality is the hypothesis `hmin : τ(H ∖ {B}) ≤ T`.
(The property `(7,2)` is not needed.) -/
theorem private_set {H : Finset (Finset α)} {B : Finset α} {T : ℕ} (hB : B ∈ H)
    (hτ : ¬ CoverableBy H T) (hmin : CoverableBy (H.erase B) T) :
    ∃ S : Finset α, S.card ≤ T ∧ S ∩ B = ∅ ∧ IsTransversal (H.erase B) S := by
  obtain ⟨S, hS, htr⟩ := hmin
  refine ⟨S, hS, ?_, htr⟩
  rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
  intro x hxS hxB
  apply hτ
  refine ⟨S, hS, fun A hA => ?_⟩
  by_cases h : A = B
  · subst h
    exact ⟨x, Finset.mem_inter.2 ⟨hxB, hxS⟩⟩
  · exact htr A (Finset.mem_erase.2 ⟨h, hA⟩)

/-! ## Lemma 4 (saturation) -/

/-- The family `H` with the member `B` replaced by `B ∖ {z}`. -/
def shrink (H : Finset (Finset α)) (B : Finset α) (z : α) : Finset (Finset α) :=
  insert (B.erase z) (H.erase B)

/-- Replacing `B` by `B ∖ {z}` keeps `τ > T`: a transversal of the new family is one of `H`. -/
theorem not_coverableBy_shrink {H : Finset (Finset α)} {B : Finset α} {z : α} {T : ℕ}
    (hB : B ∈ H) (hτ : ¬ CoverableBy H T) : ¬ CoverableBy (shrink H B z) T := by
  rintro ⟨S, hS, htr⟩
  apply hτ
  refine ⟨S, hS, fun A hA => ?_⟩
  by_cases h : A = B
  · subst h
    obtain ⟨x, hx⟩ := htr _ (Finset.mem_insert_self _ _)
    rw [Finset.mem_inter] at hx
    exact ⟨x, Finset.mem_inter.2 ⟨Finset.mem_of_mem_erase hx.1, hx.2⟩⟩
  · exact htr A (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h, hA⟩))

/-- **Lemma 4, clean core.** If `H` has `(7,2)` and the shrunk family fails `(7,2)`, the failing
subfamily uses `B ∖ {z}`: there are at most six members `G ⊆ H ∖ {B}` such that
`B ∖ {z}, G` have no transversal of at most two points. -/
theorem saturation_core {H : Finset (Finset α)} {B : Finset α} {z : α}
    (hP : HasPropertyAtMost H 7 2)
    (hfail : ¬ HasPropertyAtMost (shrink H B z) 7 2) :
    ∃ G ⊆ H.erase B, G.card ≤ 6 ∧ ¬ CoverableBy (insert (B.erase z) G) 2 := by
  unfold HasPropertyAtMost at hfail
  push Not at hfail
  obtain ⟨G', hG'sub, hG'card, hG'nc⟩ := hfail
  have hmem : B.erase z ∈ G' := by
    by_contra hn
    apply hG'nc
    refine hP G' (fun A hA => ?_) hG'card
    rcases Finset.mem_insert.1 (hG'sub hA) with h | h
    · exact absurd (h ▸ hA) hn
    · exact Finset.mem_of_mem_erase h
  refine ⟨G'.erase (B.erase z), fun A hA => ?_, ?_, ?_⟩
  · rcases Finset.mem_insert.1 (hG'sub (Finset.mem_of_mem_erase hA)) with h | h
    · exact absurd h (Finset.ne_of_mem_erase hA)
    · exact h
  · have h1 := Finset.card_erase_of_mem hmem
    clear hG'nc hG'sub hP
    omega
  · rwa [Finset.insert_erase hmem]

/-- **Lemma 4 (ii).** If `B ∖ {z}, G` have no 2-transversal, every transversal `X` of `B, G`
with `|X| ≤ 2` satisfies `X ∩ B = {z}`. -/
theorem saturation_ii {B : Finset α} {z : α} {G : Finset (Finset α)}
    (hnc : ¬ CoverableBy (insert (B.erase z) G) 2) {X : Finset α} (hX : X.card ≤ 2)
    (htr : IsTransversal (insert B G) X) : X ∩ B = {z} := by
  have key : ∀ y ∈ X, y ∈ B → y = z := by
    intro y hyX hyB
    by_contra hyz
    apply hnc
    refine ⟨X, hX, fun A hA => ?_⟩
    rcases Finset.mem_insert.1 hA with h | h
    · subst h
      exact ⟨y, Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hyz, hyB⟩, hyX⟩⟩
    · exact htr A (Finset.mem_insert_of_mem h)
  obtain ⟨x, hx⟩ := htr B (Finset.mem_insert_self _ _)
  rw [Finset.mem_inter] at hx
  have hxz : x = z := key x hx.2 hx.1
  subst hxz
  ext y
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hyX, hyB⟩
    exact key y hyX hyB
  · rintro rfl
    exact ⟨hx.2, hx.1⟩

/-- **Lemma 4 (saturation), parts (i) and (ii).** Minimality is the hypothesis `hmin`: if the
family with `B` replaced by `B ∖ {z}` keeps `τ > T`, it fails `(7,2)` (it is smaller, so it is
not a counterexample). Then there are at most six members `G ⊆ H ∖ {B}` with
(i) `B ∖ {z}, G` have no 2-transversal; and `B, G` do have one (by `(7,2)`), and
(ii) every 2-transversal `X` of `B, G` has `X ∩ B = {z}`.
(The hypothesis `|B| ≥ 2` of the note only makes `B ∖ {z}` nonempty, i.e. makes `hmin` follow
from minimality; it is not used below.) -/
theorem saturation {H : Finset (Finset α)} {B : Finset α} {z : α} {T : ℕ}
    (hP : HasPropertyAtMost H 7 2) (hB : B ∈ H) (hτ : ¬ CoverableBy H T)
    (hmin : ¬ CoverableBy (shrink H B z) T → ¬ HasPropertyAtMost (shrink H B z) 7 2) :
    ∃ G ⊆ H.erase B, G.card ≤ 6 ∧
      ¬ CoverableBy (insert (B.erase z) G) 2 ∧
      CoverableBy (insert B G) 2 ∧
      ∀ X : Finset α, X.card ≤ 2 → IsTransversal (insert B G) X → X ∩ B = {z} := by
  obtain ⟨G, hGsub, hGcard, hnc⟩ := saturation_core hP (hmin (not_coverableBy_shrink hB hτ))
  refine ⟨G, hGsub, hGcard, hnc, ?_, fun X hX htr => saturation_ii hnc hX htr⟩
  refine hP _ (Finset.insert_subset hB (hGsub.trans (Finset.erase_subset _ _))) ?_
  have h1 := Finset.card_insert_le B G
  clear hnc hGsub hP hmin hτ
  omega

/-! ## Antichain (verification note, remark A) -/

/-- **Antichain.** Minimality is the hypothesis `hmin`: removing a member never leaves a
counterexample (the result is smaller). Then no member contains another: if `C ⊆ B` with
`C ≠ B`, removing `B` keeps `τ > T` (anything hitting `C` hits `B`) and keeps `(7,2)`. -/
theorem antichain {H : Finset (Finset α)} {T : ℕ}
    (hP : HasPropertyAtMost H 7 2) (hτ : ¬ CoverableBy H T)
    (hmin : ∀ B ∈ H, ¬ CoverableBy (H.erase B) T → ¬ HasPropertyAtMost (H.erase B) 7 2) :
    ∀ B ∈ H, ∀ C ∈ H, C ⊆ B → C = B := by
  intro B hB C hC hCB
  by_contra hne
  refine hmin B hB ?_ (fun G hG hc => hP G (hG.trans (Finset.erase_subset _ _)) hc)
  rintro ⟨S, hS, htr⟩
  apply hτ
  refine ⟨S, hS, fun A hA => ?_⟩
  by_cases h : A = B
  · subst h
    obtain ⟨x, hx⟩ := htr C (Finset.mem_erase.2 ⟨hne, hC⟩)
    rw [Finset.mem_inter] at hx
    exact ⟨x, Finset.mem_inter.2 ⟨hCB hx.1, hx.2⟩⟩
  · exact htr A (Finset.mem_erase.2 ⟨h, hA⟩)

/-- In an antichain, `B ∖ {z}` (for `z ∈ B`) is not a member: it is a proper subset of `B`. -/
theorem erase_not_mem_of_antichain {H : Finset (Finset α)} {B : Finset α} {z : α}
    (hanti : ∀ B ∈ H, ∀ C ∈ H, C ⊆ B → C = B) (hB : B ∈ H) (hz : z ∈ B) :
    B.erase z ∉ H := by
  intro h
  have h1 := hanti B hB _ h (Finset.erase_subset z B)
  have h2 : z ∈ B.erase z := by rw [h1]; exact hz
  exact (Finset.mem_erase.1 h2).1 rfl

/-- **Lemma 4 with the antichain property used explicitly.** Under both minimality hypotheses
(shrinking `B`, and removing any member), `B ∖ {z}` is a new set, not an existing member
(so the shrunk family really has the same number of members), and (i), (ii) hold. -/
theorem saturation_of_minimal {H : Finset (Finset α)} {B : Finset α} {z : α} {T : ℕ}
    (hP : HasPropertyAtMost H 7 2) (hB : B ∈ H) (hz : z ∈ B) (hτ : ¬ CoverableBy H T)
    (hminRemove : ∀ B ∈ H, ¬ CoverableBy (H.erase B) T → ¬ HasPropertyAtMost (H.erase B) 7 2)
    (hmin : ¬ CoverableBy (shrink H B z) T → ¬ HasPropertyAtMost (shrink H B z) 7 2) :
    B.erase z ∉ H ∧ (shrink H B z).card = H.card ∧
    ∃ G ⊆ H.erase B, G.card ≤ 6 ∧
      ¬ CoverableBy (insert (B.erase z) G) 2 ∧
      CoverableBy (insert B G) 2 ∧
      ∀ X : Finset α, X.card ≤ 2 → IsTransversal (insert B G) X → X ∩ B = {z} := by
  have hnew := erase_not_mem_of_antichain (antichain hP hτ hminRemove) hB hz
  refine ⟨hnew, ?_, saturation hP hB hτ hmin⟩
  have h1 : B.erase z ∉ H.erase B := fun h => hnew (Finset.mem_of_mem_erase h)
  have h2 := Finset.card_insert_of_notMem h1
  have h3 := Finset.card_erase_add_one hB
  unfold shrink
  clear hmin hminRemove hP hτ hnew h1
  omega

/-! ## Lemma 1 (padding) -/

/-- Pad `B` with `k - |B|` private points `(B, i)`, `i < k - |B|`. -/
def pad (k : ℕ) (B : Finset α) : Finset (α ⊕ (Finset α × ℕ)) :=
  B.disjSum ({B} ×ˢ Finset.range (k - B.card))

omit [DecidableEq α] in
theorem card_pad {k : ℕ} {B : Finset α} (hB : B.card ≤ k) : (pad k B).card = k := by
  unfold pad
  rw [Finset.card_disjSum, Finset.card_product, Finset.card_singleton, Finset.card_range]
  omega

omit [DecidableEq α] in
theorem pad_injective (k : ℕ) : Function.Injective (pad (α := α) k) := by
  intro B C h
  ext a
  have := congrArg (fun s => Sum.inl a ∈ s) h
  simpa [pad, Finset.inl_mem_disjSum] using this

/-- The padded family. -/
def padFamily (k : ℕ) (H : Finset (Finset α)) : Finset (Finset (α ⊕ (Finset α × ℕ))) :=
  H.image (pad k)

theorem padFamily_uniform {k : ℕ} {H : Finset (Finset α)} (hk : ∀ B ∈ H, B.card ≤ k) :
    IsUniform (padFamily k H) k := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hA
  exact card_pad (hk B hB)

/-- Padding preserves `(p,t)` (in particular `(7,2)`): the original points stay. -/
theorem padFamily_hasProperty {k p t : ℕ} {H : Finset (Finset α)}
    (hP : HasPropertyAtMost H p t) : HasPropertyAtMost (padFamily k H) p t := by
  intro G' hG' hcard
  classical
  set G := H.filter (fun B => pad k B ∈ G') with hGdef
  have himg : G.image (pad k) = G' := by
    ext A
    simp only [Finset.mem_image, hGdef, Finset.mem_filter]
    constructor
    · rintro ⟨B, ⟨-, hB⟩, rfl⟩
      exact hB
    · intro hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 (hG' hA)
      exact ⟨B, ⟨hB, hA⟩, rfl⟩
  have hGcard : G.card ≤ p := by
    rw [← himg, Finset.card_image_of_injective _ (pad_injective k)] at hcard
    exact hcard
  obtain ⟨T, hT, htr⟩ := hP G (Finset.filter_subset _ _) hGcard
  refine ⟨T.disjSum ∅, by rw [Finset.card_disjSum, Finset.card_empty]; omega, ?_⟩
  intro A hA
  rw [← himg] at hA
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hA
  obtain ⟨a, ha⟩ := htr B hB
  rw [Finset.mem_inter] at ha
  exact ⟨Sum.inl a, Finset.mem_inter.2
    ⟨Finset.inl_mem_disjSum.2 ha.1, Finset.inl_mem_disjSum.2 ha.2⟩⟩

/-- Push a point of the padded ground set back: `inl a ↦ {a}`, a private point of `B` ↦ one
point of `B` (or nothing if `B = ∅`). -/
noncomputable def pullPoint : α ⊕ (Finset α × ℕ) → Finset α
  | Sum.inl a => {a}
  | Sum.inr p => if h : p.1.Nonempty then {h.choose} else ∅

omit [DecidableEq α] in
theorem card_pullPoint_le (x : α ⊕ (Finset α × ℕ)) : (pullPoint x).card ≤ 1 := by
  rcases x with a | p
  · simp [pullPoint]
  · simp only [pullPoint]
    split_ifs <;> simp

/-- Padding does not decrease `τ`: a transversal of the padded family pushes back, without
growing, to a transversal of the original family (members nonempty). -/
theorem padding_coverable {k t : ℕ} {H : Finset (Finset α)} (hne : ∀ B ∈ H, B.Nonempty)
    (hcov : CoverableBy (padFamily k H) t) : CoverableBy H t := by
  obtain ⟨X, hX, htr⟩ := hcov
  refine ⟨X.biUnion pullPoint, ?_, ?_⟩
  · have h1 := Finset.card_biUnion_le_card_mul X pullPoint 1
      (fun x _ => card_pullPoint_le x)
    clear htr
    omega
  · intro B hB
    obtain ⟨x, hx⟩ := htr (pad k B) (Finset.mem_image_of_mem _ hB)
    rw [Finset.mem_inter] at hx
    obtain ⟨hxB, hxX⟩ := hx
    rcases x with a | p
    · refine ⟨a, Finset.mem_inter.2 ⟨Finset.inl_mem_disjSum.1 hxB, ?_⟩⟩
      exact Finset.mem_biUnion.2 ⟨Sum.inl a, hxX, by simp [pullPoint]⟩
    · have hp := Finset.inr_mem_disjSum.1 hxB
      rw [Finset.mem_product, Finset.mem_singleton] at hp
      have hne' : p.1.Nonempty := hp.1 ▸ hne B hB
      refine ⟨hne'.choose, Finset.mem_inter.2 ⟨hp.1 ▸ hne'.choose_spec, ?_⟩⟩
      exact Finset.mem_biUnion.2 ⟨Sum.inr p, hxX, by simp [pullPoint, hne']⟩

/-- **Lemma 1 (padding), `f≤(k,7) = f(k,7)`.** For `k ≥ 1` and every `t`: every `k`-uniform
`(7,2)`-family (over any type) has `τ ≤ t` iff every `(7,2)`-family of nonempty sets of at most
`k` points has `τ ≤ t`. -/
theorem padding_iff {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    (∀ (β : Type) [DecidableEq β] (H : Finset (Finset β)),
        IsUniform H k → HasPropertyAtMost H 7 2 → CoverableBy H t) ↔
    (∀ (β : Type) [DecidableEq β] (H : Finset (Finset β)),
        (∀ B ∈ H, B.Nonempty) → (∀ B ∈ H, B.card ≤ k) → HasPropertyAtMost H 7 2 →
          CoverableBy H t) := by
  constructor
  · intro hU β _ H hne hk' hP
    exact padding_coverable hne
      (hU _ (padFamily k H) (padFamily_uniform hk') (padFamily_hasProperty hP))
  · intro hL β _ H hU hP
    refine hL β H (fun B hB => ?_) (fun B hB => (hU B hB).le) hP
    rw [← Finset.card_pos, hU B hB]
    omega

end MinimalFrame
end Erdos644
