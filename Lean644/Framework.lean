import Lean644.Defs

/-!
# The avoidance framework (manuscript §2)

Source: six_sevenths_v3.tex, Section 2 ("The framework").

* If `τ(H) > T`, every set of at most `T` points (a *request*) is disjoint from some edge
  (a *response*): `exists_response`.
* **Request-cover principle** (manuscript Lemma 2.1): edges `E` and requests `D` with
  `|E| + |D| ≤ 7`, such that every two-point transversal of `E` lies inside some request,
  contradict property (7,2) once each request has a response: `request_cover`.
-/

namespace Erdos644

variable {α : Type*} [DecidableEq α]

/-- If `H` cannot be covered by `T` points, every set of at most `T` points misses some edge. -/
theorem exists_response {H : Finset (Finset α)} {T : ℕ} (hτ : ¬ CoverableBy H T)
    {d : Finset α} (hd : d.card ≤ T) : ∃ B ∈ H, Disjoint B d := by
  by_contra h
  push_neg at h
  exact hτ ⟨d, hd, fun A hA => Finset.not_disjoint_iff_nonempty_inter.1 (h A hA)⟩

/-- **Request-cover principle** (manuscript Lemma 2.1).
`E` is a nonempty set of edges, `D` a set of requests, each with a response in `H`.
If every pair `x, y` meeting all edges of `E` lies in a common request, then `E` together
with the responses is a subfamily of at most `|E| + |D|` edges without a 2-point cover;
so `|E| + |D| ≤ 7` contradicts property (7,2). -/
theorem request_cover {H : Finset (Finset α)} (hprop : HasPropertyAtMost H 7 2)
    {E D : Finset (Finset α)} (hEH : E ⊆ H) (hEne : E.Nonempty)
    (hcard : E.card + D.card ≤ 7)
    (hresp : ∀ d ∈ D, ∃ B ∈ H, Disjoint B d)
    (hcov : ∀ x y : α, (∀ A ∈ E, x ∈ A ∨ y ∈ A) → ∃ d ∈ D, x ∈ d ∧ y ∈ d) : False := by
  classical
  choose! resp hrespH hrespD using hresp
  set G := E ∪ D.image resp with hG
  have hGH : G ⊆ H := by
    intro B hB
    rcases Finset.mem_union.1 hB with hB | hB
    · exact hEH hB
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hB
      exact hrespH d hd
  have hGcard : G.card ≤ 7 :=
    (Finset.card_union_le _ _).trans ((Nat.add_le_add_left Finset.card_image_le _).trans hcard)
  have hGne : G.Nonempty := hEne.mono Finset.subset_union_left
  obtain ⟨x, y, hxy⟩ := (coverableBy_two_iff hGne).1 (hprop G hGH hGcard)
  obtain ⟨d, hd, hxd, hyd⟩ := hcov x y (fun A hA => hxy A (Finset.mem_union_left _ hA))
  have hB : resp d ∈ G := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hd)
  rcases hxy (resp d) hB with hx | hy
  · exact Finset.disjoint_left.1 (hrespD d hd) hx hxd
  · exact Finset.disjoint_left.1 (hrespD d hd) hy hyd

end Erdos644
