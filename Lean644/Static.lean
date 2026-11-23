import Lean644.Triple

/-!
# Static closures (manuscript §3)

**Hall allocation** (manuscript Lemma 3.1). For a good triple `E, F, G` with
`X = E ∩ F`, `Y = E ∩ G`, `Z = F ∩ G` of sizes `a, b, c`, and private parts
`P_E, P_F, P_G` (sizes `k-a-b`, `k-a-c`, `k-b-c`), the four requests
```
R₁ = X ∪ G₁,  R₂ = X ∪ Y ∪ F₂ ∪ G₂,  R₃ = X ∪ Z ∪ E₃ ∪ G₃,  R₄ = Y ∪ Z ∪ E₄ ∪ F₄
```
with `P_G = G₁ ⊔ G₂ ⊔ G₃`, `P_F = F₂ ⊔ F₄`, `P_E = E₃ ⊔ E₄` cover all candidate pairs.
Instead of the manuscript's max-flow argument (Lemma 2.2) we give explicit piece sizes;
the formulas were first validated exhaustively in `compute/hall_formula_check.py`.
-/

namespace Erdos644

/-- Three bins with capacities `u₂ u₃ u₄`; demand `e` may use bins 3,4, demand `f` bins 2,4,
demand `q` bins 2,3. Hall's conditions suffice for an integral split. -/
theorem triangle_split (u₂ u₃ u₄ e f q : ℕ) (h1 : e ≤ u₃ + u₄) (h2 : f ≤ u₂ + u₄)
    (h3 : q ≤ u₂ + u₃) (h4 : e + f + q ≤ u₂ + u₃ + u₄) :
    ∃ e₃ e₄ f₂ f₄ q₂ q₃ : ℕ, e₃ + e₄ = e ∧ f₂ + f₄ = f ∧ q₂ + q₃ = q ∧
      f₂ + q₂ ≤ u₂ ∧ e₃ + q₃ ≤ u₃ ∧ e₄ + f₄ ≤ u₄ := by
  -- x = min e u₃ (P_E into bin 3), y = min f u₂ (P_F into bin 2)
  obtain ⟨x, hxe, hxu, hx⟩ : ∃ x, x ≤ e ∧ x ≤ u₃ ∧ (x = e ∨ x = u₃) :=
    ⟨min e u₃, min_le_left _ _, min_le_right _ _, min_choice _ _⟩
  obtain ⟨y, hyf, hyu, hy⟩ : ∃ y, y ≤ f ∧ y ≤ u₂ ∧ (y = f ∨ y = u₂) :=
    ⟨min f u₂, min_le_left _ _, min_le_right _ _, min_choice _ _⟩
  -- d = deficit of q in the leftover of bins 2,3
  obtain ⟨d, hd⟩ : ∃ d, (d = 0 ∧ q + x + y ≤ u₂ + u₃) ∨ d + u₂ + u₃ = q + x + y :=
    ⟨q + x + y - (u₂ + u₃), by omega⟩
  -- move `de` of P_E and `df` of P_F from bins 3,2 to bin 4
  obtain ⟨de, hde1, hde2, hde⟩ : ∃ de, de ≤ d ∧ de ≤ x ∧ (de = d ∨ de = x) :=
    ⟨min d x, min_le_left _ _, min_le_right _ _, min_choice _ _⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, x = x₂ + de := ⟨x - de, by omega⟩
  have hdfy : d - de ≤ y := by omega
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, y = y₂ + (d - de) := ⟨y - (d - de), by omega⟩
  -- z = min q (u₂ - y₂): rest of q into bin 2, remainder into bin 3
  obtain ⟨z, hzq, hzu, hz⟩ : ∃ z, z ≤ q ∧ z + y₂ ≤ u₂ ∧ (z = q ∨ z + y₂ = u₂) :=
    ⟨min q (u₂ - y₂), min_le_left _ _, by omega, by
      rcases min_choice q (u₂ - y₂) with h | h <;> [left; right] <;> omega⟩
  refine ⟨x₂, e - x₂, y₂, f - y₂, z, q - z, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · omega
  · omega

/-- Integer core of the Hall allocation: under the manuscript's inequalities (eq. (3.1)–(3.2);
two of the eleven, `2k+2a+b ≤ 4T` and `2k+2a+c ≤ 4T`, turn out to be implied by the others and
`a + b, a + c ≤ k`), the private parts split so that all four requests have size `≤ T`.
`pe, pf, pg` are the sizes of `P_E, P_F, P_G`. -/
theorem hall_sizes (k T a b c pe pf pg : ℕ)
    (he : a + b + pe = k) (hf : a + c + pf = k) (hg : b + c + pg = k)
    (h1 : a ≤ T) (h2 : a + b ≤ T) (h3 : a + c ≤ T) (h4 : b + c ≤ T)
    (h5 : k + 2 * b ≤ 2 * T) (h6 : k + 2 * c ≤ 2 * T) (h7 : k + 3 * a ≤ 3 * T)
    (h8 : 2 * k + b + c ≤ 3 * T) (h11 : 3 * k + a ≤ 4 * T) :
    ∃ g₁ g₂ g₃ f₂ f₄ e₃ e₄ : ℕ,
      g₁ + g₂ + g₃ = pg ∧ f₂ + f₄ = pf ∧ e₃ + e₄ = pe ∧
      a + g₁ ≤ T ∧ a + b + f₂ + g₂ ≤ T ∧ a + c + e₃ + g₃ ≤ T ∧ b + c + e₄ + f₄ ≤ T := by
  -- bin 1 (capacity T - a) is usable only by P_G: fill it first
  obtain ⟨g₁, hg1p, hg1c, hg1⟩ : ∃ g₁, g₁ ≤ pg ∧ g₁ + a ≤ T ∧ (g₁ = pg ∨ g₁ + a = T) :=
    ⟨min pg (T - a), min_le_left _ _, by omega, by
      rcases min_choice pg (T - a) with h | h <;> [left; right] <;> omega⟩
  obtain ⟨e₃, e₄, f₂, f₄, q₂, q₃, s1, s2, s3, s4, s5, s6⟩ :=
    triangle_split (T - a - b) (T - a - c) (T - b - c) pe pf (pg - g₁)
      (by omega) (by omega) (by omega) (by omega)
  exact ⟨g₁, q₂, q₃, f₂, f₄, e₃, e₄, by omega, s2, s1, by omega, by omega, by omega, by omega⟩

end Erdos644
