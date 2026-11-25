# Programme 5: target 7INV, transference and the complexity of the Fano pattern

Tags: [proved by hand], [computed], [heuristic], [open]. Nothing here is independently verified. Nothing committed.
Code: `compute/programme5/7inv/` (§8). Notation as in PROGRAMME5_SEVEN: H k-uniform, T-covering, n = (7/4+δ)k,
U = up-set, R_u = {x : ⟨χ(x),u⟩ = 1}, κ = log₁₀(P(all R_u ∈ U)/Π_u P(R_u ∈ U)) under balanced colourings.
A *seven* is a Fano-type good seven, i.e. a PG(2,2) ⊆ U.

## 0. Verdict
- **Complexity.** The Fano system has Cauchy–Schwarz complexity 2 and true complexity 2, not 1 (§1). Quadratic
  phases are exact zero mechanisms, so "Fourier-uniform ⇒ many Fano patterns" is false at density 1/2. Transference
  would output quadratic structure, not a coset.
- **Embeddings.** The colouring measure has exactly two Abelian embeddings (§2): weight (the size/fractional
  mechanism: 3H, RA, NC) and the line relations R_u+R_v+R_{u+v} = 0 (the parity mechanism: FKW, Corollary 7).
- **Prop Q.** Up-sets carry no degree-≤2 structure above level k+1 (§3.1). Algebraic structure must be read at member
  level.
- **Exactness.** Member-level quadratic obstructions are exact only at 4n = 7k (§3.2). There {B : q(B) = 1} is
  seven-free and coset-free. **A proof of 7INV must therefore use 4n − 7k → ∞, i.e. covering, not the 7-count alone.**
- **No usable majorant** (§4).
  - Covering bounds U only from below.
  - Symmetric majorants have relative density 2^{−Θ(k)}.
  - The member-count majorant ν_H has Θ(1) relative density, but its linear-forms condition lives on a 2^{−Ω(k)}-thin
    set of member tuples, and its 7-point part is the seven count itself (circular).
- **GAMMA.** Transference would escape GAMMA's step-count obstacle, but only via the missing majorant (§5).
  **Numerics:** coset bias and κ are unrelated except at exact algebraic points (§6).

## 1. Complexity of the 7 forms L_u(y) = Σ u_i y_i, u ∈ F₂³∖0
- **CS complexity 2** [proved by hand; `complexity.py`]. Fix L_{e1}. A class whose span avoids e1 lies in one of the 4
  planes avoiding e1, each with 3 nonzero vectors. Two such planes share a vector, so 2 classes cover ≤ 5 of the 6 other
  forms. Three classes suffice: {y2,y3,y2+y3}, {y1+y2,y1+y3}, {y1+y2+y3}.
- **True complexity ≥ 2** [proved by hand]. For quadratic q, Σ_u q(u·y) ≡ 0 (mod 2), since Σ_u u_i = 4 and
  Σ_u u_iu_j = 2. So {q = 1} contains no PG(2,2) (also PROGRAMME2_C §3).
  - Non-classical: Σ_u|u·y| = 4|supp y1 ∪ supp y2 ∪ supp y3|, so Π_u i^{|u·y|} ≡ 1.
  - [computed] 0 violations in 2·10⁴ random (q,y); cubic q breaks it 9926 times.
  - {x1x2+…+x9x10 = 1} ⊆ F₂¹⁰: density 0.484, max |Fourier| 2^{−6}, 0 PG(2,2) in 4·10⁵ sampled planes against 2502
    predicted.
- **True complexity ≤ 2** by U³ generalised von Neumann [standard]. "Structured" for Fano means quadratic phases.

## 2. The colouring measure [proved by hand + computed]
- Per point, (1[x∈R_u])_u is a weight-4 word of the [7,3] simplex code (0 for a zero class).
  - So the 7 forms are a correlated product space with ρ = 1 (c_u is fixed by the other six), pair correlation −1/6.
  - Under balanced colourings, |R_u ∩ R_v| = 2n/7 exactly.
- **Embeddings** E_m = {g ∈ Z_m⁷ : Σ g_u c_u constant on the support}: E_m = ⟨1⟩ + (m/2)·Ham for m even, ⟨1⟩ for
  m odd (|E_m| = 16, 3, 32, 5, 48, 7, 64 for m = 2..8). Over Z: only ⟨1⟩, since g is constant on lines and the
  incidence matrix has det ±24.
  - (a) **Weight**: Σ_u|R_u ∩ A| = 4|A∖Z₀|. Zero sets {|B∩A| ≥ t}, 7t > 4|A|, the fractional mechanism. Fixed sizes
    remove it from κ.
  - (b) **Lines** (Hamming = dual simplex): parity cosets. Corollary 7 / FKW; Theorem D caps it at e ≤ 3/2.
  - With a zero class, (a) survives only mod 4: the non-classical quadratic.
- In a Mossel / Bhangale–Khot–Minzer-type inverse theory ([cite?]; none with ρ = 1 and linear embeddings is known to us
  in usable form) the obstructions would be: low degree, (a), (b), and quadratic phases.

## 3. Where algebraic obstructions can live
**3.1 Prop Q** [proved by hand]. Let H be k-uniform and T-covering with T ≥ 4, and k+2 ≤ m ≤ n−2. If deg q ≤ 2 and q
is constant on U_m := U ∩ C(V,m), then q is constant on C(V,m).
*Proof.*
- For a member B, put W = V∖B and s = m−k. Then S ↦ q(B∪S) is constant on C(W,s).
- Swapping i ∈ S for j ∉ S (2 ≤ s ≤ |W|−2) makes a_il + a_jl independent of l. So a = z_i + z_l + c on W.
- Covering puts every ≤ T points in some W, and triangles chain through 4-sets. So c and z are global, and
  q = c·e₂ + |x∩P||x∖P| + ℓ(x) + const.
- On C(V,m): e₂ ≡ C(m,2) and |x∩P||x∖P| ≡ (m−1)|x∩P|, so q is affine there. Constancy on cones forces ℓ ∈ {0, 1_V}. ∎
- [computed] Excess dimension (`analyse.py` cone(m)) is 0 at all 9 tested m ≥ k+2 (random, TASKB ×2, star, cosets of
  codim 3/4/5, mod-4).
- **Sharp at m = k+1**: thresh(23,12) has x₂₂x₂₃ ≡ 0 on U₁₃, and the mod-4 families have excess 1. At m = k, cosets
  have excess 21–90.
- Coset structure fades in U above k+1: β_U(k+1) = 0.14–0.37 but β_U(k+2) ≤ 0.022 for coset layers.
- In the window 4n/7 = k + Θ(k), so 7INV's correlation must be stated for H, not U.

**3.2 Exactness** [proved by hand].
- If 4n = 7k, a seven has Σ|B_u| = 4n with j_x ≤ 4, so j_x ≡ 4. All s_p = 0, so {∅} ∪ {B_u} is a 3-space (Lemma 5),
  Σ_u q(B_u) = 0, and **H ⊆ {q = 1} is seven-free.**
- [computed] quad(21,12): 0 of 2·10⁵ colourings succeed (1557 predicted), with β_H = 0.009 against noise 0.014.
  τ = 8 < 3k/4, so this is not a counterexample.
- For 4n − 7k = c > 0, Lemma CL gives B_u = ψ(u) + E_u with Σ|E_u| ≤ 3c/2. Then Σ_u q(B_u) = Σ_u[q(E_u) +
  β(ψ(u),E_u)] is unforced. [computed] c = 4, 8, 10 give κ = 0.00.
- Mod-4 residues reduce to parity (with B_w = B_u+B_v, only c ≡ a+b (mod 2) is forced).
- **Summary.** In the window the exact-identity zero mechanisms of degree ≤ 2 are dead (U level: Prop Q; quadratic:
  only at 4n = 7k; Corollary-7 parity: Theorem D). Coset layers not killed by Corollary 7 are Piece B's open cases. Otherwise, a seven-free window family would need a
  non-algebraic zero mechanism.

## 4. Majorants [proved by hand unless tagged]
- **Covering gives only a minorant**: U ⊇ C(V, ≥ k+r). The Fano system cannot sit there, since Σ|R_u| ≤ 4n forces
  some |R_u| ≤ 4n/7 < k+r. This is exactly slope 3/7 (PROGRAMME5_SEVEN §1.2).
- **Symmetric ν**, including the random-family model E_{H'}1_{U_{H'}}, is constant on the balanced slice.
  - Relative density is then α = φ(4n/7) = 2^{−Θ(k)}.
  - Relative Szemerédi / removal (Green–Tao, Conlon–Fox–Zhao) needs δ bounded below. Its dense inputs lose
    exp(−poly(1/δ)) or worse, which is vacuous at δ = 2^{−Θ(k)}.
- **Member-count ν_H(R) = N_H(R)/E N_H(R_u)**, N_H(R) = #{B ∈ H : B ⊆ R} [proved + computed, `majorant.py`].
  - 1_U ≤ N_H, with relative density 1/E[N | N ≥ 1]: Θ(1) for spread H (Janson Δ ≲ E).
  - 2-point condition: E ν_H(R_u)ν_H(R_v) = E_{H²} g(|B∩B'|), with g explicit hypergeometric and Σ_i h(i)g(i) = 1
    for the complete family (checked to 10⁻⁶).
  - g(i) = 0 for i > 2n/7 < k²/n (N² < 7/2). **Typical member pairs are never co-realisable in a balanced seven.**
  - The count is carried by i* ≈ 0.48k against typical 0.55k (N = 1.8). Such pairs are a 2^{−(0.04±0.01)k} fraction
    (k ≤ 420, still drifting).
  - 7-point condition: E Π_u ν_H(R_u) is the weighted seven count over Π marg, i.e. **the target itself**. The tuples
    involved are ≤ 2^{−(5.6…6.9)k} of H⁷ (N = 1.833…1.76).
  - CFZ's 2-blow-up condition contains this 1-copy term, so it is circular too.
  - Clustered families (star, blocks, rich) fail even the 2-point condition [heuristic].
- **Even granted ν, the dense statement is false below 3/4.** PG(2,2)-free sets of every density < 3/4 exist
  (Bose–Burton, {q = 1}). Transference carries density, not crit(U) = τ.

## 5. The angle-2 chain
1. Majorant with δ_rel = Θ(1) and the linear-forms condition. **[open; no candidate, §4]**
2. Dense model g with count(f) ≈ count(g) [standard given 1, in U³(ν) form].
3. κ = −∞ ⇒ g correlates with a quadratic phase [U³ inverse; exp(−poly) loss is fine at δ_rel = Θ(1)].
4. Quadratic ⇒ coset: robust Prop Q [open]. The cone argument suggests bias on many cones forces bounded slice-rank,
   i.e. O(log 1/η) linear forms. It must be read at member level (§3.1).
5. Robust Piece B on the coset [open; INV-P §1.3 B_sub].
- **vs GAMMA** [heuristic].
  - Plain increment needs ≈ γk/ln(1+η) steps against a slack of < 1 unit per step.
  - A Θ(1)-relative majorant needs O_δ(1) steps, and ν-relative uniformity replaces GAMMA's e^{0.4–0.7k} light
    characters. So step 1 is where the exponential wall now sits (the thin tuples of §4).

## 6. Numerics [computed; `analyse.py`, 2·10⁵ balanced colourings; k ≤ 12, out of window]
β_H is the max hyperplane-coset bias of H, slice-corrected (noise ≈ √(2n ln2/|H|)). β_U(m) is the same for U_m.

| family (n,k) | τ | 4n−7k | r | β_H (noise) | β_U(k+1), (k+2) | marg | κ |
|---|---|---|---|---|---|---|---|
| FKW m=3 (22,12) | 10 | 4 | 1 | 1.00 (.010) | – | .50/1 | −∞ |
| coset codim 3,4,5 (21,10) | 9 | 14 | 3 | 1.00 (.03–.05) | .14–.37, ≤ .022 | .91–1 | 0.00 |
| covrand (21,10), (20,10) | 9 | 14, 10 | 3, 2 | ≈ noise | .014, .001 | .97–.99 | 0.00 |
| TASKB random / planted (21,10) | 9 | 14 | 3 | .08 / .41 (.084) | .03/.06, .013 | .57 | −0.01 |
| star + patch (21,10) | 9 | 14 | 3 | .83 (\|a\|=1) | .52, .087 | .93 | −0.02 |
| quad (21,12) | 8 | **0** | 2 | **.009 (.014)** | ≈ 0 | .50 | **−∞** |
| quad (22,12), (23,12), (20,10) | 9, 10, 9 | 4, 8, 10 | 2 | ≈ noise | ≈ 0 | .5–1 | 0.00 |
| thresh \|A\|=21 (23,12) | 10 | 8 | 2 | 1.04 (subcube) | .46 | .22–1 | +0.11 |

- Coset bias is neither necessary (quad at 4n = 7k) nor sufficient (cosets with r ≥ 2) for κ < 0.
- κ = −∞ only at exact algebraic points: FKW (parity, r = 1) and 4n = 7k (quadratic). Mod-4 families are parity cosets.
- Nothing here is sparse (marginals ≥ 0.16). Sparse instances need k ≳ 10³ (INV-P §3), so the §4 tilt is untested on
  explicit families.

## 7. Strongest statements and the exact obstruction
- [proved by hand] CS = true complexity 2; embeddings = weight ⊕ lines; Prop Q (sharp at k+1 [computed]); exactness
  (quadratic, coset-free, seven-free at 4n = 7k); no covering-derived or symmetric majorant beats 2^{−Θ(k)}; ν_H's
  condition is circular; members of a balanced seven pairwise meet in ≤ 2n/7 < k²/n points.
- **Exact obstruction.**
  - The Fano count is carried by a large-deviation sub-population: pairs at |B∩B'| ≈ 0.48k, and ≤ 2^{−5.6k} of H⁷.
  - Transference needs pseudorandomness of H at exactly that scale. Density, Fourier and U³ data do not control it,
    and covering gives only lower bounds on U.
  - Since the degree-≤2 exact mechanisms are dead in the window (§3.2), a counterexample would need a depletion of
    tilted tuples with no dense analogue.
- **7INV′** [open]. In the window, κ ≤ −θk ⇒ (i) depleted tilted pair spectrum (E_{H²} g ≤ 2^{−θ′k}) or
  (ii) member-level coset correlation strong enough for B_sub.
  - Test (i) first against PEN/P1: is there a heavy-pencil covering family with depleted tilted pairs? None is known.

## 8. Reproduction (`compute/programme5/7inv/`, `py -3.14`, ≤ 4 cores)
- `complexity.py` (3 s) → `logs/complexity.log`; `majorant.py` (6 s) → `logs/majorant.log`.
- `run.sh` (16 families, ~30 s) → `logs/panel_*.log`. It uses `fam.py` and `analyse.py SPEC [samples] [seed]`, with
  PYTHONPATH=../seven.
