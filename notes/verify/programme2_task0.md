# Verification of notes/PROGRAMME_2.md, Task 0

Code: `compute/programme2/verify/` (`task0_checks.py`, `maxint7_enum.js`, `maxint7_lp.py`, `maxint7_sat.py`).
Logs: `compute/programme2/verify/out/`. Everything is integer or Fraction arithmetic. Each LP is solved in floats and then
re-certified exactly with a rational primal and dual. `task0_checks.py` seed 1: 0 failures.

## Verdicts

| Item | Verdict |
|---|---|
| Lemma 2 (colouring criterion) | PASS |
| Theorem 3 (incl. greedy bound, both consequences, LP duality for τ*_b) | PASS |
| Lemma 5 (identity, inequality, zero-slack subspace, (Σ)(b) translation, 12δk) | PASS |
| Corollary 7 (incl. FKW at 7m+1 and 7m+2) | PASS. The 7m+2 claim is not a consequence of Cor 7; we checked it separately |
| Lemma 8 (both parts) | PASS, with a remark on distinct members |
| Heavy-atom case of Theorem 3 | **FAIL as stated** (counterexamples). Refined Theorem 3H proved. Asymptotic version: **GAP** |
| Every good seven is Fano-type for N < 11/6 | **PASS, EXACT** computer-assisted proof, by two independent methods. Sharp (the infimum over non-Fano patterns is exactly 11/6) |
| (Σ)(a) in F₂ form | PASS. It is a four-term relation, as expected |
| (Σ)(c) in F₂ form | **FAIL of the expected shape**. It is not a four-term ≈ 0 relation; the correct form is given below |

## 1. Lemma 2, Theorem 3, Lemma 5, Corollary 7, Lemma 8

**Lemma 2.** If no L_ℓ is a transversal, then each line has a member B_ℓ ⊆ R_ℓ; repeats are allowed, since (7,2) concerns at most seven members. Take any x, y ∈ V with colours p and q. Some line ℓ contains both p and q (any line through p if p = q). Then x, y ∈ L_ℓ, so B_ℓ misses both, and there is no 2-point transversal. Points outside V hit nothing.
- Test: 567 random instances with no transversal line. Every resulting seven was checked by brute force for a 2-transversal; none had one.

**Theorem 3.** Greedy: put each point into the currently lightest class. When x enters class c, load(c) ≤ (mass already placed)/7 ≤ (y(V) − y(x))/7. So the final load is ≤ y(V)/7 + (6/7)·y(x), slightly better than the stated bound, and this holds for any order of the points.
- A line then has mass < 1, so L_ℓ is not a transversal, because transversals have y-mass ≥ 1. Then Lemma 2 applies.
- Consequence 1: y ≡ 1/τ gives τ ≤ 3(n+7)/7.
- Consequence 2: for the pool family K_{k+τ−1}^{(k)}, 7τ > 3(n+7) ⟺ 4τ > 3k + 18, i.e. τ > 3k/4 + 9/2. Checked for all k < 200.
- τ*_b is the LP min y(V) subject to y(M) ≥ 1 over minimal transversals. Its dual is the fractional packing of transversals (standard).
- Tests: 3000 random and adversarial weight vectors (equal weights, a few heavy plus many light) in random orders; the class and line bounds held exactly. 11 end-to-end instances (complete or 97%-dense K_n^(k), n = 9..13, optimal y from the LP): the greedy lines are non-transversals and the seven is good.

**Lemma 5.** Let x have colour c. Then x ∉ B_ℓ for the 3 lines through c, so j_x ≤ 4, and J_x (the lines whose member contains x) is a set of lines avoiding c.
- Let f(j) be the number of points lying on an odd number of the lines in J_x. Then f = 0, 3, 4, 3, 0 for j = 0..4.
  - j = 3: three lines avoiding c are never concurrent, since a pencil always contains the line to c. They form a triangle with 3 odd points.
  - j = 4: every point other than c lies on exactly 2 of the 4 lines.
  - So f(j) = j(4 − j).
- Inequality: j(4 − j) ≤ 3(4 − j) for 1 ≤ j ≤ 4, summed over ∪B_ℓ.
- No slack means j_x = 4 on ∪B. Then every s_p = 0, so ℓ ↦ B_ℓ (with lines read as nonzero vectors of the dual F₂³) satisfies the linear relations and extends to a linear map. Its image is {∅} ∪ {B_ℓ}. It has dimension exactly 3, since any kernel vector would force some B_ℓ = ∅.
- (Σ)(b): for three k-sets with empty triple intersection, wt(x₁+x₂+x₃) = 2|∪| − 3k. So |∪| ≤ 2T ⟺ wt ≤ 4T − 3k.
- 12δk: follows from |∪B| ≤ n.
- Tests: 20000 random (χ, B_ℓ ⊆ R_ℓ), exact equality and inequality. 2043 zero-slack instances: all s_p = 0, and they form a 3-dimensional subspace. Control: without B_ℓ ⊆ R_ℓ the identity fails.

**Corollary 7.** Each s_p is a sum of three elements of a + C (repeats allowed), so s_p ∈ a + C and wt ≥ ρ ≥ 1. Then 7ρ ≤ Σ wt(s_p) ≤ 3(4n − 7k).
- Exact SAT test on 281 random coset families (n ≤ 11), 139 of them satisfying the hypothesis: none has a Fano-type good seven. Every SAT witness satisfies 7ρ ≤ Σ wt(s_p) ≤ 3(4n − 7k).
- FKW (edges with |A∩X| odd, which forces |A∩Y| odd; ρ = 2), exact search over class sizes for m = 1, 2, 3:
  - on 7m+1 points: no Fano-type good seven;
  - on 7m+2 points: one exists, e.g. m = 1 with X-classes (0,0,0,0,1,1,2) and Y-classes (0,1,0,2,1,1,0).
  - The 7m+2 statement is true but is NOT implied by Cor 7 (24 > 14 only removes the obstruction).

**Lemma 8.** Hand proof:
- Pick B₁. Let j = ⌊(k+1)/2⌋. Take S₂ = (j points of B₁) ∪ (k + r − j outside points); this needs n ≥ 3k/2 + r. A member B₂ ⊆ S₂ has i = |B₁∩B₂| ∈ [j − r, j].
- Then d = |B₁+B₂| = 2(k − i) ∈ [k − 1, k + 2r].
- If d ≤ k + r: take S ⊇ B₁+B₂ with |S| = k + r. A member B₃ ⊆ S gives wt ≤ (k + r − d) + r ≤ 2r + 1.
- If d ≥ k + r: take S ⊆ B₁+B₂. Then wt = d − k ≤ 2r.
- Part 2: choose S ⊆ supp(c) and B ⊆ S; then B + c ∈ a + C has weight w − k.
- Remark: the three members can coincide only when k ≤ 2r + 1. For the coset conclusion ρ ≤ 2r + 1, repeats are harmless.
- Tests: 131 random instances plus 20 greedy-deletion adversarial ones, all ≤ 2r + 1. Part 2 tested on random codes. The adversarial test is weak (minimum triple sums 0–1).

## 2. Heavy-atom case: FAIL as stated, refined theorem, GAP

The natural statement is "τ*_b < 7/3 (rich) ⟹ not (7,2)", or the same with "an optimal y with atoms ≥ a". It is **false**:
- (i) H = {{a}}: τ*_b = 1 and H is (7,2). Uniform version: star_a(U) ∪ {complements of singletons in [8]} is 7-uniform, (7,2), τ = 3, τ*_b → 2.
- (ii) Large τ/k: K_10^(6) is (7,2), since 7 co-edges of size 4 cover ≤ 42 < 45 pairs. It has τ = 5 > 3k/4 and τ*_b = 2 = 7/3 − 1/3 (exact LP).
  - Every optimal y has an atom ≥ 1/5, because the average weight is 1/5. There are 10 heavy points ≤ 7/(3a).
  - So it satisfies exactly the heavy-atom hypotheses, with η = 1/3.
- (iii) A case analysis on y alone cannot work. Take three atoms of 49/100 plus light mass 4/5 split into atoms ≤ 1/100 (y(V) = 2.27 < 7/3, every pair of atoms sums to < 1). Over all 7³ placements of the heavy atoms, the best fractional max line mass is 13/12 > 1. So no colouring has all lines < 1, and any proof must use H, not only y.

**Theorem 3H (proved; strictly extends Theorem 3, the case A = ∅, c ≡ L/7).** Let A ⊆ V, let a′ = max y on V∖A, and L = y(V∖A). Suppose there is a map π: A → Π and c ∈ R⁷_{≥0} with Σc = L and, for every line ℓ, y(π⁻¹(ℓ)) + Σ_{p∈ℓ} c_p + 3a′ < 1. Then H is not (7,2).
*Proof.* Fill the classes with light points in sequence, class p until its load reaches c_p, so each overshoot is < a′ and the last class takes only the remainder ≤ c_p. Then apply Lemma 2. ∎
For |A| < 7/(3a) this is a finite set of 7-variable LPs: this is the honest "finite case analysis".

**GAP:** whether rich ⟹ not (7,2) holds asymptotically (η and a fixed, k → ∞, τ > (3/4 + ε)k). Examples (i)–(iii) show that Programme A needs this restricted form and an argument that uses H.

## 3. N < 11/6 ⟹ every good seven is Fano-type: EXACT proof

**Model** (CORE 1.3/16). Co-types F ⊆ [7] with masses m_F, pairwise intersecting support, Σ_{F∌i} m_F = 1 for each i, and N = Σm_F. Integer data at finite k is the special case m ∈ (1/k)Z, and repeated members are allowed.

**Reduction (proved).** Fano-type means the support lies in the up-set U_P of the lines of some plane P. Each U_P is a maximal intersecting family, since for every G exactly one of G and Gᶜ contains a line.
- A non-Fano support S extends to a maximal intersecting M ⊇ S with M ≠ every U_P.
- The masses are feasible for LP(M) = min Σm subject to Σ_{F∌i} m_F ≥ 1, F ∈ M. So N ≥ LP(M).
- Hence the claim ⟺ LP(M) ≥ 11/6 for every maximal intersecting M on [7] other than the 30 Fano up-sets.

**Method A (exhaustive).** `maxint7_enum.js` enumerates all self-dual up-sets of 2^[7].
- It finds 1 422 564 of them, which matches the known count of maximal intersecting families on 7 points (OEIS A001206). They fall into 716 S₇-classes; the orbit-stabiliser sum equals the total.
- `maxint7_lp.py` solves each class exactly: rational primal and dual, both checked feasible in Fractions, with equal objectives.
- Results:
  - the dictator class is infeasible (no pattern lives on it);
  - the Fano class has LP 7/4;
  - every other class has LP ≥ **11/6**;
  - 4 classes reach exactly 11/6, with dual w = (1/6,1/6,1/6,1/3,1/3,1/3,1/3), and their optimal supports are CORE's Fano-supported 11/6 pattern;
  - the next value is 15/8, consistent with CORE §16.

**Method B (independent).** `maxint7_sat.py`, CEGAR with CaDiCaL:
- Clauses encode "M is a self-dual up-set and not a Fano up-set".
- Each rational dual w is exactly checked and forbids every S₇-image of {G : w(G) > 1} ⊆ M.
- The solver returns UNSAT after 44 iterations (43 certificates, the least being 11/6).
- Control: with threshold 15/8 it immediately returns a non-Fano M with LP 11/6.

**Conclusion.** For N < 11/6 every good seven is Fano-type, so the float MILPs of CORE 1.3 and 8.3 are now exact. The bound is sharp as an infimum: add mass ε on a lineless co-type of an 11/6 class.
- Remaining trust: Method B rests on an unchecked SAT UNSAT. Method A needs no solver trust beyond the enumeration code, whose count matches the known value.

## 4. (Σ)(a) and (Σ)(c) in F₂ form (member language, integer units)

**(a) Q′ quadruple.** Let g = |V∖(B₁∪…∪B₄)| and σ = number of points in ≥ 3 of the members.
- Identity: W = wt(x₁+x₂+x₃+x₄) + 2g = 2n − 4k + 2σ.
- Q′ ⟺
  - wt(x₁+x₂+x₃+x₄) + 2g ≤ n + 3T − 4k = (δ + 3ε)k, and
  - for each matching {ij|uv}: c_{ij|uv} + σ ≤ T, where c_{ij|uv} = #{points with x_i = x_j, x_u = x_v, x_i ≠ x_u}.
- So it is a four-term relation x₁+x₂+x₃+x₄ ≈ 0 with the three pair cells capped, as expected.
- Exact affine planes (sum 0, g = 0) have b₄ = 2k − n and pair mass 2n − 2k. They are Q′ iff the pair cells are balanced (each ≤ T − b₄), which is possible for n ≥ 7k/4.
- Q′ ⟺ Theorem Q (existence of a τ-distribution): verified.
- Tests: 20000 random integer Venn diagrams; all identities and equivalences hold.

**(c) Theorem-T triangle (κ = ∅).** CORE's cell conditions ⟺ the closed form ⟺
- B₁∪B₂∪B₃ = V, and
- wt(x_i + x_j) ≥ n − T for all three pairs, and wt(x₁+x₂+x₃) ≥ n − T.

Equivalently, the four requests S₄₋₆ = 𝟙 + x_i + x_j and S₇ = 𝟙 + x₁+x₂+x₃ all have weight ≤ T (and S₄+S₅+S₆ = 𝟙). Replies B₄..B₇ lie inside the four nonzero combinations x₁+x₂, x₁+x₃, x₂+x₃, x₁+x₂+x₃.
- This is a "heavy simplex-code" condition on the span of x₁, x₂, x₃, not a four-term relation ≈ 0. At the zero-slack point all four combinations have weight exactly n − T.
- The ≈ 0 relations that do appear are three-term pencil relations x_i + x_j + B ≈ 0, of weight ≥ ωk, small only near the bottom of the window.
- Tests: 9384 random triples; the three forms agree in every case.
