# Programme 5: quadratic (and higher-degree) obstructions under slack

Tags: [proved by hand], [computed exact], [computed, solver], [heuristic], [open]. Not independently verified; nothing
committed. Code: `compute/programme5/quad/` (§6). Notation (PROGRAMME5_7INV): H k-uniform on V, |V| = n, c := 4n−7k (= 4s),
T = τ−1, r = n−k−T, c = 4r + (4T−3k). Fano seven: χ: V → F₂³, R_u = {x : ⟨χ(x),u⟩ = 1}, members B_u ⊆ R_u,
E_u = R_u∖B_u, Σ|E_u| = 4|V∖Z₀|−7k ∈ {c, c−4, …}. q = e_G + ℓ, β(x,y) = q(x+y)+q(x)+q(y), t(abc) = G_ab+G_bc+G_ac
(two-graph). L_{q,a} := {B ∈ C(V,k) : q(B) = a}; sdeg(H) := least degree of a polynomial equal to 1_H on C(V,k).

## 0. Verdict: DEAD (binary test, coordinator's framing)
- **Test.** s_min(k) is the least c = 4n−7k at which every quadratic-type obstruction acquires a good seven.
  Bounded or sublinear means dead; linear in k for an explicit family means alive.
- **Result: s_min(k) ≤ 128 for every k** [proved by hand, all k ≥ 2; Theorem QK, §2]. This covers every full
  degree-≤2 level set L_{q,a}, with any graph G, any rank, any ℓ and either level, unless τ ≤ 26.
  - Lower end: s_min ≥ 8. Exactness is c = 0, and FKW (linear, so degree ≤ 2) is seven-free at c = 4.
  - [computed for k ≤ 12] Every tested level set with τ ≥ ⌊(3k+5)/4⌋ at c = 4 (30 of them) has a Fano seven (§5).
  - RM(2,m) and Kerdock codeword families fail covering, by a factor of about 10^10.
- **No family with s_min linear in k exists in this class.** So τ − 3k/4 ≤ 131/4 for pure quadratic certificates.
- **Caveat (scope).** Proper subfamilies H ⊊ L_{q,a} are not quadratic obstructions: with q = |x| mod 2 they are
  arbitrary families, and the quadric contributes one bit (§1.3).
- **Counterexample side: nothing.** No (q,H) beats ⌊(3k+5)/4⌋. Level sets do reach the record τ at k = 10, 12, but
  all have Fano sevens (§5); Lemma PAIR (§4) explains why at r = 1.
- **Corollaries of QK.** The quadratic parity barrier is τ ≤ (3k+131)/4 (linear: 3k/4 + 3/2). A (7,2) family with
  τ > 26 and c ≥ 128 has sdeg ≥ 3.
- **Degree d** [open; sketch §3]. If QK_d holds for all d, window counterexamples have sdeg → ∞.
  Bounded-codimension cosets would then die too; window cosets have codimension Θ(k), where Theorem D and Piece B act.

## 1. The quadratic Lemma Q, exactly [proved by hand]
**1.1 Identity.** Normalise q(0) = 0. Σ_u q(R_u) = 0 for every colouring (true complexity 2). So for k-sets B_u ⊆ R_u:
Σ_u q(B_u) = Σ_u δ(B_u,E_u), with δ(B,E) := q(B∪E)+q(B) = q(E)+β(B,E) = ℓ(E)+e_G(E)+Σ_{x∈E}|N(x)∩B| (mod 2).
- A seven in H ⊆ {q=1} needs **Σ_u δ(B_u,E_u) = 1** with Σ|E_u| ≤ c. As a certificate ("no member configuration
  achieves 1") this is tautological. The non-trivial forms are:
  - **c = 0** (E ≡ ∅): the exactness lemma. The level {q = q(0)} is never obstructed.
  - **Per-line rigidity** (δ(B,E) = 0 for all B ∈ H and |E| ≤ c) is impossible once c ≥ 2 and τ(H) ≥ 3.
    E = {x} gives |N(x)∩B| ≡ ℓ_x for members B ∌ x, a coset condition. E = {x,y} then forces G_xy = 0 for every
    pair avoided by a member, so G = ∅, then ℓ = 0, so q ≡ 0. Per-line forms collapse to Corollary 7.

**1.2 Quotient form (Lemma Q7).** Let Ψ: F₂^V → F₂^m be linear with Ψ(H) ⊆ T, and d_Ψ(y) = min{|e| : Ψ(e) = y}.
Let D(T) be the minimum, over τ_u ∈ T and linear ψ: F₂³ → F₂^m, of Σ_u d_Ψ(τ_u+ψ(u)).
**If D(T) > c, then H has no Fano seven.**
- *Proof.* Ψ(R_u) = ψ(u) is linear and τ_u = Ψ(B_u) = ψ(u)+Ψ(E_u). ∎
- Summing over lines gives 3D ≥ 7W_σ, so linear Lemma Q is the three-term relaxation.

**1.3 What a quadric adds.** Let τ_1..τ_7 be distinct and nonzero. Some quadric Q' with Q'(0) = 0 has Q'(τ_u) = 1 for
all u **iff {0, τ_u} is not a 3-dimensional subspace**.
- *Proof.* If not, there is an odd S with Σ_{u∈S} f(τ_u) = 0 for every f of degree ≤ 2 with f(0) = 0. Then
  1_{τ(S)}+1_{0} ∈ RM(2,m)^⊥ = RM(m−3,m). Its nonzero words of weight ≤ 8 are 3-flats, so |S| = 7 and the set is
  linear. ∎
- So T ⊆ {Q'=1} forces D ≥ 1 and nothing more.

## 2. Theorem QK [proved by hand]
**Lemma K1.** Let 2 ≤ k ≤ |R|−2. If q is constant on C(R,k), then t is constant on C(R,3).
Then G[R] ∈ {K_{P,R∖P}, K_P ⊔ K_{R∖P}}, and q = C₀ + λ on C(R,k) with λ = ℓ+(k−1)1_P.
- *Proof.* Take S with i,l ∈ S and j,m ∉ S, and compare the swaps i→j at S and at S−l+m. This gives
  G_il+G_jl+G_im+G_jm = 0, i.e. t(ijl) = t(ijm); exchange-connectivity finishes. For t ≡ 0, x(k−x) ≡ (k−1)x;
  t ≡ 1 is the complement, with C(x,2)+C(k−x,2) ≡ (k−1)x+C(k,2). ∎
- [computed exact] Both directions, and "constant ⇔ λ ∈ {0,1_R}", were checked with 0 violations in 6.2·10⁵ (G,l,k)
  cases: all graphs on 5 points (all l), all graphs on 6 points (five l), and on 7 points 3000 random graphs plus
  all 232 with ≤ 2 edges.
- A **mixed 4-set** is a W on which t is not constant. If W ⊆ R and |R| ≥ k+2, q takes both values on C(R,k).

**Theorem QK.** Let deg q ≤ 2, a ∈ F₂, k ≥ 2 and c ≥ 128. Then L_{q,a} has a Fano seven, or τ(L_{q,a}) ≤ 26.
*Proof.*
- **(i) Seven disjoint mixed 4-sets W_u exist.** Give W_u's points the 4 colours p with p·u = 1; each colour gets 4.
  Balance the classes (n ≥ 36, so n_p ≥ 5). Then |R_u| ≥ 4(n−6)/7 ≥ k+2 (needs c ≥ 38) and W_u ⊆ R_u. By K1 every line
  holds both values, which gives a seven in either level, without covering.
- **(ii) Otherwise** a maximal matching covers the mixed 4-sets with |X| ≤ 24, so t is constant on V' = V∖X and
  q = C₀+λ on C(V',k). Colour X by 0 and let A = supp λ ∩ V'.
  - (a) If |A|, |V'∖A| ≥ 3: colour 3 points on each side e₁,e₂,e₃ and balance. Every R_u meets both sides and has
    |R_u| ≥ k+1 (needs c ≥ 127). A swap flips λ.
  - (b) Otherwise colour the smaller side Y (≤ 2 points) by 0. q is constant on C(V'',k), V'' = V'∖Y. If the constant
    is a, then L ⊇ C(V'',k), which has a seven (needs c ≥ 128). If not, X∪Y is a transversal and τ ≤ 26. ∎
- [computed] The case-(i) construction was run on 18 random q (n = 60–90, k = ⌊(4n−38)/7⌋, densities 0.02/0.1/0.5).
  Sevens were found in both levels and re-checked pair by pair.

**Corollaries.**
- (1) If H ⊆ L_{q,a}, τ(H) > 26, and L_{q,a} is (7,2), then c ≤ 127 and τ(H) ≤ (3k+131)/4.
- (2) A (7,2) family with τ > 26 and c ≥ 128 has sdeg ≥ 3. This covers coset layers of codimension ≤ 2 and every
  family that is a function of two parities.
- (3) In the window c = Θ(k), so every member-level degree-≤2 zero mechanism is dead as a certificate. This includes
  low-rank q, girth or expander G, and circulants, and makes 7INV §3.2's "unforced" rigorous for c ≥ 128.
- Not covered: proper subfamilies. "Robust QK" ((1−γ)-dense in L_{q,a} ⇒ seven, for γ < 1/7) is [heuristic]; it needs
  q to be equidistributed on random lines.

## 3. Degree d, and "non-algebraic"
**3.1 QK_d** [open; sketch]. Δ_{ij}P(y) = P(y+i)+P(y+j) has degree ≤ d−1. If Δ_{i₁j₁}⋯Δ_{i_sj_s}P(y) = 1 at some
y ⊆ R, then P is non-constant on C(R,k); this is K1's mechanism.
- Inducting on s (Δ^{(d+1)} ≡ 0; derivatives that are constantly 1 are witnesses) should give one of two outcomes:
  7 disjoint O(d)-witnesses, or a bounded X with P constant on C(V∖X,k).
- **Unproved step:** the exceptional sets X_ij depend on (i,j). Absorbing them into one bounded X needs a walk
  through iterated derivatives, carried out only for d = 2.
- For d ≥ 3 no identity Σ_u P(R_u) ≡ 0 holds (7INV: 9926 cubic violations), so QK_d is about covering only.

**3.2 Precise record.** Assume QK_d for all d. Take a (7,2) window family with τ ≥ (3/4+ε)k, so c = Θ(k) and τ → ∞.
Then sdeg(H) → ∞: H is the full k-slice level set of no bounded-degree polynomial.
- Unconditionally: sdeg ≥ 3.
- sdeg(L(a+C)) ≤ codim C, consistent with CX §4's codimension budget.
- The notion is weak: typical families have sdeg ≈ min(k, n−k), and subfamilies of level sets are unconstrained.

**3.3 Codeword families** [computed exact]. RM(2,6) has 888 832 words of weight 36 (k = 36, N = 1.78), but covering
at T = 27 needs ≥ 3.0·10^16 members. Kerdock is a subcode. RM(2,5) has no weight in the window.

## 4. Lemma PAIR and small-k records [proved by hand; computed exact]
**Lemma PAIR.** Let H be (k+r)-covering, A, B ∈ H, |A∩B| = j, |A△B| = 2k−2j ≥ k+r.
- Colour A∩B, A∖B, B∖A by {p₃,p₃+w}, {p₁,p₁+w}, {p₂,p₂+w} (p₃ = p₁+p₂) and the outside by w.
- Then R_u = A, R_v = B, R_{u+v} = A△B. The four lines with x·w = 1 have size |O| + Σ_i(s_i ? α_i : size_i−α_i),
  s even-weight.
- If some split α makes all four ≥ k+r, H has a Fano seven. For even j and k this reads 2(k−T) ≤ j ≤ (k−r)/2.
- This is P1 for the pencil (A, B, C ⊆ A△B) without the +3 rounding loss. It is not new asymptotically (needs ε ≥ δ/5).
- [computed] 270 window pairs in random covering families gave sevens, re-checked (`test_pair.py`).

**Consequence.** A record needs τ ≥ T+1 with T = ⌊(3k+5)/4⌋. On n = k+T+1 points (r = 1), |H| ≥ C(n,k+1)/(n−k), and H
must avoid the window intersections. Delsarte LP, with an exact rational dual certificate (`pairwin.py`):
- **No record on k+T+1 points for k = 11, 13, 15** (LP bound vs members needed: 22 795 < 29 393;
  274 873 < 371 450; 2.03·10⁶ < 2.34·10⁶). k = 8, 9 agree with the known f.
- Inconclusive: k = 10 (9 029 vs 8 398), k = 12 (104 975 vs 104 006, a 1% miss), k = 14, 16, and all r ≥ 2.
- The window is empty for (k,r) = (10,3), (11,2), (14,3), (15,2).

## 5. Computations: full level sets L_{q,a} [τ computed exact; Fano: exact search, sevens found and re-checked]
- q classes: G(n,p) with p = 0.05, 0.15, 0.5 and random ℓ; linear ℓ = 1_A plus 1–3 edges; random circulants with
  ℓ ∈ {0, 1_V}; rank-2/4 cell forms Σ 1_{X_t}1_{Y_t}. Both levels a are included.
- Fano checks were run when τ ≥ bound − 1.

| k | n | c | (q,a) tested | max τ | bound ⌊(3k+5)/4⌋ | # τ ≥ bound | Fano seven / none / undecided (τ ≥ bound−1) |
|---|---|---|---|---|---|---|---|
| 8 | 15–18 | 4–16 | 287 | 7–10 | 7 | 220 | 269 / 1 (τ = 6, a cells2 form) / 0 |
| 10 | 19, 20 | 6, 10 | 100 | 9, 10 | 8 | 92 | 89 / 0 / 3 |
| 12 | 22–24 | 4–12 | 72 | 10–12 | 10 | 52 | 65 / 0 / 2 |
- No seven-free level set has τ ≥ bound. The only Fano-free one (k = 8, n = 15) has τ = 6. Per-n rows are in
  `logs/table.md`.
- The 5 undecided cases are dense random q at c = 10, 12 (solver budget; the scan stopped at the first undecided
  d-vector). [recheck pending] `recheck_unknown.py` → `compute/programme5/quad/logs/recheck_unknown.log`: fresh dense q at
  (20,10) with τ = 9 so far all have Fano sevens (4/4).

## 6. Reproduction (`compute/programme5/quad/`, `py -3.14`, ≤ 3 cores)
- `qlib.py`: q on the 2^n cube, τ by up-closure (no solver); `fano_exact` (deviation vectors d up to GL(3,2),
  n_p = (k−D+2d(p))/4, lines with d_u ≥ r_L good by covering, random pre-pass, then CaDiCaL with exact class sizes);
  `seven_sat` (general 7-set encoding). Every seven is re-checked by plain code.
- `sanity.py` (K(13) seven-free, K(14) not; FKW m = 2, 3 Fano-free, m = 2 has a non-Fano seven), `exactness.py`,
  `verify_qk.py` (≈ 5 min), `test_pair.py`, `pairwin.py`, `delsarte.py n k r j…`, `rm_budget.py` → `logs/*.log`;
  `scan.py k nmin nmax per seed` → `logs/scan_k{8,10,12}.jsonl`, summarised by `table.py`.
