# PROGRAMME 2, piece B: covering coset families with many point classes

Tags: [proved by hand], [computed exact], [computed MILP], [heuristic]. Code: `compute/programme2/B/`. Nothing committed.
Conventions as in PROGRAMME_2.md and PROGRAMME2_TASK3.md: H = (a + C) ∩ (V choose k), C even WLOG (Lemma 2.1 of Task 3),
columns h_x ∈ F₂^M (parity-check columns), the *classes/cells* of V are the fibres of x ↦ h_x, c = number of cells.

## 0. Verdict

- **The gap is narrowed, not closed.** It was "c ≤ 2^r, i.e. codimension O(log k)".
  - **Theorem B1** (§3) [proved by hand] removes every condition on the number of classes c: singletons, mixed cells,
    near-coloops and planted dual structure are all allowed. It needs only a small *linear* codimension:
    codim(C_ev) − 1 ≤ min((k − 5r − 41)/15, (r + 4εk − 11)/5).
  - With Theorem D's Ω's this gives B for those families when N < 1.852.
- **Still open: codimension between that bound and the counting bound** (up to about 0.43k at N → 11/6).
  - Random codes live there. The multipart construction B1m (§4) handles them in every exact test, and its empirical
    capacity, e ≲ 2.8·m_min, covers the random-code covering range in N < 11/6 [heuristic as a statement about all codes].
  - B1m's proof needs a span hypothesis (SPAN) that is not proved in general.
- **Counting route (§5).**
  - The MacWilliams identity is exact.
  - The error is governed by the *punctured dual* D, not by the number of classes.
  - Coloops make the count 0. Series pairs make the absolute error huge, yet the count stays positive. So structure must be
    quotiented exactly (B1's blocks and dump), with counting on the rest.
  - The two missing rigorous pieces are listed in §5.5.
- **The reviewer's dual-distance dichotomy (§1).**
  - Theorem R never applies to coset families: they contain no perfect pencil, deterministically.
  - S⁺ applies with m = c.
  - The trigger is primal (c), not dual distance.
- **No counterexample to B.** Small exact search: 217/219 instances satisfying (H0)+(H1) with V = ∪H have a Fano-type good
  seven. The 2 exceptions have τ = 2. They are not covering, but they **refute Task 3's conjecture** that (H0)+(H1)+V = ∪H
  suffice.

- **Second pass (remaining gap, route (b)).**
  - Item 1 of §5.5 is now proved: Lemma F1, a fixed-count Fourier bound via Parseval on F₂³, gives the rigorous
    criteria Theorem F and F2 (§5.6).
  - Item 2 (a deterministic decomposition) is open (§5.7). The third pass proved the Möbius form, Theorem F‴ and the
    no-go P3; routes (i)–(iii) fail as stated.
  - Short dual words cannot obstruct (§5.8).
  - See §7.

- **Fourth pass (third brief, Task A(a)–(b); §8–§9).**
  - *All shifts (§8).* Every linear layer is either a coset family as in §1–§7 (shift ≥ 1, or shift 0 with k odd) or
    H = C₀ ∩ (V choose k) with k even (case S0). In the Venn form the target is 0 for every shift. So 9′, B1, F, F2, F‴
    and S⁺ hold verbatim at shift 0, with Ω = ∅, W = 0, and for B1 with no N restriction. NC does **not** handle every
    shift-0 layer.
  - **Theorem S0** [proved by hand; 319/319 verified sevens]. A shift-0 layer contains a Schur triangle x₁ + x₂ + x₃ = 0
    with empty triple intersection, by two applications of Lemma C. NC1 with W = V then finishes it. **B holds for every
    shift-0 layer with 4 ∣ k and τ > 3k/4 in N < 11/6, for every k** (counting, exact for k ≤ 400). k ≡ 2 (mod 4) is
    unconditional for N < 1.7985.
  - **Theorem S1** [proved by hand, untested]. The same construction with x₁ + x₂ + x₃ = Ω gives B at every shift
    whenever r ≤ 4εk − 7, at any codimension up to about k/2. The gap of B is now r ≥ 4εk with codimension above B1's.
  - *Contraction (§9).* Ω-first order: Lemma P shows that lost parity and Ω-met blocks do not arise. Proved: the exact
    contraction lemma, F1w (weighted F1), the P_m^w bound (size repair), F‴w (with a mixed-constant hypothesis), and
    **F1⁺** (rigorous damping 1/7 near the constants). P3 survives for series pairs, so contraction is necessary.
    Giant blocks of words of weight ≥ 3 are open.
  - *N ≥ 11/6:* three disjoint Ω's to N < 1.861 (no recount). Empty common intersection to N < 1.909 (patterns checked
    exhaustively). S1 needs only one Ω, so it reaches 1.9385.
  - *Check (ii)* (codimension > 0.09k, no short dual words, r ≥ 4εk): **open**. The missing piece is a bound on the
    number of medium-weight words of D′ ⊗ F₂³, not the damping. "They do not exist" is dead (random codes).

## 1. The reviewer's dual-distance dichotomy (checked first)

**Verdict: the dichotomy does not apply as stated. Theorem R never applies to a coset family, at any dual distance.
Theorem S⁺ applies, but its trigger is the number of cells c, which is a *primal* quantity, not the dual distance.**

### 1(a) Theorem R (CORE §57.2, §59) against coset families [proved by hand]
- *R's objects.* R works in co-edge language: requests are T-sets S, replies are S ∪ B_r for a head B_r with |B_r| = ω (= r here),
  and σ(S) is a class label, random over *requests*. Its certificate is a **head pencil**: three members κ ∪ P_1, κ ∪ P_2,
  κ ∪ P_3 with |κ| = n − 3k/2 and P_1, P_2, P_3 disjoint halves of V ∖ κ. This is then completed by 55.2.
- *A coset family has no perfect pencil at all.* The complement of κ ∪ P_i is P_j ∪ P_l. All three are in a + C exactly when
  [P_1] + [P_2] = [P_1] + [P_3] = [P_2] + [P_3] = α. Summing the three gives 0 = 3α = α, but α ≠ 0 because a ∉ C.
  This is Corollary 7 with zero slack. It holds for every C and every coset, whatever the dual distance.
- *Where independence fails.* For a frame, the three membership events are the linear conditions [P_i ∪ P_j] = α. Their
  left-hand sides always sum to 0. So the three events are inconsistent, identically. Nothing is random: the coset is
  fixed, and even a uniformly random coset a would not help.
  - R needs the class events on the three requests of a frame to be 3-wise (indeed 6-wise) independent.
  - Coset families violate this at order 3, deterministically.
  - Every selector one could extract from H (a choice of reply per request) gives a subfamily of H, so it is pencil-free too.
  - R's conclusion (a head pencil w.h.p.) is therefore *false* for every coset-derived selector. Its hypothesis fails at
    order 3, so this does not contradict R.
- *Dual distance is a different independence.* d(C^⊥) ≥ 7 means: a uniform element of a + C, restricted to any 6
  *coordinates*, is uniform. R's independence is across *requests* (T-sets, e^{Θ(k)} of them). One does not imply the
  other. For coset families the request-level events are deterministic linear functions of the class map [·].
- **Conclusion (a): R's hypotheses (selector, heads of size ω, independence) are not met by any coset family.** No
  zero-slack certificate (perfect pencil, Theorem H's kernel density > 2/3, (PR_i)) exists in a coset family. Every
  certificate must use slack, i.e. Ω-type deficient patterns (Lemma 5). This is why B needs Theorem 9′-type
  constructions and cannot borrow a pencil theorem.

### 1(b) Theorem S⁺ (CORE §39.4, §45.1) against coset families [proved by hand, given S⁺]
- **The match.** Membership in a + C depends only on the cell parities (Task 3, Lemma 2.2). So H, and the co-edge family
  {V ∖ B : B ∈ H}, are invariant under ∏_g Sym(V_g) over the c cells. The family is T-covering in co-edge language (a (k+r)-set
  contains a member ⟺ its T-complement lies in a co-edge). So S⁺ applies verbatim with m = c:
  **if c ≤ 4(T − 3k/4) − 12 and n/3 + c ≤ T, then H has a good seven** (45.1; 39.4 gives the weaker 4(T − 3k/4)/3 − 4).
  Since S⁺ handles odd cells and singleton cells itself, there is no parity or H4′ issue.
- **This covers more than 9′ in one respect and less in another.**
  - More: 9′ also needs (H2)–(H4′), which S⁺ does not.
  - Less: S⁺ needs c ≤ 4εk − 12 with ε = T/k − 3/4. That is vacuous as ε → 0. 9′ allows c up to about (k − 5r)/4,
    independently of ε.
  - Neither allows c ≈ n.
- **The trigger is primal, not dual.** c small means many columns coincide, which means many weight-2 codewords x + y ∈ C
  (small *primal* distance). Small *dual* distance says nothing about c:
  - A dual word λ of small weight w has λ·a = 0. If λ·a = 1, the set X = supp λ meets every member oddly, so it is a
    transversal and w ≥ T + 1.
  - So a small-weight dual word only says that members meet a small set X evenly.
  - Example: a random code C₁ of codimension M, plus one parity row on a 4-set X. Its dual distance is ≤ 4 and it still has
    c = n singleton cells.
  - Conversely, a cell family with all cells of size ≥ 7 typically has dual distance well above 7.
- **Conclusion (b):** case (i) of the dichotomy ("small dual distance ⟹ profile family or few classes") is false. The
  correct split is by c (primal). Small c is handled by S⁺ (c ≤ 4εk − 12) or by 9′ (c ≲ (k − 5r)/4 with H3, H4′).

### 1(c) Intermediate dual distance, and where dual distance really enters [proved by hand: the identity; heuristic: the sizes]
Dual distance does matter, but for a different route: equidistribution of the *colouring sums* (§3 below).
- A Fano-type seven built from three disjoint parity-correct Ω's and a colouring of the rest needs three codewords
  c_1, c_2, c_3 ∈ C (on V′ = V ∖ ∪Ω_i) with prescribed Venn region sizes (§2).
- Count such labellings by Fourier over (C′^⊥)³, where C′^⊥ is the punctured dual. The term of λ = (λ_1, λ_2, λ_3) is
  damped by about 7^{−w(λ)}, where w(λ) = |supp λ_1 ∪ supp λ_2 ∪ supp λ_3|.
- So what matters is the whole *weight enumerator* of C′^⊥ against 7^w. It needs A_w(C′^⊥ ⊗ F₂³) ≪ 7^w for all w, roughly
  "few dual words of every weight". d(C^⊥) ≥ 7 is far from enough: it controls only w ≤ 6.
- So an intermediate dual distance is neither case of the dichotomy. A single word of weight w costs a factor 7^{−w}·7,
  which is harmless. What hurts is near-coloop structure in D, made precise in §5.3.

## 2. The Venn form of the adjustment step [proved by hand]

- **Fano points as vectors.** Identify the Fano points with F₂³ ∖ 0, so that the lines are the kernels of the 7 nonzero
  functionals φ. The bijection used is `b1.LAB`.
- **Pure colouring part.** For a colouring v of V″ by F₂³ ∖ 0 (this is the Y_p of 9′), put D_φ = {x : φ(v(x)) = 1} = ∪_{p ∉ ℓ_φ} Y_p.
  Then D_{φ+ψ} = D_φ + D_ψ. So **all seven D_ℓ lie in C iff the three bit-classes D_1, D_2, D_3 do.**
- **The step to solve.** Given Ω's, Z and F as in 9′, the Y-step of Theorem 9′ is exactly this. Find v: V″ → F₂³ ∖ 0 with
  |v⁻¹(p)| = m_p and Σ_{x : v_i(x) = 1} h_x = 0 for i = 1, 2, 3. Equivalently, Σ_x v(x) ⊗ h_x = 0 in F₂³ ⊗ F₂^M.
- **Two relaxations of 9′, both free.**
  1. Z (pattern ∅) is unconstrained in class: no condition on [Z].
  2. The fixer may be any codeword F ∈ C with |F| ≡ s (mod 4), not just a same-class pair. It is placed on
     T* = ANTI(7) ∖ {156}.
     - The integrality conditions of 9′ survive: Σt = 7k − 3W − 3|F| ≡ 3(s − |F|) ≡ 0 (mod 4), and F adds
       |F|·#{ℓ ∈ T* : p ∈ ℓ}, which is even, to Σ_{ℓ∋p} t_ℓ.
     - The size shift is ≥ −3|F|, so 4m_p ≥ k − W − 2Δ − 3|F|.
- **Where 9′ sits.** 9′ is the special case where each class solves its own parity by a Hamming word π_g. B1 instead
  solves the three bit constraints *globally* by Lemma C (Task 2). That is what removes the dependence on c.

## 3. Theorem B1 (many classes, small linear codimension) [proved by hand]

**Setting.**
- This is 9′'s setting with C even, H = (a + C) ∩ (V choose k), and disjoint Ω₁, Ω₂, Ω₃ ∈ a + C satisfying (H0) and (H1).
- s = 4n − 7k − W, V′ = V ∖ ∪Ω_i, and h_x are the columns, so every h_x has parity coordinate 1 and h_x ∉ E.

**The packable part and the remainder.**
- Let A ⊆ V′ carry four pairwise disjoint bases R₀, R_A, R_B, R_F of its own column span. Put e_A = rk(A) − 1 = dim E_A.
- Let X = V′ ∖ A, and let π be the projection modulo span(A).
- Split X into **blocks** K₁, …, K_q with Σ_{K_j} π(h_x) = 0, plus a remainder X₀ that is π-independent. Greedy removal of
  quotient circuits does this.

**Hypotheses.**
- **(B-F)** If s ≡ 2 (mod 4), there is a codeword F ⊆ A ∖ (R₀ ∪ R_A ∪ R_B) with |F| ≡ 2 (mod 4) and |F| ≤ e_A + 4.
  This holds by Lemma C inside A ∖ (R₀ ∪ R_A ∪ R_B), which contains R_F, once that set has at least 3e_A + 5 points.
  Otherwise F = ∅. Put u = (s − |F|)/4.
- **(B-Z)** |X₀| ≤ u, and A ∖ (R₀ ∪ R_A ∪ R_B ∪ F) has at least u − |X₀| points.
- **(B-m)** With m_p from the 9′ formulas (fixer of size |F| on T*), the blocks can be given regions so that every residual
  r_p = m_p − (block load on p) is ≥ e_A + 1.

**Conclusion.** H contains a Fano-type good seven of the 9′ form.

**Proof.** Put Z = X₀ plus u − |X₀| filler points of A ∖ (R₀ ∪ R_A ∪ R_B ∪ F), and V″ = V′ ∖ (Z ∪ F).
- **Fixed labels.** Blocks get their regions' labels. R_A ∪ R_B is forced into bit-class 1, and R_B into bit-class 2.
- **Free points lie in A.** Every free point is in A, because X₀ ⊆ Z and the blocks are fixed. So every free set that
  contains a base has difference span E_A.
- **The coset condition, once for all three steps.** Columns of A lie in h₀ + E_A. A block's sum lies in span(A) =
  ⟨h₀⟩ ⊕ E_A, with h₀-coefficient |K| mod 2. Hence for each step, target and a·h₀ differ by |D_i|·h₀ modulo E_A.
  Each D_i has size t_ℓ for a line ℓ, and t_ℓ is even (9′). So the target always lies in the right coset.
- **Step 1 (bit 1).** Free set U₁ = V″ ∖ (blocks ∪ R_A ∪ R_B), which contains R₀. Its size is |U₁| = Σ_p r_p − 2(e_A + 1).
  - Choose Q ⊆ U₁ with |Q| = Σ_{4 regions with bit 1} r_p − 2(e_A + 1) ≥ 2(e_A + 1), so that the column sum of Q cancels
    the forced part of D₁.
  - Lemma C applies: |U₁| − |Q| = Σ_{3 other regions} r_p ≥ 3(e_A + 1), so e_A ≤ |Q| ≤ |U₁| − e_A and |U₁| ≥ 2e_A + 1.
- **Step 2 (bit 2).**
  - Outside D₁, choose the bit-2 points arbitrarily; the counts fit.
  - Inside D₁ the free set is U₂ = (D₁ ∩ V″) ∖ (blocks ∪ R_B), which contains R_A.
  - The number to choose is a₂ = (residuals of the 2 regions with bits 1, 2) − (e_A + 1) ≥ e_A + 1. The rest of U₂ fills
    the residuals of the 2 regions with bit 1 and not bit 2, which is ≥ 2(e_A + 1). So Lemma C applies again.
- **Step 3 (bit 3).**
  - In the three other parts, choose arbitrarily.
  - The free set U₃ is the free part of D₁ ∩ D₂, which contains R_B. Choose a₃ = r_{111} ≥ e_A + 1 of it; the
    rest is r_{110} ≥ e_A + 1. Lemma C applies.
- **Blocks.** Their labels are respected. Each bit-class contains a block entirely or misses it, and Σ_K π = 0, so blocks
  contribute only within span(A). The coset bookkeeping above covers that.
- **Conclusion.** Every D_i ∈ C, hence every D_ℓ ∈ C (§2). The rest is the 9′ proof verbatim: [B_ℓ] = α, |B_ℓ| = k,
  Fano-type (anti-pencil, triangle, T* and ∅ patterns), and the sets are distinct because every Y_p is nonempty
  (m_p ≥ r_p ≥ e_A + 1). ∎

**Choosing A [proved by hand; standard matroid theory].**
- Take A to be the minimiser in Edmonds' matroid-union formula for 4 copies of the column matroid on V′:
  max |I₁ ∪ … ∪ I₄| = min_A (|V′ ∖ A| + 4·rk A).
- Minimality gives |A ∖ A′| ≥ 4(rk A − rk A′) for every A′ ⊆ A. By Nash-Williams/Edmonds base packing, A then has 4 disjoint bases.
- Also |X| ≤ 4(rk V′ − rk A).
- X₀ is π-independent, so **|X₀| ≤ rk V′ − rk A ≤ e + 1**, where e = dim E_{V′}.
- A block is a quotient circuit, so it has at most e + 2 points.
- `b1.partition4` computes A by the augmenting-path partition algorithm, taking A = the set reachable from uncovered elements.

**Corollary B1 (worst case over all column structures) [proved by hand].**
- **Conditions.** Let e = dim E_{V′}. Then (B-Z) holds if s ≥ 5e + 8. (B-m) holds if m_min ≥ 3(e + 2): greedy placement of
  blocks of total ≤ 4(e+1) and size ≤ e + 2 leaves residuals ≥ m_min − 4(e+1)/7 − (e+2). Both follow from
    k − W − 2Δ ≥ 15e + 36   and   s ≥ 5e + 8.
  Both are linear in e. There is **no condition on c, on singleton classes, or on a large class.**
- **With Theorem D's Ω's** (W ≤ 3(r + 1), Δ ≤ r, for N < 1.852): s ≥ r + 4εk − 3, where n − 7k/4 = r + εk. So
  **B holds for every T-covering coset family with N < 1.852 and**
    codim(C_ev) − 1 ≤ min( (k − 5r − 41)/15 , (r + 4εk − 11)/5 ).
- **Against 9′.** The verifier's objection was that 9′'s corollary needs c ≤ 2^r, i.e. codimension O(log k). B1 replaces
  that by codimension ≤ κ·min(k, δk + 3εk) with explicit constants.
- **What is still not covered.** The counting bound allows codimension up to about n − log₂|H| (0.026k at N = 7/4,
  0.43k at N = 11/6). Random codes have codimension ≈ log₂ C(k+r, r), about ωk·log₂(e/ω), which exceeds (r + 4εk)/5 for
  every ω. **So B1's worst-case corollary does not cover random codes. B1m (§4) does, in practice.**

## 4. B1m: Lemma C* over all parts (the spread case)

**Lemma C* [proved by hand].** Let P₁, …, P_q be disjoint parts with targets a_j.
- Hypothesis: there are disjoint pairs inside the parts, at most b_j = min(a_j, |P_j| − a_j) of them in P_j, whose
  differences span F.
- Conclusion: the set of column sums of choices (Q_j ⊆ P_j, |Q_j| = a_j) contains Σ_j a_j h_{(j)} + F, where h_{(j)} is
  any column of P_j.
- *Proof.* Take one endpoint per pair, fill, and swap.
- If every part has E_{P_j} = E, Lemma B applied part by part in the quotient (`b1.multi_lemma_c`) gives such pairs with
  F = E as soon as Σ_j min(b_j, ⌊(|P_j| − 1)/2⌋) ≥ e. The coset is then the parity coset, as in §3.

**B1m.** Run the three bit steps of §2, each by Lemma C* over all 2^{i−1} parts of its Venn level, with no reserved bases.
- *Capacity.* The usable capacity is 3m at every level: step 1 is min(4m, 3m); step 2 is 2m + m; step 3 is m + m + m + 0.
  So B1m needs e ≲ 3m (m = typical region size ≈ (k − W)/4).
- *Hypothesis (SPAN).* Every part used has full difference span E, or at least the quotient-greedy pairs reach F = E.
  This is checkable per instance. It is not proved for general columns, and it fails for structured ones; there §3's
  reserved bases are needed.
- *Isolation test* (`ystep.py`, random columns, 10 trials per point) [computed exact per trial: the three sums are
  recomputed]:

  | e / m | 0.5–2.5 | 2.8 | 3.0 | ≥ 3.2 |
  |---|---|---|---|---|
  | success, m = 20 | 10/10 at each | 8/10 | 2/10 | 0/10 |
  | success, m = 40 | 10/10 at each | 10/10 | 2/10 | 0/10 |

  The threshold is exactly the capacity 3m.
- *Is that enough for random codes in the regime [heuristic]?* Random codes are covering only for codimension
  ≲ log₂ C(k+r, r) ≤ (13/12)h(1/13)k ≈ 0.42k when N < 11/6. That is ≤ 0.42k / ((k − 3r)/4) ≈ 2.2m < 2.8m. So the spread case
  is inside B1m's empirical range throughout N < 11/6. The 3m limit is an artefact of the pair method: information-theoretically,
  e < (2/3)N suffices (§5).

## 5. Counting (Fourier over F₂ / MacWilliams): the reviewer's route

Work in the Venn form (§2) with Ω, F, Z fixed. Put N = |V″| and let D ⊆ F₂^{V″} be the punctured dual: the row space of
the column matrix on V″, of dimension d = rk(V″), with 1 ∈ D. Put A = D ⊗ F₂³ (words λ: V″ → F₂³, |A| = 8^d) and
A^⊥ = C″ ⊗ F₂³, the labellings whose three bit-classes are codewords of C″ = C|_{V″} (shortened code).

### 5.1 Exact identity without counts [proved by hand: MacWilliams over the alphabet F₂³, Krawtchouk K_N(w) = 7^{N−w}(−1)^w]
The number of labellings v: V″ → F₂³ ∖ 0 with all three bit-classes in C is

  #full = (7^N / 8^d) · Σ_{λ ∈ A} (−1/7)^{wt λ},   where wt λ = |supp λ₁ ∪ supp λ₂ ∪ supp λ₃|.

- The main term is λ = 0. The error is E = Σ_{λ≠0} (−1/7)^{wt λ}.
- By MacWilliams again, Σ_{λ∈A} 7^{−wt λ} = 8^d 4^{−N} Σ_{c ∈ C″⊗F₂³} (3/7)^{wt c}. So the *absolute* error is the
  excess of the (3/7)-weighted weight enumerator of C″ ⊗ F₂³ over its λ = 0 share.

### 5.2 With the region sizes fixed [exact formula; the size of the error is heuristic]
- **Exact formula.** N_m = 8^{−d} Σ_{λ∈A} [z^m] Π_x ĝ_{λ(x)}(z), with ĝ_u(z) = Σ_{v≠0} z_v (−1)^{⟨u,v⟩}.
- **The main term.** The 8 constant words λ = u ⊗ 1 each contribute exactly Mult(m) = N!/Π m_v!, because |D_i| is even.
  So N_m = 8^{1−d} Mult(m) (1 + E_m).
- **The error [heuristic, saddle point].** A word at distance d(λ) = min_u wt(λ + u⊗1) from the constants contributes
  |·| ≲ poly(N)·κ^{d(λ)}, with κ = max_{w≠0} |Σ_v p_v (−1)^{⟨w,v⟩}| = 1/7 + O(δ) for p_v = m_v/N ≈ 1/7.
  - With fixed counts the cancellation survives only up to aligning phases, which costs κ on the points off the
    dominant value. The binomial check is the Krawtchouk value K_a(w)/C(N,a) ≈ (1 − 2a/N)^w.
- **Sufficient condition (DW) for a seven.** Σ_{λ∈A, d(λ)≥1} κ^{d(λ)} < 1/poly(N).
- **The main term itself.** log N_m ≈ N ln 7 − 3d ln 2, and per k this is ≥ 1.6·1.95 − 0.9 > 0. This is the e^{Θ(k)}
  of CORE §57.

### 5.3 Where the error can win [proved by hand: the local factors; computed: Monte Carlo `montecarlo.py`]
A dual word μ ∈ D of weight w that is "isolated" (its directions appear nowhere else) multiplies the count by the local factor
P(Σ_{x∈supp μ} v(x) = 0)·8 = 1 + 7(−1/7)^w. That is 0 for w = 1, 8/7 for w = 2, 48/49 for w = 3, and so on.
- **w = 1: coloops of C″.** The count is exactly 0. A point that lies in no codeword of C supported in V″ must go to Z or to
  an Ω. Monte Carlo, one planted coloop: 0 hits in 4·10⁵ samples, against a main-term rate of 2.4·10⁻⁴. These points are
  B1's X₀. In V itself there are none when τ ≥ 2, since a coloop lies in all members or in none; but deleting the Ω's can
  create them.
- **w = 2: series pairs.** Here |E| ≥ (8/7)^q − 1 is huge for q planted pairs, but the sign is +. With fixed counts the
  exact factor per pair is 8(m−1)/(7m−1) → 8/7. Monte Carlo at m = 6: ratios 0.96 and 0.95 for q = 1, 2, against 0.976 and
  0.953 predicted. **So an absolute-value bound on E fails while the count is fine.** These must be quotiented
  exactly; they are B1's blocks.
- **w ≥ 3.** Factors 1 ± 7^{1−w}, harmless unless there are exponentially many. Disjoint short words damp the count by at
  most e^{−q/49}, against a main term e^{Θ(k)}.
- **General.** The error from a set S is at most 8^{dim D_S}·7^{−|S|}, where dim D_S = rk V″ − rk(V″ ∖ S) is the rank drop.
  It is dangerous only if the rank drop exceeds (log 7/log 8)|S| ≈ 0.94|S|: **near-coloop sets**. B1's packing
  deficiency, with threshold |S|/4, is a much cruder version of the same thing.
- **Small cells** (few-class regime). A cell with an independent column gives a dual word of weight equal to its size. So
  small cells raise the error. This is why the few-class case belongs to 9′ / S⁺ and not to counting.
- Monte Carlo, random columns and 3 big cells: ratios 1.03, 0.97 and 1.01 to the main term (`logs/montecarlo.jsonl`).

### 5.4 "Many classes ⟹ small error" is false as stated; the correct parameter [proved by hand: the examples]
- c large means that C″ has no weight-2 words. That is a *primal* fact. In MacWilliams form it lowers Σ_c (3/7)^{wt c},
  which helps slightly, but it says nothing about the low-weight words of D, which carry the error.
- The series-pair families have c = n − O(1) and |E| ≥ (8/7)^q − 1.
- The right parameter is the weight distribution of D ⊗ F₂³ near the constants, equivalently (by 5.1) the (3/7)-weighted
  enumerator of C″ ⊗ F₂³.
- **For random-like D** (B_w ≈ C(N,w)·7^w·8^{d−N} above the dual distance) [heuristic]:
  Σ_{λ≠0} 7^{−wt λ} ≈ 2^{3d−2N}. This is tiny, since d ≤ e + 1 ≲ 0.43k and N ≈ 1.6k. So the main term dominates by
  e^{Θ(k)} in the whole regime N < 11/6, and (DW) needs only e < (2/3)N, far beyond B1m's 3m.

### 5.5 What a complete counting proof of B still needs (precise)
1. **A rigorous fixed-count estimate.** **Now proved (Lemma F1, §5.6)**, with κ_eff = 7^{−1/2} in place of 1/7.
2. **A deterministic decomposition.** Remove (dump to Z, or glue into monochromatic blocks) a set X of near-coloop
   structure, at cost |X₀| ≤ u, after which (DW) holds on the rest.
   - B1 does this for the threshold |S|/4, but only proves the *construction*, not (DW).
   - The obstacle to a clean union bound is the number of supports: Σ_S 8^{dim D_S} 7^{−|S|} with S ranging over unions
     of cocircuits. That is not controlled by local deficiency alone.
3. **Blocks.** They interact with the count only through their fixed labels, which shift the target of the Fourier sum
   over the free points. Harmless.

### 5.6 Item 1 made rigorous: Lemma F1 (fixed counts) [proved by hand; checked exactly in `f1_check.py`]
**Notation.**
- p_v = m_v/N (v ∈ F₂³ ∖ 0) and P₂ = 8 Σ_v p_v². P₂ = 8/7 for equal regions.
- P_m = Mult(m)·Π_v p_v^{m_v} is the probability that an i.i.d. p-labelling has counts exactly m. By Stirling,
  P_m ≥ c·N^{−3} when every m_v ≥ 1.
- For λ: V″ → F₂³, write n_u = |λ⁻¹(u)|.

**Lemma F1.**
  |S(λ)| ≤ Mult(m) · Φ(n)/P_m,   where Φ(n) = max { Π_u t_u^{n_u/2} : Σ_u t_u = P₂, 0 ≤ t_u ≤ 1 }.

*Proof.*
- Write S(λ) = [z^m] Π_x ĝ_{λ(x)}(z) and substitute z_v = p_v e^{iθ_v}. This gives
  S(λ) = Π_v p_v^{−m_v} (2π)^{−7} ∫ Π_x g_{λ(x)}(θ) e^{−i⟨m,θ⟩} dθ, with g_u(θ) = Σ_v p_v (−1)^{⟨u,v⟩} e^{iθ_v}.
- g_u(θ) is the F₂³-Fourier transform at u of f(v) = p_v e^{iθ_v} (with f(0) = 0). So |g_u| ≤ 1, and by Parseval
  Σ_u |g_u(θ)|² = 8 Σ_v p_v² = P₂ for every θ.
- Hence |Π_x g_{λ(x)}(θ)| = Π_u |g_u|^{n_u} ≤ Φ(n). Dividing by Mult(m) = P_m·Π_v p_v^{−m_v} gives the claim. ∎

**Consequences [proved by hand].**
- *Near-constant words.* If the dominant value has n_{u*} ≥ N/P₂ (= 7N/8 for equal regions), the maximiser has
  t_{u*} = 1. The other t_u share P₂ − 1, so Φ ≤ (P₂ − 1)^{d/2}·e^{−(d/2)H(ν′)} ≤ 7^{−d/2}, with d = N − n_{u*}. The
  rigorous per-point damping is therefore **7^{−1/2}**. The heuristic 1/7 of 5.2 is not proved.
- *Spread words.* Φ ≤ exp(−(N/2)(H(ν) − ln P₂)), where ν = n/N and H is the entropy in nats.

**Exact check.** `f1_check.py` computes S(λ)/Mult exactly, as E[Π_x (−1)^{⟨λ(x),Y_x⟩}] by DP over the remaining counts in
rationals. Over 300 random (λ, m) with N ≤ 28, near-constant and spread, the bound held every time. The largest ratio of
the exact value to the bound was 0.015, so the bound is valid and loose [computed exact].

**Theorem F (counting criterion) [proved by hand, from F1 and 5.2].** Fix Ω, F and Z as in 9′ / B1. Then
  N_m ≥ 8^{−d} Mult(m) (8 − Σ_{λ ∈ A ∖ Λ₀} Φ(n(λ))/P_m).
So **Σ_{λ ∈ D⊗F₂³, λ nonconstant} Φ(n(λ)) < 8·P_m implies a Fano-type good seven.** This criterion is rigorous and
checkable from the type distribution of D ⊗ F₂³. It has no hypothesis on c and no reserved bases.

**Theorem F2 (with a fixed part) [proved by hand].** Let S ⊆ V″ carry a fixed labelling ψ, and let R = V″ ∖ S with
remaining counts m′.
- Fourier over (F₂^M)³ gives a count of completions with target τ = Σ_{x∈S} ψ(x) ⊗ h_x.
- The fibres of λ ↦ λ|_R contribute only if τ is orthogonal to every functional that vanishes on the R-columns.
  Condition (LC0): ψ satisfies the constraints of the dual words supported in S.
- The constant words on R must come with sign +1. Condition (LC1), the parity condition.
- Under (LC0) and (LC1), the criterion of Theorem F with (D_R = D|_R, m′, p′) gives a completion, hence a good seven.

### 5.7 Item 2 (the decomposition): third pass, timeboxed [tags per item]

**Verdict: not closed.**
- All three suggested routes, as stated, fail for an identified reason.
- What survives: one exact reformulation, one rigorous criterion in a smaller codimension range, and a diagnosis of what
  a proof must do.

**(P1) Möbius form of the light-word sum [proved by hand].** For every x ∈ [0, 1],
  Σ_{λ ∈ D⊗F₂³} x^{wt λ} = E_{T ∼ Bin(V″, x)} [ 8^{drop(T)} ] =: G(x),   drop(T) = rk V″ − rk(V″ ∖ T).
- *Proof.* The number of λ with support in T is 8^{dim D_T}, and dim D_T = drop(T). By Möbius inversion over supports,
  Σ_λ x^{wt λ} = Σ_T 8^{drop T} x^{|T|} (1 − x)^{N−|T|}. ∎
- So "many near-constant words" means exactly that the column matroid loses rank on random x-subsets, with x = 7^{−1/2} ≈ 0.378.
- Monte Carlo (`gx.py`, N = 300) [computed]: G = 1.00 for random columns. Planted structure gives:

  | planted structure | G | isolated-word prediction |
  |---|---|---|
  | 5 series pairs | 31 | 32 |
  | 20 series pairs | 6·10⁵ | 1·10⁶ |
  | 20 triads | 1.1·10³ | 6·10² |
  | 3 coloops | 45 | 48 |

  The predictions are Π(1 + 7x^w) over the planted words.

**(P2) Theorem F‴: a rigorous criterion in terms of G [proved by hand, from F1 and P1].** Let x = (P₂ − 1)^{1/2}
(= 7^{−1/2} for equal regions). Group λ by its nearest constant.
- Words at distance ≤ N(1 − 1/P₂) contribute at most 8(G(x) − 1).
- The rest have dominant value < 1/P₂, so H(ν) ≥ h(1/P₂) (0.377 nats at P₂ = 8/7). Together they contribute at most
  8^{d}·e^{(N/2)(ln P₂ − h(1/P₂))}.
- **So 8(G(x) − 1) + 8^{d} e^{−0.12N} < 8P_m implies a Fano-type good seven.**
- The second term limits this to d = rk V″ ≲ 0.058N (codimension ≲ 0.09k). That is independent of ε, so it beats B1's
  (r + 4εk)/5 when ε is small. But it is conditional on G(x) ≈ 1.
- Removing the 0.058N restriction needs a type-refined count of λ by full value-distribution, i.e. a multi-variable G.
  Not done.

**(P3) Why every absolute-value criterion fails, so a decomposition must be exact on short words [proved by hand; computed above].**
- q disjoint isolated dual words of weight w give G ≥ (1 + 7x^w)^q: 2^q for series pairs, 1.38^q for triads.
- The true count changes only by the local factors 8(m − 1)/(7m − 1) and about 48/49 (§5.3).
- So with linearly many disjoint short dual words, Theorems F, F2 and F‴ all fail, even though sevens exist. Even the
  heuristic κ = 1/7 gives Π(1 + 7^{1−w}) = e^{Θ(N)} for linearly many triads.
- Short-word structure has to be summed *multiplicatively* (local factors), not bounded.

**Slack cost of one decomposition step, against the budget 3(4n − 7k) (incidence units; 1 unit of deficiency = 3 units) [proved by hand].**
- *Dual word of weight w ≥ 2 disjoint from the Ω's (fixed or glued, F2): **0**, for every w.*
  - Labels with XOR 0 can all be nonzero (anti-pencil) patterns: (v, v); (v₁, v₂, v₁ + v₂); and so on.
  - No deficient pattern is needed.
- *Coloop (w = 1): 12 units per point.* It must be dumped (pattern ∅: deficiency 4, 0 incidences).
- *Dual word meeting the Ω's:* the outside points must XOR to the Ω patterns there.
  - One outside point opposite one Ω point: that point takes the triangle pattern. Cost 3 units, i.e. β = 1/3, the same as
    an Ω point.
  - Outside points opposite two points of the same Ω (a fan whose pair lies in Ω_i): they must be dumped. Cost 12 units
    per point.
  - These cases are avoidable by the choice of Ω, since the Ω's are ours.
- So the cost is **not** proportional to w. It is 0 off the Ω's and between 3 and 12 units per forced point on them.
- **Does the increment argument close? No.** Slack is not the binding constraint. Steps off the Ω's are free, so a slack
  count can neither block nor finish the decomposition. What blocks it is analytic:
  - after fixing an overlapping word, D|_R gains new light words (§5.7 (ii));
  - absolute-value criteria fail on linearly many short words (P3).
  The β = 1/3 versus 4/7 margin of §5.8 rules out slack-based *obstructions*. It does not supply the missing
  *control* of the remainder.

**(i) Potential-function closure [proved by hand: properties; fails: size].**
- g(K) = 3 dim K − (log₂7/2)|supp K| is supermodular on subcodes K ≤ D. So a maximal maximiser K* exists and is unique,
  with S* = supp K*.
- Afterwards, every subcode M of D|_{V″∖S*} satisfies dim M ≤ 0.468|supp M|.
- But (a) this bounds dimensions, not *numbers* of supports, so it does not give G ≈ 1. (b) |S*| ≤ 2.14·dim K* is ≤ 2.14d,
  not ≤ u. (c) On S* the problem (LC0) is of the original type. **Fails.**

**(ii) F2 with S = the light-word support, labels fixed [proved by hand: works for isolated words; fails in general].**
- If the short words have pairwise disjoint supports and private directions (isolated), fix on each support a labelling
  with XOR 0. That is possible for every weight ≥ 2, and with free points for any counts. Then D|_R loses those
  directions, and F2 applies to the rest.
- For overlapping or nested short words, D|_R gains new light words (heavy on S, light on R). This is the puncturing
  problem again.
- Also, fixing the labels of a series pair throws away its factor 8/7; gluing (a 2-point unit) is the right operation,
  but F1 is not proved for units of size > 1.

**(iii) "Many near-constant words ⟹ few classes or small codimension on a large subset" [false as stated, proved by hand].**
- q planted series pairs or triads on random columns keep c = n − O(1).
- Restricted to any large subset, the column space is not smaller: each planted direction lives on ≤ 3 points, so
  deleting them lowers the rank by at most q, and q can be o(N).
- Yet G ≥ 1.38^q. Near-constant words come from *sparse* structure, not from few classes.

**Polymer route (the natural next step) [heuristic; one obstruction found].**
- For the uncounted identity (5.1), Σ_λ (−1/7)^{wt λ} would be a hard-core polymer gas if every λ split uniquely into
  disjoint-support indecomposable words. Kotecký–Preiss would then give non-vanishing under a local smallness condition
  per point. That is exactly a multiplicative treatment of short words.
- **The uniqueness fails**: in D = ⟨1100, 0011, 1010⟩, 1111 = 1100 + 0011 = 1010 + 0101.
- So a polymer representation needs a canonical decomposition, for example by a matroid connectivity decomposition of
  the columns. Fixed counts need F1-style saddle control on top. Not done.

### 5.8 Building an obstruction from short dual words (route (c)): dead [proved by hand: the reduction; computed exact: the ratios]
- **The test.** Lemma 5 gives Σ_p wt(s_p) = Σ_x j_x(4 − j_x), where j_x = |J(x)|. The total deficiency is
  Σ_x (4 − j_x) = 4n − 7k (more is allowed, since points can be wasted).
  - Every s_p ∈ a + C, so Σ_p wt(s_p) ≥ 7ρ_par.
  - A Fano-type seven therefore needs β·7ρ_par ≤ 4δk, where β is the least deficiency per pencil-incidence available.
  - Free points have β = 1/3 (triangles). That is Corollary 7.
  - So a structural obstruction would need structure forcing β > 4δk/(7ρ_par) ≥ 4/7 − o(1), using ρ_par ≤ r + 1 ≤ δk + 1.
- **The natural candidates.** Short dual words λ with λ·a = 0 force local XOR relations on patterns:
  - "even blocks": w points whose patterns XOR to 0;
  - "fans": dual words {x_i, y, y′}, which force J(x_i) = J(y) Δ J(y′).
- **`ratio.py` (exhaustive over the 64 admissible patterns):** the minimum β is **1/3** for even blocks of every size
  w = 2..6 and for fans of every size q = 1..10. Two triangles can have an anti-pencil as symmetric difference, for
  example {124, 235, 346} Δ {124, 457, 267} = ANTI(1).
- **Conclusion.** Local even-intersection structure never raises the cost of a Fano-type seven. An obstruction would
  have to be global (non-local). My first hand estimate, β = 2/3 for fans, was wrong; the exhaustive check corrected it.
  No counterexample candidate was produced.

## 6. Computations (`compute/programme2/B/`, logs in `logs/`)

### 6.1 Theorem B1 stress test (`run_b1.py`, `fam.py`, `b1.py`) [computed exact per instance]
- **Families.** Random codes of codimension M = 6–14 (+1 after evenising):
  - `rand`: uniform columns;
  - `mix`: half the points from a pool of 5/20/80 cell columns, half singletons;
  - `series`: 1–12 planted weight-2 dual words;
  - `sparse`: 1–12 planted dual words of weight 3–6.
- **Sizes and Ω's.** k = 200, n = 360/366, and k = 400, n = 732 (N ≤ 1.83). The Ω's are greedy-minimal, computed exactly by
  BFS in syndrome space.
- **Checking.** Every output went through two verifiers: `b1.check_seven` (independent; membership with the original rows,
  distinctness, no transversal of size ≤ 2 via incidence patterns, pencils) and task3's `core.verify_seven`.

| | instances | B1 succeeds and verifies | 9′ (H2) fails | certified T-covering, T ≥ 3k/4, N < 11/6 |
|---|---|---|---|---|
| all | 496 | **496** | 482 | 90 (86 `rand`, 4 `mix`; up to c = 718 classes) |

- **Coverage of the gap.** Of the 90 certified covering families, 82 violate 9′'s (H2). They lie exactly in the verifier's
  gap, and B1 handles all of them.
- **What the structure looks like.** c/(n − W) has mean 0.66 and minimum 0.09. The structured part X is up to 36 points,
  X₀ up to 8 points. Blocks were used in 196 instances and a general fixer in 478.
- **Covering certificate** (`fam.cover_cert`) [exact]: no affine hyperplane of the columns holds k + r points, and r ≥ e.
  Then Lemma C makes every (k+r)-set contain a member.
- `run_large_M.py` (k = 200, n = 366, M = 16–24, Ω's by exact meet-in-the-middle): B1 and B1m both succeed and verify in
  6/6. At M ≥ 28 there are no Ω's of weight ≤ 5, and the search stops.

### 6.2 Y-step capacity (`ystep.py`): see the table in §4.

### 6.3 Route 3: exact small instances with many classes (`route3_sat.py`, `unsat_check.py`)
- **Setup.** n = 14–26, codimension 4–8, mean c/n = 0.78. Dead points are removed by exact DP, so V = ∪H. Then
  0 ≤ 4n − 7k ≤ 24, and parity-correct disjoint Ω's with W ≤ 4n − 7k are found by greedy BFS.
- **Results.** Ground truth by SAT (CaDiCaL) on the sets, Fano-type:
  - 219 instances satisfy (H0) + (H1);
  - **217 have a Fano-type good seven**;
  - **2 have no good seven of any kind** (SAT 'any': UNSAT).
- **The 2 failures** (`logs/unsat_check.log`, columns stored): n = 14, k = 6, with 15 and 10 members, **τ = 2** by
  exhaustive search, N = 2.33.
  - They are not covering in any regime.
  - But they satisfy (H0) + (H1) with V = ∪H, so **Task 3's conjecture (§4.3) is false as stated**. A hypothesis such as
    τ ≥ 3 or T-covering is needed.
- B1's asymptotic hypotheses fail at this size, and B1 never succeeds there. That is expected: e is comparable to m and u is 1–5.

### 6.4 Counting (`montecarlo.py`): §5.3.

## 7. Status of B and what is left (updated after the second pass)

**Proved [by hand].**
- *Few classes.* S⁺: c ≤ 4(T − 3k/4) − 12 and n/3 + c ≤ T [given S⁺]. 9′: c ≲ (k − 5r)/4, with H3 and H4′.
- *Theorem B1.* B holds for N < 1.852 whenever codim(C_ev) − 1 ≤ min((k − 5r − 41)/15, (r + 4εk − 11)/5), for every
  column structure (committed).
- *Lemma F1 (§5.6).* A rigorous fixed-count Fourier bound, with per-point damping 7^{−1/2} near the constants and an
  entropy form elsewhere. This settles item 1 of §5.5.
- *Theorems F and F2.* Counting criteria for a Fano-type good seven:
  Σ_{λ nonconstant in D⊗F₂³} Φ(n(λ)) < 8P_m, optionally after fixing labels on a set S satisfying (LC0) and (LC1).
  They need no hypothesis on c, no reserved bases and no (SPAN).
- *The reduction of route (c) to the deficiency ratio β (§5.8).* A structural obstruction needs β ≥ 4/7.
- *Third pass (§5.7).*
  - P1: the Möbius identity Σ_λ x^{wt λ} = E_T 8^{drop T}.
  - P2: Theorem F‴, a rigorous criterion for codimension ≲ 0.058N given G(7^{−1/2}) ≈ 1.
  - P3: no absolute-value criterion survives linearly many disjoint short dual words.
  - (iii) is refuted by series-pair and triad families.

**Computed exact.**
- 496/496 B1 constructions verified; Y-step capacity 3m (§4).
- 217/219 small instances satisfying (H0)+(H1) with V = ∪H have a Fano-type seven. The 2 exceptions have τ = 2, which
  refutes Task 3's conjecture.
- Lemma F1 checked exactly on 300 cases; the largest ratio of exact value to bound was 0.015.
- β = 1/3 for every even block (w ≤ 6) and fan (q ≤ 10). Short-dual-word structure gives no obstruction.
- G(7^{−1/2}) by Monte Carlo (`gx.py`): 1.00 for random columns, and about Π(1 + 7x^w) for planted words, up to 6·10⁵ for
  20 series pairs [computed, sampling].

**Heuristic.**
- B1m handles random-like codes in the whole range N < 11/6.
- For random-like D the Theorem F sum is about exp(N[H/2 + 0.067 − 2.08(1 − d/N)]) ≤ e^{−0.41N} (type counting). So
  Theorem F holds with exponential margin for random-like codes.
  - This is heuristic only because B_w(D⊗F₂³) is replaced by its random value. The rigorous F1 bound is kept.

**The remaining gap, exactly (after the third pass, §5.7).**
- Covering coset families with codimension above B1's bound and above F‴'s 0.058N whose column matroid loses rank on
  random 38% subsets: G(7^{−1/2}) ≫ 1 in the Möbius form P1.
- The proved criteria F, F2 and F‴ are absolute-value bounds. P3 shows that no such bound can handle linearly many
  disjoint short dual words, although those are harmless for the true count (local factors ≈ 1).
- So the decomposition must treat short-word structure *multiplicatively* (cluster/polymer expansion, or exact local
  factors), and bound only the global remainder.
- Routes (i), (ii) and (iii) fail as stated (§5.7). (ii) works for isolated short words.
- The polymer route needs a canonical decomposition, because the naive one is not unique, and fixed-count control.

**Counterexample search.**
- Local structures are excluded (§5.8).
- No global structured candidate was built.
- The deficiency LP of §5.8 is the right test for any future candidate: compute β on its dual-word structure before any
  SAT run.

**11/6 ≤ N < 1.938.** B1 and Theorem F need three disjoint small Ω's, which are proved only for N < 1.852 (t = 3/4).
Updated in §9.5: N < 1.861 without the recount, N < 1.909 with empty common intersection, and Theorem S1 (one Ω) to 1.9385.

**Update after the fourth pass (§8–§9).**
- **Shift 0 is closed** for 4 ∣ k in the Fano range (Theorem S0), with no condition on c, cells or short dual words.
  k ≡ 2 (mod 4) is closed below N = 1.7985. Above that it is conditional on one non-self-orthogonality choice [open].
- **At every shift**, B holds for r ≤ 4εk − 7 (Theorem S1, untested) and for codimension within B1's bound.
- **The remaining gap** is r ≥ 4εk − O(1) with codimension above B1's bound.
  - Contraction removes short dual words exactly (§9.1). After it, the step left is check (ii): a bound on the
    medium-weight word counts A_w(D′ ⊗ F₂³), plus giant blocks of words of weight ≥ 3 and the F‴w mixed-constant
    condition.
  - The damping side is no longer the bottleneck. F1⁺ gives 1/7 per point near the constants, and for random-like D′
    the reach is about 0.47N [heuristic].
- **NC's robustness** does not dispose of blocks. It closes B in the regime r < 4εk through NC1 with linear triples,
  which makes the decomposition unnecessary there (§9.4).

Files: `b1.py` (B1, B1m, Lemma B/C/C* constructive, matroid partition, independent verifier); `fam.py` (families, exact
BFS / meet-in-the-middle Ω's, covering certificate); `run_b1.py`; `run_large_M.py`; `ystep.py`; `route3_sat.py`;
`unsat_check.py`; `montecarlo.py`; `f1_check.py` (Lemma F1, exact); `ratio.py` (deficiency ratios, exhaustive); `gx.py` (G(x), sampling); logs in `logs/`.

## 8. B for every linear layer, all shifts (third brief, Task A(a))

Tags as above, plus [dead] and [open]. Code and logs: `compute/programme2/B/shift/`. Units: deficiency, i.e. a point x costs
4 − j_x against the budget 4n − 7k = 4δk (a dumped point costs 4, an Ω-point 1). This is the same thing as the
(3 − j)(4 − j) count against 3(4n − 7k): "4|Z|" and "a coloop costs 12" are the same cost.

### 8.1 Reduction to two cases [proved by hand]
Let H = (e + C) ∩ (V choose k) be a linear layer (e of least weight in its coset, shift wt(e)), H ≠ ∅. Put C₀ = C ∩ Even and
pick e′ ∈ e + C of parity k. Then H = (e′ + C₀) ∩ (V choose k) (Lemma 2.1 of Task 3).
- **Case S≠0: e′ ∉ C₀.** This is a coset family in the sense of §1–§7, with a = e′ and ρ_par = min wt(e′ + C₀) ≥ 1.
  Everything in §1–§7 applies unchanged.
- **Case S0: e′ ∈ C₀.** Then H = C₀ ∩ (V choose k): the members are the weight-k words of an even linear code.
  - Case S0 happens exactly when the shift is 0 **and k is even**. If e′ ∈ C₀ ⊆ C, then e ∈ C.
  - Shift 0 with k odd is case S≠0, with ρ_par = the least odd weight in C.
  - Example: "all k-sets even on X" with k even is S0, with C₀ = {even on X, even}.
- In the Venn form (§2) the shift never enters the counting problem. The Ω's carry α. Every bit-class D_i must lie in C,
  so the target on V″ is 0 for every shift. The shift enters only through the Ω's: through their existence (Theorem D), W, Δ
  and the slack s = 4n − 7k − W.

### 8.2 Which results hold at shift 0 (case S0)

| result | at shift 0 | tag |
|---|---|---|
| Lemma 2.1, Lemma 2.2 (cells, C ⊇ ⊕ Even(V_g)) | yes, with α = 0 | proved by hand |
| Lemma 5, Corollary 7 | Corollary 7 is vacuous (ρ_par = 0). Exact pencils (s_p = 0) are allowed: Schur triangles, 3-dim subspaces | proved by hand |
| Theorem 9′ | yes, with Ω₁ = Ω₂ = Ω₃ = ∅ (W = Δ = 0). The proof is verbatim: Ω enters only through [B_ℓ] ∋ α = 0 and the (now empty) T_i patterns. H2–H4′ (few classes) remain | proved by hand |
| Theorem D | not needed: Ω = ∅ costs nothing | — |
| Theorem B1 | yes, with W = Δ = 0. Conditions: k ≥ 15e + 36 and 4δk ≥ 5e + 8, for **every N**. There is no N < 1.852 restriction and no r in the bound | proved by hand; computed exact (199 verified sevens, §8.5) |
| Theorems F, F2, F‴, P1–P3, §5.8 | verbatim (target 0 for every shift) | proved by hand |
| S⁺ | verbatim: the symmetry argument does not use α | given S⁺ |
| RA | applies to any family. A shift-0 layer is rich only when it is near-complete, so RA is not a route for general shift-0 layers | proved by hand |
| NC | **not every** shift-0 layer (see below) | proved by hand |
| **Theorem S0 (new, §8.3)** | B for every shift-0 layer with 4 ∣ k and N < 11/6 | proved by hand; computed exact |

**NC at shift 0, explicitly [proved by hand].**
- With W = V and d = r (T-covering is (V, r)-completeness), Corollary NC handles every T-covering family of any shift
  with r < 2εk − 3, i.e. n − 2r > (7/4 − ε)k + 5/2.
- With W = one cell V_g (k even, so every k-subset of a cell is in C₀ and d = 0), NC handles every layer with a cell of
  size ≥ (7/4 − ε)k + 3.
- "All k-sets even on X" (k even) is (V, 1)-complete. A (k+1)-set U with a point outside X has a k-subset that is even
  on X: drop an outside point if |U ∩ X| is even, an X-point otherwise. U ⊆ X is also fine. So NC with d = 1 handles it
  as soon as 2εk ≥ 5.
- **NC does not handle every shift-0 layer.**
  - A random even code with all cells singletons has no cell to use. Its covering excess r is not < 2εk when ε is small
    against ω, and restricting to a W ⊊ V does not lower d for a random code.
  - So NC needs d < (ε + δ)k/2 on some W, which fails there.
  - RA does not help either: such layers are thin.
- What does handle them is NC1 fed with a *linear* triple, which exists only because the shift is 0 (§8.3).

### 8.3 Theorem S0: shift 0 is closed by a Schur triangle [proved by hand; computed exact]

**Lemma S0a (Schur triangle).** Let C₀ be even, k even, H = C₀ ∩ (V choose k), with columns h_x (parity coordinate 1) and
e = dim E = codim(C₀) − 1. Suppose some member x₁ satisfies:
- (i) k ≥ 2e_{x₁} + 1 and e_{x₁} ≤ k/2, where e_S = dim E_S and E_S = span{h_x + h_y : x, y ∈ S};
- (ii) e″ := dim((E_{x₁} + E_{V∖x₁})/E_{x₁}) ≤ n − 3k/2, and n − k ≥ 2e″ + 1;
- (iii) 4 ∣ k, or x₁ ∉ C₀^⊥.

Then there are A ⊆ x₁ and B ⊆ V ∖ x₁ with |A| = |B| = k/2 and ΣA = ΣB. So x₂ = A ∪ B and x₃ = x₁ + x₂ = (x₁∖A) ∪ B are
members. The three members have pairwise intersections of size k/2, x₁ + x₂ + x₃ = 0, x₁ ∩ x₂ ∩ x₃ = ∅ and |x₁ ∪ x₂ ∪ x₃| = 3k/2.

*Proof.*
- **The sums over A.** By Lemma C (Task 2) on x₁ with a = k/2, the sums ΣA, |A| = k/2, fill (k/2)h_u + E_{x₁} (u ∈ x₁).
- **The sums over B.** By Lemma C on V ∖ x₁, with columns taken modulo E_{x₁} and a = k/2 (≤ |V∖x₁| − e″ by (ii)), the
  sums ΣB fill (k/2)h_v + E_{x₁} + E_{V∖x₁} modulo E_{x₁} (v ∉ x₁).
- **The two sets meet** iff (k/2)(h_u + h_v) ∈ E′ := E_{x₁} + E_{V∖x₁}.
  - If 4 ∣ k this is 0.
  - Otherwise, suppose E′ ≠ E. Then E = E′ ⊕ ⟨h_u + h_v⟩, and a functional φ with φ(E′) = 0 and φ(h_u + h_v) = 1 gives the
    dual word (φ(h_x))_x ∈ {1_{x₁}, 1 + 1_{x₁}}. Since 1 ∈ C₀^⊥, this puts x₁ ∈ C₀^⊥, which (iii) excludes.
- **The triangle.** x₂ and x₃ are codewords of weight k. x₁ ∩ x₂ = A, and A ∩ x₃ = ∅. ∎

**Lemma S0b (choosing x₁) [proved by hand].**
- Let U ⊇ an affine basis of the columns (e + 1 points), with |U| = k + r. Then E_U = E, and any member x₁ ⊆ U (T-covering)
  has e − e_{x₁} ≤ r, since deleting a point lowers the affine rank by at most 1.
- So e″ ≤ r ≤ n − 3k/2, because n − 3k/2 = k/4 + r + εk.
- Also n − k ≥ 2r + 1. So (ii) is automatic, and (i) holds once e ≤ (k − 1)/2.

**Theorem S0.** Let H = C₀ ∩ (V choose k) be a shift-0 layer (k even), T-covering with T = n − k − r and T ≥ ⌈3k/4⌉
(that is, τ ≥ ⌈3k/4⌉ + 1). Suppose e ≤ (k − 1)/2 and either 4 ∣ k, or the x₁ of Lemma S0b can be taken outside C₀^⊥.
Then H has a Fano-type good seven, so H is not (7,2).

*Proof.* This is NC1 (PROGRAMME2_NC.md §3) with W = V, d = r and G = (x₁, x₂, x₃) from S0a/S0b.
- The X-sets are X₁ = B, X₂ = x₁∖A and X₃ = A, each of size k/2.
- Each line avoiding NC1's point 0 takes one half of each X_s. So |L| ≤ 3k/4 if 4 ∣ k.
- If k ≡ 2 (mod 4), give the larger halves to three colours that are not collinear; then |L| ≤ (3k+2)/4 = ⌈3k/4⌉.
- So |R_ℓ| ≥ n − T = k + r, and R_ℓ contains a member. The three lines through 0 are closed by x₁, x₂ and x₃. ∎

**Range [proved by hand + computed exact].** e ≤ n − ⌈log₂|H|⌉ − 1, and |H| ≥ C(n, k+r)/C(n−k, r) (Task 2).
- **4 ∣ k.**
  - `s0_finite.py`: for every k ≤ 400 (k even), every r and every T ≥ ⌈3k/4⌉ with n < 11k/6 (39,304 triples), counting
    forces e ≤ (k − 1)/2. There are 0 exceptions [computed exact, integer arithmetic].
  - For k > 400, the asymptotic margin is (1/2 − 0.435)k − log₂(n + 1) − 2 > 0 [proved by hand; `ranges.py`].
  - The asymptotic counting range extends to N < 1.8525.
  - **So B holds for every shift-0 layer with 4 ∣ k and τ > 3k/4 in the whole Fano range N < 11/6, for every k ≥ 4.**
- **k ≡ 2 (mod 4).**
  - The unconditional version uses x₁ ∉ C₀^⊥ from counting: |H| > 2^{n/2} rules out a self-orthogonal span(H). It also
    needs e ≤ n − 3k/2, so that (ii) holds for that x₁.
  - Counting guarantees both for N < 1.7985 (asymptotic) [proved by hand]. `s0_finite.py` lists 2,429 finite triples
    near the top of the window where counting does not guarantee them.
  - Beyond that, the extra hypothesis "the S0b member can be taken outside C₀^⊥" is [open]. It held in every test.
- **What S0 needs and what it does not.** There is no condition on c, on singleton cells or on short dual words; the
  planted tests have weight-2 and weight-4 dual words. Neither (SPAN), nor reserved bases, nor counting is used. The
  linear algebra is two applications of Lemma C. The rest is covering.

**Why this is the right mechanism.** The pencil shape (Σ)(b) needs three members with empty common intersection and
wt(x₁+x₂+x₃) ≤ 4T − 3k. At shift ≠ 0, x₁ + x₂ + x₃ ∈ a + C has weight ≥ ρ_par ≥ 1 (§1(a): no perfect pencil). At shift 0
it can be 0, and Lemma C makes it 0.

### 8.4 The same construction at every shift (Theorem S1) [proved by hand; not yet tested]
**Construction.** Let Ω ∈ a + C have parity k and weight ρ = ρ_par.
- Take a member x₁ disjoint from Ω (covering on V ∖ Ω).
- Choose A ⊆ x₁ with |A| = (k+ρ)/2 and B ⊆ V ∖ (x₁ ∪ Ω) with |B| = (k−ρ)/2, such that ΣA + ΣB = σ(a).
- Put x₂ = A ∪ B and x₃ = x₁ + x₂ + Ω = (x₁∖A) ∪ B ∪ Ω.

**Properties.**
- x₂ and x₃ are members. x₁ ∩ x₂ ∩ x₃ = ∅. |∪| = (3k + ρ)/2, and x₁ + x₂ + x₃ = Ω.
- In NC1 (W = V, d = r): X₃ = A, X₂ = x₁∖A, and X₁ = B. The points of Ω lie only in x₃, so they are split between X₁ and X₂.
  Then |L| ≤ (3k + ρ)/4 + 3/2.
- **So H is not (7,2) once ρ_par ≤ 4T − 3k − 6 and the Lemma C steps go through.**
  - Lemma C on x₁ needs e_{x₁} ≤ (k − ρ)/2.
  - On V ∖ (x₁ ∪ Ω), modulo E_{x₁}, it needs e″ ≤ n − 3k/2 − ρ/2.
  - Plus a separation condition: no dual word λ with λ ∖ Ω ∈ {x₁, V∖(x₁∪Ω)}.

**Range.**
- With Theorem D (ρ_par ≤ r + 1), this gives B whenever r ≤ 4εk − 7 and e ≲ (k − r)/2, at any codimension up to k/2.
  - Corollary NC only reached r < 2εk.
  - B1 needs codim ≲ (r + 4εk)/5.
- So **B's remaining gap at shift ≠ 0 is r ≥ 4εk − O(1) (ω ≥ 4ε), together with codimension above B1's bound.**
- Theorem S1 is S0 with ρ = 0. It was not stress-tested in this pass, so it stays at [proved by hand, untested].

### 8.5 Tests (`shift/s0.py`, `shift/tri_test.py`; logs `shift/logs/`) [computed exact per instance]
**Families.**
- Random even codes (parity row plus M random rows), some with planted rows of support 2 or 4. The planted rows are
  short dual words, which break the covering certificate.
- k = 8, 10, 12, 14, 32, 40, 42, 60, 62, 80, 106, 200, 202, including k ≡ 2 (mod 4). n is up to 370.

**Certified hypotheses.**
- r_cert is the least r with r ≥ e such that every nontrivial dual word λ has |λ|, n − |λ| < k + r.
- Then every (k+r)-set U has E_U = E, and Lemma C puts a member in U, which certifies T-covering.
- "hyp" means 4T ≥ 3k, e ≤ (k−1)/2 and n ≥ k + r + 2.

**Verifier.** Every produced seven went through `verify7.py`, written fresh with no shared code:
- seven pairwise distinct sets;
- each of size k with zero syndrome under the original rows;
- no transversal of size ≤ 2, by brute force over all point pairs.

**Results.**

| | instances | S0 seven built and verified | B1 (Ω = ∅) built and verified |
|---|---|---|---|
| hypotheses certified | 132 (35 with k ≡ 2 mod 4) | **132** | 72 (60: B1's size hypotheses fail at small k) |
| not certified (n small, or planted short words) | 187 | **187** | 127 |
| **all** | **319** | **319**, 0 verifier failures | 199 |

- `tri_test.py`: the Schur-triangle step alone, in the large-codimension range k/4 < e ≤ (k−1)/2 (e up to 90 at k = 200;
  planted words included; k ≡ 2 mod 4 included): **109/109** triangles built by the proof's Lemma C steps and checked
  directly (three distinct members, sum 0, empty triple intersection).
- B1 at shift 0 needs k ≥ 15e + 36. That is why it fails at small k, while S0 does not.

## 9. Contraction instead of expansion (Task A(b)), and the two checks

### 9.1 The objects [proved by hand]
**Wording** (corrected per the reviewer). A *short dual word* is h ∈ C^⊥ with ⟨h, B⟩ = 0 for every member B, i.e.
⟨h, a⟩ = 0, so members meet supp h evenly. Its weight need not be even, and that is why odd pieces exist. Every h with
⟨h, a⟩ = 1 has weight ≥ T + 1 (covering dictionary). At shift 0 every dual word has ⟨h, a⟩ = 0.

**Order of operations: Ω first, then contraction on V″.**
- Fix Ω, F and Z₀ (Theorem D and B1, or ∅ at shift 0). Then work with the punctured dual D = C^⊥|_{V″}, as in §5.
- **Lemma P (puncturing keeps parity).**
  - If h ∈ C^⊥ has ⟨h, a⟩ = 0, then |h ∩ Ω_i| is even for each i (since Ω_i ∈ a + C) and |h ∩ F| is even (F ∈ C).
    So |h|_{V″}| ≡ |h| + |h ∩ Z₀| (mod 2).
  - If ⟨h, a⟩ = 1, then |h|_{V″}| ≥ T + 1 − |V ∖ V″|. This exceeds w₀ as soon as w₀ < T + 1 − W − u − |F| (about
    3k/4 − 4δk).
  - So the short words of D are exactly the restrictions of short words of C^⊥ with ⟨h, a⟩ = 0. They keep their weight
    parity, except through Z₀, which we choose.
- **"Lost parity" does not arise in this order.**
  - The condition for B_ℓ is ⟨∪_{p∉ℓ}Y_p, λ⟩ = 0 for λ ∈ D. The Ω's already carry ⟨a, h⟩.
  - A word that is even on every block is satisfied by every block-respecting labelling.
  - The brief's lost-parity case is an artefact of contracting before choosing the Ω's. Then the Ω's would have to be
    unions of blocks with ⟨Ω, h⟩ = 1.
- **"Blocks met by an Ω" disappear the same way.** The Ω's are removed before the blocks are formed, and Lemma P says
  removing them never creates an odd short word.
  - The price: puncturing can make medium words of C^⊥ short in D. These are simply short words of D and are handled
    with the rest.
  - So there is no need to run Theorem D on the contracted family.

**The contraction.**
- **Blocks.** Let D_s = span of the words of D of weight ≤ w₀. Its blocks S₁, …, S_q are the components of the hypergraph
  of supports. Each short word lies inside one block.
- **Contracted problem.** Labellings constant on each block correspond exactly to labellings of the contracted ground
  set, in which block j has weight w_j = |S_j ∖ Z| and unit points have weight 1. The contracted dual is
  D′ = π(D), where π(λ)_j = |λ ∩ S_j| mod 2.
  - The number of Fano-type sevens of the 9′/B1 form with monochromatic blocks equals the weighted count of §9.2 for
    (D′, w, m), exactly.
  - Every word even on every block lies in ker π and costs nothing (zero slack, §5.7).
- **Odd pieces.**
  - Weight parity is linear on D[S_j] = {λ ∈ D : supp λ ⊆ S_j}. If it is nonzero, choose Z_j ⊆ S_j with
    ⟨1_{Z_j}, λ⟩ = |λ| for all λ ∈ D[S_j] (an information set gives |Z_j| ≤ dim D[S_j]) and dump Z_j.
  - The cost is 4|Z_j| deficiency. Note that the parity must be fixed on all of D[S_j], not only on D_s. A long word
    inside a block with odd weight would otherwise become a coloop of D′.
  - Alternative at zero slack: give the block a fixed non-monochromatic labelling with XOR 0 on every word (possible iff
    D[S_j] has no weight-1 word). That is F2 with S = S_j. It keeps the slack but loses the block's count factor.
- **Iteration.** D′ can have new light words: images of long words that are even on most blocks. Merge blocks along
  them and repeat.
  - Every round merges at least two units, so the process terminates.
  - At the end, D′ has no nonzero word of weight ≤ w₀ (weight = number of units), and every remaining coloop has been
    dumped.
  - Total dump: |Z| ≤ Σ over odd merged blocks of dim D[S_j].
  - **Budget condition:** |Z₀| + |Z| ≤ u (deficiency 4 each).

### 9.2 Weighted points: Lemma F1w, size repair, Theorem F‴w [proved by hand; F1w checked exactly]
**Lemma F1w.** Blocks j have integer weights w_j. For λ: blocks → F₂³,
  S(λ) = Σ_{v: Σ_{j: v_j = v} w_j = m_v} Π_j (−1)^{⟨λ_j, v_j⟩}.
For every ζ ∈ (0, ∞)^7,
  |S(λ)| ≤ ζ^{−m} Π_j Z_j(ζ) · Π_{w} Φ(n^{(w)}(λ); P₂^{(w)}),
where:
- Z_j = Σ_v ζ_v^{w_j};
- n^{(w)}_u = #{j : w_j = w, λ_j = u};
- P₂^{(w)} = 8Σ_v ζ_v^{2w}/(Σ_v ζ_v^w)²;
- Φ is as in F1.

Equivalently, |S(λ)| ≤ S(0)·Π_w Φ^{(w)}/P_m^w, with P_m^w = S(0)ζ^m/ΠZ_j the probability that the i.i.d. model (block j
gets v with probability ζ_v^{w_j}/Z_j) hits the counts m exactly.

*Proof.*
- S(λ) = [z^m] Π_j F_{j,λ_j}(z), with F_{j,u}(z) = Σ_v (−1)^{⟨u,v⟩} z_v^{w_j}. Substitute z = ζe^{iθ}.
- For a fixed weight w, F_{j,u}/Z_j is the F₂³-Fourier transform at u of f(v) = ζ_v^w e^{iwθ_v}/Z_j (f(0) = 0). So it has
  modulus ≤ 1, and its squared moduli sum over u to P₂^{(w)} for every θ (Parseval).
- Bound the θ-supremum of the product by the product over weight classes of the F1 maxima. ∎

- **Exact check (`f1w_check.py`).** S(λ) was computed by rational DP, with weights in {1, 2, 3}, near-constant and
  spread λ, and ζ both at m/N and random. The bound held in 153/153 cases (loose, as for F1) [computed exact].
- **The damping does not depend on the weight when the regions are equal.** With ζ constant, P₂^{(w)} = 8/7 for every
  w, so every block, of any weight, is damped by 7^{−1/2}. For unequal regions, P₂^{(w)} = 8/7 + O((w·Δm/m)²), so bounded
  weights cost O(1).

**Size repair = a lower bound on P_m^w [proved by hand, standard].**
- The counts in S are exact, so a positive count is an exactly sized seven. Nothing has to be repaired afterwards. What
  is needed is P_m^w ≥ poly(N)^{−1}.
- Choose ζ at the saddle point, where the model mean equals m. This exists because m is interior and the log-partition
  function is strictly convex.
- Let N₁ be the number of unit points and Q = Σ_{heavy j} w_j².
  - Chebyshev puts every heavy count within √N₁ of its mean with probability ≥ 1 − 7Q/N₁.
  - Conditionally, the unit points hit the residual counts with probability ≥ c(min_v ζ_v/Σζ)·N₁^{−3} (Stirling).
- **So P_m^w ≥ (c/2)N₁^{−3} once Q ≤ N₁/14.** "Giant blocks" are, by definition, the failure of Q ≤ N₁/14 (§9.4).

**Theorem F‴w [proved by hand].** Write c_w for the number of distinct weights and M for the 8^{c_w} "mixed constants"
Σ_w u_w ⊗ 1_{class w}. Then
  Σ_{λ ∈ D′⊗F₂³ nonconstant} Π_w Φ^{(w)} < 8 P_m^w
gives a Fano-type good seven with monochromatic blocks.

The F‴ split goes through, with one change:
- The near-constant part is bounded by 8(G_M(x) − 1), where G_M(x) = Σ_λ x^{dist(λ, M)} and x = 7^{−1/2}. Each weight
  class has its own nearest constant.
- G_M − 1 is small iff D′ has no light words **and** no word close to a nontrivial mixed constant. That second condition
  says that the class indicators 1_{class w} are far from D′ + ⟨1⟩, which is a genuine extra hypothesis [open in general].
- With a single weight (c_w = 1) this is F‴ itself. Then the spread term 8^{d′} e^{−0.12N′} again limits d′ ≲ 0.058N′,
  where N′ is the number of units.

### 9.3 Lemma F1⁺: the heuristic damping 1/7 is rigorous near the constants [proved by hand; checked exactly]
- **The extra Parseval constraints.** For a two-element subgroup U = {0, u} ≤ F₂³, the transform values g₀(θ), g_u(θ) of F1
  satisfy, for every θ,
    |g₀|² + |g_u|² = 2|Σ_{⟨u,v⟩=0, v≠0} p_v e^{iθ_v}|² + 2|Σ_{⟨u,v⟩=1} p_v e^{iθ_v}|² ≤ c_u := 2(a_u² + (1 − a_u)²),
  with a_u = Σ_{⟨u,v⟩=1} p_v. For equal regions, c_u = 50/49.
- **The bound.** Shift λ by its dominant value; this changes S only by a sign, since Σ_x ⟨u, v(x)⟩ = Σ_v m_v⟨u,v⟩ is
  fixed. Then
    |S(λ)| ≤ (Mult(m)/P_m) · max_{0 ≤ t₀ ≤ 1} t₀^{n₀/2} Π_{u≠0} min(1, c_u − t₀)^{n_u/2}.
- **Near the constants.** For equal regions and d(λ) ≤ N/50, the maximum is at t₀ = 1, and the bound is **7^{−d(λ)}**.
  That is per-point damping 1/7, where F1 gave 7^{−1/2}.
- **Beyond.** For d(λ) = fN > N/50, the bound is exp((N/2)(ln(50/49) − h(f))). It is valid for every λ, not only for
  two-valued ones, and it is tight for two-valued words: it is the Krawtchouk magnitude.
- **Exact check (`f1w_check.py`).** The bound held in 148/148 cases (N = 10–22), and it was sharper than F1 in 65 of them
  [computed exact].
- **Consequences.**
  - Theorem F‴ holds with G(7^{−1/2}) replaced by G(1/7) for the words with d ≤ N/50. That is a much weaker hypothesis:
    a weight-w word now costs 7·7^{−w}, not 7·7^{−w/2}.
  - Theorem F‴w holds in the same way, class by class, with c_u^{(w)} from the tilted law.
  - **But P3 survives:** q isolated series pairs still give G(1/7) ≥ (8/7)^q, and these terms have sign +. No
    absolute-value bound, however sharp, removes them. They must be contracted (§9.1), and after contraction this is
    exactly what is needed.

### 9.4 Giant blocks, and the coordinator's NC question
**Giant blocks** (Q > N₁/14, or one block carrying a fixed fraction of N) [partly proved; open in general].
- **Few giant blocks.** Fix each one monochromatically (F2 with S = the giant blocks; (LC0) holds after the Z-fix, and
  (LC1) is the parity condition), choosing the labels so that the residual m′ stays balanced. The rest is counted. This
  works when the number of giant blocks is O(1) [proved by hand, from F2].
- **Many giant blocks.** Not handled.
  - **The brief's route ("low rate on the block, profile-type, route to S⁺/9′") is [dead] as stated.** A connected union
    of words of weight ≤ w₀ on S has dim D[S] ≥ (|S| − 1)/(w₀ − 1). That makes the shortened code of rate ≤ 1 − 1/w₀ on S,
    which is not low rate.
  - Nor is the family invariant under Sym(S), so S⁺ does not apply. The one exception is the series-pair case (all words
    of weight 2), where S is a cell.
  - **Series-pair giant blocks *are* cells, and the right tool for them is 9′'s cell machinery or B1's blocks**, which
    already allow them.
- **The case of [open] content is giant blocks of short words of weight ≥ 3**, for example a long chain of overlapping
  triads.

**Does NC's robustness help the decomposition step?**
- **No, as a disposal tool for a block [proved by hand].**
  - NC needs a W with |W| ≥ (7/4 − ε)k + 2d + 3. A light-word block or a giant block is a proper part of V, with
    |V| = (7/4 + δ)k. To qualify it would have to be almost all of V.
  - It would also have to be near-complete. But a block carrying many short dual words has dim D[S] ≥ (|S| − 1)/(w₀ − 1).
    So H[S] is a high-codimension layer on S whose (S, d)-completeness excess d grows with |S|/w₀ [heuristic for the size
    of d].
  - NC's tolerance of outside members does not buy anything here. The members outside a block are not arbitrary: they
    are the same layer.
- **Yes, as a closing tool [proved by hand, §8.3–8.4].**
  - What NC1 really needs is three members with empty common intersection and small union. Its four other lines are
    closed by covering alone, so no linear algebra is spent on them.
  - At shift 0 a linear (Schur) triple always qualifies, and that closes S0 (Theorem S0).
  - At shift ≠ 0 the triple sum lies in a + C, and S1 makes it equal to a minimum-weight Ω. That closes B whenever
    r ≤ 4εk − 7.
  - Like NC, this route is indifferent to short dual words and to c. Its limit is r versus 4εk, not codimension.
- **So NC1 removes the need for the decomposition in the regime r < 4εk.** Contraction is needed only for r ≥ 4εk.

### 9.5 N ≥ 11/6 (replaces check (i))
The reviewer is right: "1.852 ≤ N < 11/6" is empty, since 11/6 ≈ 1.833. B1's Ω's already cover N < 11/6.

**What B has for N ≥ 11/6.**
- A Fano-type good seven is sufficient at every N, and every construction here produces one (9′, B1, F, NC1, S0, S1). So
  the classification "good sevens are Fano-type" is not needed for B. It matters only for the obstruction (Corollary 7).
- **Single Ω (Theorem D, ρ_par ≤ r + 1):** N < 1.9385 [VERIFIED].
- **Three pairwise disjoint Ω's:** N < 1.852 with the recount of Task 2. **N < 1.861 without the recount** [proved by hand,
  `ranges.py`]: Theorem D on V ∖ X needs only e′ ≤ e and e ≤ T − |X|, and e′ ≤ e holds trivially, so no new count on the
  smaller ground set is required.
- **Shift 0:** B1 (Ω = ∅) at every N under its codimension bound. S0 for N < 1.8525 (4 ∣ k, counting).
- **N > 1.9385:** nothing for coset families beyond Lemma 8 (ρ ≤ 2r + 1). The core-window results (CORE, up to about
  N ≈ 2.25) are not coset-family statements, and nothing here extends them.

**Does the empty-common-intersection relaxation extend anything? Yes, the three-Ω range, from 1.852/1.861 to 1.909.**
- **The patterns [computed exact, `omega_overlap.py`, exhaustive on Π].**
  - A point of Ω_i ∩ Ω_j gets colour q ∈ ℓ_m ∖ {p₀}, with pattern P = ANTI(q) ∖ {ℓ_i, ℓ_j}: two lines, j = 2,
    admissible, and omitted from ℓ_i and ℓ_j.
  - For all 6 choices, T_i + T_j + P is a nonzero anti-pencil ANTI(p_ij) ∈ S. So the pencil sums are unchanged as vectors.
  - The Y-step target then shifts by [O_ij] ⊗ ANTI(p_ij). That is reachable: it lies in S ⊗ Q. Its parity coordinate is
    the size equation, so B1's coset bookkeeping is unaffected.
  - t mod 2 changes by Σ|O_ij|·ANTI(p_ij) ∈ S, so integrality of m_p is unaffected (mod-4 fixer as before).
  - The deficiency per Ω-incidence is still 1, so the budget is Σ|Ω_i| ≤ 4n − 7k, and 3(r + 1) ≤ 4δk holds throughout
    [proved by hand].
  - The full re-write of the 9′/B1 size formulas with overlaps was not carried out [sketch].
- **Getting the Ω's.**
  - Ω₁: Theorem D on V. Ω₂: Theorem D on V ∖ S₁, with S₁ ⊆ Ω₁ and |S₁| = ⌈|Ω₁|/2⌉. Ω₃: Theorem D on V ∖ (Ω₁ ∩ Ω₂).
  - Then ∩Ω_i = ∅, and the largest shrink is ⌈(r + 1)/2⌉, against 2(r + 1) for disjoint Ω's. Halving is optimal for
    this scheme.
  - Thresholds (t = 3/4 worst case, `ranges.py`): **N < 1.909** (no recount) or 1.9065 (recount) [proved by hand:
    asymptotic counting].
- **Not extended:** 1.909 ≤ N < 1.9385 (only one Ω), and nothing above 1.9385, because Theorem D itself stops there.
- **Alternative above 1.909:** Theorem S1 needs only **one** Ω. So it covers r ≤ 4εk − 7 up to N < 1.9385 as well
  [proved by hand, untested].

### 9.6 Check (ii): codimension above 0.09k with no short dual words
**Verdict: open.** It is the exact remaining step of B after contraction, in the regime r ≥ 4εk − O(1) (below that,
S1/NC1 closes B).

**Why it is open [proved by hand].**
- After contraction, D′ has no words of weight ≤ w₀.
- The proved criteria still need either:
  - d′ ≲ 0.058N′ (F‴'s spread term 8^{d′}e^{−0.12N′}); or
  - control of the number A_w(D′ ⊗ F₂³) of words at distance w from the constants, for medium w. F1⁺ needs about
    Σ_w A_w exp(−(N/2)(h(w/N) − ln(50/49))) ≪ 1 in the range N/50 < w ≤ N/2.
- Minimum distance > w₀ bounds only the w ≤ w₀ part. A code can have no light words and still have 2^{d′} words packed
  near weight N/50.

**Route (1), "such families do not exist in the Fano range": [dead] for random-like codes.**
- Random codes of codimension M are covering when log₂C(k+r, r) ≳ M [heuristic: covering of random codes]. Codimension
  0.09k then needs only ω ≈ 0.0115, i.e. N ≈ 1.762 + ε.
- Their dual distance is at the GV bound, so they have no short dual words.
- So these families exist throughout 1.77 ≲ N < 11/6. They are near-perfect coverings only when M is close to the
  counting bound n − log₂|H| (0.026k at N = 7/4, 0.435k at N = 11/6), which they need not be.

**Route (2), exact signs instead of absolute values: partly done, not closed.**
- F1⁺ (§9.3) achieves the true magnitude 1/7 per point near the constants. The two-valued words are exactly Krawtchouk
  values, with signs (−1)^w at small w.
- What is still missing is the cancellation *between* medium-weight words. For that one needs the signed sum
  Σ_λ S(λ)/S(0), which equals the uncounted identity 5.1 up to the fixed-count correction. Bounding it from below with
  signs needs the weight enumerator of D′, which "no short words" does not give.
- **The precise sufficient condition, rigorous:** Σ_{w>N/50} A_w(D′⊗F₂³)·exp(−(N/2)(h(w/N) − 0.0202)) + 8(G′(1/7) − 1) < P_m
  (plus F1's entropy bound for words with dominant fraction < 1/2).
  - For random-like D′ [heuristic, `reach_f1plus.py`], replace A_w by its random value.
    - Words of typical type: the F1 bound already reaches d′ ≈ 0.47N, because off-dominant points spread over 7 values
      get 7^{−1} from F1 itself.
    - Two-valued words: F1⁺ reaches d′ ≈ 0.49N, against 0.40N with F1 alone.
    - So F‴'s 0.058N is an artefact of the crude count 8^{d′}, not of the damping. This agrees with §5.4's heuristic
      e < (2/3)N.
  - No rigorous bound on A_w for medium w is available for general codes. That count, not the damping, is the whole
    content of check (ii).

### 9.7 Summary of Task A(a)–(b)
**[proved by hand]**
- The two-case reduction.
- The shift-0 table.
- **Theorem S0**: B for every shift-0 layer with 4 ∣ k in N < 11/6, any column structure.
- S1 (B for r ≤ 4εk − 7 at any shift, untested).
- Lemma P (puncturing keeps parity; lost parity and Ω-met blocks do not arise in the Ω-first order).
- The contraction lemma and its termination.
- F1w, the P_m^w bound (size repair), F‴w (with the mixed-constant hypothesis), F1⁺.
- Thresholds for N ≥ 11/6: three disjoint Ω's to 1.861, empty common intersection to 1.909.

**[computed exact]**
- 319/319 S0 sevens and 199 B1 (Ω = ∅) sevens independently verified.
- 109/109 Schur triangles in the large-codimension range.
- 0 counting exceptions for 4 ∣ k, k ≤ 400.
- F1w 153/153 and F1⁺ 148/148.
- Overlap patterns: 6/6.

**[open]**
- k ≡ 2 (mod 4) at shift 0 near the top of the window.
- Giant blocks of words of weight ≥ 3.
- Check (ii) (codimension > 0.09k with no short words, r ≥ 4εk).
- The mixed-constant hypothesis of F‴w.
- The full overlap version of 9′/B1.

**[dead]**
- Routing giant blocks to S⁺/9′ as stated.
- Route (1) of check (ii).
- NC as a block-disposal tool.

**[heuristic]**
- Random codes exist in check (ii)'s range.
- The reach of F1/F1⁺ for random-like D′: about 0.47N (typical types) and 0.49N (two-valued words).

Files (`compute/programme2/B/shift/`):
- `s0.py`: Theorem S0 construction, the covering certificate, B1 at Ω = ∅.
- `verify7.py`: independent verifier.
- `tri_test.py`: Schur triangles.
- `s0_finite.py`: counting for S0.
- `ranges.py`: asymptotic thresholds.
- `f1w_check.py`: F1w and F1⁺, exact.
- `omega_overlap.py`: overlap patterns.
- `reach_f1plus.py`: heuristic reach for random-like D′.
- Logs are in `logs/`.
