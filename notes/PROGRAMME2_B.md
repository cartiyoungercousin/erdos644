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
  - Item 2 (a deterministic decomposition) is open (§5.7).
  - Short dual words cannot obstruct (§5.8).
  - See §7.

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

### 5.7 Item 2 (the decomposition): status [proved: the reduction; not proved: the size bound]
- **What a decomposition must do.** The words that break Theorem F are those near the constants: Φ ≈ 7^{−d/2} against
  their number. Theorem F2 removes them by fixing labels on their supports. Any word of D supported in S becomes a local
  constraint (LC0) and disappears from D_R.
- **Why this is not yet a proof: puncturing lowers weights.** D_R = D|_R can acquire *new* light words: words heavy on S
  and light on R.
  - The closure S* (the least S such that D|_{V″∖S} has no nonconstant word at two-sided weight < w₀) exists, by
    iteration.
  - But nothing known bounds |S*|.
  - Moreover, (LC0) on S* is a labelling problem of the same type on S*, with no spread. That is circular.
- **What would close B.** One of:
  - (i) a bound |S*| ≤ c·u together with a B1-type solution on S*; or
  - (ii) a direct type-distribution bound for D ⊗ F₂³ under T-covering (covering only constrains the words of
    C^⊥ ∖ C₀^⊥, which have weight ≥ T + 1, and says nothing about C₀^⊥); or
  - (iii) a structural reason why covering coset families in the gap have random-like D.
  I found none of these. **Item 2 is open.**

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

**Computed exact.**
- 496/496 B1 constructions verified; Y-step capacity 3m (§4).
- 217/219 small instances satisfying (H0)+(H1) with V = ∪H have a Fano-type seven. The 2 exceptions have τ = 2, which
  refutes Task 3's conjecture.
- Lemma F1 checked exactly on 300 cases; the largest ratio of exact value to bound was 0.015.
- β = 1/3 for every even block (w ≤ 6) and fan (q ≤ 10). Short-dual-word structure gives no obstruction.

**Heuristic.**
- B1m handles random-like codes in the whole range N < 11/6.
- For random-like D the Theorem F sum is about exp(N[H/2 + 0.067 − 2.08(1 − d/N)]) ≤ e^{−0.41N} (type counting). So
  Theorem F holds with exponential margin for random-like codes.
  - This is heuristic only because B_w(D⊗F₂³) is replaced by its random value. The rigorous F1 bound is kept.

**The remaining gap, exactly.**
- Covering coset families with codimension above B1's bound whose punctured dual D has *many* near-constant words of
  D⊗F₂³: more than about 7^{d/2} words at distance d.
- These are codes with a large amount of near-coloop structure: subsets S with rank drop ≥ 0.47|S|, the threshold where
  8^{drop}·7^{−|S|/2} ≥ 1.
- For them Theorem F fails, B1's dump budget u is too small, and Theorem F2 needs the closure S* of §5.7, whose size is
  not controlled.
- Choice made: route (b). Item 1 is done. Item 2 is open, and §5.7 (i)–(iii) are the three possible ways to close it.

**Counterexample search.**
- Local structures are excluded (§5.8).
- No global structured candidate was built.
- The deficiency LP of §5.8 is the right test for any future candidate: compute β on its dual-word structure before any
  SAT run.

**11/6 ≤ N < 1.938.** B1 and Theorem F need three disjoint small Ω's, which are proved only for N < 1.852 (t = 3/4).
Unchanged.

Files: `b1.py` (B1, B1m, Lemma B/C/C* constructive, matroid partition, independent verifier); `fam.py` (families, exact
BFS / meet-in-the-middle Ω's, covering certificate); `run_b1.py`; `run_large_M.py`; `ystep.py`; `route3_sat.py`;
`unsat_check.py`; `montecarlo.py`; `f1_check.py` (Lemma F1, exact); `ratio.py` (deficiency ratios, exhaustive); logs in `logs/`.
