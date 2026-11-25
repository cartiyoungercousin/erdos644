# PROGRAMME_2, Task 3: the adjustment step of Proposition 9

Status tags: **[proved by hand]**, **[computed exact]** (a finite exhaustive check, or explicit sets passed through
the exact verifier), **[computed MILP]** (HiGHS infeasibility, float-based, not a proof), **[heuristic]**.
Code is in `compute/programme2/task3/`. Fano labelling as in the notes: points 1..7, lines
124, 235, 346, 457, 156, 267, 137, and p₀ = 7. The pencil at p₀ is ℓ₁ = 457, ℓ₂ = 267, ℓ₃ = 137.

## 0. Verdict

- **The adjustment step closes.** Theorem 9′ (§3) gives a hand proof under explicit hypotheses.
  - Linear algebra over F₂ handles the classes.
  - A separate counting argument handles the sizes.
  - The cell-parity structure of a + C handles the realisation.
- **Proposition 9 as literally stated is FALSE**, and the fault is *size parity*. The Ω_i must have |Ω_i| ≡ k (mod 2).
  - Counterexample in §4.1 [proved by hand; computed exact].
  - With that one correction, no counterexample was found. Every tested family with V = ∪H and parity-correct Ω's
    satisfying Σ|Ω_i| ≤ 4n − 7k has a Fano-type good seven: 284/284 instances [every positive answer is computed
    exact].
- **"C too small to absorb deficiencies" is not an obstruction.** C always contains every even subset of every class
  cell (§2, Lemma 2.2). Absorption therefore depends only on how big the cells are, not on C.
- **The remaining hypotheses of Theorem 9′ are mild in the Programme's regime.** They are a size margin k ≥ W + O(2^r)
  and a largeness condition on one class cell (§3, §5). Computation suggests they are artefacts of the construction (§4.3).

## 1. The linear algebra (the brief's 7×7 system) [proved by hand; F1–F5 computed exact in `claims.py`]

Write Q = F₂^V / C and [S] for the class of S, so a + C = {S : [S] = α}.

- **The system.** For a colouring χ with classes x_p = [χ⁻¹(p)] ∈ Q, the line classes are [R_ℓ] = Σ_{p∉ℓ} x_p.
  Over F₂ the matrix N = (𝟙[p ∉ ℓ]) has:
  - row space equal to the [7,3] simplex code S, so rank 3;
  - kernel equal to the [7,4] Hamming code Ham, which is the span of the lines (F1).
- **Which targets are reachable.** The reachable class vectors ([R_ℓ])_ℓ form exactly S ⊗ Q. The three "pencil-sum"
  invariants Σ_{ℓ∋p} [R_ℓ] = 0 cut out S ⊗ Q. Moving a point x from colour p to colour q adds [x] ⊗ c, where c is
  the weight-4 word "lines through exactly one of p and q".
- **The brief's target is reachable.** The target is [R_ℓ] = 0 on the pencil at p₀ and α off it. That vector is
  α ⊗ (anti-pencil of p₀) ∈ S ⊗ Q, so it is always reachable. The full solution set is α e_{p₀} + Ham ⊗ Q.
  **The class part of the adjustment step therefore never blocks.**
- **Fano-type in terms of patterns.** For seven sets B_ℓ indexed by lines, put J(x) = {ℓ : x ∈ B_ℓ}. The seven sets are
  Fano-type (every pencil triple has empty intersection) iff every J(x) lies inside some anti-pencil
  ANTI(p) = {ℓ : p ∉ ℓ}. Equivalently, J(x) contains no concurrent triple (F2). There are 64 admissible patterns.
  - Colouring x by such a p gives a Fano colouring with B_ℓ ⊆ R_ℓ.
  - So a Fano-type good seven is an assignment of admissible patterns with |{x : ℓ ∈ J(x)}| = k and
    Σ_x [x] ⊗ 𝟙_{J(x)} = α ⊗ 𝟙.
- **Triangles.** A triangle T is three non-concurrent lines, i.e. ANTI(q) minus one line; q is the *colour* of T.
  - Its degree-1 points form a line (F3).
  - Call (T₁, T₂, T₃) an **odd triple** if every line lies in an odd number of the T_i. Then the pencil-degree
    parities of the T_i sum to the all-ones vector (F4).
  - There are 336 ordered odd triples. 8 of them have the brief's form T_i = ANTI(q_i) ∖ {ℓ_i} with q_i ∉ ℓ_i (F5).
  - The ones used here are T₁ = {124, 156, 267} (colour 3), T₂ = {124, 137, 346} (colour 5) and
    T₃ = {124, 235, 457} (colour 6). Each line lies in exactly one T_i, except 124, which lies in all three.

## 2. Reductions [proved by hand]

**Lemma 2.1 (parity half).** Let C₀ = C ∩ Even. Every k-set of a + C lies in the coset a′ + C₀ of words of parity k.
So H = (a′ + C₀) ∩ (V choose k), and one may assume C is even.
- Then |Ω| ≡ k (mod 2) is exactly the condition Ω ∈ a′ + C₀.
- The pencil sums s_p in Lemma 5 / Corollary 7 are sums of three members, so they lie in a′ + C₀. Corollary 7 therefore
  holds with ρ₀ = min wt(a′ + C₀) ≥ ρ. This is a slightly stronger obstruction. ρ₀ is also the natural constant for
  Proposition 9.

**Lemma 2.2 (cells).** Let V_g = {x : [x] = g} for g ∈ Q. Then [S] = Σ_g (|S ∩ V_g| mod 2)·g.
- Hence C ⊇ ⊕_g Even(V_g), and every pair of points of one cell is a weight-2 codeword.
- Every coset family is therefore a "generalised parity family": membership of a set depends only on its cell parities.
  The q-cell parity families are the case where the cell classes are independent.
- **Consequence.** Whether H has a Fano-type good seven depends only on the cell sizes (N_g), α and k. Exactly, it is the
  integer program over z_{g,J} ≥ 0 (g ∈ Q, J admissible) with:
  - Σ_J z_{g,J} = N_g;
  - Σ_{g, J∋ℓ} z_{g,J} = k;
  - Σ_{g, J∋ℓ} (z_{g,J} mod 2)·g = α for every ℓ;
  - the seven sets distinct.

  This is `ilp.good_seven_counts`. Its size is independent of n.

## 3. Theorem 9′ (Proposition 9 with exact hypotheses) [proved by hand]

**Setting.** V is finite with n = |V|, C ≤ F₂^V, a ∉ C, k ≥ 1, and H = (a + C) ∩ (V choose k).
Ω₁, Ω₂, Ω₃ ∈ a + C are pairwise disjoint, w_i = |Ω_i|, W = Σ w_i, Δ = max w_i − min w_i, and V′ = V ∖ ∪Ω_i.

**Hypotheses.**
- **(H0)** W ≤ 4n − 7k.
- **(H1)** w_i ≡ k (mod 2) for i = 1, 2, 3. This is automatic when C is even (Lemma 2.1).

Put s = 4n − 7k − W. Then s ≡ k − W ≡ 0 or 2 (mod 4), because 4n − 7k ≡ k (mod 4) and W ≡ 3k (mod 2).
Put f = 𝟙[s ≡ 2 (mod 4)] and u = (s − 2f)/4 ≥ 0. Let c be the number of classes occurring in V′.
- **(H2)** k ≥ W + 2Δ + 4c + 6.
- **(H3)** Some class g* has |V′_{g*}| ≥ u + 2f + 7.
- **(H4′)** At most u classes occur exactly once in V′.

**Conclusion.** H contains seven distinct members B_ℓ forming a Fano-type good seven, so H is not (7,2).
- There is a Fano colouring χ with B_{ℓ_i} = R_{ℓ_i} ∖ Ω_i on the three lines through p₀ = 7. This is the brief's form.
- On the other four lines B_m = R_m ∖ Ω′_m, where Ω′_m consists of the unused points, plus the fixer pair when m = 156.
- Here [Ω′_m] = [unused set], so the brief's extra demand Ω′_m ∈ C is unnecessary. Only B_m ∈ a + C matters, and that holds.

**Construction.**
1. **Unused points.** Delete Z from V′. Z consists of the singleton-class points (at most u of them, by H4′), plus
   u − #singletons further points of g*.
2. **Fixer.** If f = 1, delete also a fixer pair F of two points of g*. The pair F is a weight-2 codeword.

   Call the remainder V″. No class occurs exactly once in V″, and |V″_{g*}| ≥ 7.
3. **Line counts and colour sizes.** Put e_ℓ = Σ_{i : ℓ ∈ T_i} w_i + 2f·𝟙[ℓ ∈ T*], with T* = {124, 235, 346}
   (colour 7, = ANTI(7) ∖ {156}). Put t_ℓ = k − e_ℓ and
   m_p = (Σ_ℓ t_ℓ)/4 − ½ Σ_{ℓ∋p} t_ℓ.
   This is the unique solution of Σ_{p∉ℓ} m_p = t_ℓ.
4. **Colour classes.** Choose disjoint Y_p ⊆ V″ with |Y_p| = m_p and Y_1 ∪ … ∪ Y_7 = V″, as follows. For every class g
   choose π_g ∈ Ham:
   - π_g = 0 if |V″_g| is even;
   - π_g = a line if |V″_g| is odd and g ≠ g* (cycling through the lines);
   - π_{g*} = (m mod 2) + Σ_{g≠g*} π_g.

   Put one point of V″_g into Y_p for each p ∈ π_g. Then fill every Y_p up to m_p with same-class pairs.
5. **The seven sets.** B_ℓ = ∪_{p∉ℓ} Y_p ∪ ∪_{i : ℓ ∈ T_i} Ω_i ∪ (F if ℓ ∈ T*).
   The colouring is χ = p on Y_p, q_i on Ω_i, and 7 on F and on Z.

**Proof.**
- **Integrality.**
  - m_p ∈ ℤ needs Σt ≡ 0 (mod 4) and Σ_{ℓ∋p} t_ℓ even.
  - The first is 7k − 3W − 6f ≡ 3(k − W − 2f) ≡ 0, which holds by the choice of f.
  - The second holds by (H1) and F4.
- **Sizes.** For f = 0, 4m_p takes the values k − W + 2(w₁+w₂), k − W + 2(w₁+w₃), k − W − 2w₁ + 2w₂,
  k − W + 2(w₂+w₃), k − W − 2w₂ + 2w₃, k − W − 2w₃ + 2w₁ and k − W, for p = 1, …, 7.
  - The fixer changes 4m_p by −6 + 4·#{ℓ ∈ T* : p ∈ ℓ} ≥ −6.
  - Hence 4m_p ≥ k − W − 2Δ − 6f, and (H2) gives m_p ≥ c ≥ 1. [formulas checked exactly in `claims.py`, F6–F7]
  - Σ m_p = (7k − 3W − 6f)/4 = |V″|, by the definition of u.
- **Parities (Step 4).**
  - t_ℓ ≡ k − (number of i with ℓ ∈ T_i)·k ≡ 0 (mod 2), because the triple is odd and (H1) holds. So
    (m mod 2) ∈ ker N = Ham, and therefore π_{g*} ∈ Ham.
  - Odd cells other than g* have at least 3 points, which fits weight 3. For g*, wt(π_{g*}) ≤ 7 ≤ |V″_{g*}|, and
    wt(π_{g*}) ≡ |V″_{g*}| because weight is additive mod 2 and Σ m_p = |V″|.
  - Every p receives at most c singles, and m_p ≥ c. The parity of m_p minus the singles is even, since
    Σ_g π_g = m mod 2.
  - After the singles, every cell has an even remainder, and the total remainder equals Σ_p (m_p − load_p). So the pairs
    fill every Y_p exactly.
- **Classes.**
  - By Lemma 2.2, [Y_p] = Σ_g π_g(p)·g, so [∪_{p∉ℓ} Y_p] = Σ_g g·|π_g ∖ ℓ| = 0, because π_g ∈ Ham = ker N.
  - Each line lies in an odd number of T_i, so the Ω's contribute α. F contributes 0.
  - Hence [B_ℓ] = α. Also |B_ℓ| = Σ_{p∉ℓ} m_p + e_ℓ = k, so B_ℓ ∈ H.
- **Good seven.**
  - Every point has pattern ANTI(p), T_i ⊆ ANTI(q_i), T* ⊆ ANTI(7), or ∅. So the seven sets are Fano-type (§1), and
    B_ℓ ⊆ R_ℓ for the colouring χ.
  - Any two points x, y have colours on a common line ℓ, and B_ℓ misses both.
  - The sets are distinct: for p ∈ ℓ′ ∖ ℓ, the nonempty set Y_p lies in B_ℓ but not in B_ℓ′.
  - Finally, on ℓ_i the construction gives B_{ℓ_i} = R_{ℓ_i} ∖ Ω_i. ∎

**General form.** Hypotheses (H2)–(H4′) are used only to produce Z, F and the partition (Y_p) with |Y_p| = m_p and
[R_ℓ ∩ V″] = 0. Any other way to produce them, for example C-words of size ≤ b packed greedily with a single-class
reserve of ≥ 7(b − 1) points, gives the same conclusion. `ystep_ilp.py` searches this space exactly.

**Corollary (Programme regime).** Assume n = (7/4 + δ)k, C has codimension r (so c ≤ 2^r and the largest class has
≥ (n − W)/2^r points), and the Ω's are parity-correct with W ≤ 4n − 7k = 4δk. Then:
- (H2) holds once (1 − 4δ)k ≥ 2Δ + 2^{r+2} + 6;
- (H3) holds once (7/4 − 3δ)k/2^r ≥ δk + 9.

So for δ < min(1/4, 7/(4·2^r + 12)) and k large, only (H4′) is left. It holds automatically when no class occurs exactly
once outside the Ω's, and §4.3 suggests it is not needed when V = ∪H.

## 4. What blocks, exactly

### 4.1 Size parity: the literal Proposition 9 is false [proved by hand; computed exact]
- **The family.** Take V = X ⊔ Y ⊔ {z₁, z₂} with |X|, |Y| ≥ 3, and a + C = {S : |S ∩ X| and |S ∩ Y| both odd}.
  C is "even on X, even on Y, free on {z₁, z₂}". Take k odd.
- **Every member contains exactly one z_j**, since |S ∩ (X ∪ Y)| is even and k is odd. So {z₁, z₂} is a 2-point
  transversal, and H has no good seven at all.
- **But the literal hypothesis holds.** Ω_i = {x_i, y_i} are disjoint members of a + C with W = 6 ≤ 4n − 7k. For
  example |X| = |Y| = 5, n = 12, k = 5 gives 4n − 7k = 13, and V = ∪H.
- SAT confirms there is no good seven of any type (`sat_check.py`, UNSAT).
- **The correct hypothesis is (H1).** Equivalently, the Ω's lie in the parity-k half a′ + C₀. In this example only two
  disjoint parity-correct Ω's exist ({x, y, z_j}).
- In the experiments, all 66 instances where the literal hypothesis held but no Fano-type good seven exists are of this
  type: W_k > 4n − 7k, or there is no disjoint parity-k triple.

### 4.2 Dead points and singleton cells [proved by hand]
- **Example.** Take a parity family on cells of sizes 26 and 17, plus one free point, with k = 24.
  - The free point lies in no member, so V ≠ ∪H.
  - W = 6 ≤ 4n − 7k = 8 when n = 44 is used.
  - On the effective ground set (n = 43), 7ρ₀ = 14 > 3(4·43 − 168) = 12, so Corollary 7 forbids a Fano-type good seven.
- So with n = |V| as stated, something like (H4′) is necessary. This is exactly the case u = 0 with one singleton class.
- With V = ∪H no such failure was observed.

### 4.3 Sizes: (H2) appears unnecessary [computed MILP, positives exact]
- In 284 instances (all parity-correct, V = ∪H, W_k ≤ 4n − 7k), a Fano-type good seven exists in every case. This
  includes the cases where (H2), (H3) or (H4′) fail; most of those are small k with W comparable to k.
- The structured construction alone (triangles, fixer, unused points, anti-pencil Y's, with the Y-step solved exactly)
  succeeds in 130 of them. The C1 rule succeeds in 108.
- **Conjecture [heuristic].** (H0) + (H1) + V = ∪H suffice. Proving it would need more pattern types than the
  triangle/anti-pencil skeleton, for example points with |J(x)| = 2 when W > k.

### 4.4 Not blocking
- **Classes.** Always solvable (§1).
- **"C too small".** C ⊇ ⊕ Even(V_g) by Lemma 2.2, so every deficiency is absorbed by same-class pairs once the cells are
  non-degenerate.
- **The mod-4 residue s ≡ 2.** One same-class pair on a triangle fixes it.

## 5. Computations

The exact verifier `core.verify_seven` checks, by brute force on the sets, that a seven is a good seven:
- membership in H: size k and syndrome α;
- the seven sets are distinct;
- no transversal of size ≤ 2;
- the pencil (Fano-type) condition.

Every positive result below passed it.

| Suite | Instances | Literal hyp. | Of which no seven | (H0)+(H1) | Good seven exists | Verifier failures |
|---|---|---|---|---|---|---|
| FKW + 1 point (n = 7m + 2, k = 4m, m = 2..10) | 9 | 9 | 0 | 9 | 9 | 0 |
| q-cell parity families (q = 2..4, cells 2–7, 0–3 free points) | 536 | 221 | 62 | 159 | 159 | 0 |
| random codes (codimension 1–4, n = 9–20) | 109 | 90 | 1 | 88 | 88 | 0 |
| large (parity q ≤ 5 with cells up to 30; random codes n = 30–80, r = 2–4) | 48 | 31 | 3 | 28 | 28 | 0 |
| **All** | **702** | **351** | **66 (all of type §4.1)** | **284** | **284** | **0** |

- **Instances.** Each instance is a family with H ≠ ∅ and V = ∪H (dead points deleted), and k with 0 ≤ 4n − 7k ≤ 24.
- **Columns.**
  - "Literal hyp." means that some disjoint triple in a + C, of any parity, has W ≤ 4n − 7k.
  - "(H0)+(H1)" means the same with every Ω_i of parity k.
  - "Good seven exists" is ground truth from the count ILP. Every positive answer was turned into explicit sets and passed
    the exact verifier.
- **No-seven cases.** 59 of the 66 have n ≤ 20, and SAT confirms them for both Fano-type and arbitrary good sevens
  [computed exact]. The other 7 are [computed MILP].
- **Construction coverage on the 284 parity-correct instances.** The proof's C1 rule succeeds on 108. The skeleton with
  the exact Y-step succeeds on 130. The failures are (H2) for small k, or singleton cells; ground truth is positive in
  every case. Raw data: `logs/*.jsonl`, `logs/summary.txt`.

- **FKW at n = 7m + 2.** The proof construction (C1 rule, brief form) succeeds for every m = 2..10. Here W = 6,
  s = 2 and f = 1, so the parity-family case needs the fixer pair [computed exact].
- **Theorem stress test (`check_theorem.py`).** 10,300 instances: random parity families, random codes, and codes with
  few, unequal cells, with n ≤ 120, codimension ≤ 5 (+1 after evenising), and random parity-correct Ω's.
  - In every instance (H0)–(H4′) held, and the literal proof construction (no search) produced seven sets that passed
    the exact verifier: 10,300 / 10,300 [computed exact per instance].
  - Seeds: 1 (300 instances) and 2–5 (2,500 each). Logs: `logs/check_theorem_*.log`, summarised in `logs/summary.txt`.
- **Status of the "no seven" claims.** These are HiGHS-infeasible [computed MILP]. For n ≤ 20 they were cross-checked by
  SAT (CaDiCaL) for both Fano-type and arbitrary good sevens [computed exact].

## 6. Files (`compute/programme2/task3/`)
- `core.py`: coset families, cells, Fano data, the exact verifier.
- `claims.py`: exhaustive checks F1–F7 of the Fano facts and size formulas used in §1 and §3.
- `proof_mode.py`, `check_theorem.py`: Theorem 9′ implemented literally, and its stress test.
- `construct.py`: the same skeleton with a small search over triples, fixers and parity vectors (C1 rule).
- `ystep_ilp.py`: the same skeleton, with the Y-step solved exactly.
- `ilp.py`: the exact count-ILP ground truth (§2), and min-W disjoint triples.
- `sat_check.py`: SAT ground truth on sets, for both Fano-type and arbitrary good sevens.
- `run.py`, `summarize.py`, `logs/`: the experiment suites and their raw JSON lines.
