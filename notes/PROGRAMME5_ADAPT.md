# Programme 5: adaptive finishing against Theorem O, and the depth-3 spectrum game — CAPPED AT 6/7

Tags: [proved by hand] / [computed exact] / [computed, grid] / [heuristic] / [open]. Units of k, t = T/k = 3/4 + ε,
ν = n/k. Code and logs: `compute/programme5/adapt/` (`logs/`; `logs/old_buggy/` = superseded runs, see §2.2), `py -3.14`,
≤ 6 cores. Nothing committed; LEDGER, Lean644/, notes/sources/ untouched. Nothing here is independently verified.

## 0. Verdicts
- **Q1. YES** [proved by hand; computed on sets]. The manuscript's Theorem 5.2 path (M ≤ h branch, Lemma 4.8) beats
  the Theorem O two-cluster adversary for every t ≥ 9/11 + o(1): 3 adaptive rounds from the glue pair, 4 anchors and
  an adaptive 5th answer. Mechanism §1.2.
- **Q2. CAPPED AT 6/7, i.e. ε* = 3/28** [computed, grid G = 168]. The depth-≤3 spectrum game, with all our lemmas
  plus the manuscript's, has value 3/28 for every ν ≥ 3 (so ν → ∞), and ≥ .105 already for ν ≥ 2.375.
  - Adversary: spectrum S* = [0, .268] ∪ [5/14, .435] ∪ [10/21, 1). The cascade never starts.
  - Below 6/7 only for ν ≤ 2.25 (ε* ∈ (.100, .1025) there, .0677 at ν = 2). This is range-limited, so useless for
    (G) by padding. Table §2.2.
- **Q3.** Lemmas 2.5, 2.6, Prop 5.1, Thm 5.2, Prop 5.3 and the §7 assembly are [checked by hand]; **no gap found**.
- **Reviewer's Fano repair.** Proof correct (one fix to its sufficient condition); it does not beat the two-cluster
  adversary, whose best response creates Θ(k) common omission cores (§2B).

## 1. Q1 — the manuscript's adaptive machinery against Theorem O
### 1.1 The run [proved by hand]
Theorem O adversary: clusters R1, R2, |R_i| = s = ⌈(2−c)k⌉, c ∈ (1/2, 1 − t/2); answers in one cluster plus one glue
point per earlier other-cluster answer. Its spectrum is {1..2m} ∪ [ck−2m, k], so the **dichotomy with threshold 2m**
holds for free. That is the hypothesis of Theorem 5.2, branch M ≤ h:
- **R1.** T points of E. G must join the other cluster (s − T < k), so |E∩G| = 1 =: M.
- **R2.** Balanced request (Lemma 2.5) → F. Say F joins E's cluster: x = |E∩F| ∈ [ck−2m, k − ⌊(T+1)/2⌋] > k/2.
- **R3.** X∪Y∪Z + private points of G → H. H must join G's cluster (s − x < k): b = |G∩H| ∈ [ck−2m, k−T+x] > k/2.
  Now there are four anchors, all triple intersections are empty, there are two heavy opposite cells X, B and four
  glue cells of size ≤ 2m.
- **R4 (Lemma 4.8).** I avoids all glue + ≈ k/2 of B + ≈ T − k/2 of X. Its trace on G is ≤ k/2, hence ≤ 2m.
- **R5.** X ∪ B1 (B1 ⊇ B∩I) and (X∩I) ∪ (B∖B1). The seven have no 2-point transversal.
- **Condition.** 3T ≥ 2x + b + ⌈k/2⌉ + 2m. His best is x = (1−t/2)k, b = (2−3t/2)k, so the route works iff
  **t ≥ 9/11**. At t = 7/8 it holds for every c ∈ (1/2, 9/16].
- **Comparison.** The best static four-anchor layout I found after R3 (triangle labels on X×B) needs 2(x+b)/3 ≤ t,
  i.e. 6/7. Theorem O's three-anchor static finishes need (c+3)/4.
- **Sets** [computed exact] (`q1_two_cluster.py`: every adversary branch, brute-force 2-transversal check).
  - k = 160 (t = .875; c = .51, .5625) and k = 400 (t = 6/7, .83, .82): all leaves are bad sevens with all
    requests ≤ T.
  - t = .80: a request of 359 > T = 320 points is needed, as 9/11 predicts.
### 1.2 Mechanism (the "new ingredient")
Static finishes must put the glue products Y×Y′, Z×Z′ into blocks that also carry heavy cells. Glue is o(k) but not
empty, which is Theorem O's (c+3)/4. The adaptive finish spends ONE request on all the glue: the 5th answer I avoids
it, so every candidate pair must meet I. I's far-cluster traces are forced ≤ k/2, and the dichotomy makes them o(k).
The live pairs are then (X∩I)×B and X×(B∩I), and two requests chosen after seeing I cover them (B1 ⊇ B∩I).
This needs a 4th anchor and a gap in the spectrum. Theorem O's adversary supplies the gap.

## 2. Q2 — the depth-≤3 spectrum game (S-game)
### 2.1 Definition [soundness proved by hand]
- **Information.** The adversary commits to the set S ⊆ [0,1) of normalised pair-intersection sizes of his family.
  - Every answer meets every earlier member in a size from S.
  - She may start from any pair q ∈ S (it exists in the family).
  - Gap(ℓ,u) means S ∩ (ℓ,u] = ∅; the dichotomy (m) means S ∩ (m,1/2] = ∅.
  - This is exactly the manuscript's information. In this model its proof has depth ≤ 3 per closure; a literal request
    game without S would need unboundedly many restarts ("creeping M").
- **Moves from a pair**: ≤ 3 adaptive requests, then one static batch; ≤ 7 kept, discards allowed.
  - (D) DUMP(h1,h2) and START(u) exactly as in BEAT78 §1.3: answers y ≤ h1, z ≤ h2, y + z ≥ h1 + h2 − ρ with
    ρ = ν − 1 − t, y, z ∈ S. This covers the pencil bound and the two-stage dump.
  - (a) static finish of the triple: t*_+ over all 715 classes (P1, HUB, Hall, symmetric).
  - (b) one adaptive request + static: Lemmas 4.1–4.7 normalised. 4.4–4.6 take ℓ = max S∩[0,u] for every u; 4.7
    takes m = max S∩[0,1/2].
  - (c) heavy route (Thm 5.2 generalised to any triple with a cell > 1/2): X∪Y∪Z + rest of P_C → H.
    - If b ≤ 1/2, (A,C,H) or (B,C,H) must close by (a)/(b).
    - If b > 1/2, Lemma 4.8 with exact normalised conditions.
- **Fixed point.** q leaves S when some DUMP leaves only closing answers. Iterate to the greatest fixed point S*. She
  wins iff S* misses a START window.
- **Soundness.** A win is an asymptotic theorem, since each move is a lemma valid in any family with spectrum S. An
  adversary win caps only these tools.
- **ν, grid.** ν enters only through ρ, and every constraint is vacuous for ν ≥ 3, so the value is constant there.
  Sizes are on (1/G)Z, with t*_+ tabulated on the same grid (`grid_t3.py`; G = 168: 208 335 triples).
### 2.2 Results [computed, grid]
| ν | 2 | 2.25 | 2.375 | 2.5 | ≥ 3 (= ∞) |
|---|---|---|---|---|---|
| G = 168 | — | ADV .850, REQ .8525 ⇒ ε* ∈ (.100, .1025) | ADV at .855 | ADV at .855 | ADV .8570, REQ .8572 ⇒ ε* ∈ (.1070, .1072) ∋ 3/28 |
| G = 96 | ε* ∈ [.0675, .0679] | [.1041, .1044] | — | [.1041, .1044] | [.1041, .1044] |
- **ν = ∞ at G = 168.** The adversary survives at t = 0.8570 = 6/7 − 1.4·10⁻⁴; the requester wins at 0.8572.
  By monotonicity ε*(2.375), ε*(2.5) ∈ [.105, .1072]. At ν = 2.25 the room constraint kills the critical window.
- **G = 96 at ν ≥ 2.25** stops ≈ .003 below 3/28. This is a grid artefact: the critical window (t/2, 3 − 3t) below
  contains no point of (1/96)Z for t > .854, but contains 72/168 at t = .8570.
- **ν = 2** equals BEAT78 Game P (.0677), the P1/pencil-bound slope: spectrum information adds nothing there.
- **Bug fixed.** A first version let the adversary use infeasible answers (y + z > 1). The runs in `logs/old_buggy`
  are superseded; at ν = ∞ the fixed runs give identical S* and thresholds.
### 2.3 The adversary below 6/7 [computed, grid; mechanism proved by hand at the point]
- S* (G = 168, t ∈ [.855, .857], ν ≥ 2.5) = [0, .268] ∪ [5/14, .435] ∪ [10/21, 1). It meets every START window.
- **Critical pairs** q ∈ (t/2, 3 − 3t), non-empty iff t < 6/7.
  - Every DUMP leaves Y + Z = 2 − t − q > 2(t − 1/2), so he answers (y, z) = (medium ≥ 5/14, 0⁺).
  - The triple (q, 5/14⁺, 0⁺) fails statically: t*(3/7, 5/14, 0⁺) = 6/7 exactly, rising like 1/2 + y.
  - It fails 4.1–4.3, which need y ≤ t − 1/2.
  - It fails 4.4–4.7, since S* has every medium size and all of (1/2,1), so no gap exists.
  - By hand: the split closure (request X∪Y∪Z + private) has total load 2x + 2y + a + b = 3t exactly at
    (3/7, 5/14, 0⁺), t = 6/7.
- **No cascade.** Without stage 1 there is no Gap(t/2, β), so stages 2–3 and the finishing theorem never fire (above 6/7 it runs in 7 iterations).
- So the manuscript's three 6/7 constraints, our exact static optimum (all classes, P1, HUB) and the heavy route all
  meet at 6/7. At ν ≥ 2.5 our light-configuration lemmas add nothing.
### 2.4 Beyond the lemma list: general one-request closures [heuristic]
- `depth1.py`: any request; any answer with traces in S*; exact 3-block MILP finish (Lemma 2.4 pairs) or discard + t*.
- The random/greedy spoiler is too weak. Its "closure" of (.073, .510, .281) was refuted by the exhaustive check
  `verify_closure.py` (value .854 > t = .852).
- The two heuristic candidates for critical answers of q = 41/96, (.427, .229, .365) and (.427, .219, .365), are both
  refuted exhaustively (value .878 > .852), by K taking all of X.
- No general one-request closure of a critical answer is confirmed.
### 2.5 What is still missing [open]
A depth-≥2 adaptive closure of (q, y, 0⁺), q ∈ (t/2, 3−3t), y ∈ (t − 1/2, 2 − t − q], with no gap information, or
information beyond the spectrum (CORE §29: one family across all branches). Either would start the cascade below 6/7.

## 2B. External "weighted Fano repair" (reviewer), tested
- **(i) Proof** [checked by hand].
  - If y ∈ Y is omitted at both earlier points of a line, it lies in R_{i_λ} ⊆ K_{i_λ}. So O_y contains no line,
    I_y meets every line, and I_y contains a line (a Fano blocking set contains a line). Also I_x ⊇ λ on X_λ.
  - Each pair is a line's "earlier pair" with probability 1/3, so E Q = G/3. Uniform caps give η ≤ 4εk/7.
  - **Fix.** Q ≤ 7T − 3m is only the summed condition. Since x_λ = (Σ_{i∈λ} ℓ_i − m)/2 (AᵀA = 2I + J), one needs
    ℓ_i ≤ T − q_i, Σℓ = 3m and line sums ≥ m. A sufficient form is Q ≤ 4T − 3k plus q(λ) ≤ 2T − k − 3(4T − 3k − Q)/7
    on every line. This is harmless when q = O(εk), false if q is concentrated.
  - The caps must hold for every history: a pool-type input that no request supplies.
- **(ii) Two clusters: overlaps are NOT forced small** [first-order hand argument; computed on sets].
  - Her Y-requests (R_i) come only at the last point of each line, after the omissions. A cluster-j reply misses only
    (1−c)k of R_j, so he puts the omission on Y∩R_j∖S_i, and same-cluster replies share a Θ(k) omission core.
  - Keeping all seven out of cluster j needs |S_i∩R_j| > (1−c)k every round, hence |Y∩R_j| < (4c−1)k/3. The other
    cluster then carries ≳ 0.58k of Y (t = 7/8, c = 9/16).
  - `fano_repair.py` (k = 160, t = 7/8, c = 9/16; pools Y ⊆ R1, ⊆ R2, split 1:1, 1:3, 3:1; 151 orders incl. oval
    first): Q ≥ 120 > slack 7T − 3m = 80; requests reach 248–289 > T = 140.
- **(iii) Depth.** It batches into depth 3 (an oval, two points of the remaining line, its third point). But it needs
  omission caps, not a spectrum, so it is not an S-game move. The S* above violates every cap too.

## 3. Q3 — manuscript parts not in Lean [all checked by hand, exact integers]
- **Lemma 2.5.** ⌈(T−M)/2⌉ ≤ k − M ⇔ T + M ≤ 2k (+1 if odd); M + ⌊(T−M)/2⌋ = ⌊(T+M)/2⌋.
- **Lemma 2.6.** The union minus the u + v kept points has 2k − q − (2k−T−q) = T points. u = k never occurs
  (caps β, γ < k/2).
- **Prop 5.1.**
  - Case 1: z > γ ⇒ y + z ≥ 2T − k + 1 > 3T − 2k.
  - Case 2: both sub-cases of M + y − z < k − T/2 and S ≤ 3T/2.
  - Case 3: g = ⌈k/2⌉ − z ≤ y from y + z ≥ ⌊k/2⌋ + 1; first request 2⌈k/2⌉ − z ≤ T from z ≥ h+1.
  - Case 4: all conditions of 4.7 in the variables (M, z, y), each reducing to T ≥ 5k/6 or 7T ≥ 6k.
- **Thm 5.2.**
  - M ≥ h+1: ⌊(T+M)/2⌋ ≥ ⌈k/2⌉.
  - M ≤ h: x + 2M ≤ k/2 + 2h + 1/2 ≤ T. Lemma 4.8's three conditions need k ≥ 6h+1, 4h+1, 6h+2 (⇔ h + s ≥ 2).
  - The discard branch keeps E, G, H + 4 edges.
- **Prop 5.3 (rank 7).**
  - Case 1: E1, E2 disjoint, and G meets each in 0 or 4 points (not both 4). The candidate pairs are Q × E2, covered
    by Q ∪ S_i with sizes 6, 6, 6, 5.
  - Case 2: |G∩E| ≤ 1 and |G∩F| ∈ {0,1,4}; Cor 3.2 holds with a = 1, b + c ≤ 2 ≤ 3T − 2k = 4.
  - In the 4-branch: |D| = 6; H ≠ A, B, C; |H∩A|, |H∩B| ≤ 1; η ∈ {0,1,4,5}.
  - The candidate-pair list is complete: a pair avoiding X is A′×B′, forcing u = y and v ∈ H∩B′∖{b*}.
  - All six request schemes have sizes ≤ 6 (6/6, 6/6/4, 6/6/6; ≤5/≤2, 6/6/≤2, 6/6/6), cover their pairs, and keep
    ≤ 7 edges.
- **§7.** (α, ⌊k/2⌋] is covered by 6.2, or by 6.2 + 6.3 + 6.4. T = k − h = ⌈6k/7⌉ for s = 0..6. Padding is fine.
- **No gap found.** Lemmas 2.1–4.8 are in Lean; Lemma 6.1 and Props 6.2–6.4 are audited by `audit_cases.py`.

## 4. Files (`compute/programme5/adapt/`)
- `q1_two_cluster.py k t c`, `grid_t3.py G NPROC`, `sgame.py G nu t [v]`, `scan_nu.py G nu lo hi steps`, `survivors.py`,
  `critical.py`, `depth1.py`, `verify_closure.py`, `fano_repair.py k t c Y`.
