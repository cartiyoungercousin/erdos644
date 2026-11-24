# Independent verification: Theorem PS3 and the "limit of window-and-seal" (PETAL 28), and the corrected step of 27.2

Verifier's note. Re-derived from the statements and cited definitions (PETAL 1-2, 12, 26.2, 27.2, 28.1-28.3). New code, nothing from `compute/petal5`:
`compute/verify/ps3_lp.py` (Part A: LP of the method with the all-singles adversary over 256 assignments; Part B: LP over the exact adversary set for PS3),
`ps3_check.py` (finite-k replay of PS3), plus my earlier `ps2_lp.py` (the 94-vertex polytope) and `ps_check.py` (model, adversaries, literal 2-cover test).
Logs: `compute/verify/logs/ps3_lpA.log`, `ps3_lpB.log`, `ps3_check_main.log`, `ps3_check_main2.log`, `ps3_check_ctrl.log`. Not committed.

## Verdicts

| Item | Verdict |
|---|---|
| Theorem PS3, pooled 𝒜 loses for δ < t/2 - 1/6 (all t >= 3/4; all δ < 1 - t for t >= 7/9) | **PASS** (hand check; vertex LP over the exact adversary set; about 31,000 finite-k games, 0 covers, 0 overruns; threshold sharp) |
| Limit claim: δ* = t/2 - 1/6 is the limit of the window-and-seal method | **CONFIRMED within the stated model** (independent LP, t = 0.75 ... 0.80); the claim is about that method only (see "scope") |
| Corrected step in 27.2 (fixed S-choice (S_1 = petal a in {1,2,3}, S_2 = petal 4); B-load max = 2δ) | **PASS** (my earlier PS2 LP already had a fixed; max f_a = 2δ for each a, each of the 93 nonzero vertices) |

Minor remarks (no gap): M1 the shrink of W_4 must come out of Σ_0 and this couples T_3 to petal 4's leak (not written in 28.2; the LP in 28.1 must include it, and mine does), M2 F_2, F_3 do not seal earlier R_Y parts any more (3δ > t/2 here) so R_Y leaks may be shared like pool points; the proof is unaffected, M3 the model scope of the limit claim.

## 1. Hand check of PS3 (28.2)

n = 1 + t/2 - δ, hit = t/2 + ε in both arenas, p = 1 - t - δ, σ = t/2 - p = 3t/2 - 1 + δ.
- Windows: W_1, W_2 private, W_3 = P ∪ Σ_0, W_4 = P' ∪ Σ_0, |W_i| = t/2 each, |P| = |P'| = p. Check t + 2p + σ = n: t + p + t/2 = 1 + t/2 - δ. Correct, and ∪W = R_X, so no point of R_X lies in all four petals.
- Petals: F_i ⊂ R_Y of size t/2 + ε forces class X; |R_X ∖ W_i| = n - t/2 = 1 - δ, so P_i ∩ R_X = R_X ∖ W_i exactly and leak_i = δ for i <= 3 (the adversary has no freedom here). Triple cells: T_1 = W_1, T_2 = W_2 (t/2 each), T_3 ∩ R_X = W_3 ∖ W_4 = P, T_4 ∩ R_X = P' (before the shrink of M1). Correct.
- Request 4: F_4 ⊇ common R_Y points of petals 1-3 (<= s <= δ <= t/2), plus the pool common points J (mass s_O), plus W_4 shrunk by s = s_Y + s_O. Size t/2 + ε + s_O + (t/2 - s) = t + ε - s_Y <= t. R_Y common points need only be sealed from the triple intersection, not from each earlier part: that is what makes 3δ > t/2 harmless here. Correct.
  M1: the s removed points must come from Σ_0 (they are in W_3, so absent from P_3, hence not common to all four petals). Removing them from P' would leave R_X points in all four petals. After the removal petal 4 may contain them: R_X ∖ W_4 has mass 1 - δ + s, so petal 4's leak is ℓ_4 >= δ - s, and T_3 ∩ R_X = p + (δ - ℓ_4) <= p + s. So cell T_3 grows exactly when petal 4 leaks less. 28.2 says "covered by the LP" but does not state this coupling; it must be in the LP (mine has it: Part B).
- Centres, assignment (petal 1 D; 2 S5; 3 S6; 4 S7): G_5 = t/2 (⊇ T_2). G_6 ⊇ Z_5 ∪ T_3: δ + p + (δ - ℓ_4); G_7 ⊇ Z_5 ∪ Z_6 ∪ T_4: 2δ + p = 1 - t + δ. P2: every S-single's neighbourhood is its triple cell sealed in the same request (R_X part via G_j, B part via the pattern rule), every other point lies in at most one centre. Same case list as 27.2, re-derived, correct.
- All-singles arithmetic: costs t/2 + δ + l_5, t/2 + δ + l_6 (G_6 = t/2 since δ + p = 1 - t <= t/2), 1 - t + 2δ + l_7; with l_5 + l_6 + l_7 = 2δ, l_j <= δ the balanced value is L = (1 + 6δ)/3 with l_7 = t - 2/3, l_5 = l_6 = 1/3 + δ - t/2 in [0, δ] (needs δ >= t/2 - 1/3; below that PS2 applies). L <= t iff δ <= t/2 - 1/6. Re-derived, correct. The binding conditions at δ near 1 - t: p >= 0 (δ <= 1 - t), σ >= 0 and G_6 <= t/2 are all fine for t >= 2/3.

## 2. LP re-derivations (`ps3_lp.py`)

**Part B (PS3 for general leaks).** Exact adversary set Q (δ = 1): types J ⊂ {1,2,3,4} (14), Σ_{J ∋ i} m_J = 1 for i = 1,2,3 (equalities, as forced above), ℓ_4 = Σ_{J ∋ 4} m_J <= 1 and ℓ_4 + m_{123} >= 1 (s = m_{123}).
Q has **42 vertices** (exact Fractions). The cost of a structure is the optimum of an LP with the structure only on the right-hand side (G_6 = max(t/2, δ + p + (δ - ℓ_4)) is a convex piecewise-linear function of the parameters), hence convex, so the maximum is at a vertex; I solved all 42.
The patterns: single of petal 2/3/4 may have P = {5}/{6}/{7}; types {1,3,4}, {1,2,4}, {1,2,3} must have 5, 6, 7 resp. in P with |P| >= 2; all other points |P| >= 2. Result (bisection on δ):

| t | δ at which max_v cost = t | t/2 - 1/6 | worst vertex |
|---|---|---|---|
| 0.75 | 0.20833 | 0.20833 | singles of petal 1 (mass δ) and pool pairs {2,3},{2,4},{3,4} of mass δ/2 each |
| 0.76 | 0.21333 | 0.21333 | same |
| 0.77 | 0.21833 | 0.21833 | same |
| 0.775 | 0.22083 | 0.22083 | singles of 1 and 4, pair {2,3} |
| 0.78 | max cost <= t up to 1 - t = 0.22 | 0.22333 > 1 - t | - |

Grid check: at t = 0.75, 0.78, 0.80 no violation at 40 values of δ in (0, min(δ*, 1 - t)]. As a cross-check I also ran the 94-vertex polytope of 27.2/28.1 (my enumeration, budgets <= δ, 93 nonzero + zero): the same crossing values (cost 0.75000 at δ* - 10^-6, 0.756 at δ* + 0.003 for t = 0.75; 0.77000 / 0.776 for t = 0.77). So PS3 holds exactly to t/2 - 1/6 for every leak structure, W_4 adapting only to s (information available before request 4).
Interesting: the worst structure is not all singles (the all-singles plan has the same value (1 + 6δ)/3, but pair types make no difference there either).

**Part A (limit of the method).** Model (28.1): atoms μ_M of R_X (M = petals missing the atom), |W_a| = Σ_{M ∋ a} μ_M <= t/2, T_a ∩ R_X = μ_{{a}}, Σ μ = n; each petal D (singles requested in two of the three requests, load split with <= δ per request) or S_j (singles once in j with T_a);
G_j >= t/2, G_j >= (j - 5)δ + Σ_{S_j} μ_{{a}}; value = min over atoms and over all 256 assignments of max_j(G_j + load_j); adversary: all singles.
Result (`logs/ps3_lpA.log`): the bisection crossing equals t/2 - 1/6 for t = 0.75, 0.76, 0.77, 0.775 (0.20833, 0.21333, 0.21833, 0.22083) and equals 1 - t for t = 0.78, 0.79, 0.80; the optimal assignment is (D, S5, S6, S7) in all cases; the value for t = 0.75 is exactly (1 + 6δ)/3 for δ = 0.18, 0.20, 0.2083, 0.21, 0.23 (T = 0.75: 0.69333, 0.73333, 0.74993, 0.75333, 0.79333). Independent of the author's LP. Combined with Part B this closes the loop: the upper bound (best the method can do against all-singles) and the lower bound (PS3 against all structures) coincide at t/2 - 1/6.
Mechanism (my reading): sum of the three request costs is forced to be 1 + 6δ (windows total, 2δ trace seal, one triple cell p, singles once or twice) against 3t.

**Scope of the limit claim (M3).** It is a statement about the model: forced class-X petals with windows <= t/2, forced class-Y centres with G_j >= t/2 and trace sealing of (j - 5)δ inside G_j, patterns of the PS2 type, one D petal etc. Not in the model (so the claim does not say these fail): petals of both classes, more than 7 replies with re-selection, releasing the trace seals adaptively (28.3 calls it useless, heuristic), a P2 refinement that seals only edges with an endpoint in two traces, windows with a different request shape. I did not try to extend the model; the claim "no improvement inside the model" is verified, the claim "open range is hard" is not a theorem.

## 3. Finite k (`ps3_check.py`)

Requester: 28.2 verbatim in integers (hit numbers (h_X, h_Y), h_X + h_Y = T + 1, w = T - h_Y, p = n_X - 3w, σ = w - p, F_4 ⊇ common R_Y points, W_4 = P' ∪ (Σ_0 minus s), cells and patterns on the actual replies, patterns by an integer program, G sizes as above).
Checks: request <= T, reply in H, petal/centre classes, empty petal intersection, structure facts (P_i ∩ R_X = R_X ∖ W_i, i <= 3), literal all-pairs 2-cover test.
Adversaries: structured (all 42 vertices of Q scaled to integers; pool groups for multi-types; singles in R_Y or pool; petal 4's R_X part chosen adversarially: prefer the removed Σ_0 points, avoid them, or random; centres by priority genomes with the extremal hand-made ones) and generic genome adversaries with hill climbing.
Main runs (`ps3_check.py 31 3`, `41 20`; both orders of the hit numbers; free and pool variants): (k,T,d) = (40,30,8), (80,60,16), (120,90,24), (100,78,21), (80,62,17), (60,45,12), (100,80,19), (50,40,9), (80,60,12): about 31,000 games, **0 covers, 0 requests above T, 0 planned overruns, 0 no-reply, 0 structure flags**; largest request = T in every row.
Controls (`ps3_check.py 32 3 ctrl`, δ above the limit): (40,30,9), (80,60,17), (80,60,18), (100,78,24), and (20,15,4) (the notes' k = 20, d = 4 case): the integer plan overruns T in 45-107 of 332 games each (the adversaries that reach the structure; the limit is sharp), as in 28.2. (100,80,22) has d >= (1 - t)k and is outside the family's range (parameter check fails).
The row (100,80,19) is inside the range (δ = 0.19 < 1 - t = 0.20) and passes.

## 4. The 27.2 correction

27.2 now fixes the S-choice before taking the vertex maximum. My PS2 verification (`ps2_lp.py`) computed f_a(vertex) for a = 1, 2, 3 separately with S-petals (a, 4): max over the 93 nonzero vertices = 2δ for each a, and the exhaustive integer check (987 structures at d = 2, 51 at d = 1) gave 2d. The repaired argument is valid (per fixed a, f_a is convex in the leak masses). In PS2 (`ps2_check.py`) the requester takes the best a on the actual structure, which can only help. No issue.

No counterexample to PS3, and no gap in the limit claim inside its model.
