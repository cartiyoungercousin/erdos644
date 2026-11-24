# Independent verification: Theorem PS2 (PETAL 27.2), pooled 𝒜, δ < t/4

Verifier's note. Re-derived from the statement and the cited definitions (PETAL 1-2, 12, 23, 26.2, 27.2). New code, nothing from `compute/petal5`:
`compute/verify/ps2_lp.py` (LP re-derivation: vertices, patterns, integer exhaustive), `ps2_check.py` (finite-k replay, structured and generic adversaries),
`ps_check.py` (my own model from the PS verification). Logs: `compute/verify/logs/ps2_lp.log`, `ps2_check_main.log`, `ps2_check_ctrl.log`. Not committed.

## Verdict

| Item | Verdict |
|---|---|
| Theorem PS2, δ < t/4 (all t >= 3/4) | **PASS** (hand check of every step; B-load LP re-derived independently; ~17,000 finite-k games: 0 covers, 0 budget overruns, 0 structure flags; threshold sharp) |
| "93 extreme leak structures are all of them" | **CONFIRMED** (94 vertices incl. zero, 93 nonzero, enumerated exactly) |
| B-load <= 2δ | **CONFIRMED** (every vertex, every S-petal a; plus exhaustive integer check d = 1, 2) |

Minor remarks (no gap): M1 the convexity sentence, M2 integer boundary δ = t/4 needs the right choice of X, M3 k = 16 overrun is rounding only, M4 one-line justification for singles-in-pairs.

## 1. Hand check, step by step

Setting as in 27.2: classes by ">= 1 - δ in R_c", n = 1 + t/2 - δ, τ_X = τ_Y = t/2, hit_c = τ + ε points of R_c block class c.

**Petals.** Request i = F_i ∪ W_i. |F_i| > τ_Y so class Y is dead and every reply is class X (existence by τ(H) > t). For i <= 3: |R_X ∖ W_i| = n - (t/2 - ε) = 1 - δ + ε, and a class-X reply needs >= 1 - δ there, so
P_i ∩ R_X = R_X ∖ W_i up to ε, and its B-part (= P_i ∖ R_X) has mass δ. (In integers: |F| = hit_Y, |W_i| = T - hit_Y gives |R_X ∖ W_i| = k - d exactly, checked by the harness.)
R_Y-parts disjoint because F_i contains the earlier ones. Common intersection: on R_X, ∩_{i<=3} (R_X ∖ W_i) = W_4 and petal 4 avoids W_4; on R_Y the parts are disjoint; pool points common to P_1..P_3 are in request 4. So empty. Correct.
Budgets: requests 1-3: max(t/2+ε, (i-1)δ) + t/2 - ε = t needs 2δ <= t/2, i.e. δ <= t/4 (this is already one source of the t/4 limit). Request 4: w = n - 3(t/2-ε) = 1 - t - δ + 3ε; with s the common pool mass,
max(t/2 + s, 3δ - 2s) + w <= max(1 - t/2, 1 - t + 2δ) <= t iff t >= 2/3 and δ <= t - 1/2. Re-derived, correct. (Finite k: w_4 = k - d + 2 - 2h_X; request 4 = max(h_Y, 3d - 3s) + s + w_4; e.g. (80,60,14): 42 + 8 = 50.)
Triple cells: T_a ∩ R_X ⊂ W_a (a <= 3), T_4 ∩ R_X = W_4. Correct (harness asserts both).
Also: R_X points of U have types of size >= 2 (no R_X point lies in a single petal since W_1 ∩ W_2 ∩ W_3 = ∅), so they never need single-sealing. Not stated in the text but true.

**Centres and P2.** G_j ⊂ R_X of size >= hit_X + ε kills class X, so the reply is class Y; its R_X-trace on U is <= δ. G_5 ⊇ T_a ∩ R_X (<= t/2 - ε), G_6 ⊇ (T_4 ∩ R_X) ∪ Z_5: δ + w = 1 - t <= t/2, G_7 ⊇ Z_5 ∪ Z_6: 2δ <= t/2. Correct.
Every R_X point of U lies in at most one centre (sealed). Every B point with |P| >= 2 lies in at most one centre. An edge {x, y} (J_x ∪ J_y = [4], no point in all four) with both endpoints of these kinds meets at most two centres, so the third misses both.
The only other endpoints are the allowed single-sealed points: a single x of S-petal a with P = {5} (or a single of petal 4 with P = {6}). Its neighbours are exactly the points of type [4] ∖ {a} (resp. [4] ∖ {4}), because two types with union [4] and x of type {a} force J_y ⊇ [4] ∖ {a} and J_y ≠ [4]. All of T_a is in request 5: the R_X part by G_5 ⊇ T_a ∩ R_X, the B part by the rule 5 ∈ P (resp. 6 ∈ P for petal 4, G_6 ⊇ T_4 ∩ R_X). So centre 5 (resp. 6) contains neither x nor y. Singles of different petals are never adjacent. I re-derived the case list and found no missing case (edges between two single-sealed points: different petals, not adjacent; same petal: not adjacent).

**B-load.** Request j costs |G_j| + B-load_j and |G_j| = hit_X (the three size conditions above hold), so everything rests on B-load <= 2δ.
M1 (wording, harmless): 27.2 says "the least max load, minimised over the S-choice, is a convex function of the masses ... so its maximum sits at a vertex". A minimum of convex functions is not convex, so the sentence is not valid as written. It does not matter:
for each fixed a the value f_a is a convex piecewise linear function (an LP value as a function of the right-hand side), its maximum over the leak polytope is at a vertex, and I computed f_a at every vertex for a = 1, 2, 3 separately: max f_a = 2δ for each a. So any a works and the bilevel issue never arises. (Hand reason: with singles of a on request 5, singles of 4 on request 6, T_a pairs through 5, T_4 pairs through 6, everything else in pairs, the loads are bounded by
max((s_a + s_4 + 2Q)/3, s_a + F_a, s_4 + F_4), and s_a + s_4 + 2Q <= 4δ + σ_b + σ_c <= 6δ, s_a + F_a <= 2δ because T_a does not use petal a's budget, s_4 + F_4 <= 2δ likewise.)

## 2. The 93 structures and the LP, re-derived (`ps2_lp.py`, `logs/ps2_lp.log`)

Types: the 14 nonempty proper subsets J of {1,2,3,4}. Leak polytope Pol = {m >= 0 : Σ_{J ∋ i} m_J <= δ for i = 1..4}, with δ = 1. R_Y points are singles (disjoint R_Y parts), multi-types are pool points; the pattern rules
do not distinguish R_Y from pool, so one polytope covers both. Exact enumeration (Fractions, all 14-subsets of the 18 constraints): **94 vertices, of which 93 nonzero** (the number in the text).
Pattern LP for S-petal a: a point of type J gets a nonempty P ⊆ {5,6,7}: single of a may have {5}, single of 4 may have {6}, every other point |P| >= 2, with 5 ∈ P for T_a and 6 ∈ P for T_4 (types [4] ∖ {a} and {1,2,3}).
Results: max over the 93 vertices of f_a = 2 for each a ∈ {1,2,3}; attained at the all-singles vertex, also max of min_a f_a = 2. 3000 random convex combinations: max f_a = 1.22 <= 2.
My closed-form upper bound (above) agrees with the LP at all interior samples and is above it at 21 of 279 vertex/a pairs, as it should be, because a single can also be double-sealed (M4: the text's rule "may have P = {5}" is an option, not a requirement).
Integer version: all integer leak structures with petal budget d (987 for d = 2, 51 for d = 1; the count 987 agrees with the text), integer MILP over the splits: max over structures of min_a f_a = 2d (2 and 4). No rounding loss.

## 3. Finite k and adversarial placements (`ps2_check.py`)

Requester: 27.2 verbatim in integers (blocks of size T - hit_Y, F_i = max(hit_Y, |R_Y-parts|) points containing them, request 4 with the common pool points, S-petal chosen by an integer program on the actual B points that minimises
max_j(|G_j| + load_j), G_5 ⊇ T_a ∩ R_X, G_6 ⊇ (T_4 ∩ R_X) ∪ Z_5, G_7 ⊇ Z_5 ∪ Z_6, request j = G_j ∪ {B points with j ∈ P}). Free choices (block order, fillers) random / low / high.
Checks: request <= T, reply in H and avoids S, petals class X, centres class Y, empty petal intersection, the structure facts of the proof (P_i ∩ R_X = R_X ∖ W_i, R_Y-parts disjoint, T_4 ∩ R_X = W_4, T_a ∩ R_X <= block), literal all-pairs 2-cover test.
Adversaries. (i) Structured: for each of the 93 vertices (scaled to integers by d) the petals' leaks realise the vertex (pool groups of the multi-types shared by exactly the petals of J, singles fresh in R_Y or pool, petal 4's R_X part random/low/high); centres by priority genomes
(hand-made extremes: centre leak on U ∩ R_X, on earlier leak points, shared outside points, plus random genomes). (ii) Generic priority-genome adversaries for all seven replies with hill climbing on the largest request. Variants 'free' (leak anywhere) and 'pool' (leak only in own arena or pool), both orders of the two hit numbers.
Main run (`ps2_check.py 21 3`): (k,T,d) = (40,30,6), (40,30,7), (80,60,12), (80,60,14), (100,78,18), (100,78,19), (50,40,9), (120,90,22), (60,45,10), (60,45,11), (100,80,19) etc., 678 games per row and variant, about 17,000 games:
**0 covers, 0 requests above T, 0 no-reply, 0 wrong-class, 0 structure flags.** In every row the largest request equals T (e.g. centres 30 + 2·14 = 58 at (80,60,14) with h_X = 30; the all-singles vertex attains hit_X + 2d), so the accounting is attained.
Asymmetric leaks (d_X, d_Y) = (14,8), (8,14), (14,2) at (80,60): 0 flags.
Controls (`ps2_check.py 22 3 ctrl`, δ above t/4): (40,30,8), (80,60,16), (80,60,18), (100,78,22): the requests overrun T (in the planned centre request in the pool variant, in the executed game in the free variant: 64-121 of 678), as predicted. Threshold t/4 is sharp for this strategy.
M2 (integer boundary): at δ = t/4 exactly with T even (k = 80, T = 60, d = 15) the hit numbers are (30, 31); the strategy is within budget only if X (the petals' class, whose hit number is the centres' G size) is the class with hit 30. With the other labelling the planned centre request is 61 (31 + 30). The requester may choose X, so this is fine, but 27.2 should say "X = the class with the smaller hit number". The text's table (80,60,15) works for that reason. For δ < t/4 strictly (d <= 14) both labellings fit.
M3: (16,12,3) overruns by one point (rounding, in 27.3), confirmed in the control run.

## 4. Remaining remarks

- 27.2 does not need the pool to be small or the singles to be in R_Y: the S-petal singles can be pool points, the replay uses both.
- The class-existence step for centres: |S ∩ R_X| >= hit_X leaves |S ∩ R_Y| <= T - hit_X < hit_Y, so a class-Y reply exists; I verified it is the same count as in PS.
- The claim "closed for all t >= 4/5" is just t/4 >= 1 - t. Correct.
- I did not examine 27.4 (subfamily lever) beyond the statement; the k = 12 integer budget quoted (request 4 <= 9, B-load <= 4) matches my integer exhaustive result (987 structures, max 4).

No counterexample and no gap in PS2.
