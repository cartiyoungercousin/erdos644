# Programme 5: can one-configuration lemmas beat 7/8 at n ≥ 2k? — CAPPED AT 1/8

Tags: [proved by hand] / [computed exact] (rational arithmetic, certificates) / [computed, grid] / [heuristic] / [open].
Code and logs: `compute/programme5/beat78/` (`logs/`). Nothing committed; LEDGER and Lean644/ untouched. Nothing here is
independently verified. Units of k; t = T/k = 3/4 + ε (T = τ − 1), ν = n/k, ρ = r/k = ν − 1 − t.

## 0. Verdict (pre-registered outcome 2)
- **CAPPED AT 1/8.** For every t < 8/9 and ν > 2 + t (ν > max(2 + t, 4t) if non-pencil triples are also allowed),
  an explicit adversary defeats *every* bounded combination of the covering lemmas (start, pair bound, window/centred
  dump, pencil bound, two-stage dump) with *every* static three-anchor finish (P1, HUB, all P1-type lemmas of the
  LP-11/6 and LP-15/8 classes, indeed all 715 classes and labellings) (Theorem O, §2).
  - So these lemmas cannot prove ε < 5/36 for ν ≥ 26/9, or ε < 1/8 for ν ≥ 23/8.
  - By padding (BULK §1.2), (G) on ν ≥ ν0 is all of (G). So no uniform bound below FKW's 1/8 comes from these tools.
- **Extremal configuration.** Profile {ck, o(k)⁺, o(k)⁺} with 4t − 3 < c ≤ 1 − t/2; at t = 7/8, c ∈ (1/2, 9/16]. Two
  anchors share ck points; the third meets each in ≥ 1 but o(k) points ("glue"). Every static finish then needs a
  block of (c+3)k/4 > 7k/8.
- **Mechanism.** t* jumps at empty pairwise parts: c + 1/4 ≤ 0.81 if both glue parts are empty, (c+3)/4 ≥ 0.875 if
  they are nonempty but o(k). A request can never empty a pairwise part (each private part keeps ≥ (1−t)k points
  outside U), so request-built configurations always pay for the glue.
- **Middle range** [computed, grid; not certified]. The composable-lemma game (§1.4) has value < 1/8 on about
  [53/24, 2.45], about 1/8 on [2.45, 2.6], and > 1/8 from 2.65 on (table §2.1). This would push the FKW-beating range
  past 53/24 by combining the dumps with HUB/15/8-class finishes. It is range-limited, hence useless for (G) by padding.

## 1. The adversary problem, exactly
### 1.1 Good-seven side: all static three-anchor finishes [proved by hand; computed exact]
- **Setting.** Pencil x_a, x_b, x_c, x_i the pairwise-only part opposite anchor i, E_i = 1 − x_j − x_l; candidate
  pairs X_i–X_j and E_i–X_i. A static finish is four blocks L_g, |L_g| ≤ T, covering every candidate pair (answers
  B_g ⊆ V∖L_g then complete a good seven).
- **Patterns.** Each point takes a pattern S ⊆ [4]; patterns on adjacent regions intersect. WLOG an antichain A_i on
  X_i and its blocker b(A_i) on E_i; a config C = (A_a, A_b, A_c) has pairwise cross-intersecting antichains.
- **Duality.** Every cover has max_g|L_g| ≥ Σ_g λ_g|L_g| ≥ Σ_R |R|·min_{S∈A_R} λ(S) for every λ in the simplex. This is
  exact at every k, and gives
  **t*(x) = min_C max_{λ∈Λ} Σ_R m_R(x)·min_{S∈A_R} λ(S)**.
  - Λ = the 101 vertices of the arrangement {λ(P) = λ(Q) : P ∩ Q = ∅} ∪ {λ_g = 0}. The inner function is linear on its
    cells.
  - 296 951 configs reduce to 15 889 (S4 symmetry and exact dominance). `tstar.py`
- **Validation.** Agrees with the independent MILP `bulk/pencil_cover.py` on 300 random + 7 named shapes (0 mismatches,
  `logs/validate_300_1.log`) and with the per-class LP `bulk/anchor3_lp.py` (`logs/classes_at.log`).
- **Lemma S (loss counting)** [proved by hand]. For any config C (equivalently any class and labelling), if
  v_C(d)·k ≤ T − 10, then H has a good seven.
  - Proof: a basic LP optimum has ≤ 10 nonzero (region, pattern) masses. Rounding them to integers with exact region
    sums changes each block load by < 10.
  - P1 is the Fano config, v = (3 − Σd)/2 (constant 6). HUB is class 195.
  - The P1-type lemmas of the LP-11/6 and LP-15/8 classes are the corresponding v_M = min over labellings
    (`classes_at.py` computes them). Their values on the extremal family are in the table below.

| lemma (class) | Fano P1 (706) | HUB (195) | LP-11/6: 430, 574, 675 | 707 | best LP-15/8 (250) = all classes |
|---|---|---|---|---|---|
| value at {c, 0⁺, 0⁺}, c ∈ [1/2, 5/9] | (3−c)/2 | c + 1/2 | (3c+5)/7 | (3−c)/2 | **(c+3)/4** |

### 1.2 Exact value on the extremal family [computed exact, certificate]
- Write f1(c) := t*(0⁺, 0⁺, c). **f1(c) ≥ (c+3)/4 on [1/2, 1]**, with a rational certificate for each of the 15 889
  configs (`exact_cert.py`, `logs/exact_cert.log`).
  - Each certificate is one λ-form ≥ the target at both endpoints, or a zero-slope convex combination of two forms.
    Concavity in λ makes that combination again a single λ.
- **Exact values:** f1(1/2) = 7/8, f1(17/32) = 113/128, f1(5/9) = 8/9, f1(9/16) = 43/48, f1(3/5) = 14/15, and
  f1 = 1 on [2/3, 1]. So f1 = (c+3)/4 on [1/2, 5/9] and c + 1/3 on [5/9, 2/3].
- With empty glue the value is (c,0,0) ↦ c + 1/4. That is the discontinuity in §0.

### 1.3 Covering side: every listed lemma is a request [proved by hand]
- **START(u).** Request u points of x1 plus t − u outside. This gives x2 with j = |x1∩x2| ∈ [max(0, 1−u−ρ), 1−u].
- **DUMP(h1, h2)** on a pair with j ≤ t: U ⊇ x1∩x2, A_i ⊆ x_i∖x_{3−i} of mass h_i ∈ [1−t, 1−j],
  2−t−j ≤ h1+h2 ≤ min(2−2j, 1+ρ). The answer has y_i ≤ h_i, h1+h2−ρ ≤ y1+y2 ≤ 1; it gives the pencil {j, y1, y2} and
  new pairs y1, y2.
- **The listed lemmas as requests.** Pair bound (h_i = 1−j) and the window/centred dump (h1 = h2) are DUMPs. The pencil
  bound is START + DUMP + DUMP. The two-stage dump is START + 3 DUMPs.
- **Frankl–Wilson** is not a request. Its hypothesis r ≤ c0(ν)k fails for all ν ≥ 2 when ε ≤ 1/8: c0 = 0.060, 0.082,
  0.110, 0.149, 0.207 at ν = 2, 2.2, 2.5, 3, 4, against ρ ≥ ν − 15/8 (`fw_c0.py`; c0(2) matches the paper).

### 1.4 Two adversary problems
- **(Game P, composable lemmas: only lemma-controlled information).** The adversary needs a set S ⊆ [0,1] of pair
  intersections meeting every START window, with every j ∈ S, j ≤ t, surviving every DUMP by a response in S² of
  t*_+(j, y1, y2) > t (t*_+: no move can force an empty pairwise part). Value(ν) = sup{t − 3/4 : such S exists};
  `pairgame.py` (greatest fixed point), `scan.py` (bisection in t; t* table on a 1/G grid).
- **(Game F, full).** Any bounded number of arbitrary requests; the requester sees every set. She wins if any three
  answers admit a static finish. F dominates P and every lemma combination.

## 2. Results
### 2.1 Value of Game P [computed, grid G = 96 (G = 48 in brackets); bisection in t; artefacts up to about 0.01]
| ν | 2.0 | 2.1 | 2.2 | 53/24 | 2.3 | 2.4 | 2.45 | 2.5–2.6 | 2.65 | 2.7 | 2.8 | 2.875 | ≥ 2.9, ∞ |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ε* | .0677 | .0868 | .1024 | .1042 | .1125 | .1198 | .1229 (.125) | .125 | .1276 | .1302 | .1354 | .138 (.146) | .1458 |
| proved | ≤ 3σ/11 = .068 | .095 | .123 | 1/8 | — | — | — | — | — | — | — | ≥ 1/8 (Thm O) | ≥ 5/36 = .1389 |
- **ν → ∞.** The grid's .1458 = f1(9/16) − 3/4 is an artefact (the requester's optimal box h = 1 − t/2 is off-grid).
  Conjecture: exactly 5/36 [heuristic].
- **Strategy at ν ≥ 3, t = 7/8.** The fixed point is S = [0, 11/96] ∪ [49/96, 1]: light pairs plus heavy pairs
  (`logs/pairgame_t875.log`). This is the two-cluster picture of Theorem O.
- **Consistency.** Every entry is ≤ the verified 3σ/11 where that applies (ν ≤ 53/24).

### 2.2 Theorem O (two-region adversary) [proved by hand + the certificate of §1.2]
**Statement.** Fix t < 8/9, c with max(1/2, 4t−3) < c < 1 − t/2, and m. Let
k > max((4m+2)/(2c−1), 9m/((c+3)/4 − t), m/(1−t)), and n ≥ 2⌈(2−c)k⌉. In the m-round request game
(|U| ≤ T = ⌊tk⌋; answers are k-sets in V∖U), the adversary can answer so that no three answers with empty common
intersection have a static finish. If n > 4T, no three answers have one at all.
**Proof.**
- **Answers.** Disjoint R1, R2, |R_i| = s = ⌈(2−c)k⌉. To answer U pick i with |R_i∖U| ≥ k (|R1∖U| + |R2∖U| ≥
  2s − T ≥ 2k as c < 1 − t/2). B takes one point of x∩R_{3−i}∖U for each earlier answer x of the other cluster (≤ m
  "glue" points; they exist as |x∩R_{3−i}| ≥ k − m > T), and is filled up from R_i∖U.
- **Intersections.** Same cluster: |B∩B'| ≥ 2(k−m) − s ≥ ck − 2m − 1. Different clusters: 1 ≤ |B∩B'| ≤ 2m (the later
  answer contains glue from the earlier one).
- **Three answers in one cluster** meet pairwise in > k/2, since (2c−1)k > 4m+2. So they share a point.
- **Two answers in one cluster and one (W) in the other**, with empty common intersection.
  X_W = B∩B' has mass c'' ≥ c − (2m+1)/k; B∩W, B'∩W are nonempty pairwise-only parts of size ≤ 2m; E_B, E_B' ≥
  (1−c'')k − 2m and E_W ≥ k − 4m. Every coefficient lies in [0, 1], so the certified λ of §1.2 gives
  max_g|L_g| ≥ (c''+3)k/4 − 8m > T.
- **Non-pencil triples.** If the three anchors share a point p, every pair {p, q} is a candidate. So the blocks
  containing p cover V, which needs 4T ≥ n. ∎
- **Optimising.** c → 1 − t/2 needs ν > 2 + t and allows any t < 8/9 (4t − 3 < 1 − t/2 ⇔ t < 8/9; closes at c = 5/9).
- **Simulation** (`sim_two_region.py`, k = 2000–3000, 8–12 rounds of mixed START/DUMP/random requests): 841 pencils,
  all with lower bound > T (min 0.884 at t = .875). Negative control: without glue the bound drops to 0.775 and
  finishes exist (`logs/sim_two_region.log`).

### 2.3 Which lemma fails on {ck, 0⁺, 0⁺}, t = 7/8, c ∈ (1/2, 9/16]
- **P1.** It needs weight ≤ 4εk = k/2; the weight is (3 − 2c)k ≈ 1.94k.
- **HUB.** It needs Σ max(0, g_i) ≤ k/2; the sum is (2c − 1/4)k ≥ 0.75k.
- **LP-11/6 classes.** They need (3c+5)/7 ≤ t, but the left side is ≥ 13/14.
- **Best class (an LP-15/8 class).** It needs (c+3)/4 ≤ 7/8, i.e. c ≤ 1/2.
- **Pencil bound and two-stage dump.** Their size conditions fail (4T < 2k + 3r since r > k). Their conclusion,
  weight ≤ 3r/2 + 1, is satisfied by the adversary.
- **Pair bound.** Its weight bound r + |k − r − 2j| ≥ r > k/2 never reaches P1.

## 3. Consistency checks
- **FKW.** Theorem O bounds what proofs can reach; it is not a family, so it does not contradict τ ≤ 7k/8 + 1 (FKW uses adaptive finishes, §4).
- **Lower bounds.** min t* = 3/4 on the grid (perfect pencil), never below the FKW value 3/4. No entry of §2.1 lies
  below 0, and none conflicts with f(4m,7) ≥ 3m+1 (ν = 7/4) or with the cell extremals (ε ≈ 0, PROGRAMME4_CELLS).
- **BULK §3.3 erratum** [computed, grid]. `bulk/game3.py` omitted d13 + d23 ≤ 1; its 15/16 at t = 7/8 sits at the
  infeasible response (0, 9/16, 9/16). Corrected (`game3_fixed.py`): **9/10**, at d12 = 0; "needs adaptive finishes"
  stands. BULK's pencil_cover grid also capped x_i ≤ 1/2; on the full domain max t* = 1 (e.g. (0⁺, 0⁺, ≥ 2/3)).

## 4. The new ingredient that is needed [heuristic / open]
Any proof below 7/8 must use something other than "one request-built pencil + four T-blocks". At the obstruction,
exactly three things are available:
- **(a) Adaptive finishing.** In the two-region adversary, an answer in one cluster avoids almost all of the other
  region. A finish that reads where B_1 actually lies, not just that it avoids L_1, gains up to (1−c)k per block.
  This is FKW's mechanism; quantifying it is the next step.
- **(b) ≥ 4 anchors.** For example, four answers of one cluster with empty intersection plus three of the other. Any
  three members of one cluster share a point (3(1−c) < 2 − c), so only finishes with four or more members from one side
  can see past the glue.
- **(c) A global (non-request) lemma that kills o(k) glue.** A real family would need two clusters cross-intersecting
  with o(k) intersections *against all* T-sets, not only m of them [open]. A lemma "every T-covering family has a
  pencil {c, ∅, ∅} with c ≤ 5/8, or one with Θ(k)-balanced parts" would reopen static finishes; none is known.
- The middle-range values of §2.1 (if certified) are range-limited and do not help (G).

## 5. Files (`compute/programme5/beat78/`, `py -3.14`)
- `tstar.py`: exact t* and certificates. The table cache is rebuilt in about 2 min.
- `validate.py`, `grid_t3.py G NPROC` (t* tables `logs/t3_{48,96}.npy`), `pairgame.py G nu t|scan`, `scan.py G`
  (`logs/scan_{48,96}.log`).
- `exact_cert.py`, `classes_at.py NPROC`, `fw_c0.py`, `game3_fixed.py G t`, `sim_two_region.py k t c rounds trials seed`.
- At most 6 cores were used.
