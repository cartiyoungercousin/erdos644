# Programme 5: below 6/7? Closures of the critical medium+tiny triple — CAPPED AT 6/7

Tags: [proved by hand] / [computed exact] / [computed, grid] / [heuristic] / [open]. Units of k, t = T/k. Code and logs:
`compute/programme5/below67/` (`logs/`), `py -3.14`, ≤ 8 cores, about 45 min of runs in total. Nothing committed;
LEDGER, Lean644/, notes/sources/ untouched. Nothing here is independently verified.

## 0. Headline (pre-registered form)
**CAPPED AT 6/7 for closures that keep the triple E, F, G and the answers that follow it:**
- **any adaptive depth** (1–4 adaptive requests, then static blocks), when the first request contains X ∪ Y ∪ Z
  (this includes rule R0) [proved by hand, Theorem P; spectrum-free request game];
- **depth 2** (two adaptive requests, then two static blocks), for every sampled first request [computed, grid;
  her second request from a structured family, his answers MILP-exact].

No closure of the critical triple was found anywhere, so the S-game is not rerun and t* stays 6/7. Untested:
discard finishes, and play that steers answer traces into the gaps of S*. These are the two live avenues (§5).

## 1. The critical configuration at t = 6/7 − δ [proved by hand, as in ADAPT §2.3]
- **Pair.** E, F with q = |E∩F| ∈ (t/2, min(3 − 3t, 9/7 − t)], an interval of length O(δ) around 3/7.
  q lies in the medium band [5/14, .435] of S* = [0, .268] ∪ [5/14, .435] ∪ [10/21, 1).
- **DUMP.** Her best request is balanced: E∩F plus (t − q)/2 of each private part. His answer G has
  y = |G∩(E∖F)| ∈ [5/14, (2 − t − q)/2] (medium band again, y > t − 1/2) and z = |G∩(F∖E)| = 0⁺ (small band).
  This works because Y + Z = 2 − t − q > 2t − 1.
- **Triple cells** (limit point; units of k/14 in brackets): X = E∩F = 3/7 (6), Y = E∩G = 5/14 (5), Z = F∩G = 0⁺,
  E' = 3/14 (3), F' = 4/7 (8), G' = 9/14 (9), |V| = 31/14. Candidate pairs: X×G, Y×F, Z×E.
- **Bridge.** F and G are two near-disjoint "regions" (glue Z = 0⁺). E is a bridge, with Θ(k) in each region
  (X in F, Y in G). So the external note's view (TARGET3 §8) is correct here: the medium cell Y is the bridge's
  foot in G. R0 (always request the glue) costs nothing here and does not remove the bridge.
- **Why each listed closure fails.**
  - Static: t*(q, y, 0⁺) = max((q+3)/4, 1/2 + y) near the point [computed exact, `beat78/tstar.py`, 12 points].
    Both terms exceed t: Theorem O's glue term (q > 4t − 3) and the medium term (y > t − 1/2).
  - Lemmas 4.1–4.3 need y ≤ t − 1/2. Lemmas 4.4–4.7 need a gap in S*, but S* contains all medium and heavy sizes.
  - Heavy route: no cell exceeds 1/2.
  - Split closure (X∪Y∪Z + private): it needs 2x + 2y + 1 ≤ 3t. At the point this is an equality, and below
    6/7 it fails, because x > t/2 and y > t − 1/2 give 2x + 2y + 1 > 3t.
  - So three independent constraints all bind at 6/7.

## 2. Theorem P (passive adversary): hub-complete first requests fail at every depth [proved by hand]
**Biclique accounting lemma.** Let U×W be complete bipartite (measure spaces) with u + w > t, and let sets
S_1, …, S_r with |S_i| ≤ t contain every pair of U×W. Then Σ_i |S_i ∩ (U ∪ W)| ≥ u + w + min(u, w).
*Proof.* Every point lies in some S_i. If every point of U lies in ≥ 2 sets, the sum is ≥ 2u + w; the same holds
with U and W swapped. Otherwise take p ∈ U and q ∈ W, each in exactly one set. The pair (p, q) forces these to be
one set S. Every w ∈ W pairs with p, so W ⊆ S; likewise U ⊆ S. Then |S| ≥ u + w > t, a contradiction. ∎

**Passive play.** Suppose that after some answer K the "live" points (those in an alive candidate pair of
E, F, G, K) have mass ℓ ≤ 1 + t. To every later request R the adversary answers M = (live ∖ R) ∪ (points outside V),
or any unit-mass part of live ∖ R if that part is larger. Either way the pairs killed by M lie inside a live set of
mass ≤ max(t, ℓ − 1) ≤ t. Adaptivity then reveals nothing: three more members close only if three t-sets cover
every alive pair.

**Theorem P.** Let the pencil (x, y, z) satisfy 2x > t, 2y > 2t − 1 and x + y + z ≤ t ≤ 1 − z. Let R1 ⊇ X ∪ Y ∪ Z
put its rest f, g, e on F', G', E'. Answer K = (F'∖R1) ∪ A with A ⊆ G'∖R1, |A| = α := x + z + f. This fits, since
x + 2z + f + g ≤ 1 − y ⇐ t + z ≤ 1. Then:
- β := |F'∖R1| = 1 − x − z − f and α + β = 1, so K has mass 1. Its traces are 0 on E, β on F and α on G.
- The alive graph is exactly X×A ∪ Y×B (B = F'∖R1). Everything else was killed in round 1: X, Y, Z, E',
  F'∖K and G'∖K are all out of K, and K∩E' = ∅. Live mass x + y + 1 ≤ 1 + t.
- x + α = 2x + z + f > t, and y + β ≥ 1 + 2y − t > t (using f ≤ t − x − y − z). Also α ≥ x and β ≥ y.
- So any three later members need Σ ≥ (2x + α) + (2y + β) = 2x + 2y + 1 > 3t.

Hence no strategy of any depth whose seven is E, F, G, K plus three later answers closes. The critical triple
satisfies the hypotheses: x > t/2, y > t − 1/2. ∎
- Consistency [computed exact on the grid]. The depth-1 value of the state α = β = 1/2 is exactly 12/14 = 6/7 for
  δ = 0.25 and δ = 0.5 (`t_biclique2.py`). This equals (2x + 2y + 1)/3: below 6/7 the adversary restores exactly 6/7.
- Scope. The adversary is spectrum-free: passive answers ignore S*. K's own traces can be chosen in S*, since
  α ranges over (t − x, 1 + y − t) ∩ S* ⊇ [10/21, 1/2) near 6/7. The later passive answers' traces are forced by
  her requests, so the S*-legal version is [open] (§5).

## 3. Searches (critical triple x = 6/14, y = 5/14, z = 0⁺; t = (12 − δ)/14)
### 3.1 Depth 2, class A: R1 ⊇ X ∪ Y ∪ Z (R0-style) [computed, grid]
- `run_A.py`. Every R1 extra on (E', F', G') on grid s1. Every answer K on grid s1, critical first. Her R2: all
  maximal grid requests on live types. His L: exact MILP over continuous answers (`fast2.adv_best`). Finish: two
  blocks, all labellings, exact.
- Spoiled at every δ and grid tried. The worst state always has α ∈ (t − x, 1 + y − t), β = 1 − α, γ = 0.

| δ (units 1/14) | R1 grid / K grid | R2 grid | first requests spoiled | depth-1 values at the spoiler |
|---|---|---|---|---|
| 0.5 | .25 | .25 | 6 / 6 | 12.0–12.25 |
| 0.25 | .25 / .125 | .25 / .125 | 10/10, 28/28 | 12.0–12.25 |
| 0.1 | .1 | .1 | 55 / 55 | 12.0–12.1 |
| 0.05 | .05 | .25 | 210 / 210 | 12.0–12.05 |

  Every value is ≥ 12/14 = 6/7, the static value: one hub-complete round gains nothing. Theorem P explains this.

### 3.2 Depth 2, class B: R1 misses part of X ∪ Y [computed, grid; her R2 structured]
- `run_B.py`, δ = 0.25, R1 on the unit grid (3815 requests). Random sample: 16/16 (`classB_test.log`) plus 257/257
  finished of a 600-sample (`classB_d0.25_600.log`; the run was stopped by the watchdog). All 273 are spoiled.
- In 254 of the 273 the first answer tried already spoils; the rest need up to 39 tries. The spoiling K keeps
  the hub remainder, excludes E' and splits F' / G' near 1/2 : 1/2.
- Spoiled means: every structured R2 (any set of live types requested fully, plus one or two partial fills; 154–905
  requests per state) is refuted by an exact MILP two-block value > t at some answer L.
- Not exhaustive over R2, and his L is taken from a candidate list. A refutation is sound; a missed closure is possible.
- The passive certificate (`passive.py`, stride 4, 955 R1) applies only to hub-complete-type R1 (108 certified,
  every class-A R1 among them). For 833 R1 the hub remainder in K makes the live mass exceed 1 + t, so passivity is
  unavailable there. So class B rests on the depth-2 computation, not on Theorem P [open beyond depth 2].
- Earlier finding (`pool1.py` test): one hub-keeping K for R1 = (4,5,0,1,1.75) is closable (value ≤ .80); the
  adversary must pick K carefully. The spoiling K does exist.

### 3.3 S1/S2 forms and R0 (external note TARGET3_ADAPTIVE) [proved by hand]
- Both are particular good sevens (sixes) on E, F, G and later answers. The exact finish enumerates all labellings,
  so §3.1–3.2 already include them.
- Directly: S2 (pencil + three C's with C_i ∩ C_j ∩ V = ∅) needs every point of V outside two answers. Each answer
  excludes at most |V| − 1 = 17/14 of V, so 2|V| = 62/14 > 3·17/14 = 51/14, impossible. After a class-A K, under
  passive play, it needs 2ℓ = 50/14 ≤ 3t, false.
- S1 (4 + 3, with B's = E, F, G, K) fails the same way. R0 is already free here (Z = 0⁺).
- Unlike the cluster adversary, the bridge E keeps Θ(k) live hub mass (X, Y) that R0 cannot touch.

### 3.4 A 4th or 5th member from an earlier stage (task 2b)
- One earlier member D [proved by hand].
  - If D is free, the adversary puts X ∪ Y in D, and D kills no hub pair.
  - If E was built avoiding t points of D (|D∩E| ≤ 1 − t), the adversary takes D∩E = ∅, D = (F'-part) ∪ (G'-part).
    That is exactly Theorem P's K with f = 0, so passive play caps E, F, G, D plus three later answers at every depth.
- Two earlier members D1, D2 with forced |D1∩D2| ≤ 1 − t, both avoiding E. Then hub pairs must hit D1 ∩ D2, which
  is small, and the alive graph collapses. It is not known whether the history can force this against an adversary
  who also chooses E, F, G [open]. This "history engineering" is the analogue of Q1's fourth anchor, and was not tested.

### 3.5 Spectrum information beyond the S-game (task 2c)
- Two pairs, triple profiles [proved by hand, spectrum-free model]. Members outside the kept seven do not enter
  the alive graph. Kept ones act as earlier members (§3.4). Passive answers are determined by her requests, so
  existence statements about other pairs give her nothing in this model.
- Gap steering [open, the real candidate]. S* has gaps (.268, 5/14) and (.435, 10/21). A passive answer's trace
  on K, |M∩K| = 1 − |R∩(A∪B)|, is set by her request. She can push it into a gap, which forces him to drop
  ≥ .015–.09 of extra live mass. Theorem P's margin 2x + 2y + 1 − 3t is O(δ), so this could matter.
  `run_AS.py` / `fast2.adv_best_S` (L's traces constrained to S*) were written; the δ = 0.1 run did not finish.

## 4. What is ruled out, precisely
- Model: the request game, answers any k-sets (spectrum-free), first-order masses, all 0⁺ parts made nonempty by him,
  final seven ⊇ {E, F, G} plus the answers after them (no discards of E, F, G).
- (i) First request ⊇ X ∪ Y ∪ Z: every continuation of every depth [proved by hand].
- (ii) Any first request, depth 2, R2 structured: [computed, grid] on a 273-request random sample of the unit
  grid at t = 11.75/14.
- (iii) One earlier member forced to avoid E: [proved by hand] via (i).
- Why the triple survives: the bridge creates two disjoint complete bicliques X×A, Y×B, each heavier than t, with
  α + β = 1 because the answer is a full member. Any hub-complete progress round leaves only t − x − y = O(1/14) of
  free mass. The accounting lemma then makes the 3t budget short by 2x + 2y + 1 − 3t > 0. Adaptivity is worthless
  once the live mass is ≤ 1 + t: passive answers reveal nothing.

## 5. What is needed instead [heuristic / open]
1. **Discards / new pencils.** Drop F or G and use K, L as anchors, e.g. the pencil (F, G, K) with cells
   (0⁺, β, α) ≈ (0⁺, 1/2, 1/2). Not covered by Theorem P. `disc_check.py` was written; the run did not finish.
2. **Spectrum-gap steering** (§3.5). It is the only place the S-game's information beats passive play. If it works,
   it changes S* and the fixed point, so it must be run inside the S-game.
3. **History engineering** (§3.4): two earlier members with forced small mutual intersection.
4. Any successful argument must defeat the passive adversary of §2. So it must use information or members outside
   "triple + the next four answers".

## 6. Files (`compute/programme5/below67/`)
- `engine.py`: general type engine, exact MILP finish, discards. Validated against `tstar` on 5 points.
- `fast2.py`: two-block labellings, depth-1 solver with exact adversary (`adv_best`, `_S` variant).
- `depth2.py`, `run_A.py`, `run_B.py`, `pool1.py`, `passive.py`, `run_AS.py`, `disc_check.py`, `t_biclique2.py`.
- Logs: `classA_d*.log`, `classB_test.log`, `classB_d0.25_600.log` (partial), `passive_d0.25_stride4.log`,
  `classAS_d0.1.log` (empty, unfinished).
