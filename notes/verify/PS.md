# Independent verification: Theorem PS (PETAL 26.2) and the reconciliation of the open strip

Verifier's note. Re-derived from PETAL 1-2 (P1-P4), 12, 20.2, 23, 26.2. Code is new: `compute/verify/ps_check.py`
(model, adversary, PS verbatim, tiny exhaustive), `ps_big.py`, `ps_dup.py`; logs in `compute/verify/logs/ps_check_{main,tiny}.log`,
`ps_big.log`. Nothing imported from `compute/petal5`, `petal3` or other verify files. Not committed.

## Verdicts

| Item | Verdict |
|---|---|
| Theorem PS (26.2), pooled 𝒜, δ < 3t/16, no condition on c | **PASS** (hand check of every step; 151,000+ adversary games and ~501,000 exhaustive-last-reply games: 0 covers, 0 budget violations, 0 flags; threshold sharp) |
| Corollary (pooled 𝒜: (a) iff t >= 2/3, (b) iff δ < 3t/16) | **PASS** |
| LEDGER open item "reconcile 3t/16 <= δ < 1-t vs 7/5-17t/10" | **RESOLVED**: no contradiction; the strip [3t/16, 1-t) is truly open for pooled 𝒜 (table in section 3) |

Minor remarks (not gaps): R1 duplicates of replies, R2 integer rounding, R3 "τ(H) > t" needs ε, R4 the t/6 -> 3t/16 claim for the pool-free DS.

## 1. Hand check of PS, step by step

Setting: R_X, R_Y disjoint, classes by ">= 1 - ρ_c in R_c", everything else pool. hit_c := τ_c + ε = n_c - 1 + ρ_c + ε: a subset of R_c of that
mass meets every class-c set, so a request containing it cannot be answered in class c. Existence of a reply: |S| <= t < τ_X + τ_Y gives
|S ∩ R_X| <= τ_X or |S ∩ R_Y| <= τ_Y, hence a member avoiding S (checked exhaustively on tiny instances, `ps_check.py tau`:
brute-force τ(H) = hit_X + hit_Y for 'free' and 'pool'; for the 'exact pool' variant τ can drop through the pool when it is too small,
which is a failure of the adversary's premise, not of PS).

**Petals (requests 1-4).** Request = F ∪ J, F ⊂ R_Y, |F| = τ_Y + ε, F ⊇ I_i ∩ R_Y; J = min(b, |I_i ∖ R_Y|) points of I_i ∖ R_Y; b = t - τ_Y - ε.
- Class Y is dead (|R_Y ∖ F| < 1 - ρ_Y), so the reply (exists by τ(H) > t) is class X. Correct, and it holds whatever J is, because
  the existence argument counts only |S| <= t. J may lie in R_X or in the pool; irrelevant.
- |I_i ∩ R_Y| <= ρ_X (each class-X reply has <= ρ_X outside R_X), and ρ_X < τ_Y follows from (b) and τ_X + τ_Y > t. So F ⊇ I_i ∩ R_Y fits. Correct.
- New petal avoids F ⊇ I_i ∩ R_Y, so I_{i+1} ∩ R_Y = ∅, and avoids J, so |I_{i+1}| <= |I_i ∖ R_Y| - min(b, |I_i ∖ R_Y|). With |I_1| <= 1:
  |I_2| <= 1 - b, |I_3| <= 1 - 2b <= b iff b >= 1/3, then request 4 has J = I_3 and I_4 = ∅. Pool points are in I and are removed by J exactly as
  arena points. Correct. Cost |F| + |J| <= τ_Y + ε + b = t. J ⊂ complement of R_Y, so disjoint from F. Correct.
- (a) t - τ_Y >= 1/3 + ε. Correct (and in points: 3b >= k).

**Centres (requests 5-7).** U = union of petals, B = U ∖ R_X (other arena and pool), |B| <= 4ρ_X, B = B_0 ∪ B_1 ∪ B_2 equal thirds.
Request j = G_j ∪ (B ∖ B_j), G_j ⊂ R_X, |G_j| = max(τ_X + ε, |Z_{<j} ∩ R_X|), G_j ⊇ Z_{<j} ∩ R_X.
- Class X dead (|G_j| >= τ_X + ε inside R_X), so the reply is class Y; it exists because S ∩ R_Y ⊂ B ∖ B_j has mass <= t - |G_j| <= t - τ_X < τ_Y.
  (The proof says "R_X ∖ G_j has mass < 1 - ρ_X"; the existence of a class-Y reply is the same τ(H) > t count. Fine.)
- A class-Y centre has <= ρ_Y outside R_Y, hence |Z_i ∩ R_X| <= ρ_Y and |Z_{<j} ∩ R_X| <= 2ρ_Y. Correct (R_X ∩ R_Y = ∅ is used).
- Traces on U: U ⊂ R_X ∪ B. On R_X the centre j avoids G_j ⊇ earlier traces: pairwise disjoint. On B each point lies in B_i for exactly one i, so it is
  requested in both other requests and can lie only in centre i. So traces on U are pairwise disjoint, pool points of B included. Correct. P4(c) then
  needs the petals to have empty common intersection (done) and gives no 2-cover (P1: any 2-cover has both points in U; three centres, two points,
  pigeonhole gives a point in two centres on U). I re-derived this: correct.
- Cost: max(τ_X, 2ρ_Y) + ε + (2/3)|B| <= max(τ_X, 2ρ_Y) + ε + 8ρ_X/3 <= t by (b). Correct.
- Pooled 𝒜: ρ = δ, τ = t/2, (b): t/2 + 8δ/3 <= t iff δ <= 3t/16 (the other branch 14δ/3 <= t is weaker). Correct.

Nowhere does the proof use c, an overlap, or the pool's size. The only information used: R_X, R_Y, ρ's and τ's. No gap found.

R1 (duplicates). The adversary may repeat a reply (42,367 of 144,000 games in the main run contain two equal replies, e.g. two centres equal with empty
trace on U). The game of PROOFS Theorem 8 is about a sequence A_1..A_7 and allows this. If seven DISTINCT members were required: the distinct sets are
a sub-collection of the uncoverable seven, hence uncoverable, and adding any further members of H keeps the family uncoverable (more sets are harder to
cover), so PS is unaffected. One sentence would make this explicit.
R2 (rounding). In points, F has hit_Y points, b = T - hit_Y must satisfy 3b >= k (round up, as in DS_FF_AP.md item 4), and the sealed part is
|B| - floor(|B|/3). All consistent with the integer feasibility test `feasible_hits` used below.
R3. 𝒜 itself has τ_X + τ_Y = t exactly; "τ(H) > t" holds with one extra point (hit_X + hit_Y = T + 1). Same remark as AP.
R4. Hand claim in 20.2 that DS extends to 3t/16 by sealing only the common part is now superseded by PS (which is DS-free).

## 2. Computation (independent code)

Model. Points as bitmask integers. Ground set R_X ∪ R_Y ∪ O. Members: k-sets with >= k - d_c points in R_c, rest anywhere ('free'), only in R_c ∪ O ('pool'), or
exactly d_c points in O ('exact'). hit_c = n_c - k + d_c + 1 (matches brute-force τ on tiny families). T = hit_X + hit_Y - 1 (the adversary's best family).
Strategy PS verbatim (F ⊇ I∩R_Y plus J from I∖R_Y with J of size min(b,|I∖R_Y|); B = U∖R_X in thirds; G_j ⊇ Z_{<j}∩R_X; request B∖B_j). Free choices
(which extra points fill F and G_j, which points of I∖R_Y form J, the split of B) are taken 'random' or 'low'.
Harness flags: request > T; no reply; reply not in H or hits S; petal not class X; centre not class Y; non-empty petal intersection; |B| > 4d_X;
centre traces on U intersecting; and a LITERAL all-pairs 2-cover test of the seven replies (cross-checked with a membership-type test by assertion).
Adversary: per-reply priority genomes over 12 features (multiplicity in earlier replies, same-class multiplicity, common point of all replies, requested before,
pool, other arena, own arena, earlier leak points, in U ∩ R_X, other-class multiplicity, fresh), class choice (X, Y, random), noise; handcrafted extremes
(petal leaks into fresh pool points, into the other arena, shared leak points; centres putting their outside-R_Y points on petal points of R_X and on earlier
leak points); random genomes; hill climbing on (largest request, any flag). Leak points lie in all four petals, centres share outside points whenever the
genome asks for it (these are the genomes the climb keeps, since they maximise the request).

| run | instances | games | covers | request > T | no reply | class / intersection flags | trace clashes |
|---|---|---|---|---|---|---|---|
| main (`ps_check.py main 11 120`): k,T in {(60,45),(60,47),(80,64),(100,80),(90,77)}, d = floor(3tk/16) (tight) with five (d_X,d_Y) patterns incl. d_Y = 1, d_X = d/2, d_Y = d/2, hit_X at its smallest / middle / largest feasible value, X = either class, variants free (pool 0 and k), pool (k/2), exact (T+2d+2), fills random/low | 1200 | 144,000 | 0 | 0 | 0 | 0 | 0 |
| big (`ps_big.py`): k = 120..240, t = 0.783..0.789, pools 3k-5k, asymmetric d | 64 | 7,680 | 0 | 0 | 0 | 0 | 0 |
| tiny exhaustive-last-reply (`ps_check.py tiny 7 150`): (k,T,d_X,d_Y,m) = (6,6,1,1,3), (6,6,1,1,6), (7,7,1,1,3), (6,7,1,2,2), all three variants, both X: random prefix of 6 uniformly random members, then ALL members as the seventh reply | 26 | ~501,000 | 0 | 0 | 0 | 0 |

In every tight row the largest request equals T (the adversary reaches the predicted bound max(hit_X, 2d_Y) + |B| - floor(|B|/3)), so the accounting is
attained, not just safe.
Controls (`ps_check.py ctrl`), strategy verbatim, d above the threshold: (k,T) = (60,45): d = 8, 9 fit; d = 10, 12 overrun T in 91/100, 94/100 games.
(100,80): d = 15, 16 fit; d = 17, 19 overrun in 86/100, 91/100. The integer threshold d <= 3T/16 (up to rounding) is exact, so 3t/16 is the sharp limit
of PS, and the harness does detect budget failures.
No counterexample, no instance where PS fails inside its hypotheses.

## 3. Reconciliation: which δ are closed for POOLED 𝒜

What the notes actually say. §19.1 and §12 never state that any requester strategy wins for δ >= 7/5 - 17t/10. The number 7/5 - 17t/10 is where
c = 1 - t/2 - δ equals θ(t) = (6t-2)/5: below it (c > θ) a single-served 2+2 quadruple is impossible (11.3, necessary condition) and AP's hypothesis
holds; above it 11.3 merely stops being an obstruction. Theorem N shows the 2+2 architecture loses for δ <= δ_N(t) only (and for no δ at t >= 0.7903),
and §12/§13 list "δ_N < δ < 7/5 - 17t/10 against simultaneous serving" as undecided. No theorem in PETAL gives a win for pooled 𝒜 at
δ >= 7/5 - 17t/10; the LEDGER sentence ("known strategies already win for δ >= 7/5 - 17t/10") is not supported by the text. The DS_FF_AP.md addendum
had it right: AP/§19.1 cover pooled 𝒜 for δ < 7/5 - 17t/10 only. Further, for t >= 3/4 one has 7/5 - 17t/10 < 3t/16 (they cross at t = 0.7417), so AP's pooled range is
contained in PS's and the two statements do not overlap in a contradictory way.

Ranges for pooled 𝒜 (arena-aware requester: she knows R_X, R_Y, ρ), all δ >= 0 with δ < 1 - t:

| t | PS closed: δ < 3t/16 | AP closed (c > θ): δ < 7/5 - 17t/10 | DS (pool-free only): δ < t/6 | J'' / J / 12.3 (blind or pool-free): t/18, t/26, t/8 | 2+2 loses (Thm N): δ <= δ_N | **truly open**: 3t/16 <= δ < 1 - t |
|---|---|---|---|---|---|---|
| 0.75 | 0.1406 | 0.125 | 0.125 | 0.0417, 0.0288, 0.094 | 0.0510 | [0.1406, 0.25) |
| 0.76 | 0.1425 | 0.108 | 0.1267 | 0.0422, 0.0292, 0.095 | 0.0383 | [0.1425, 0.24) |
| 0.78 | 0.14625 | 0.074 | 0.13 | 0.0433, 0.0300, 0.0975 | 0.0130 | [0.14625, 0.22) |
| 0.80 | 0.15 | 0.040 | 0.1333 | 0.0444, 0.0308, 0.10 | none (t > 0.7903) | [0.15, 0.20) |

Reading, for each t in {0.75, 0.76, 0.78, 0.8}:
- Closed (requester wins in seven requests, PS, pooled or not, symmetric or not): 0 <= δ < 3t/16. This includes everything AP, DS (which fails with a pool, now repaired by PS),
  12.3, J'', J'. The arena-aware knowledge (R_X, R_Y, ρ) is assumed throughout; the blind versions only reach t/12 (DS-b) or t/18.
- Open: 3t/16 <= δ < 1 - t. At t = 0.75 this is [0.1406, 0.25), at 0.8 it is [0.15, 0.20). Nothing in the notes decides it, and the family has no known
  adversary win either (26.1: the fixed pooled family fails (7,2), which is not decisive). PS is sharp there: the double seal costs (2/3)·4δ on top of
  t/2 and the harness reproduces the overrun exactly. The only ideas not examined are those listed in 26.4 (seal only B ∩ U*, more than three centres) and the
  re-selection variants of 2+2 for c <= θ (open: for δ >= 7/5 - 17t/10 no 2+2 win has been proved either).
- Not open any more: the strip 7/5 - 17t/10 <= δ < 3t/16 (it is closed by PS), which is the strip the LEDGER wanted reconciled.
- For t >= 16/19 = 0.842 the open interval is empty (3t/16 >= 1 - t), so all of pooled 𝒜 (δ < 1 - t) is closed, as 26.4 states. None of the four t above is that large.
- δ >= 1 - t is outside 𝒜's definition (same-colour pairs no longer share a point forced by a_0 > t/2).

Suggested edits: replace the LEDGER open item by "pooled 𝒜 open for 3t/16 <= δ < 1 - t (3/4 < t < 16/19); no known strategy wins there (7/5 - 17t/10 is only the
2+2/AP threshold)"; add the one-sentence duplicate remark (R1) to 26.2.
