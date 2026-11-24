# Verification: PETAL Theorem J (§3), Theorem K (§7), fourth petal / Theorem L (§8), Theorem N (§12)

Independent read of statements and proofs only (plus the cited TWIN 13.5 Theorem D, TWIN 15.4 Theorem I / L*, PETAL 11.2 sliver rule, 14.1 J').
New code, all in `compute/verify/jkln/`: `jtest.py`, `kgame.py`, `kdesign.py`, `kdesign_test.py`, `gamma_test.py`, `ltest.py`, `ldiscrete.py`, `ntest.py`, `n123.py` (`leg.py` is a scratch legality probe).

## Verdicts

| Item | Verdict |
|---|---|
| (1) Theorem J (§3) | **PASS** (minor M1-M4); consistent with J' (14.1) and J'' (18.1) |
| (2) Theorem K (§7) | **PASS** (minor M5-M6) |
| (3) fourth petal §8 and Theorem L | **PASS** (minor M7-M8) |
| (4) Theorem N (§12), L* > t, adversary legality | **PASS** (minor M9-M10); the add-on 12.3 is a **GAP** (ground-set convention, M11) |

## (1) Theorem J: PASS

Hand check, every step.
- "~" (overlap > c) is an equivalence: p_il >= p_ij + p_jl - k > 2c-1 >= lambda, not in the band, hence > c. OK (J1).
- Standing request X_1 n Y_1 (mass < lambda): any later third-class reply E has E n X_1 n Y_1 = empty, the three pair masses are each < lambda, so p < 3 lambda <= t-1/3 (J2) and Theorem D applies (TWIN 13.5: all four requests contain P, |X_3| <= 1-2(t-p) <= t-p iff p <= t-1/3). E is always later than Y_1 and than the first standing request. OK.
- Step 1: request mass 2b + lambda = t exactly; RI gives |I_3| <= 1-2b <= b iff t-lambda >= 2/3 (this clause is the one hidden after "(J4)"), so the 4th member of a class misses I. Pigeonhole 7 = 3+4 over <= 2 classes; a third class goes to D. At most 7 requests. OK.
- Step 2: F_j of mass 1-c forces |C_j n X_1| <= c, hence < lambda (no band), so C_j is not in X's class and meets each X_m (m=2..4) in < lambda: |Z_i \ X_1| < 3 lambda, |Z_i n X_1| < lambda, so F_j can contain Z_{<j} n X_1 (< 2 lambda <= 1-c, J4). S_j contains all of Z_{<j}, so traces are pairwise disjoint and P4(c) closes (petals have empty common intersection, U* in U). Budget |S| < 1-c+6 lambda+lambda <= t (J3). If C_j is in a third class, D (<= 7+3+4 = 14 requests). OK.
- Consistency with J'/J'': J' is the same Step 2 without the standing request and with mu for lambda (1-c+6 mu = J's 1-c+7 lambda minus the standing lambda); J'' only sharpens the trace count; Step 1 differs only by b = t/2 versus (t-lambda)/2. No conflict. Remarks: t/2+delta+14 delta <= t gives delta <= t/30, and the 6-lambda count gives t/26 (0.0288 at 3/4): arithmetic correct.

Computation (`jtest.py`). Integer model (k, T, C, Lm). The adversary is any legal sequence: each reply is an ILP over the Venn cells of all earlier replies, disjoint from the request, enforcing same-class overlap >= C+1 and different-class <= Lm-1, for a chosen class (join an existing class or open a new one; policies random/new/big/small; objectives keepI, avoidI, traceU, maxold, minold, rand). The requester is the proof's strategy with asserted budgets (never clipped) and an exact 2-cover test of the 7 certificate replies. Parameters at the integer boundary of J1-J4: (k,T,C,Lm) = (40,30,24,3), (60,45,36,4) [J3 tight: (k-C)+7(Lm-1) = T], (50,40,31,4), (40,36,32,5), (60,45,40,3). About 1,300 games: 0 assertion failures, 0 covers; outcomes are win7 (Step 2 route) or winD. Step 1 requests reach exactly T (45/45, 36/36). Step 2 requests only reached 33/45 (the ILP adversary does not find the worst trace); the hand count covers it. The adversary was never forced into the band, so the band disjunct itself was not exercised.

Minor errors / clarifications (J):
- M1. "t-lambda >= 2/3" (and 3b >= 1) is independent of J1-J4 (J2 gives it only for t >= 5/6); it is packaged after (J4).
- M2. The Example c = 4t/5, lambda = (9t/5-1)/7 satisfies J1-J4 only for t <= 45/46 (J4 fails above; checked numerically). The alternative c = t^2 fails J4 for t > 0.895. Harmless for t <= t_1 = 0.781, but "for every t >= 3/4" in the Bottom line is over-stated.
- M3. Classes use "overlap > c" while the band is the closed [lambda, c]; the leaky-arena remark (cross <= 2 delta < lambda) needs strictness care at the boundary only.
- M4. The third-class branch needs the second class's first member Y_1 to exist before E (true, unstated); the case "only one class in Step 2, C_1 creates Y" is silent.

## (2) Theorem K: PASS

- Triple-free, so Gamma = the three grids (singles have |M_x| = 3 and every other point |M_y| >= 2, so M_x n M_y is nonempty). K(i): requests S_i = points whose type contains i; replies avoid S_i; K_i contains the design's round i; P2. Correct. The closed forms (matching a_r+b_r, all-pairs 2 sigma/3, freeze Sum a + Sum b/3) are feasible designs; stated examples reproduced (uniform K4 0.6667, (1/2,1/2) 0.625, (1/3,2/3) 0.5556).
- K(ii) necessity: against the adversary "reply contains all of U* \ S (padded outside U*) if |U* \ S| <= 1, else any mass-1 subset of U* \ S", |K_i| <= max(|S|, sigma-1) <= t when sigma <= 1+t. Her whole play is then a fixed triple (K_1,K_2,K_3), each of mass <= t, which must satisfy P2, i.e. a design with all loads <= t. Correct; adaptivity gives nothing because each reply is a function of S alone.
- Checks. (a) `kgame.py`: exact brute force of the 3-round game (all requests, all maximal replies, final P2 test) for every integer cell vector (cells 0..3, empty allowed) at (k,T) = (4,3), (5,4), (6,4), (3,2), about 510 shapes, with 3 to 10 losing shapes per (k,T) inside sigma <= k+T, against exact integer design feasibility: **0 violations** of "design implies game win" and of "sigma <= k+T implies (game win iff design)". Also no shape with sigma > k+T has a game win without a design. (b) `kdesign.py` / `kdesign_test.py`: independent L(a,b) from all 18 maximal cross-intersecting pairs per grid (5832 LPs per instance) equals TWIN's L* on 60 random single grids (error 2e-16); L* is monotone (20,000 random pairs); equals the author's `design.py` MILP on 12 random six-cell instances (max difference 1e-6). (c) `gamma_test.py`: 5,788 random triple-free four-petal systems with singles and random centres, exact 2-cover versus "some edge of the three grids has every centre containing x or y": 0 mismatches.

Minor (K):
- M5. K(ii): "no better for her than requesting them" is asserted, not argued (the argument: the outcome K_i of a request depends on S_i alone, so she may request K_i, of mass sigma-1 <= t).
- M6. A cell of mass exactly 0 (no points) has no grid and gives a smaller L (the exact game follows the true-empty design); K(iii)'s "mass epsilon" is right only for a nonempty O(1) cell. K(ii) says "L(a,b)" with zero allowed; state the convention.

## (3) Fourth petal on a spread triple and Theorem L: PASS

- S_4 = P u R has |S_4| = t exactly; B_4 n P = empty, so no point lies in three of B_1..B_4; the cells are the three pair cells and c_i4 = |B_4 n Q_i| <= q_i - r_i; sigma = p + Sum c_i4 <= p+1 <= 1+t, so K(ii) applies. q_i = 1-p+p_jl is correct (triple empty). Legality: r_i <= q_i and Sum q_i = 3-2p >= t-p. Correct.
- Theorem L recomputed: rho_i = 1-t-p+2 a_i; need Sum max(rho,0) <= t-p. Three terms: 3(1-t)-p <= t-p iff t >= 3/4. Two terms: 2(1-t)-2 a_l <= t-p iff a_i+a_j-a_l <= 3t-2. One term: a_i <= t-1/2. Correct. Also rho_i <= q_i iff a_i <= t, so the caps are not binding.
- `ltest.py` (continuum, t in {.75,.76,.8,.9,1}, about 20,000 triples): whenever the hypotheses hold an r exists and every vertex of the adversary's polytope {b_i <= q_i-r_i, Sum b <= 1} gives matching loads <= t (worst excess 2e-16). An r exists iff the hypotheses hold (no counter-case printed), so Theorem L is exactly the matching-design condition and is only sufficient (`ldiscrete.py` shows other triples are also won). 51 samples re-checked with the independent LP design (L <= t). `ldiscrete.py`: the full exact game (fourth petal for every r, adversary every b, then brute-force 3-round game) at (k,T) = (4,3) and (5,4): all hypothesis triples (5 and 8) are won; non-hypothesis triples 6/15 and 15/27 are also won. The (6,5) run was not completed.

Minor (L):
- M7. For t > 3/4 the two stated inequalities do not imply p <= t (all p_ab = t-1/2 gives p = 3t-3/2 > t), and p <= t is needed for S_4 to exist. §8's heading assumes spread; the theorem statement should repeat "p <= t".
- M8. "r exists iff every sub-sum of rho is <= t-p" also uses rho_i <= q_i and t-p <= Sum q_i (both true, not mentioned).

## (4) Theorem N: PASS

- Legality of A(t,delta) (`ntest.py` Part 2, exact rationals, 5,950 (t,delta) pairs, t in [0.66,1], delta < 1-t, all worst-case S): free mass in the chosen arena >= 1-delta and in the other arena >= delta whenever t >= 2/3. (At t = 0.66, delta >= 0.336 "n-t >= delta" fails; irrelevant for t >= 3/4, but the claim needs t >= 2/3, unstated.) The colour rule is consistent, since |S n V_A|, |S n V_F| > t/2 together is impossible.
- Proof recomputed. (i) a_0 > t/2 iff delta < 1-t; the sliver rule gives a common point of every same-colour triple. (ii) u n v subset of S_E (11.2) forces |S_E n V_A| >= a_0 > t/2, so E has colour F and y <= t-a_0; the F-pair case is symmetric. (iii) (1-delta)(1-delta-y)/(n-y) is decreasing (1-delta < n); at y = t-a_0 it equals beta (algebra checked). (iv) one grid with cells >= (a_0, beta): L >= L*(a,b) >= L*(a_0,beta) by monotonicity (verified numerically).
- Missing one-liner (not an error): sigma <= 1+t holds for every quadruple of the adversary (the three pair cells of T have mass <= |S_E| <= t, the three cells meeting E are disjoint subsets of E), so K(ii) applies and "no quad certificate" really means "no winning 2+2 quadruple". The text proves only the certificate (L <= t, 11.1); the headline "beats every 2+2 quadruple" needs this line.
- L* > t computed independently with exact Fractions: t = 3/4, delta = 0.051: a_0 = 0.574, beta = 0.6390, L* = 0.75000 (margin 2e-6), so delta_N(3/4) = 0.0510. delta_N(0.76, 0.77, 0.78, 0.79) = 0.0383, 0.0257, 0.0130, 0.0004. (N) at delta = 0 iff t < 0.79031; delta_N(t) > t/26 iff t < 0.76699. Single-serve column 7/5-17t/10 correct. Whole table reproduced; the margin changes sign once in delta.
- Simulation (`ntest.py` Part 3): discrete legal adversary (proportional own parts by atoms, random or reuse-aimed leaks, sliver rule) against a randomised requester (colour forcing, serving triples), k=120, (t,delta) = (.75,.04), (.75,0), (.76,.03), (.75,.05). Every triple-free quadruple found (7, 817, 113, 1) had a grid with cells >= (a_0, beta) minus O(1) and sigma <= k+T. Yield is low for delta > 0, so this tests the mechanism, not the constants.

Minor (N):
- M9. The sigma <= 1+t line and the t >= 2/3 legality condition above are unstated.
- M10. The 12.1 "reporting defect" at delta = 0.17 is outside every claim.

### 12.3 (4+3 beats A for delta < t/8): GAP (ground-set convention, M11)
"Requests 1-4: t/2+eps in V_F, containing the V_F-parts of the earlier replies." If "anywhere" (12.3's phrase "colour c: at least 1-delta in V_c") may lie outside V_A u V_F, petals can share outside points; the forcing request no longer pins the colour (leak not counted in V_F), and covering V_A needs 4(t/2-eps-leak) >= n, which holds only for delta of order t/18, not t/8. `n123.py` (k=120, T=90, dk up to 11, random and reuse leaks, requester exactly as in 12.3): all 1,200 games give 7 replies with no 2-cover when the ground set is V_A u V_F; with outside-arena leaks the literal construction breaks (colour-A assertion fails in about 90% of games for dk >= 5). Fix: state that the ground set is the two arenas (as in A(t,delta), whose leak lies in the other arena), or redo the count with outside leaks. Theorem N itself is not affected.

## Budget bookkeeping
J: 7 + 3 (+4) = 14 requests; K: 3 requests after the petals; L: 1 + 3; N: statement about certificates for every m. No quantifier errors found.
