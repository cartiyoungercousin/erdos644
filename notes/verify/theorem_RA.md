# Verification of Theorem A (ledger: Theorem RA), notes/PROGRAMME2_A.md

Code: `compute/verify/RA/ra_verify.py` (own implementation, exact Fractions, nothing imported from the author's code).
Run: `py -3.14 ra_verify.py <seed> <T4 iterations>`. Seeds 1-5 all pass.

## Verdict: PASS (no counterexample, no gap found)

| Step | Verdict | Evidence |
|---|---|---|
| Lemma A0 (3-wise intersecting => tau <= (k+1)/2) | PASS | Proof re-derived. Repeats are used correctly (B1,B2,B3 with B3 arbitrary), and |B1| <= k is the only size input. Tight on K_n^(k), n = floor((3k-1)/2), k = 2..8. 300 random 3-wise families: tau <= (k+1)/2, and |B1 cap B2| >= tau for all pairs. |
| |A| < 49/(3 eta); a' < eta/7; y(V)+7a' < 7/3 | PASS | y(V) <= 7/3 - eta < 7/3, so |A| <= y(V)/theta < 49/(3 eta). Also eta <= 4/3 (tau*_b >= 1), so a' < 4/21 < 1/3, which makes s > 0 in A2. |
| Deleting A: tau(H_A) >= tau(H) - |A|; strict > (k+1)/2 | PASS | Hand proof (transversal of H_A plus A). 1500 random exact tests. tau(H) > (k+1)/2 + 49/(3 eta) > (k+1)/2 + |A| gives strictness. A0 contrapositive gives a triple with empty intersection (repeats allowed; Lemma 2 allows <= 7 members). |
| A1 colouring and the bound (Lambda+3a')/2 < 1 | PASS | Light v goes to some X_s with v not in B_s (exists, triple empty). A is in no member of H_A, so B_s avoids L = A + X_s. Greedy split of X_s has half-mass difference <= a', so each half <= (m_s+a')/2. A line avoiding 0 takes one half per pair: <= (Lambda+3a')/2 < 1. The 4 lines avoiding 0 and the 3 lines through 0 were checked against the Fano table. 1,500+ explicit applications (random, H1+{{b}}, H1 + star_b, dense complements, inflated y with heavy atoms, many A): the mass bound holds, no L is a transversal, and every explicit seven has no 2-point transversal by brute force. |
| A2 branch, consistency with 3H | PASS | t = Lambda - 6s >= 3a'+6sigma >= 0 follows from Lambda+3a' >= 2; sum c = Lambda; line avoiding 0: 3s+3a' = 1-3sigma; line through 0: y(V)-4/3+7a'+4sigma < 1 iff y(V)+7a' < 7/3 - 4sigma, available by strictness. s > 0 needs a' < 1/3, true. The branch conditions are compatible and 3H's hypotheses (strict < 1, sequential fill, overshoot < a') hold. Boundary Lambda+3a' = 2 (t = 3a'+6sigma) is covered. |
| A2 END TO END on actual families | PASS | Implicit-oracle families (all k-subsets; k-subsets with <= c points of A; k-subsets with >= e points of A), k = 40..140, 0..5 heavy points of weight 0.05-0.3, feasible y certified exactly (exact min-weight transversal), light weights roughly 1/tau. Full pipeline: Theorem 3H fill with pi = 0, line masses < 1, no L a transversal (oracle), explicit seven of members, brute-force: no 1- or 2-point transversal. Seeds 2-5: 408 A2 applications (about 140 with heavy points), 39 A1, 0 failures. |
| Dependence on eta; no 3/4 threshold | PASS | Only eta > 0 is used. Sanity: for K_n^(k) the hypotheses force tau >= about 3k/4, so there is no conflict with known (7,2) families. |
| Known (7,2) families | PASS | K_10^(6) (tau 5, tau*_b 2) and star + co-singletons (tau 3, tau*_b 2.75): across several y and thresholds, no A1 or A2 branch is applicable (as required). |

## Remarks (non-blocking)
- T4 reaches the A2 regime only for large k (a' small), as the author noted; our families are implicit but are real families with an oracle for members. y is a certified feasible weight, not the LP optimum. The mechanics of A1/A2 need only feasibility.
- Theorem A rests on Lemma 2 and Theorem 3H, which are separately verified (programme2_task0.md). The Lean statements are still not done.
- No uniformity, minimality or spreading is used anywhere; this matches the claim.
