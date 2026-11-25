# Verification of notes/MINIMAL_FRAME.md (Lemmas 1, 3, 4, Corollary 5, Statement (G))

Verifier: independent hand re-derivation plus code in compute/verify/minframe.py, minframe_pad.py, minframe_crit.py.
Conventions: "(7,2)" means every at most seven members have a transversal of at most 2 points.
A counterexample is a (7,2)-family of nonempty sets of size at most k with tau > T.

## Verdicts

| Item | Verdict |
|---|---|
| Lemma 1 (padding) | PASS |
| Definition (minimal) | PASS, plus remark A below |
| Lemma 3 (private sets) | PASS, minor wording GAP (remark B) |
| Lemma 4 (saturation) | PASS statement; GAP in proof text (remark C) |
| Corollary 5 (co-edge form) | PASS statement; no proof given in the note (derivation D below) |
| (G) <=> f(k,7) <= (3/4+o(1))k | PASS (remark E) |

No FAIL found. No counterexample to any statement.

## Remarks and the exact points probed

**Lemma 1.** The padded family is (7,2) because any <= 7 padded members are hit by the same <= 2 points as the originals (the original points stay in the members). A transversal X of the padded family becomes a transversal of the original by replacing each private point of B' by any point of B (B nonempty), without growing. So tau(original) <= tau(padded), and equality holds. Tested on 1925 random (7,2)-families: padded family is (7,2) and tau is equal in every case. Only implicit: f(k,7) is defined as max tau over k-uniform (7,2)-families.

**A. Minimality and duplicates.** A minimal counterexample is an antichain with no repeated member. Removing a repeated or containing member keeps tau (a transversal of the rest meets the smaller set, hence the larger) and keeps (7,2), but lowers the size. So "B minus z coincides with another member" cannot occur (see C). Lemma 3 shows no repeats directly as well. Verified by code on every sample (check() flags duplicate or non-antichain; none).

**B. Lemma 3.** Proof is right: H minus B has smaller size, inherits (7,2), so it has a transversal of at most T points, and that transversal cannot meet B. Edge case H = {B}: S = empty set works. Wording GAP, not an error: "S_B contained in K_B" needs S_B inside V (replace points outside V by any point of a member they hit, or drop them) and "S_B not inside K for another co-edge K" needs members distinct (remark A). Both follow in one line.

**C. Lemma 4.** Replacing B by B minus z (|B| >= 2, so nonempty) keeps tau > T, because a transversal of the new family meets B minus z, which is inside B. The size drops, so the new family is not a counterexample, so it fails (7,2). The failing subfamily must contain B minus z, because otherwise it is a subfamily of H minus B, which is (7,2). This holds also in the duplicate case: if B minus z equalled some member B'' of H, the new family would be a subfamily-as-set of H, hence (7,2), contradicting minimality. So the duplicate case is vacuous. Edge case |B| = 1 is excluded by hypothesis (shrinking would give an empty set). GAPs in the proof text only: (i) the line "the failing subfamily must use B minus z" is the whole proof, and part (ii) is not derived. Derivation of (ii): B, B_2..B_m is a subfamily of H with at most 7 members, so it has a transversal X of size <= 2. If X met B minus z, it would contradict (i), so X meets B only in z. Also m >= 3 (fewer than three members always have a 2-transversal), so there are 2 to 6 other members.

**D. Corollary 5 (derivation, since the note gives none).** Set K_i = V minus B_i. A set X of at most 2 points of V is a transversal of B_1..B_m exactly when it is a pair not covered by any K_i (FABLE_C Def 2.1 with x = y allowed; points outside V are useless). With K = V minus B, z in B, and B_2..B_m from Lemma 4:
- (i) says K union {z}, K_2..K_m cover all pairs, which by Lemma 2.3 means U(K_2..K_m) is inside K union {z}. Correct.
- z in U: by (7,2) for B, B_2..B_m there is an uncovered pair {x,y} for K_2..K_m, hence x, y in U; it is not covered by K (it is a transversal of B...). By (ii) it meets B exactly in z, so z in {x,y} inside U. Correct.
- U is not inside any co-edge K' of C (including K itself): otherwise K_2..K_m, K' cover all pairs (Lemma 2.3), i.e. at most 7 members of H without a 2-transversal, contradicting (7,2). Correct.
- |U| >= T+1: if |U| <= T, extend U to a T-subset S of V (possible since |V| > T, V being a transversal). tau > T gives a member B' disjoint from S, so S, hence U, lies in the co-edge V minus B', contradicting the previous bullet. Correct.
- "At most six": the witness has m <= 7 members including B, so at most 6 others. Correct (and at least 2).
- Edge case |V minus K| = 1 is excluded by hypothesis |V minus K| >= 2, matching Lemma 4's |B| >= 2.
All five properties were also checked by code for every witness set (not only one), see below. No failure.

**E. Equivalence with (G).** Using Lemma 1: if (G) holds, any (7,2)-family of sets of size <= k has tau <= T, so f(k,7) <= T <= (3/4+eps)k + 1 for k >= k0(eps); this gives f(k,7) <= (3/4+o(1))k. Conversely if f(k,7) <= (3/4+delta(k))k with delta -> 0, take k0 with delta <= eps; then a family with tau > T cannot be (7,2), so some at most seven members have no 2-transversal. "At most seven" and "exactly seven" agree (pad with arbitrary members; a superfamily still has no 2-transversal, and tau > T >= 2 means there are at least seven members). Needs T >= 2, harmless.

## Exhaustive / randomized tests (code in compute/verify)

Checked on each counterexample H: antichain and no duplicates; Lemma 3 for every B; Lemma 4 existence for every (B, z) with |B| >= 2 by brute force over all subsets of at most 6 other members; Corollary 5 properties (z in U, U inside K union {z}, U not inside any co-edge, |U| >= T+1, at most 6 sets) for EVERY witness set of Lemma 4, not just one. Negative controls (minframe_pad.py) confirm the checker flags non-minimal families.

- **T = 1** (SAT enumeration of all minimum-size counterexamples at k=2,3, ground set 4 to 7, plus locally-minimal ones): the only minimal counterexample is two disjoint singletons, so Lemma 4 is vacuous. 0 failures, but this regime is degenerate.
- **T = 2, k = 4,5 (non-degenerate).** The exhaustive SAT enumeration did not finish for T >= 2 within the time limit, so this part is SAMPLED, not exhaustive. Method: random families, reduced to tau-critical (every proper subfamily has tau <= 2, so (7,2) holds iff there are at least 8 members), then locally minimised (no member removal and no point deletion leaves a counterexample; this is the only property the lemma proofs use). Distinct locally-minimal counterexamples found and checked: k=4, n=8: 953; k=4, n=9: 81; k=4, n=10: 1; k=5, n=9: 271; total 1306. All have 8 members and total size 23 to 32. **0 failures** for Lemma 3, Lemma 4, Corollary 5, antichain and no-duplicates. No such family was found for k=3 (n up to 9), consistent with tau-critical 3-uniform families with tau=3 needing more room; that is a sampling observation only.
- **Lemma 1:** 1925 random families, 0 failures.

## What is not covered
- No exhaustive proof at T >= 2 (only sampling); all non-degenerate samples have exactly 8 members (the smallest case), so configurations with m close to 7 others and many members are not tested.
- Lean formalisation (Task 0, second half) not done.
- Statements about the verified machinery in the Cautions section (non-uniform families) are not examined here.
