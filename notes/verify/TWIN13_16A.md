# Verification of TWIN.md §13 (anchor reduction, padding transfer) and §16.3 (Proposition 16.A)

Code: `compute/verify/twin13_16a.py` (parts 1-3, Theorem C split solver, exhaustive/random), `run16a_scan.py`,
`run16a_fix.py`, `c_excess.py`, `twin16a_complete.py`. Own game model: requester asks S (|S| <= T), adversary
replies a k-set disjoint from S; requester wins iff the 7 replies have no 2-point transversal (x = y allowed).
(`compute/twin/anchors.py` was not reused.)

## Verdicts

| Item | Verdict |
|---|---|
| (1) §13.1-13.2: anchor lemma, Theorem A, padding transfer | PASS |
| (2) §16.3 Prop 16.A | PASS as stated with an unspecified O(1) (see below); the proof as written has a finite-k GAP (line 904), and O(1) cannot be 0 |

## (1) §13: PASS

Checked by hand and by code.
- Lemma 13.1: no common point means each cover point lies in some anchor, so a cover is a pair inside V. Also x = y
  is impossible (it would be a common point). Code: 20000 random tuples with outside points, cover over all points ==
  cover over V == cover of traces on V; enlarging a trace never destroys a cover.
- Creating anchors (lines 518-520): S_2 with |S_2 ∩ B_1| >= k-T gives |B_1 ∩ B_2| <= T; S_3 ⊇ B_1∩B_2 gives
  an empty triple intersection. This needs T >= k/2, which is implicit (T ~ 3k/4). |V| = 3k - p is correct
  (the pairwise intersections are disjoint).
- Quantifiers in Theorem A (ii): a real reply E has E∩S = ∅, so |E∩V| <= min(k, |V∖S|); padding inside V∖S is always
  possible, and by monotonicity (i) an uncoverable padded tuple means the real tuple is uncoverable. This is
  per-play, so it holds for every family and every adversary, including real replies with fewer than min(k,|V∖S|)
  points in V and cases |V∖S| < k. Nothing is lost: V is determined by the real anchors, requests lie in V, and
  the count of rounds is unchanged. Code: part 2 (k=4, T=3, exhaustive for 2 outside points, 30000 samples for
  4 and 6) and part 2b (2942 random adaptive confined plays with arbitrary padding, including |V∖S| < k).
- No reduction loss found. (iii) is correct but should say that extra outside points in a reply are useless by
  the lemma.

Minor errors / remarks for §13
1. Line 559 "Theorem C: |V| <= 2T (+O(1))" has the wrong sign. At finite k it needs |V| <= 2T - O(1) (see below).
2. The transfer needs the confined strategy to be correct against replies of mass exactly min(k,|V∖S|), which
   is how the confined game is defined. This is fine but should be stated.
3. Line 536 "she may keep the anchors among her seven" is correct. The cost of re-anchoring is not part of the
   reduction (not checked).

## (2) Proposition 16.A

Hand check of the algebra is correct: α = N - 2t, |S_2| = α + (t-α) = t, |B_1∩B_2| <= r + α,
|S_3| = 2α + r = 2N+1-5t <= t iff N <= 3t - 1/2. In integers this is exactly n <= 3T - k/2 with no O(1)
(code asserts |S_3| <= T for all B_2). The union of the anchors avoids a_0, so |U| <= n - α = 2T. The requests
and the rest of the argument are as stated, and the replies in V are handled by Theorem A.

Findings.
- GAP at line 904 (integer rounding in Theorem C). With |U| = 2T exactly, "request half of every part" is not
  integral. The exact min-max load of the Theorem C split (solved exactly by DFS) exceeds T in 16.A instances:
  (k,T,n) = (5,4,9), (7,6,13), (7,6,14), (9,7,16), (9,8,17..19) (the code reports the first few failing shapes,
  e.g. (7,6,13): P_12, P_13, P_23, Q's = 2,5,2,0,3,0, |U| = 12 = 2T, load 7 > 6). The worst excess over |U|/2 on
  equal-size anchors is <= 1 (k <= 8, `c_excess.py`). Fix: take the kernel α' = N - 2t + c with c = 1 (the proof then
  needs N <= 3t - 1/2 - c); then |U| <= 2T - c. With c = 1 all tested instances pass (`run16a_fix.py`, 10 instances
  with n <= 3T - k/2 - 1, also c = 2, 3). This is the O(1) of the statement, so the statement is fine if
  read with O(1) >= 1 (proof of the uniform bound is not given in the note; I only observe excess <= 1).
- The O(1) cannot be 0 (exact counterexample to the O(1)-free version): k = 5, T = 4, V = 9 points, n = 9 <= 3T - k/2 = 9.5,
  4T >= 3k. The complete family K(9,5) has tau = 5 > 4, and it is a (7,2)-family: a 7-tuple of edges
  has complements = 4-subsets, and 7 4-subsets of a 9-set cannot cover all 36 pairs (covering number C(9,4,2) = 8;
  `twin16a_complete.py` DFS confirms). So no requester strategy can win there, and the 16.A hypothesis
  must read |V| <= 3T - k/2 - c with c >= 1/2. (K(n,k) counterexamples for the other small (k,T) in the range, k <= 6: none.)
- Minor: for N < 2t, α is negative; clamp α = max(0, ·). Needs N >= 1 + t (replies must exist), t >= 1/2 for
  a_0 ⊂ V∖B_1; "a_0 ⊂ V∖B_1 of mass α" needs |V| - k >= α.
- The statement "seven requests, no discard" is correct (S_2, S_3, then four).

## Not covered
Theorems C/D beyond the finite-k rounding above, 13.3, 13.7 and §16.4+ were not examined.
