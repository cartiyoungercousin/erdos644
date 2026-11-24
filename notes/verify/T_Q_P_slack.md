# Verification: slack count (§2), Theorem T (§3), Theorem Q (§4) vs Q' (§37), Pool theorem P (§5)

Definitions used: CORE.md §1 and §33. Code: `compute/verify/tqp_verify.py` (modes S, T, Q, P, R), `scan_round.py`,
`cover7_ilp.py`, `neg_control.py`. All finite-k, integer: |V| = N, c = N-k, requests |S| <= T, k+T <= N; a win means
all pairs {x,y} (x = y included) lie in a common reply.

## Verdicts

| Item | Verdict |
|---|---|
| (1) Slack count §2.1-2.3 | PASS (minor remarks below) |
| (2) Theorem T §3 | PASS |
| (3) Theorem Q §4, and Q = Q' | PASS (one-direction theorem); the "iff" in §33 is only relative to the scheme (minor) |
| (4) Pool theorem P §5 | PASS in the first-order regime (epsilon fixed, k large). **FAIL as literally stated for every integer k** (counterexample below) |

## (1) Slack count

By hand:
- 2.1: sum |I_x| = 7c, so sum(|I_x|-3) = 7(N-k) - 3N = 4N - 7k = 4 delta. OK. A co-type {i,j} needs K_i u K_j = V, which
  needs 2c >= N; for N < 2k this fails, and |I| = 1 would need K_i = V. OK.
- 2.2: sum|L_i| = 3N, |L_i n S_i| <= |S_i| <= T gives sum|L_i \ S_i| >= 3N - 7T = 3 delta - 7 eps. OK.
  The conclusion "at least three replies with L_i not inside S_i when delta > 5 eps" is correct, and is true for any requests (also
  non-full ones): if at most two replies had L_i not inside S_i, then 3N <= 2c + 5T, i.e. N <= 5T - 2k. The text's justification
  ("a reply to a full request contributes at most omega") only covers full requests; the contrapositive above removes that need.
- 2.3: slack q(N-1) + (7-q)t - 3N = (q-3)(N-7/4) + (7-q)eps, checked symbolically for q = 3, 4, 6. OK.
- Parenthetical 5T-2k: N - 2t <= (t+N-2)/2 iff N <= 5t - 2, arithmetic OK.

Code: `S` mode, 20000 random sevens (waste identity exact; every co-type of a winning seven on N < 2k has |I| >= 3), and
7556 (Fano blow-up seven, random 3-subsets l(x), random requests |S_i| = T) triples for 2.2: the inequality
sum|L_i \ S_i| >= 3N - 7T and the "three replies" claim hold in all.

## (2) Theorem T: PASS

Hand check: the seven cells a, b, d, e1, e2, e3, g are the Fano points with lines abe1, ade2, bde3 (K_1..K_3) and ae3g, be2g,
de1g, e1e2e3 (K_4..K_7); all 21 pairs occur once. Every cell lies in the three co-edges of its pencil (a in K_1, K_2, K_4 etc.), and
kappa_4, kappa_5, kappa_6 lie in K_1, K_2, K_3 plus K_4, K_5, K_6, which contain the pencils of a, b, d respectively. Budgets are exactly
the four stated inequalities. All 8 cells partition V. Closed form (kappa = 0): a + e3 + g = 2a + 2k - N and sum e_i = 3(N-k) - 2(a+b+d),
the stated window and the x_ij form, and the three special points N = 7k/4, 2k, 3k-T, all reproduced.

Code: (a) all 72289 integer cell vectors (k <= 12, all T, N) : hypotheses of T <=> the closed-form inequalities, 0 mismatches.
(b) every integer cell vector meeting the hypotheses for k <= 8, N up to 3k+2, T from 3k/4 - 1 up (including kappa > 0 with greedy
split, tight instances with equality in a request or e1+e2+e3 = T): 23064 plays, adversary = random supersets plus hill-climbing
to maximise uncovered pairs; 0 failures, 3303 boundary instances. Power control (`neg_control.py`): dropping one point from a tight
request lets the adversary win in 29 of 29 tried cases.

Minor: the edge-language sentence omits kappa_4 in S_4 (S_4 = (B1 n B2) u (only B3) u kappa_4); replies may coincide with K_1..K_3
(harmless, fewer than seven distinct members is fine since adding members only helps).

## (3) Theorem Q and Q'

Hand check of the proof: dual labelling, K_1..K_4 = a quadrangle, K_5, K_6, K_7 on its diagonal line. Co-type {1,2}/{3,4} completes only with 5,
{1,3}/{2,4} with 6, {1,4}/{2,3} with 7; |I| <= 1 needs the whole line 567; |I| >= 3 needs any one of 5, 6, 7. So request r must contain
c(m_r) + s_0 + s_1 + tau_r. Load identity: sum of loads = 4k - N + W, re-derived (sum|K_i| = 4c, N = sum of cells), exact.

Q vs Q': 4c - 2N = W - 2 sigma gives W = 2N - 4k + 2 sigma, so 4k - N + W <= 3T iff N + 2 sigma <= 3T iff sigma <= (3t-N)/2, and "pair-only
mass of the matching" = c(m). The two statements are the same theorem. Asserted equal, together with both identities, on 9761
random quadruples (2090 satisfying the hypotheses, k <= 9). On those 2090: tau split built at integer level, three requests applied verbatim,
7 replies tested with hill-climbing adversary; 0 failures.

Minor: (i) §33 says "iff W <= delta + 3 eps and loads <= t": the theorem in §4 is only the "if" direction. The "iff" is true for the scheme (fixed quadrangle
labelling, completion rules above) and needs the loads to be the base loads c(m_r) + s_0 + s_1 (each <= t) and W <= delta + 3 eps. (ii) §37 "the tau-distribution
exists iff the first inequality holds" also needs base_r <= t for each r. (iii) §4 proof does not say why the request budget of 5, 6, 7 is
all that is needed (a request only guarantees S_r in K_r), but it is clear.

## (4) Pool theorem P

Proof steps checked: w_o range nonempty iff T >= 3k/4 (N - 2T <= N - 3k/2); lines through o have mass (N+2w_o)/3 <= c iff w_o <= N - 3k/2;
other four <= (N - w_o)/2 <= T iff w_o >= N - 2T; |L \ Z''| = |L| - omega <= T since |L| <= c; padding exists (N - omega = k + T >= T) and avoids Z'', so
Z \ S = Z'' exactly, the pool rule binds with equality (|Z \ S| = omega = c - |S|), K \ S is inside Z \ S with |K \ S| = omega, hence K = S u Z'' contains L. Fano/1.3(ii) finishes.
Code: 6000 plays at integer plans (random Z, random pool adversaries free outside the rule), 0 failures.

**FAIL at literal finite k: rounding.** The proof needs six classes of mass (N - w_o)/6 and integer masses do not exist in some cases.
Counterexample to the theorem as stated: (k, T, N, |Z|) = (5, 4, 9, 0). Hypotheses hold: T = 4 >= 3.75, k + T = 9 <= N, omega = c - T = 0 <= |Z| = 0 <= N - 3k/2 = 1.5.
With omega = 0 the pool rule forces K = S for every full request, so she wins iff seven 4-subsets of a 9-set cover all 36 pairs. They cannot (covering number
C(9,4,2) = 8; confirmed with an exact ILP in `cover7_ilp.py`, which also says YES for the controls (4,3,7), (6,5,11), (8,6,14), (7,6,13), (5,4,10)).
The same happens for the infinite family k = 1 mod 4, T = (3k+1)/4 (that is, epsilon k = 1/4), N = k + T, Z = empty: ILP infeasible for (9,7,16), (13,10,23),
(17,13,30). Scan of the integer version of the proof (`scan_round.py`, k <= 30, all T >= 3k/4, N up to 3k+2, all |Z|): no integer plan exists exactly for
T = (3k+1)/4 (and k = 1, T = 1); there is one for every T >= 3k/4 + 1/2 tested. So the statement is correct whenever epsilon k >= 1/2 (checked k <= 30, not proved for all k),
and false at epsilon k = 1/4. Required fix: state hypothesis T >= 3k/4 + 1/2 (or divisibility), and add a one-line integer rounding lemma. In the first-order
language (masses in units of k, epsilon fixed, k >= k_0(epsilon)) this is harmless.

## Minor errors list

1. §2.3 anchors: "p = 3 - N + kappa, q = 2N - 3 - 2kappa" are the masses of the single and pair parts respectively (check: N = kappa + p + q and 3(N-k) = 3 kappa + pair*2 + single).
   The text says "pair parts p, single parts q"; labels swapped relative to the TWIN notation as quoted. 2p + q = 3 holds with the numbers as written.
2. §2.2 "a reply to a full request contributes at most omega": implicit full requests; claim true anyway (see above).
3. §2.2 parenthetical (kernel >= N - 2t, S_3 contains kernel u (V minus K_1 u K_2)) is stated without proof; only the arithmetic was checked.
4. §3 edge language omits kappa_4 in S_4.
5. §33 and §37 "iff" statements for Q/Q' (see (3)).
6. §5 Theorem P: integer rounding (see (4)); also "|Z| <= N - 3/2" in §33(2) is k = 1 units (N - 3k/2).
