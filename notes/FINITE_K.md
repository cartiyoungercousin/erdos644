# FINITE_K: exact finite-k statements for the items the verifiers flagged

All integers; k = reply size, T = request budget, N = |V|, c = N - k, omega = c - T = N - k - T >= 0. Tags: [proved by hand],
[computed exact]. Code: `compute/finitek/` (run with `py -3.14 <file>`); every script below exits with the numbers quoted.
Sources of the flags: `notes/verify/T_Q_P_slack.md` (P), `TWIN13_16A.md` (16.A), `46_W.md`, `Jprime_J2prime.md`, `DS_FF_AP.md`.

Summary of the thresholds

| Item | exact finite-k hypothesis | what fails outside |
|---|---|---|
| Pool theorem P | 4T >= 3k and 4T != 3k+1 (so epsilon*k >= 1/2 suffices, and so does T = 3k/4 exactly) | 4T = 3k+1: P is FALSE at N = k+T, Z empty (k = 1 mod 4) |
| Prop. 16.A | 4T >= 3k, k+T <= N <= 3T - k/2 - 1 (kernel enlarged by 1) | N = 9, (k,T) = (5,4): no strategy at all |
| Theorem W | 4T >= 3k, 4T != 3k+1, window |W| <= T - ceil(k/2), any k | k = 1 mod 4 with T = (3k+1)/4: false (it contains P's counterexample) |
| DS-b | n - k + 7 delta + 1 <= T (strict form), plus T >= 2 ceil(k/3) | n - k + 7 delta = T: request of T+1 points |
| J' | T >= 2 ceil(k/3); f + 6m <= T with f = k - floor(ck), m = floor(mu k) | k = 1, 4 at T = ceil(3k/4) |
| CORE 46 | L: omega <= T - ceil(k/2); H: o <= 4 omega - 3; one of them always holds | none found (k <= 120) |

---------------------------------------------------------------------------------------------------------------------------
## 1. Pool theorem P (CORE 5)

**Theorem P'.** Integers k, T, N, Z with 4T >= 3k, 4T != 3k+1, k + T <= N, omega <= Z <= floor(N - 3k/2). Against a pool
adversary (K\S inside Z whenever |Z\S| >= c - |S|) she wins in seven requests without discard. In particular it holds whenever
T >= 3k/4 + 1/2 (epsilon k >= 1/2), and also at T = 3k/4 exactly (4 | k). [proved by hand; computed exact]

The proof of CORE 5 goes through verbatim once the real-valued class plan is replaced by an integer plan (below); nothing else
in it uses rounding: lines through o have mass w + m_i + m_j <= c, the other four lines have mass <= T, |L\Z''| = |L| - omega <= T
because |L| <= c, padding exists because N - omega = k + T >= T, and Z\S = Z'' exactly, so the pool rule forces K = S u Z'' contains L.

**Integer plan.** A *plan* is an integer w with Z <= w <= floor(N - 3k/2), V = V_o u C_1 u ... u C_6, |V_o| = w, |C_i| = m_i >= 0, with
(a) w + m_1 + m_2, w + m_3 + m_4, w + m_5 + m_6 <= c; (b) m_1+m_3+m_5, m_1+m_4+m_6, m_2+m_3+m_6, m_2+m_4+m_5 <= T; Z inside V_o.

**Lemma R (rounding).** If 4T >= 3k and 4T != 3k+1 then a plan exists, for every N, Z satisfying the hypotheses.
*Proof.* Note first the two ends of the window for w: w >= N - 2T and w <= N - 3k/2 (these are the real-valued bounds).

*Case A: Z <= N - 2T.* Take w = N - 2T (allowed, since N - 2T <= N - 3k/2 iff 4T >= 3k). Then M := N - w = 2T and the four
transversal sums add to 2M = 4T, so (b) forces all four to equal T; this holds exactly for m = (x,x,y,y,z,z) with x+y+z = T.
(a) reads 2x, 2y, 2z <= c - w = 2T - k, i.e. x,y,z <= T - ceil(k/2). Three nonnegative integers with sum T and each
<= T - ceil(k/2) exist iff 3(T - ceil(k/2)) >= T iff 2T >= 3 ceil(k/2). For even k this is 4T >= 3k. For odd k it is 4T >= 3k + 3,
and for odd k the numbers 4T in {3k, 3k+2} do not occur (parity), so 4T >= 3k and 4T != 3k+1 give 4T >= 3k+3. Take x,y,z balanced.

*Case B: Z >= N - 2T + 1.* Take w = Z <= floor(N - 3k/2). Now M = N - w satisfies 3k/2 <= M <= 2T - 1.
Pair masses: p_1, p_2, p_3 = balanced integers with sum M (each floor(M/3) or ceil(M/3)). (a) needs p_i <= M - k, i.e. the two
smaller pairs sum to >= k: they sum to M - ceil(M/3) = floor(2M/3) >= k because M >= 3k/2. Split each p_i into halves
(ceil(p_i/2), floor(p_i/2)) and choose the position b_i of the larger half. A transversal takes position t_i in pair i and the four transversals
are exactly the t of even parity. Its sum is (M + sum_i s_i d_i)/2 where d_i = 1 for odd p_i (0 for even) and s_i = +1 if t_i = b_i, else -1.
 - 0 odd pairs: every transversal = M/2 <= T - 1/2 so M/2 <= T. 
 - 1 odd pair: both signs occur, max = (M+1)/2 <= T since M <= 2T - 1.
 - 2 odd pairs: the four transversals realize all four sign patterns on them, max = (M+2)/2; here M is even, so M <= 2T - 2 and max <= T.
 - 3 odd pairs (M odd): choose b of odd parity; then every even-parity t differs from b in 1 or 3 coordinates, so at most two signs are +1
   and the sign sum is <= +1, max = (M+1)/2 <= T.
So (b) holds. ∎

**Where it is sharp: 4T = 3k+1 (k = 1 mod 4, T = (3k+1)/4).** Here floor(N - 3k/2) = N - 2T, so w = N - 2T is forced, M = 2T, all
transversals = T, the shape is (x,x,y,y,z,z) and (a) needs x,y,z <= T - (k+1)/2, whose sum is < T since 4T < 3k+3.
No integer plan exists for any (N, Z) [computed exact: 984 of 984 hypothesis-instances with k <= 30, no integer plan, found by brute-force
over all six-class vectors for k <= 13 and the forced shape beyond]. And P itself is false there:

**Proposition 1.1 (counterexample family).** k = 1 mod 4, T = (3k+1)/4, N = k + T, Z empty (omega = 0): the adversary has no freedom (K = S for every
full request), and she needs seven T-sets covering all pairs of an N-set. This is impossible.
- [computed exact] ILP (`pool_counterexamples.py`, HiGHS): infeasible for (k,T,N) = (5,4,9), (9,7,16), (13,10,23), (17,13,30), (21,16,37);
  feasible for the controls 4T = 3k+3: (3,3,6), (7,6,13), (11,9,20), (15,12,27).
- [proved by hand, using ROADMAP 0.1: for N < 11k/6 every pair-covering seven is a Fano blow-up (here N = (7k+1)/4 < 11k/6); every point type then contains a line]. Seven sets of size T cover
  7T = 3N + 1 incidences, every type has >= 3 elements, so all types are lines except one point x_0 of type (line l_0) + {q}. Let u_l = #points of type l
  (x_0 counted in l_0). Each set has exactly T points, so sum_{l contains p} u_l = T - [p = q] for every Fano point p. The incidence matrix has
  M M^T = 2I + J, so u_l = (sum_{p in l} s_p - N)/2 with s_p = T - [p = q], i.e. u_l = (3T - N - [q in l])/2. Lines through q and lines missing q give
  different parities, so u cannot be integral. ∎
The status of P for 4T = 3k+1 and N > k+T is not decided here (no plan of the proof's shape exists; other shapes untried).

**Tests** (`pool_rounding.py 30 3`): [computed exact] for every k <= 30, T from ceil(3k/4) to k+3, N from k+T to 3k+2, every Z in the hypothesis range:
48864 instances with 4T >= 3k, 4T != 3k+1: the explicit plan of Lemma R satisfies (a), (b), w in range, in all 48864 (0 failures); 3 random
pool plays each (the 7 requests of the proof against a random pool adversary, Z-last and random modes, K built verbatim, all pairs of the seven
co-edges tested): 0 failures. (The earlier verifier scan agrees: failures only at T = (3k+1)/4.)

---------------------------------------------------------------------------------------------------------------------------
## 2. Proposition 16.A and Theorem C (TWIN 13.4, 16.3)

**Theorem C'.** Let B_1, B_2, B_3 be replies with empty triple intersection, U = B_1 u B_2 u B_3, and suppose |U| <= 2T - 1. Then four
requests S_4..S_7 inside U, each of size <= T, chosen in advance, force that the seven replies have no 2-cover. [proved by hand; computed exact]

*Proof.* Name the parts P_12 = B_1 n B_2, P_13, P_23 (pairwise disjoint) and Q_1, Q_2, Q_3 (points in exactly one anchor); sizes
a, b, c, q_1, q_2, q_3, sum U. By TWIN 13.3 (Theorem B) it suffices that every required pair of points has intersecting request-sets,
where a point's request-set is {i : the point is in S_i}. Use the vertices of K_4 = {4,5,6,7} as requests and give each point an *edge* of K_4 as
request-set. The three perfect matchings are M_1 = {47, 56} (for P_12), M_2 = {46, 57} (P_13), M_3 = {45, 67} (P_23).
P_ab uses edges of its own matching; Q_c (the part opposite P_ab) uses edges of the other two matchings; two edges of K_4 are disjoint only if
they are the two edges of one matching. So a point of P_ab and a point of B_c (which lies in P_ac, P_bc or Q_c) never have disjoint edges:
P_ac, P_bc use other matchings; Q_c uses edges not in M_ab. Hence all pairs required by Theorem B are covered, as in TWIN 13.4.
Integer loads. Route Q_1 to M_1, Q_3 to M_2, Q_2 to M_3. Then matching j carries W_1 = a + q_1, W_2 = b + q_3, W_3 = c + q_2 points, sum U.
Put x_j on the first edge and y_j on the second edge with x_j + y_j = W_j, x_j = (W_j + e_j)/2, e_j = 0 if W_j is even and e_j = +-1 if odd.
The load of 4,5,6,7 is (U + e_1+e_2+e_3)/2, (U - e_1 - e_2 + e_3)/2, (U - e_1 + e_2 - e_3)/2, (U + e_1 - e_2 - e_3)/2. If the number of odd W_j is
 0: all loads U/2; 1: (U+1)/2 at most; 2: (U+2)/2 at most; 3: choose e = (1,1,-1), all loads <= (U+1)/2.
The count of odd W_j has the parity of U. So for U odd the maximum is <= (U+1)/2 <= T when U <= 2T - 1, and for U even it is <= U/2 + 1 <= T when U <= 2T - 2. ∎
*Remark (U = 2T).* All four loads equal T iff every W_j is even: with e_j in {0, +-1}, the four loads equal U/2 iff e_1+e_2+e_3 = 0, e_1+e_2 = e_3, e_1 - e_2 = e_3... i.e. e_1 = e_2 = e_3 = 0.
Moving a unit of Q_c between its two matchings changes the parity of two W_j, so U = 2T works exactly when the parities can be repaired this way; in general they cannot (below).

**Proposition 16.A'.** Integers k, T, N with 4T >= 3k and k + T <= N <= 3T - k/2 - 1 (i.e. 2N <= 6T - k - 2). If all replies lie in a known N-set V she wins
in seven requests without discard. [proved by hand; computed exact]

*Proof.* Let alpha = max(0, N - 2T + 1) (the original kernel N - 2T enlarged by 1, clamped). B_1 arbitrary; fix a_0 inside V\B_1 with |a_0| = alpha
(room: |V\B_1| = N - k >= alpha = N - 2T + 1 iff 2T - 1 >= k, true for 4T >= 3k). Let S_2 = a_0 u (min(k, T - alpha) points of B_1);
|S_2| <= T since alpha <= T (as N <= 3T - 1). Then |B_1 n B_2| <= max(0, k - T + alpha). S_3 = a_0 u (B_1 n B_2), of size
<= 2 alpha + k - T <= 2N - 4T + 2 + k - T <= T iff N <= 3T - k/2 - 1 (if alpha = 0 then |S_3| <= k - T <= T). B_3 misses S_3, so B_1 n B_2 n B_3 is empty, and B_1, B_2, B_3 avoid a_0, so
U <= N - alpha = 2T - 1 (or U <= N <= 2T - 1 when alpha = 0). Theorem C' finishes with four non-adaptive requests (Theorem A of TWIN 13.2 covers replies
outside U). ∎

**Why +1 is needed and what is exact.** At (k,T,N) = (5,4,9): N <= 3T - k/2 = 9.5 but the complete family has no seven-cover (C(9,4,2) = 8), so no strategy exists; this is the
case omega = 0, 4T = 3k+1 of Prop. 1.1 as well. The O(1) of the statement is therefore exactly "1": the proof gives N <= 3T - k/2 - 1; it gives nothing in the strip 3T - k/2 - 1 < N <= 3T - k/2
(that strip is where Theorem C meets U = 2T, which the Remark above shows can genuinely fail with the fixed routing; whether a different routing/strategy works there is not decided).
For k odd the integer form is N <= 3T - (k+3)/2, for k even N <= 3T - k/2 - 1.

**Tests** (`twin16a_fix.py 5 26 150`): [computed exact] Part 1: all 7274 part-size vectors (a,b,c,q_1,q_2,q_3) with T <= 5 and U <= 2T - 1: loads <= T and every Theorem-B pair intersects, 0 failures
(for U = 2T with the fixed routing 3528 of 4899 vectors have a load > T, which is why the +1 is needed in general). Part 2: end-to-end 16.A', 949 (k,T,N) with k <= 26, 4T >= 3k,
k+T <= N <= 3T - k/2 - 1: 142350 plays against random and overlap-maximising adversaries (B_2 takes as much of B_1\S_2 as possible, B_3 as much of B_1 u B_2), the final seven replies checked over all pairs x <= y of V: 0 two-covers. (The adversary after round 3 is random: the proof, not the test, covers the worst case.)

---------------------------------------------------------------------------------------------------------------------------
## 3. Exact finite-k hypotheses for the other flagged items

### 3.1 Theorem DS-b (PETAL 21.1) [proved by hand; computed exact on the strategy]
In points: reply of a class has >= k - delta points in its region, regions of size n, same-class overlaps >= 2(k - delta) - n, cross overlaps <= 2 delta.
The forcing set has f = n - k + 2 delta + 1 points (the +1 is the strictness: forcing needs the overlap bound c strictly below 2(k - delta) - n). The step-2 request is
F_j u (Z_{<j} \ X_a), of size max(f + 5 delta, 6 delta) = n - k + 7 delta + 1, because 6 delta <= n - k + 7 delta + 1 iff n >= k - delta - 1, true when n >= k - delta
(arithmetic checked identically, `small_hyps.py`; this is the missing "2 mu <= 1 - c" sentence of the verifier). Hence

 **DS-b (this proof) needs  n - k + 7 delta + 1 <= T**, i.e. the strict inequality n - k + 7 delta < T, together with Step 1 (3.3): T >= 2 ceil(k/3).

[computed exact] `compute/verify/dsb_tight.py` (k = 80, T = 60, hill-climbing adversary, 10 tight settings): the largest step-2 request equals n - k + 7 delta + 1 in all ten, e.g.
(delta,n) = (5,105), (4,112), (3,119) give 61 = T + 1 (budget overrun, hypothesis n - k + 7 delta = T violated), (4,106) gives 55, (2,128) gives 63.

### 3.2 Theorem W (CORE 47.2) for every residue of k [proved by hand; computed exact]
**Theorem W'.** Integers k, T, n with 4T >= 3k, 4T != 3k+1, n >= k + T. If the selector sigma depends only on S n W with |W| <= T - ceil(k/2) (any number of classes, any orders; the rule replies
S u (first c - |S| unrequested points of the class order)), she wins in seven requests. The bound T - ceil(k/2) equals T - k/2 for even k.
*Proof.* Kernel size h = floor(n - 3k/2), omega = n - k - T. Room: h - omega = T - ceil(k/2) >= |W|. Use the plan of Lemma R with w = h (it exists by the same case analysis: h = n - 2T gives Case A when 4T = 3k;
otherwise h >= n - 2T + 1, Case B). Let r = sigma(any request containing W), Z = first omega points of V\W in the order of r, kernel kappa = W u Z u filler (size h), petals = the plan's classes.
Requests S_i = (kappa u P_i)\Z **padded with points outside kappa u P_i to exactly T points** (the padding is outside L_i, hence requested points only delay nothing: Z still precedes every
unrequested point). All S_i contain W, so sigma(S_i) = r (the selector never reads |S|; this removes the "sizes T, T, T-1" worry of verifier remark 2 for odd k); the reply is S_i u Z = kappa u P_i (|S_i| = T so exactly omega points are added). Four transversal requests (plan (b)) finish by 1.3(ii). ∎
*Other residues of k, T = ceil(3k/4):* k = 0 mod 4: Case A (T = 3k/4), fine. k = 2 mod 4: 4T = 3k+2, Case B. k = 3 mod 4: 4T = 3k+3, Case B. k = 1 mod 4: 4T = 3k+1, **no frame, and W is false**:
at n = k + T, omega = 0, every greedy rule answers K = S (there is no choice), so the Prop. 1.1 counterexample applies to every selector. For k = 1 mod 4 the theorem is true from T = (3k+5)/4 on. This repairs verifier gap 1 (the 36/36 "noplan" cases) and replaces "exact for 4 | k".
[computed exact] `thmW_frames.py 30`: for k <= 30, T = ceil(3k/4)..+2, all n in [k+T, 3k+2]: frames exist in 1713 cases, none in 168, and all 168 have 4T = 3k+1; the real rule (random class table on S n W, a random order per class,
window |W| in {0, half, T - ceil(k/2)}) applied verbatim to the real requests: 10240 runs over all four residues of k mod 4, every pencil line inside the actual reply, all pairs covered: 0 failures.
Still outside W (unchanged): selectors reading |S|; non-greedy rules; thresholds only upward.

### 3.3 Theorem J' (PETAL 14.1) [proved by hand; computed exact arithmetic]
*Step 1 (running intersections).* Each round she requests a = ceil(k/3) points of I^X and a of I^Y (if smaller, all of it): total 2 ceil(k/3) <= T is needed. A class with three members has |I_3| <= k - 2a <= a, so its fourth member misses I,
and with seven replies in two classes one class has four members. So the hypothesis is **T >= 2 ceil(k/3)** (equivalently 3 floor(T/2) >= k; this is the integer form of t >= 2/3, which the verifier found missing).
It follows from the global T >= ceil(3k/4) except for k = 1 and k = 4 [computed exact, k <= 5000; for k = 3m+1 >= 16 it is the inequality 9m+3 >= 8m+8]. So J', J'' need "T >= 2 ceil(k/3)" as an explicit hypothesis.
*Step 2.* Same-class overlap >= floor(ck) + 1, cross <= m := floor(mu k). Forcing set F of f = k - floor(ck) points of X_a (the reply then overlaps X_a in <= floor(ck), hence is of class Y). (J') in integers: **f + 6m <= T**
(worst case |Z_i \ X_a| <= 3m). Side condition F contains Z_{<j} n X_a (<= 2m points) i.e. 2m <= f: it follows, because a legal adversary needs 2f > T (else f points of X_1 and f of Y_1 form a legal request with no reply),
so f + 6m <= T < 2f gives 6m < f.

### 3.4 CORE 46 (ordered frozen anti-plan) [proved by hand; computed exact scan]
Notation: omega = c - T, cells O (o points), U (|U| = 2(c - o) >= 2 omega, hence o <= T), g >= 0, and o >= 2 omega.
- **L-pencil** applies iff the kernel holds U_1 u (omega points of O): floor(n - 3k/2) >= 2 omega, i.e. **omega <= T - ceil(k/2)** (= T - k/2 for even k, exact).
- **H-pencil** needs each of the three petals to hold at most omega - 1 points of O\O_1: o - omega <= 3(omega - 1), i.e. **o <= 4 omega - 3** (the stated "o < 4 omega" is not enough).
- **Exhaustion:** if L fails then omega >= T - ceil(k/2) + 1, and o >= 4 omega - 2 would give o >= 4T - 2k (odd k) or 4T - 2k + 2 (even k), which exceeds T because 3T > 2k;
  contradicting o <= T. So L or H always applies, also for odd k.
[computed exact] `small_hyps.py`: k = 4..120, all T = ceil(3k/4)..k+2, n in [k+T, 3k+2], all o in [2 omega, T] with g >= 0: no instance where neither L nor H applies (0), and none where L fails and o in {4 omega - 2, 4 omega - 1}.
The additional room conditions of the H-branch (kernel mass >= n - 3k/2 - omega from |U| + |g|; petal capacity) were checked by `compute/verify/v46.py` for even k only (1606/1606); they are not re-derived here, and odd k is untested.
Rule is defined for |S| = T only, so "well defined" is used for pencil requests only (verifier remark 4).

---------------------------------------------------------------------------------------------------------------------------
## 4. Files
- `compute/finitek/pool_rounding.py`: Lemma R (explicit plan), exhaustive hypothesis scan, pool plays, no-plan count at 4T = 3k+1.
- `compute/finitek/pool_counterexamples.py`: ILP, Prop. 1.1 (needs `pulp`, `highspy`).
- `compute/finitek/twin16a_fix.py`: Theorem C' part sizes and end-to-end 16.A' plays.
- `compute/finitek/thmW_frames.py`: Theorem W' frames and the real greedy rule for all residues.
- `compute/finitek/small_hyps.py`: J' Step 1, DS-b cost identity, CORE 46 exhaustion.

LEDGER entries to change (not edited here): Pool theorem P -> "VERIFIED at finite k for 4T >= 3k, 4T != 3k+1 (FINITE_K 1); false at 4T = 3k+1"; 16.A -> "N <= 3T - k/2 - 1, proved (FINITE_K 2)";
Theorem W -> "any k with 4T != 3k+1"; J' -> "hypothesis T >= 2 ceil(k/3)"; DS-b -> "n - k + 7 delta + 1 <= T"; CORE 46 -> "L: omega <= T - ceil(k/2); H: o <= 4 omega - 3; exhaustive".
