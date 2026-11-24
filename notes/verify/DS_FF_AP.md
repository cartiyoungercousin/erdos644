# Independent verification: Theorem DS / DS-b, Lemma FF, Theorem AP (PETAL 20.2, 21.1, 23.1, 23.2)

Verifier's note. Everything below was re-derived from the statements and cited definitions (PETAL §1–§3, §12, §14.1, §20.2, §21.1, §23.1–23.2).
Code is new, in `compute/verify/` (does not import `replay43.py`):
`common.py` (point-set harness, exact 2-cover test, hill-climbing adversary), `ds.py` (DS verbatim + DS-b blind), `dsb_grid.py`, `dsb_tight.py`,
`ap.py` (AP verbatim, asymmetric arenas, optional pool), `ap_arith.py`, `ap_tight.py`, `ap_neg.py`, `ff.py`.
Game model used: request S (|S| <= T), reply = k points disjoint from S, member of H; win = seven replies with no two points hitting all seven
(exact test over membership-type masks). Adversary = priority-vector family (class choice, own part by priority, leak part by priority anywhere
outside S, incl. other arena / pool), random search + hill climbing on (max pair coverage, max request). Strategies are run verbatim and are NOT
truncated: any request above T is counted as a budget violation.

## Verdicts

| Item | Verdict |
|---|---|
| Theorem DS (20.2), delta < t/6 | **PASS** (hand check of every step; 1500 adversary games, 0 budget violations, 0 covers; threshold sharp) |
| Theorem DS-b (21.1), n-1+7delta <= t | **PASS with two minor defects** (strict inequality needed; J' side condition 2mu <= 1-c unverified, but harmless) |
| Lemma FF (23.1), tau <= 1-c-pi(X)+eps | **PASS** (proof is correct; exact check on ~1500 random + hill-climbed families, 0 violations, bound attained) |
| Theorem AP (23.2), t >= 112/151 | **PASS** (hand check; asymmetric arenas and pools replayed, 0 violations; constant 112/151 is sharp for the proof) |

No counterexample, no gap in the main claims. Minor errors/imprecisions are listed at the end.

## 1. Theorem DS (20.2)

Hand check, step by step (A = V_A, F = V_F, n = 1+t/2-delta, replies: >= 1-delta in own arena).
- Petal requests 1–4: V_F part has t/2+eps points, V_A part t/2-eps; total t. Colour F is impossible because |V_F minus S| = 1-delta-eps < 1-delta,
  so every reply is colour A. Empty common intersection: a point of V_A is missed by the petal whose chunk contains it (chunks cover V_A, needs
  4(t/2-eps) >= n, i.e. delta >= 1-3t/2+4eps, true for t >= 2/3 but not written in the proof); a point of V_F lies in the F-part of petal i, hence in
  request i+1..4, so some later petal misses it (request i+1 contains the F-parts of all earlier petals, <= 3delta <= t/2+eps; this is the binding
  condition delta <= t/6).
- Centre requests 5–7: V_F part B minus B_j (<= 8delta/3 <= t/2-eps for delta < 3t/16), V_A part filled to t/2+eps (needs <= 2delta). Colour A impossible
  (V_A has 1-delta-eps free), colour F feasible (n - 8delta/3 >= 1-delta). Total <= t. Trace of C_j on U = A-parts of petals union B: on B it lies
  in B_j (all of B minus B_j is requested), on V_A it avoids the V_A-parts of earlier centres (requested). So Z_1, Z_2, Z_3 are pairwise disjoint on U, and P4(c)
  (three centres with pairwise disjoint traces on U, hence on U*) gives no 2-cover. Pairwise disjointness really needs each B-point requested in
  two of three requests, as stated. The 8delta/3 = (2/3)(4 delta) cost is exactly right.
- Budgets: 3delta <= t/2, 8delta/3 <= t/2-eps, 2delta <= t/2: all correct.
Computation (k=80, T=60, n = k+T/2-d, 300 adversaries each): d = 6, 8, 9, 10: 0 budget violations, 0 covers (all 7 replies uncoverable), no
forcing failures, traces disjoint. d = 11 (> t/6 k = 10): the strategy as written overruns T in 230/300 games ("petal req 3: F-parts 32-33 > t/2+eps"),
so delta < t/6 is exactly the limit of this strategy and the proof's binding term is correctly identified.

## 2. Theorem DS-b (21.1)

Hand check: classes read off by overlap threshold c (same class >= 2(1-delta)-n > c, cross <= 2 delta < c; cross <= 2delta also when leaks go
outside both regions, since X cap Y lies in (X minus R_X) union (Y minus R_Y)). Step 1 (14.1): request min(t/2,|I^X|) + min(t/2,|I^Y|); after three
members of a class |I| <= 1-t <= t/2, fourth member kills I; first request empty so 7 requests give 7 replies, pigeonhole gives four. Step 2: forcing
1-c = n-1+2delta of X_a; reply avoids it so overlap with X_a <= c, so class Y. Cost: |F_j| + |Z_{<j} minus X_a| with |Z minus X_a| <= 2delta + 3delta
(centre parts outside R_Y, plus points of U cap R_Y outside X_a, which lie in the other three petals' parts outside R_X; the union over both centres
counts each once because the second request seals the first trace). Correct.
Computation: strategy run on tight arenas and on larger n (d = 1..5, n up to n_max with n-k+7d <= T): the hill-climbing adversary attains exactly
the predicted step-2 request (n-k+2d+1)+5d in every case (sharp), never a 2-cover. Replay-level threshold d <= t k/12 = 5 at k=80, T=60 confirmed
(d = 6, 7: overruns 67, 73).
Minor defects:
- (21.1, statement) "n-1+7delta <= t" must be strict (or lose eps): forcing needs c strictly below 2(1-delta)-n so 1-c > n-1+2delta. At
  d=5, n=105, k=80, T=60 the request is T+1 = 61 (n-k+7d = T exactly). Immaterial for the application (open condition) but the inequality as written is off by eps.
- (21.1, proof) the line "forcing set F_j contains Z_{<j} cap X_a (mass <= 2mu <= 1-c)" is imported from 14.1 without checking 2mu = 4 delta <= 1-c = n-1+2delta,
  which can fail when n-1 < 2delta. The gap closes: the true cost is max(1-c + |Z minus X_a|, |Z|) <= max(n-1+7delta, 6delta) and 6delta <= n-1+7delta since
  n >= 1-delta. Needs one sentence.

## 3. Lemma FF (23.1)

Proof is correct: every other member Y avoiding the request meets X inside the non-private part (private points lie in no other member), whose mass
1-pi was reduced by the request, so |X cap Y| <= c-eps, contradicting > c; X itself meets the request (nonempty because pi(X) < 1-c when another member exists). The
equal-mass hypothesis ("sets of mass 1") is used and is stated.
Computation (`ff.py`): exact transversal number (branch and bound), 1480 random families (k = 4..9, up to 9 members, overlap threshold random) plus 60 hill-climbed attempts to
maximise tau minus bound: 0 violations; bound k-m-pi+1 attained in 375 families (so FF is sharp). The "single-mass form is false" example checked (complete family: tau
attains the bound with pi = 0); the single-part count (2-3c)/2 = 0.19 at c = 0.54 re-derived (excess 2-3c over four complements covering the ground set,
each triple-covered point contributing excess 2).

## 4. Theorem AP (23.2)

Hand check. Formulas verified exactly by brute force on four small families (all members enumerated): tau_c (in points) = n_c-k+rho_c+1; least same-class overlap
2(k-rho_c)-n_c when there is room. Both cost inequalities re-derived: (i) tau_X + 8rho_X/3 < (8/3)(1-theta) - (5/3)tau_X <= (8/3)(1-theta) - (5/6)t <= t iff 1-theta <= 11t/16 iff
t >= 112/151 (with theta=(6t-2)/5; algebra confirmed); (ii) 2rho_Y + 8rho_X/3 < (14/3)(1-theta)-(7/3)t <= t iff 1-theta <= 5t/7, weaker. Case split correct
(tau_X+tau_Y > t gives one class with tau >= t/2; forced branch costs tau_Y+eps+1/3 < t/2+1/3 <= t). Centre class forced to Y because a set of mass > tau_X inside R_X hits every
member of H_X. Classes disjoint when rho_X+rho_Y < 2(1-theta)-t < 1 (implicit in the statement, true). Trace analysis (B-points in at most one centre, Z_{<j} cap R_X <= 2rho_Y,
centres disjoint on R_X) correct; P4(c) applies.
Constant 112/151: an exhaustive integer search over (tau_X, tau_Y) with rho maximal (`ap_arith.py`) gives slack >= 0 at T/k = 112/151 (k=151: slack 1 point) and
the games at (k,T) = (100,72), (100,70), (151,111) overrun T (62, 91, 2 of 150 games), at (151,112) none. So 112/151 is correct and sharp for this proof.
Computation (`ap.py`): asymmetric arenas (n_X != n_Y, rho_X != rho_Y, tau_X != tau_Y, e.g. tau=(32,44), (85,79), (70,82) rho=(29,17)), with and without a pool of 20-30 extra points, at (k,T) in
{(100,75),(151,112),(200,150),(150,115),(300,225)}: 5000+ adversary games, 0 budget violations, 0 covers, no flags (reply classes unambiguous, forced replies always of class Y, centre traces
pairwise disjoint on U). The hill-climbing adversary reaches the predicted step-2 request max(tau_X+1, 2rho_Y) + (4rho_X - floor(4rho_X/3)) in every instance tried (e.g. 111 against T = 112 at the worst
instance), so the accounting is tight, not merely safe. This covers the "not replayed" items of 23.2 (unequal arenas, leak into a pool).

## Minor errors and imprecisions

1. 23.2: "tau_c = 1-c_c-rho_c (Lemma FF with equality)" is mislabelled. FF with pi = 0 (every member of H_c has no private points) only gives tau_c <= 1-c_c; the value 1-c_c-rho_c
   comes from the direct count tau_c = n_c-1+rho_c (any set of mass > n-1+rho inside R_c hits all members, and fewer cannot). The number is right, the citation is wrong. FF is not used elsewhere in AP.
2. 20.2 does not state that covering V_A by four chunks needs delta >= 1-3t/2+4eps (true for t >= 2/3).
3. 21.1 strictness and 2mu <= 1-c side condition (see section 2).
4. Discretisation: the running-intersection rule "min(1/3,|I|)" must round up (ceil(k/3)); with floor(k/3) one point survives in the fourth member (observed in the first run of `ap.py`, flagged "no empty intersection"). Pure O(1) rounding, covered by the eps in the proof.
5. 23.2: the hypothesis tau(H) > t is used only through tau_X + tau_Y >= tau(H) > t (the "special case 𝒜" has tau_X+tau_Y = t+2eps; fine with eps, but should be stated with eps).
6. 23.2 defines c_c as the least same-class overlap = 2(1-rho_c)-n_c; this formula needs room outside R_c for the two leak parts (pool or other arena, 2 rho_c <= room). If room is short the true least overlap is larger and the
   hypothesis c_c > theta would have to be about the formula, not the true minimum; the proof uses only the formula, so it is consistent as written.
7. The remark "sealing only the common part would extend to 3t/16 [not checked]" in 20.2 was not examined.
