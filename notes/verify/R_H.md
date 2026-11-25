# Verification of Theorem R (CORE 57.2) and Theorem H (58.1)

Code: `compute/verify/rh_check.py` (independent; does not import compute/core9). Parts: A counting/exponent, B Monte Carlo
moments at (8,6,16), B2 exhaustive-ish small cases, H (MILP over one kernel), H2 (Kleitman set + 1 half, then 55.2 completion),
W (verbatim greedy rule: star hitting, window case, 55.1 criterion).

## Theorem R: PASS

Hand re-derivation of every step, then computation.
- F, D. F = C(k+T,T)C(T,k/2)C(k,k/2)/6 equals the enumerated number of perfect sunflowers on k+T points: 105 at (4,3), 420 at (4,4),
  525 525 at (8,6) (by explicit enumeration). Every request lies in exactly D = C(T,k/2)C(k,k/2)/2 frames (checked 9, 18, 525).
  3D/F = 9/C(k+T,T) (0.257, 0.129, 0.003) exact.
- Bijection head frames <-> perfect sunflowers on V minus B_r: S_i = (kappa u P_i) minus B_r has |S_i| = n - 3k/2 + k/2 - omega = T,
  kernel kappa minus B_r of size T - k/2. Correct.
- "Two distinct frames share at most one request": checked by enumeration at (4,3), (4,4), (8,6): no pair of requests lies in two frames.
- Covariance cases: (i) no common request, independent; (ii) common request, r != r': events disjoint, Cov <= 0; (iii) same class, one
  common request, P = R^-5. Var X <= E X + R*3FD*R^-5, Chebyshev gives R^2/F + 3D/F. All correct. The "6-wise independence suffices" claim
  is right: at most 6 distinct requests enter any joint probability used (3, 5, 6). The marginal must be exactly 1/R for the equal-marginal
  bound; the non-uniform variant (1+3D)/E X is also right (P(A and A') <= P(A) on a shared request).
- Exponent. Phi = (1+t)h(t/(1+t)) + t h(1/(2t)) + ln 2 recomputed: Phi/2 = 1.1828 (t=.75), 1.1925 (t=.76), 1.2295 (t=.8), 1.2586 (t=5/6).
  rho(k) = ln F/(2k) = 0.823 (k=8), 1.082 (k=40), 1.145 (100), 1.178 (400), 1.1906 (4000; t=.76). All match the note.
  Number of requests exponent: 1.226 (N=1.8), 1.374 (N=2.1), 1.435 (N=2.24): matches "1.22..1.43".
- Monte Carlo at (8,6,16), independent uniform sigma, R=16: mean X = 2065 (heads random) and 2059 (all heads equal) vs F/R^2 = 2053;
  Var 7973 and 1542, both below the bound 14683. Min X > 0 in all samples.
- Small cases (4,3,n=8,9,10) and (4,4,9), R = 2..12, random and equal heads, 2000 samples each: empirical P(X=0) never exceeded the bound
  (e.g. (4,3,8), R=6: 0.068 vs 0.60; R=8: 0.207 vs 0.867). No violation.
- (A run of the 6-wise-independent GF(2^14) degree-5 hash selector and R = 64..1024 was started but did not finish on the loaded machine;
  not needed for the PASS, which rests on the proof.)

Minor (not errors):
1. "R >= e^{(1.19 - o(1))k}" is 1.183 at t -> 3/4 and 1.259 at t -> 5/6; 1.19 is the t = 0.76 value. Say "about 1.18 or more".
2. Theorem R, like its proof, concerns random selectors only; "the adversary loses" is a probabilistic statement, not about deterministic ones
   (the note says so in 58/59).
3. 57.2's marginal condition "P(sigma(S)=r) = 1/R for every S disjoint from B_r, for all r simultaneously" needs sum over admissible r at most 1;
   fine, but a request disjoint from all R heads forces sum = 1 exactly, so the assumption is only consistent as stated, which it is.

## Theorem H: PASS (with one wording gap in the greedy/W remark)

- Averaging. Halves of V minus kappa: 3k/2 points, C(3k/2,k/2) halves, each in exactly d = C(k,k/2)/2 partitions (verified at k=4, 8:
  15 halves/15 partitions and 495/5775). Pencil-free needs every partition to contain a non-member, so (#partitions) <= m*d, i.e.
  m >= #halves/3; hence members > 2/3 gives a pencil. Correct, strict inequality used correctly.
- Sharpness / adversarial. MILP maximum pencil-free member set over one kernel: 10 (k=4), 330 (k=8), exactly 2/3 of the halves and
  equal to Kleitman's C(3k/2-1,k/2). The extremal set (halves avoiding one point) is pencil-free, and adding ANY single further half creates a
  pencil (checked for all halves, k=4 and 8). So the threshold is exactly right and cannot be improved by a near-threshold selector.
- Pencil -> good seven (55.2). The three quarter-patterns argument: patterns 000,011,101,110 restricted to any two petal coordinates give all four
  combinations, so every pair across two petals lies in one of the four requests, hence in its reply (superset); pairs inside a petal or involving kappa
  lie in a line. Machine check: 20 pencils (Kleitman set + 1) at (8,6,16) and k=12, T=9, n=25, with random replies containing the requests and random padding:
  all pairs covered every time (0 failures). Needs 4|k and T >= 3k/4 (stated).
- Star hitting for greedy rules and W as a special case. Verbatim greedy rule at (8,6,16) with R in {2,3,8} classes, random orders, random window
  W of size 0..2 = T - k/2: in 300/300 instances every one of the 495 lines over kappa is a member (density 1 > 2/3). 55.1 criterion
  (member iff some class c, omega-set Z inside J_c(K), sigma(K minus Z) = c) vs. the definition: 1500/1500 agree.

Gap (wording only, 58.1 "For greedy rules" + "Theorem W is the case..."): for W one needs the omega-set Z inside J with Z disjoint from W
(otherwise the request loses its W-trace); this requires |J minus W| >= omega, i.e. take J with omega points outside W, and
|J u W| <= omega + |W| <= n - 3k/2 is exactly the |W| <= T - k/2 condition. The note states "|J| >= omega" only; it should say "J contains omega points outside W".
Correct as used in 47.2, verified above.

No counterexample to either theorem. Not committed.
