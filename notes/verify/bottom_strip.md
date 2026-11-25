# Verification of CORE §90-§94 (bottom strip, Frankl-Rodl route)

Code: `compute/verify/bottom_strip.py`, `compute/verify/bottom_strip_fr.py` (independent of `compute/strip/`).

## (i) Certificate: PASS
- Hand re-derivation of the Fano placement: L_2 = 2o+2-N-y, L_3..L_6 = (y+N-o)/2. All five <= t for some y in [0,o]
  iff N-2t <= o <= 3t-2 (the only other constraint, o <= N+t-2, is implied for N >= 2t). Every class lies on a line
  whose three points are all in the point's co-type, so I_x contains a line. Z != empty iff N <= 5t-2. Correct.
- Parity rule 90.2 re-derived: k even o=n-2T gives loads (n-4T+2k, T,T,T,T); k odd o=n-2T+1 gives (n-4T+2k+2, T, T-1, T-1, T). Correct.
- Brute force: explicit seven sets (K, K', five padded L_j with random fill), every pair incl. x=y checked, K and K'
  verified to have size c and |K cap K'| = o. All k in 8..40, all T > 3k/4, every n in the strip (odd k: minus 2):
  986 triples, 0 failures. Just above the even/odd cutoff the recipe overloads (as expected).
- Exhaustive integer search over all Fano-shaped cell assignments (k=9,T=8; 11,10; 13,11): feasible exactly up to
  n = 5T-2k-2 for odd k, infeasible at -1, 0 above. Matches 90.2.

## (ii) Density: PASS
- |F| >= C(n,T)/C(c,T) (each member holds C(c,T) T-sets, all C(n,T) must be covered). The identity
  C(n,T)/C(c,T) = C(n,c)/C(n-T,c-T) checked algebraically. c-T = omega*k <= 4 eps k, so
  ln C(n-T,c-T) = O(eps ln(1/eps)) k. Padding costs ln[C(n+m,c)/C(n,c)] <= m ln(n/k)-ish = O(eps) k.
- Numerics r (exact binomials): eps=.04 .27, .02 .18, .01 .11, .005 .064, .002 .030 (both parities). Matches the log.
- Minor: for n in [7k/4, 7k/4+eps k) one has c < T and no T-covering family exists; the statement is vacuous there (fine).

## (iii) Frankl-Rodl application: PASS (modulo the cited theorem; one citation nit)
- Read arXiv 1402.6294v1 (pdftotext of the PDF). It is "Theorem 1 (Frankl-Rodl). Let alpha, eps in (0,1), eps <= alpha/2.
  k = floor(alpha n), l in [max(0,2k-n)+eps n, k-eps n]. Every l-avoiding A in C([n],k) has |A| <= (1-delta)^n C(n,k),
  delta = delta(alpha, eps) > 0." "l-avoiding" = |A cap B| != l for all A,B in the family. Matches the notes' statement
  (numbering "Thm 1.1" is the journal's; arXiv v1 calls it Theorem 1; no change in content). No explicit "n large" clause,
  but delta only depends on (alpha, eps).
- Hypotheses: alpha = 3/7, eta = 1/14 <= alpha/2 OK; c = floor(3(n+m)/7) holds exactly for m = ceil(7c/3)-n (asserted at
  all sampled points); 2c-n' < 0, so the range is [n'/14, c-n'/14]. Integer check of l = n-2T (even k) / n-2T+1 (odd k)
  inside that range: 0 violations for eps in {.04..002}, both parities, whole strip.
- Padding by isolated points preserves all intersections and the member size; density is computed in C(n+m,c) as the notes
  do; the exponent loss is the O(eps) term above. delta(3/7,1/14) is an absolute constant, so eps_0 is absolute (ineffective).
- Monotonicity: a T'-covering family is T-covering for T<=T', so CP at small eps gives it at all larger eps for the same N
  (N-7/4 <= 5 eps_0). This is used correctly, but it does not extend the N-range beyond the strip (§94 says so).

## Caveats, not failures
- The conclusion is only for the strip N <= 5t-2 (small eps); the core window 5t-2 < N < 3-t stays open.
- Correctness of the "Fano shape only" claim is not needed: the argument needs only existence of a good seven.
