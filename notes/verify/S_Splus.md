# Verification of Theorem S (CORE 36) and Theorem S+ (CORE 39.4, sharpened 45.1)

Verifier: independent re-derivation plus code in compute/verify/ (splus_construct.py, splus_stress.py, splus_ineq.py,
splus_sat.py, thmS_rational.py). Authors' status lines and sym*_check.py were not used.

## Theorem S (first order): PASS
Steps checked: (1) s with v/3 <= s <= v, |s| = t exists iff N/3 <= t <= N; N <= 9/4 <= 3t uses t >= 3/4. (2) member K has
profile pi >= s >= v/3, so kappa_j = (3pi_j - v_j)/2 >= 0 and v_j - pi_j >= 0. (3) kappa_j + 3(v_j - pi_j)/2 = v_j;
|kappa| = (3c - N)/2 = N - 3/2; |P_i| = (N - c)/2 = 1/2; kappa u P_i has profile pi, hence is a member by invariance.
(4) Finishing "as in 35.1": pencil at p = lines 1,2,3 (the three members); halve each petal into 1a,1b,2a,2b,3a,3b; the four
transversals {1a,2a,3a},{1a,2b,3b},{1b,2a,3b},{1b,2b,3a} cover the 12 cross pairs exactly once, so with the three
petal lines they are the 7 lines of a Fano plane; each has mass 3/4 <= t, and each class has a pencil in its co-type; two
pencils share a line, so all pairs are covered (1.3). Endpoints N = 3/2 (kappa = 0, pi = v/3) and N = 9/4, t = 3/4
(s = v/3) are fine. Exact-rational check of 94,260 random profile/partition instances (thmS_rational.py): no violation.
Implicit hypotheses (not errors): the theorem is vacuous for N < 1 + t (no member can contain a t-set), and it needs
non-atomic cells (first-order setting); finite k requires 3pi_j - v_j even, as the authors say.

## Theorem S+ (39.4): PASS
Checked: request ceil(v_j/3) per cell, total <= n/3 + 2m/3 <= n/3 + m <= T. 3p_j + kappa_j = v_j (even) or v_j + 1 (odd);
p_j >= 1 for odd cells; overlap of exactly one point is realisable (also for v_j = 1, 2). |kappa| = (3c - n - u)/2 is an
integer because each cell contributes an even number; |P_i| = (k+u)/2, so k + u is automatically even. Q-sizes
(k+u)/2, (k-u)/2, (k+u)/2; each half <= ceil((k+u)/4); transversal <= 3 ceil((k+u)/4) <= 3(k+u)/4 + 9/4 <= T when
m <= 4(T - 3k/4)/3 - 3, so the stated "-4" is valid with room to spare.
Code: explicit construction on 20,000 + 20,000 random instances at/above the minimal T (including all-cells-odd, singleton
cells, up to 40 cells): all pairs covered, all four transversal requests <= T, members K4..K7 taken as the bare requests
(worst case). 227,806 further construction checks: transversal size never exceeds the claimed formula (equality attained for
the plain construction, so the bound 3 ceil((k+u)/4) is tight). Exhaustive adversary: for 2,393 minimal T-covering profile
sets (adversary's best choices, since a good seven is monotone in the profile set) on small instances satisfying the
hypotheses (k = 8, 12), a SAT solver found a good seven in every one. SAT sanity: seven 3-sets of 16 points give UNSAT.

## Theorem S+ sharpened (45.1, 4 eps k - 12 cells): PASS
Rotating overlaps: P_i all still have size (k+u)/2; |Q_i| = (k+u)/2 - (# y assigned elsewhere) = k/2 + u/6 + O(1);
the sharing pairs (P1,P2),(P2,P3),(P3,P1) each leave a valid cover of the cell. My count gives transversal
<= 3k/4 + u/4 + 5/2, so the stated bound 3k/4 + u/4 + 3 and m <= 4 eps k - 12 are valid (observed max slack -1.5 over
227,806 checks). The quoted failing instance (16,13,31), u = 4 is reproduced for the rotating construction (largest
transversal 14 > 13). All-odd stress with cells beyond the bound did not bind because n/3 + m <= T dominates the eps condition
in random draws; the inequality itself was checked directly instead (splus_ineq.py).
Optimality claim ("optimal for the pencil certificate") was not verified; it is outside what was asked.

## Minor points (no effect on validity)
- 39.4's constant "-4" can be "-3"; 45.1's additive 3 can be 5/2.
- Both S+ statements silently need T <= n - k (otherwise the family is empty and the claim is vacuous); and n/3 + m <= T
  uses sum ceil(v_j/3) <= n/3 + 2m/3, so even n/3 + 2m/3 <= T suffices.
- "(16,13,31)" failure in 45.1 is for the rotating variant; the plain 39.4 construction gives transversal 13 there.
- Theorem S's N-window is only non-vacuous for N >= 1 + t.

No counterexample found; no gap found.
