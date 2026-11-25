# FABLE_A: proof direction for the core window

Tags: [proved by hand] / [computed exact] / [computed float] / [literature, checked] / [heuristic].
Nothing here is verified until the coordinator arranges an independent check.

## 1. Plan

**Mechanism: multi-pool designs + isoperimetry on the request space.** View a family as a reply map
F(S) = S ∪ D(S) and partition ALL T-sets into classes by dump rule (for a greedy rule: the order used;
in general: the dump). Two ingredients.
- (A) *Multi-pool designs have first-order slack* [proved by hand, count only; to be re-checked exactly].
  A Fano design whose lines take their dumps from different pools wastes less than the one-pool design:
  with pools Y_a on a pencil and Y_b on the complementary quadrangle the waste is 2ω against the budget
  4ω + 4ε, so the slack is 2ω + 4ε; with seven distinct useful dumps it is 4δ. Only the one-pool case sits
  at slack 4ε.
- (B) *Dichotomy by class density on a design frame.* If one class has density > 2/3 on the three
  dump-carrying requests of a one-pool design, a random design is monochromatic (union bound; no
  perturbation, so slack 4ε suffices). Otherwise two classes are both non-negligible, and by vertex
  isoperimetry in the Johnson graph (a class of density e^{-βk} comes within ρ(β)k of almost every
  request) each of the seven requests of a multi-pool design is moved, independently, to a nearby request
  of the class the design wants. The first-order slack of (A) absorbs the seven independent moves.

**Why it meets the four requirements.**
1. Full T-covering: the classes partition every request; (B) is false for a merely dense family (no partition).
2. Adaptivity/cycles: the design is chosen after the class densities are known (unbounded depth), and the
   seven requests are corrected independently, so no fixed point S ∈ Φ(D(S)) is needed; cyclic constraints
   are paid from slack, not solved.
3. Near-pool: that is the density > 2/3 branch, finished by the pencil with slack 4ε.
4. Anti-correlated selectors: isoperimetry uses density only, never independence.

**Against the failed routes.** 1, 9: not a fixed plan or distribution; requests are found by nearest-class
search. 2, 4: no common core is claimed. 3: nothing is symmetrised. 5, 6, 12: density is used per class of
a partition of all requests, with tolerance paid by (A); the 96.1 family is not a selector. 13: no links.
15: no entropy; cycles handled as in 2. 17: the 2/3 bound is used only as a branch threshold; the other
branch uses mixed designs, which Theorem H does not.

**Known risk (stated in advance).** With R classes the isoperimetric radius ρ(log R / k) must stay below the
slack of (A). For R = e^{o(k)} this is free; for hash-like rules with R = e^{βk} it is a quantitative race,
and for a general family (one class per dump) it may be lost. If it is lost at β below the covering
exponent γ, the route gives a theorem for sub-exponentially many classes only and is dead for CP.

**Order of work (decisive test first).**
- T1 [exact, k = 8]: two-class reversed-order rule at (8,6,17), (8,7,16): are the good sevens that every
  pencil-free selector contains of the mixed type (pencil on Y_a, quadrangle on Y_b)? If not, (A) is not
  the operative mechanism: kill or repair.
- T2 [hand + exact LP]: feasibility region of the mixed design over the whole window; exact slack.
- T3 [hand]: Theorem 2P: every two-class reversed-order rule, any selector, has a good seven for k >= k_0(ε).
- T4 [hand + float]: R classes; the exponent β_0(N, ε) up to which (B) works; compare with γ and with
  Theorem R's 1.19.

## 2. T1: the forced good sevens at k = 8 are mixed [computed exact]

`compute/fableA/t1_mixed.py` reruns core9's `escape_check` (two-class reversed-order rule, SAT over all selectors,
pencil clauses, lazy cuts on good sevens) and classifies each cut by pool (a = contains Y_a = first ω points,
b = contains Y_b = last ω points). Logs `t1_8_6_17.log`, `t1_8_7_16.log`.
- (8,6,17): UNSAT after 36 cuts. (#a, #b, #both) = (3,4,0) ×14, (4,3,0) ×9, (5,2,0) ×7, (2,5,0) ×5, (3,3,1) ×1.
- (8,7,16): UNSAT after 2 cuts: (3,3,1), (3,2,2).

All 38 forced sevens use both pools; none is a one-pool seven. So ingredient (A) is the operative mechanism at
k = 8. Neither instance is in the window (ε = 0 and t = 7/8). At (10,8,21) the same template already leaves a
pencil (CORE §113.2); there is no conflict, since the mixed design is needed only when pencils are avoided.

## 3. Two-class reversed-order rule, arbitrary selector

Setting: V = [n], ω = n − k − T, Y_a = first ω points, Y_b = last ω, M the rest, m = |M|. σ: T-sets → {a, b} is arbitrary.
F(S) = S ∪ (ω lowest points of V∖S) if σ(S) = a, and S ∪ (ω highest) if σ(S) = b.
Strata: Σ_j = {S : |S∩Y_a| = j, S∩Y_b = ∅}; a_j = density of colour a on Σ_j. Σ′_j, b′_j: the same with a and b exchanged.

**3.1 Replies [proved by hand].**
(i) S∩Y_b = ∅ and σ(S) = b ⟹ F(S) = S ∪ Y_b.
(ii) S ∈ Σ_j, I an initial segment of M with |I∖S| = j, σ(S) = a ⟹ F(S) = Y_a ∪ I ∪ S
(the ω lowest unrequested points are (Y_a∖S) ∪ (I∖S)).

**3.2 Pure branch [proved by hand; 4 | k, 3 | ω].** If a_{ω/3} < 1/3, the family has a perfect pencil, hence a good
seven (55.2).
*Proof.* Take a random frame: κ ⊇ Y_b, κ∩Y_a = ∅, |κ| = n − 3k/2; three halves P_i of V∖κ with |P_i∩Y_a| = ω/3.
S_i = (κ∖Y_b) ∪ P_i has T points and is uniform on Σ_{ω/3}. By the union bound all three are coloured b with
positive probability, and then F(S_i) = κ ∪ P_i by 3.1(i). ∎
Symmetrically for b′_{ω/3} < 1/3.

**3.3 Switch [proved by hand].** Let η = 1/(16n). If neither pure branch applies, then a_{ω/3} >= 1/3 and
b′_{ω/3} >= 1/3, and one of the following holds, possibly after exchanging a and b:
- (S0) a_0 >= η and 1 − a_0 >= η (both colours on the middle stratum Σ_0 = Σ′_0);
- (S1) there is 1 <= j* <= ω/3 with a_j < η for all j < j* and a_{j*} >= η.

*Proof.* Put j* = min{j : a_j >= η} <= ω/3. If j* >= 1 we have (S1). If j* = 0 and b_0 >= η we have (S0). If b_0 < η, run
the same argument on Σ′_j: b′_0 = b_0 < η and b′_{ω/3} >= 1/3, so the primed j′* is >= 1. ∎
This is the discrete intermediate-value step. It uses the selector on every request of the strata 0..ω/3.

**3.4 Robust mixed design [repair argument proved by hand; existence of the design computed float].**
Fano classes 0..6. The three lines through class 0 are *f-lines*: fully requested, asked last, any reply. The other
four lines (a quadrangle) are coloured: two a-lines through a class p, two b-lines through a class q, with p, q, 0
collinear.
- a-line: request S ∈ Σ_{j*} with |I∖S| = j*, I = bottom i points of M. Member Y_a ∪ I ∪ W, W = S∩(M∖I), |W| = T − i.
- b-line: request S ∈ Σ_{j_b} for any j_b < j* (j_b = 0 in (S0)). Member S ∪ Y_b.
- Capacity rows: a-line ∩ Y_b = ∅ and |a-line ∩ (M∖I)| <= T − i; |b-line ∩ Y_a| <= j_b and b-line ∩ M inside the request,
  with the modal split on (I, M∖I); |f-line| <= T − s·k.

*Repair lemma.* Suppose the coloured members come from requests within r swaps of the designed ones. Let X be the
set of points that some coloured member fails to contain although its design line does (|X| <= 4r), together with
the at most 28 rounding leftovers. If |X| <= s·k, add X to all three f-requests. Then the seven members cover all pairs.
*Proof.* A point y ∉ X of class v lies in the three members of the lines through v. A point x ∈ X lies in the three
f-members. Two pencils share a line; every class lies on an f-line (the one through 0 and v); the f-lines are
concurrent. So any two co-types meet. ∎
The repair is why no fixed point is needed: the f-lines are asked after the damage is known.

*Finding the coloured requests.* Apply a uniformly random π ∈ Sym(Y_a) × Sym(I) × Sym(M∖I) to the design.
- a-lines. Σ_{j*} is covered by the n sub-strata Ω(i) = {S ∈ Σ_{j*} : |I_i∖S| = j*}, so some i has a-density >= η/n on
  Ω(i). Then |Ω(i)| >= η|Σ_{j*}|/n, which forces |i − i_typ| = O(√(k log k)) for i_typ = j*·m/(m − T + j*).
  On the product of slices Ω(i) the swap distance to colour a is 1-Lipschitz. The Doob martingale that exposes the T
  points gives P(dist >= E + λ) <= exp(−λ²/2T). So a class of density e^{−βk} is within (√(2tβ) + o(1))·k swaps of all
  but 1/8 of Ω(i). [proved by hand, standard Azuma argument; constants not checked against a source.]
  Here β = O(log k / k), so r = O(√(k log k)).
- b-lines in (S1). The designed request is uniform on the modal profile class of Σ_{j_b}, which has measure >= 1/n in
  Σ_{j_b}. Colour a has density < ηn = 1/16 there. Union bound, no perturbation.
- In (S0) the b-lines are treated like the a-lines.

*Existence of the design* [computed float; `t2d_robust_lp.py`; ε = 0.005; N = 1.78..2.24 step 0.02;
j*/ω = 0, 1/24, .., 1/3]:
- The maximal f-slack s is positive at every grid point with N <= 2.12, between 0.011 and 0.088.
- At j* = 0, s = min((ω + 4ε)/3, (t − 2ω)/3) [proved by hand].
- For N >= 2.14, i.e. 2ω > t, s is negative for small j* (at N = 2.24 it is positive only near j* = ω/4).
  Reason: no fully requested line can hold both pools.

`t3_finite_check.py` [computed exact per instance]: integer designs at (40,31,76..84), (60,46,115) and (60,46,124)
against threshold selectors with switch j* = 1..⌊ω/3⌋; the rule is applied verbatim and all pairs are checked:
22/22 good sevens. Those selectors also lose by other theorems. The run tests 3.1, the rows and the cover, not the
isoperimetric step.

**3.5 Theorem 2P [proved by hand given the float LP of 3.4; NOT verified].** Fix ε and N with 5t − 2 < N and 2ω < t
(N < 17/8 + 3ε/2), at which the design LP of 3.4 has s > 0 for all j* in [0, ω/3]. For 4 | k, 3 | ω and k >= k_0, the
two-class reversed-order rule has a good seven for EVERY selector.
*Proof.* 3.2; else 3.3; then 3.4 with r = O(√(k log k)) < s·k/4. ∎

Gaps a verifier should attack:
1. the LP is float and on a grid; a closed-form design for j* > 0 is not written;
2. the Azuma constant;
3. rounding (3 ∤ ω, the modal profile) is argued, not machine-checked;
4. the isoperimetric step was not exercised by any computation.

What is new relative to Theorems W, H, R: no window, no randomness, no 2/3 density on one kernel; the selector may be
any function. What is not covered: 2ω > t (top strip N > 17/8); two orders that are not reverses of each other; R > 2.

## 4. The class-count exponent: where the race is lost [computed float from 3.4]

With R classes the only general lower bound on a class is density 1/R = e^{−βk} on a stratum. The repair lemma needs
4·√(2tβ) < s, i.e. **β < β_0 = s²/(32t)**. With s from 3.4:
- β_0 ≈ 5·10⁻⁶ at N = 1.78;
- β_0 ≈ 6·10⁻⁵ at N = 2.0, worst j*;
- β_0 <= 3.2·10⁻⁴ everywhere (N = 2.0, j* = 0).

Compare: Theorem R, e^{1.19k} random classes; Theorem W, juntas on k/4 points (up to 2^{k/4} = e^{0.17k} classes);
covering exponent γ ≈ 0.4. The race is lost three to four orders of magnitude below γ.
β_0 is only the point where step 3.4 breaks. For R > 2 the switch 3.3 ("not a" means "b") and the design (two
unrelated orders) are not available. **No theorem for R > 2 classes is proved here.**

## 5. Verdict

- (A) holds: mixed two-pool designs have first-order slack, and they are what the small exact instances force.
- The two-class reversed-order rule with an arbitrary selector loses for N < 17/8 (3.5), pending verification. This is
  the model case of requirement 4 of the failed-routes report, at first order rather than at k = 8.
- **Dead as a route to CP.** The isoperimetric step tolerates e^{βk} classes only for β ~ 10⁻⁴, while a general family
  has one class per dump, of density e^{−γk}. This is exactly the risk stated in §1.
- Open inside this route: the top strip 2ω > t for two classes; two arbitrary orders; R = O(1) classes.
- Superseded code: `t2_mixed_lp.py`, `t2b_typical_lp.py`, `t2c_robust_lp.py` are earlier models of the same LP
  (non-robust slack; b-lines confined to stratum j*). Only `t2d_robust_lp.py` supports 3.4.
