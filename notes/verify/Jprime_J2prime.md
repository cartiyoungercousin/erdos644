# Verification: PETAL Theorem J' (14.1), Theorem J'' (18.1), and CORE 21.2

Independent read of statements/proofs only. Code: `compute/verify/jprime_j2_verify.py`, `jj_extra.py`, `_hs.py`
(highspy ILP). Logs: `compute/verify/logs/jj_seed1{1..4}.log`.

## Setting used
k points per reply, request <= T, reply disjoint from request, same-class overlap >= floor(ck)+1, cross <= floor(mu k).
Forcing: request holding ceil((1-c)k) points of X_a leaves overlap <= ck, so the reply is not in X.

## Verdicts

**Theorem J' (14.1): PASS** (continuum model), with minor errors below.
**Theorem J'' (18.1) including "singles + pair cells < 4 - 6c": PASS**, same minor errors.

### Hand check (every step)
- Step 1 budget 2*(t/2) = t. RI: |I_{j}| <= 1-(j-1)t/2, |I_3| <= 1-t <= t/2 (needs t >= 2/3), so the 4th member misses I. 7 replies, 2 classes, so one class has >= 4 members. OK. If all 7 are one class, Y is created by C_1; fine.
- Step 2 forcing, class Y, miss of Z_{<j}, pairwise disjoint traces, P4(c) (pigeonhole on x,y in U): all correct. Only U (not U*) is needed for the disjointness argument.
- J' cost: |Z_i \ X_a| <= 3mu (each other petal <= mu), so 1-c+6mu. OK. 2mu <= 1-c is implied by hypothesis + c < 1-t/2 (t+4c<4).
- J'' : singles bound. Cells: s+2p+3T = 4, sum of pairwise overlaps = p+3T > 6c, so s+p = 4-p-3T < 4-6c. Correct (4-fold cell empty). Each single s_a < 1-c (X_a minus s_a contains X_a∩X_b > c). OK.
- J'' rotation: C_i misses s_{a_i}, so every point of Z_i outside X_{a_j} lies in one of the two petals other than a_i,a_j: |Z_i\X_{a_j}| <= 2mu; and |Z_i| <= 3mu (no point of s_{a_i}). OK.
- J'' third request: if F=1-c: cost <= 1-c+4mu. If F must be enlarged to contain s_{a_3} u (Z∩X_{a_3}): cost <= s_{a_3}+|Z_1|+|Z_2| < 1-3c/2+6mu (a_3 = argmin single, s_min < (4-6c)/4) <= 1-c+4mu iff mu <= c/4, which follows from 1-c+4mu <= t <= 1. Requests 1,2 cost <= max(1-c, s)+3mu <= 1-c+4mu (s<1-c). OK.

### Computation
Step 1 run verbatim against fully legal two-class adversaries (ILP over Venn cells; patterns of class choice, objectives keep-I / fresh / overlap / random). Step 2 verbatim (J' fixed a and adaptive a; J'' rotation, a_3 = smallest single) against a RELAXED adversary (only disjoint + <= mu with the four petals) whose traces are ILP-chosen to maximise later requests; 3 filler policies; also on arbitrary petal configurations (ILP vertices over 14 cell counts, a superset of what Step 1 yields, including Q(c)-like and large-single ones). Exact 2-cover test of the final seven.
Parameter points at the exact integer boundary of the hypothesis (t=.7,.75,.8,.9; c=.4,.5,.55,.6,.62; k=600). About 10,000 games.
- No budget violation, no adversary stuck, no 2-cover anywhere under the hypotheses.
- Non-vacuous: max third-request size reached the bound exactly (448/450, 450/450, 478/480, 480/480, 418/420, 420/420, 448/450). Violating the hypothesis (mu+4) gives 74/180 (J'') and 41/180 (J') budget failures.
- Asserted claims 2mu, 3mu, "no trace in s_{a_j}", pairwise disjoint traces held in every run.
- Not exhaustive over adaptive adversaries (greedy per-step ILP); the 3-request tree is small, hand proof covers the rest.

### Minor errors / clarifications
1. Step 1 needs t >= 2/3 (1-t <= t/2); not stated in J' or J'' (global t>=3/4 covers it). Also 3(t/2) >= 1.
2. The refinement (J') with min_a over the line played: a can be re-chosen at each j (valid since disjointness does not use a), but S_2 must use a_2 = argmin_a |Z_1\X_a| for the refinement to bound its cost; also F_j has mass max(1-c, |Z_{<j}∩X_a|), so the cost is max(1-c+|Z\X_a|, |Z|-ish); the refined statement omits both points. Worst-case form 1-c+6mu is unaffected.
3. 14.1 "(A third class ... omitted)": J', J'' are proved only inside the two-class setting; the third-class branch is not part of these proofs.
4. Integer rounding: F of mass ceil((1-c)k) and halves floor(T/2) add O(1) points; strict inequalities needed at the exact boundary only in the continuum limit.
5. 18.1 "taking a_3 with the smallest single part" is used silently in the 18.1 count; the hypothesis mu <= c/4 is derived (not stated) from the theorem's hypothesis.

## CORE 21.2 (window lower end 3t-1/2 < N <= 5t-2 via fixed class-(T) plan when omega <= 4 eps k): GAP

What checks out: 21.1 identity |D| = W6 - 3N + 6k, and "wins iff |D| <= T iff W6 <= 3(N-7/4)+eps = 3 omega + 4 eps" (units k). 4 omega <= 3 omega + 4 eps iff omega <= 4 eps iff N <= 5T-2. Arithmetic correct.

What is missing (the count alone is not a proof):
1. **Base W6 = 0 is assumed, not proved.** "Dumps of replies 3,4,6,7 are the only source of W6" requires that, for EVERY adversary choice of K_1, K_2 (and K_3), the requester can choose requests so that the non-dump part of the six kept co-edges is an exact zero-waste Fano blow-up (every x outside D in exactly 3 co-edges, every x in D in exactly 2). That is a steering lemma; none is stated. The adversary's own dumps in replies 1, 2 (each >= omega) are free to place; "lines by definition" holds only after the cells are fixed, and the loads of the four lines (each <= T) are then determined by the adversary-chosen overlaps.
2. **Tolerance of Theorem T vs window.** At kappa = 0, Theorem T needs each overlap a_i <= a*+eps/2 and sum >= 3a* - eps/2 (total deficit <= 2 eps). She controls an overlap only to within the dump width omega (x = |S∩K_1| + |E∩K_1|, E of mass omega placed anywhere). Forcing the upper bound leaves each overlap up to omega low, total deficit up to 3 omega, which exceeds 2 eps once omega > 2eps/3. So at omega in (2eps/3, 4 eps] a static Theorem T fails; the claim needs the adaptive/flexible-point mechanism (CORE §20 "flexible points", "pile pays") with a proof that it absorbs the deficit. §20 itself records that static T fails at nodes UU, UO.
3. **kappa and dump placement.** Waste is not only the four dumps: kappa-points (no reply among the first three) and dumped points landing in a cell where they have co-type size 4 add waste. CORE 21.3 notes kappa >= omega/2 forced by one bit at N=1.85; for omega <= 4 eps this is <= 2 eps, so it consumes slack that the 4 omega count already spends. Total needed: 4 omega (dumps) + kappa/mismatch waste <= 3 omega + 4 eps, i.e. omega + (extra) <= 4 eps; with omega = 4 eps the extra must be zero. The boundary case omega = 4 eps therefore has no room, contrary to "wins even if all four are fully wasted".
4. **Dump waste is not additive worst case.** Dumps into already-requested lines are harmless (monotonicity, 1.1); the count 4 omega is an over-bound for them, but the real danger is dumps landing so that W6 loses its exactness (point 1), which the count does not bound.
5. No verification was run for 21.2 (tree/LP check at e.g. t=.76, N=1.795..1.80, all adversary overlaps in the window) -- not found in repo; LEDGER already flags "needs a written proof plus verification". Required: (a) a steering lemma for replies 1-3 with explicit requests; (b) a proof that the final loads are <= T for all adversary cell vectors in the omega-window (finite LP over cells, checkable); (c) the flexible-point rule.
Verdict: GAP at CORE.md line ~793 (21.2): the inequality is right, the premise "base waste is zero" is the unproved part.
