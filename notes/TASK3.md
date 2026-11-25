# TASK3: disproof side, built from the saturated templates (MINIMAL_FRAME Task 3)

Code: `compute/task3/`. Logs: `compute/task3/logs/`. Families: `compute/task3/out/*.npy` (member bitmasks; X = bits
0..11, Y = bits 12..21). Nothing committed.

Tags: [proved by hand] (written here, not independently checked); [computed exact] (complete enumeration by our
code, or an explicit object re-checked by plain code); [solver-only] (one MILP/SAT answer, no checked certificate);
[sampled] (exact per item, but only a random sample of the items was checked).

## 0. Verdict

- **No family with (7,2) and τ ≥ 3k/4 + 2 was found.** There is no hit to report.
- **(1) Template.** H1 was made deletion-minimal: H1min has 100 506 members (H1 had 323 236). Every member has a
  private set, τ = 10 > 9, and (7,2) is inherited [computed exact]. On a sample, no incidence is loose: 1 800 of 1 800
  sampled incidences are saturated [sampled].
- **(1′) Uniform template.** From FKW: deletion gives F1, then fresh-point swaps on the j = 11, z ∈ Y class, then
  deletion again. The result U1 is H1min-type with each X∖x padded by its own private point: 12-uniform on 34 points,
  τ = 10, (7,2). Every member has a private set [computed exact]. 900 of 900 sampled swaps are excluded by Lemma 4U
  [sampled].
- **How the parity survives.** It colours the (k+1)-layer: every (k+1)-set contains members of exactly one class
  (§1.2). So deletion-minimality splits into independent covering problems, one per class. The order of deletion
  across classes is irrelevant (checked). The parity contributes no slack. Its only role is the half-point exclusions
  CORE §111 already records.
- **(2) Second constraints.** Two parity classes, products of parities, tensors of two FKW cells and mod-3 conditions
  are all profile families. Theorem S⁺ (CORE §39.4, [proved by hand, existing]) gives such a family with q cells a
  good seven once T − 3k/4 ≥ 3(q + 4)/4. So their excess is O(1), never linear. Finite scans: see §2.3.

## 1. Making H1 minimal (Task 3(1))

### 1.1 The deletion step [computed exact; `minimize_h1.py`]
- **Lemma 3 test, exactly.** B has a private set iff some 13-set W ⊇ B contains no other member.
  - Take S = V∖W, with |S| = 9.
  - Enlarging S inside V∖B only helps, and |V∖B| ≥ 10.
  - τ > 9 iff every 13-set contains a member.
- **One pass suffices.** A member that has a private set keeps it when other members are deleted, since cnt[W] = 1
  stays 1. So one pass in any order ends deletion-minimal.
- **(7,2) and τ.** (7,2) passes to subfamilies. τ = 10 exactly: it is at least 10 by covering, and the (2,8)-profile
  10-set of H1 still works.
- **Results.** Random orders, seeds 1/2/3: 100 506 / 100 329 / 100 431 members. Logs: `logs/min_random_1.log`,
  `logs/min_orders.log`.

| H1min (seed 1) | value |
|---|---|
| members | 100 506 |
| **size distribution** | 100 494 of size 12, 12 of size 11 (the X∖x) |
| total size | 1 206 060 |
| kept per edge profile | (3,9): 1 023/2 200; (5,7): 29 344/95 040; (7,5): 58 489/199 584; (9,3): 11 638/26 400; (11,0): 12/12 |
| per-class covering lower bound | 550; 15 840; 33 264; 6 600; – |
| degrees | X: 55 285–55 421; Y: 54 103–54 303 (nearly balanced, as in H1) |
| 13-set cover multiplicity | 1: 204 586, 2: 149 344, 3: 91 202, …, max 12 (the sets X+y) |
| private sets | all 100 506 members |

**H1's non-uniformity (coordinator's item 1).**
- H1 has 323 224 members of size 12 and 12 of size 11, so 0.004% of its members are short.
- H1min has 100 494 and 12, so 0.012%.
- The non-uniformity is mild, but it is essential to H1. The short members are the shrunk j = 11 class.

### 1.2 How the parity survives: the layer colouring [proved by hand for every m; computed exact at m = 3]
- **Claim.** In the FKW family at any m (|X| = 4m, n = 7m + 1, k = 4m, T = 3m), let W be a (k+1)-set with a = |W ∩ X|.
  Then every member inside W has X-count a or a − 1, and exactly one of the two is odd. So W contains members of only
  one parity class: profile (a, k+1−a) minus a Y point if a is odd, minus an X point if a is even.
- The same holds for every subfamily, and for H1, where the 13-sets X∖x + 2 points belong to the X∖x alone.
- **Consequence.** τ > T means every (k+1)-set contains a member. So T-covering, private sets and
  deletion-minimality split into independent problems, one per class j. Class j must cover the two layers of
  profiles (j, k+1−j) and (j+1, k−j).
- **Check.** `structure.py` finds 0 of 497 420 13-sets containing members of two profiles, in H1min, F1 and G′.
  Profile-first deletion orders give results identical to the random order with the same seed
  (`logs/min_orders.log`), as the decomposition predicts.
- **Reading.**
  - A minimal sub-FKW template is a union of minimal bipartite covering designs, one per class. Each is about 2×
    above its counting bound.
  - The parity is the rule saying which class owns which (k+1)-set. It is the same mechanism that kills the pencil
    (CORE §111.1).
  - The literal (Σ)(b) triple of SATURATION §1.4 ((7,3), (7,3), (1,10); κ = 4) survives in H1min: 190 110 copies
    (`logs/structure.log`). It does not occur in F1 (0 copies).

### 1.3 Saturation of H1min [sampled; `sat_transport.py`, `logs/transport_h1min_200.log`]
- **Method.**
  - Take the exact profile-level certificates of compute/saturation (FKW classes e = 2..10, 3 each; the 10 H1
    classes, 1 each).
  - Transport them by random π ∈ Sym(X) × Sym(Y) with π(K′₀) = K′ = (V∖B) + z.
  - A hit (all six other co-edges belong to the family, none equal to K_B) is a saturation certificate. It is
    re-checked by plain pair-cover code.
- **Result.** 200 random incidences in each of the 9 classes: **1 800/1 800 saturated**, and every seven also has
  union V. No loose incidence was found.
- **Not done.**
  - Exhaustive saturation over all ≈ 1.2·10⁶ incidences would take about 16 h at 47 ms each on the shared machine.
  - A direct SAT looseness test over 10⁵ member variables did not return in more than 3 min per instance, and was
    stopped.
  - So H1min is **deletion-minimal [exact] and saturated on the sample [sampled]**. It is not certified globally
    ‖·‖-minimal.

### 1.4 Uniform template (MINIMAL_FRAME "Uniform variant"; coordinator's item 2)
- **F1** = deletion-minimal subfamily of FKW (m = 3), computed with `minimize_h1.py random 1 fkw`. It has 100 524
  members, all of size 12, and τ = 10. (7,2) comes from FKW [computed exact, CORE 110.3]. Every member has a private
  set [computed exact]. It keeps 108 of the 120 class-(11,1) members.
- **Which swaps are allowed.**
  - In F1, the 200 sampled incidences of every class except (11,1), z ∈ Y, are excluded by transported sevens with
    union V, which is Lemma 4U (i) + (ii) [sampled, `logs/transport_fkwmin_200.log`].
  - The (11,1), z ∈ Y incidences are loose already in FKW (e = 1, exact). Non-uniform looseness implies the swap is
    allowed, so the swap B = (X∖x) + y → (X∖x) + f is valid.
- **Doing all those swaps at once is valid** [proved by hand].
  - Every member of the swapped family contains a member of G′ = bulk(F1) ∪ {X∖x}, which is a subfamily of H1. H1 is
    (7,2) (SATURATION §1.3: exact for r = 0, 1, by hand for r ≥ 2, MILP cross-check), so the swapped family is (7,2).
  - Swaps do not lower τ (MINIMAL_FRAME).
- **Deleting the extra copies** [proved by hand]. Suppose some x has two or more members (X∖x) + f. A private set
  of one of them must contain the other copies' fresh points, the point x, and a Y-set meeting every kept (9,3) edge
  that avoids x. That needs at least 8 + 1 + 1 = 10 > 9 points, because
  for every x the kept (9,3) members avoiding x realise all 120 Y-triples [computed exact, `copy_check.py`]. So all
  but one copy per x are deleted. The surviving copy has the private
  set {x} ∪ (Y minus two points).
- **The result.** U1 = bulk(F1) ∪ {(X∖x) + f_x : x ∈ X}, with 12 distinct fresh points. This is G′ padded by
  Lemma 1, with n = 34, 12-uniform and 100 428 members.
  - τ = 10: by padding, plus the (2,8) transversal.
  - (7,2): from H1.
  - Every member has a private set [computed exact, `uniform_check.py`, `logs/uniform_U1.log`].
- **Swap tests on U1.** f_x has degree 1, so it allows no swap. Of the 900 sampled old-point incidences (100 per
  class), **900/900 are SWAP_EXCLUDED**. Each has six members with no 2-transversal of B − z in V′ (34 points) and
  no common point, checked by brute force [sampled].
- **Structure.**
  - U1 has the same class decomposition as H1min.
  - Sizes: 12 only.
  - Degrees: X 55 272–55 352, Y 54 079–54 246 (as in G′); fresh points have degree 1.
  - So the uniform template is "H1min with 12 private padding points". It is not a different object.

**What a counterexample must imitate (the template).**
- Members are grouped into classes. Each (k+1)-set is owned by exactly one class, and each class is a minimal
  covering of its own two layers.
- Private sets are plentiful: a 13-set with cnt = 1 for every member, 41% of all 13-sets.
- Every incidence is saturated by a seven with union V.
- What it does **not** have is slack. τ − 3k/4 = 1, at ε = 0. Nothing in the minimalisation creates a second
  constraint.

## 2. Second independent constraints (Task 3(2))

### 2.1 Hand obstruction [proved by hand: CORE §39.4 Theorem S⁺, applied]
- **Which families.** Every proposed family is invariant under ∏ Sym(V_j) for a bounded partition:
  - two parity classes: q = 3, cells X1, X2, Y;
  - products of parity families: (a₁ mod 2, a₂ mod 2) ∈ R ⊆ F₂², q = 3;
  - the tensor of two FKW cells: q = 4, cells X1, Y1, X2, Y2;
  - mod-3 conditions: a₁ mod 3 ∈ R, q = 2;
  - any mod-p condition on q cells.
- **The bound.** S⁺ gives a good seven when n/3 + q ≤ T and q ≤ 4(T − 3k/4)/3 − 4. In the confined range
  n ≤ 3k − T, the first condition follows from the second. So such a family without a good seven has
  T − 3k/4 < 3(q + 4)/4, i.e. **τ ≤ 3k/4 + 3q/4 + 4 = 3k/4 + O(1)**.
- **Linear excess needs** q ≥ 4εk/3 − 4 cells, i.e. a rule whose cells depend on the request (CORE §39.5). No
  arithmetic condition on a bounded number of cells qualifies, however many independent conditions are stacked.
- **Caveat.** The confined range n ≤ 3k − T is assumed; that is the CORE setting.

### 2.2 Finite scans [`second_constraint.py`]
- **Families.** M3[R] (q = 2), P2[R] (q = 3) and P22[R] (q = 4, for k ≤ 8), over all R and all cell sizes, for
  k + T ≤ n ≤ 3k − T with T = ⌈3k/4 + 2⌉ − 1.
- **τ is exact by profiles.**
- **The seven test.**
  - First a fast Fano-type MILP: support on co-types containing a line of one fixed Fano plane. This is a
    sufficient condition.
  - Then the full intersecting-support MILP of core12/profile_search.
  - Every seven found is re-checked by plain code [computed exact]. "No seven" is [solver-only].
- **Bookkeeping.** Candidates are deduplicated by co-edge profile set. A family containing all slots of a found seven
  on the same cells is decided by monotonicity [exact].

### 2.3 Results
RESULTS_PLACEHOLDER

### 2.4 Margin of the (Σ) exclusions
MARGIN_PLACEHOLDER

## 3. Obstructions, in the format of reports/FAILED_ROUTES.tex
```latex
\item \textbf{Minimalising the FKW template} (TASK3 \S1). \lvl{EXACT+HAND}
 \begin{itemize}
 \item Deletion to private sets is exact and order-free across classes: each $(k+1)$-set is owned by one parity
 class, so minimality splits into independent per-class coverings. The result has $\tau-3k/4=1$ still.
 \item Fresh-point swaps (uniform variant) only re-create $H_1$'s short members as padded ones. The uniform template
 is $H_1^{\min}$ plus 12 private points. No incidence found loose in samples of 1\,800 and 900.
 \item Minimalisation removes redundancy. It never creates slack, so a template at $\varepsilon=0$ stays at
 $\varepsilon=0$.
 \end{itemize}
\item \textbf{A second arithmetic constraint} (two parities, parity products, tensors of FKW cells, mod 3; TASK3
\S2). \lvl{HAND+EXACT}
 \begin{itemize}
 \item All are profile families on $q\le4$ cells. Theorem S$^+$ gives a good seven once
 $T-3k/4\ge3(q+4)/4$, so the excess is $O(1)$. Linear excess needs $q\ge 4\varepsilon k/3-4$ request-dependent cells.
 \item Finite scans (SCAN_SUMMARY_TEX): every family with $\tau\ge3k/4+2$ has a good seven.
 \end{itemize}
```

## 4. Self-check
- The Lemma 3 ⇔ "13-set with cnt = 1" equivalence is a two-line argument (§1.1). τ > 9 ⇔ "all 13-sets covered" is
  the same complement argument.
- Independent checks:
  - `structure.py` recomputes coverage from scratch, by enumerating the 13-supersets of each member.
  - `uniform_check.py` recomputes the private sets of G′/U1 separately.
- Every transported seven is re-checked by plain pair-cover code. Lemma 4U for U1 is re-checked on the 34-point
  ground set by brute force over all points and pairs.
- Hand steps that are not independently checked:
  - the layer colouring for general m;
  - the simultaneous swap validity;
  - the copy deletion;
  - the application of S⁺.
- Not done: exhaustive saturation of H1min/U1, and the global ‖·‖-minimum.
