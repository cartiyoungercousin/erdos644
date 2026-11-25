# Programme 4, P1: the constant c in "seven-free and covering ⇒ w* ≥ c·e − O(1)"

Tags: [proved by hand], [computed] (exact), [heuristic], [open]. Nothing here is independently verified.
Code: `compute/programme4/p1/` (`p1_table.py`, `p1_local.py`, `p1_prime.py`), logs in `p1/logs/`. Nothing committed.
Notation as in PROGRAMME3_LT: H has sets of size ≤ k on n points and is T-covering (every (k+r)-set, r = n−k−T,
contains a member). A pencil P = (x1,x2,x3) has x1∩x2∩x3 = ∅ and weight w = wt(x1+x2+x3) = |E|. Regions:
E_i (only in x_i), D_ij, U = ∪x_i with |U| = (3k+w)/2, Z = V∖U, z = |Z|. Put q = 4T−3k (≈ 4e) and θ = w − q.

## 0. Verdict
- **No proof of c > 4, and no sharpness example. We give a precise obstruction instead.**
  - c = 4 is exact for every argument of the form "pencil + covering ⇒ a seven with P on concurrent lines" (§3).
    This holds even for the additive constant: the threshold is w ≤ 4T−3k, and P1′ (§2) reaches it.
  - Any c > 4 must use that P has *minimum* weight. The obstruction families have w* ≤ 1.
- **The data cannot bound c** (§1) [computed]. Every known family with no Fano-type seven has q ≤ 1 (e ≤ 5/4), so w*/e
  is O(1)/O(1). A sharpness example with e ≥ 2 would exceed every family known to the project (max e = 5/4).
  One with e = Ω(k) would refute (G).
- **By-product, P1′** [proved by hand; core brute-force checked]: if w ≤ 4T−3k, then H has a Fano seven. One
  O(1) parity exception, "stuck", needs w ≤ 4T−3k−4. So a family with no Fano seven has w* ≥ 4T−3k−2
  (P1: −5), and every non-stuck pencil has w ≥ 4T−3k+2.
  - FKW meets the non-stuck bound with equality (q = 0, w* = 2).
  - The slope-3/11 corollary's constant improves from (3n+3k+24)/11 to (3n+3k+17)/11. The PEN size conditions were
    not re-run for the 7 new values of T [proved by hand, unchecked].

## 1. Table: w* versus q on families with no Fano-type seven [computed, `p1_table.py`, `logs/p1_table.log`]
| family | k | n | τ | e = τ−3k/4 | q = 4T−3k | w* | P1 bound q−5 |
|---|---|---|---|---|---|---|---|
| K_{7m−1}^{(4m)} (m = 1..6 checked) | 4m | 7m−1 | 3m | 0 | −4 | 0 | −9 |
| K_{(7k+1)/4}^{(k)}, k ≡ 1 (4): k = 5, 9, …, 21 | k | (7k+1)/4 | (3k+5)/4 | 5/4 | **1** | 1 (stuck) | −4 |
| K_n^{(k)}, k ≡ 2, 3 (4), largest seven-free n | k | ⌈7k/4⌉−1 | | 1/2, 3/4 | −2, −1 | 0, 1 | |
| FKW m = 2, 3, 4 | 4m | 7m+1 | 3m+1 | 1 | 0 | **2** | −5 |
| SAT/selector families at (8,6,15) (TASK4 table) | 8 | 15 | 7 | 1 | 0 | 2 | −5 |
| two-block H_J, all J, all splits, 3k/2 ≤ n ≤ 2k, k = 5..11 | | | | | max 1 (k = 5, 9), 0 (k = 8), < 0 else | 1, 2 at the max | |
- The two-block scan reports the largest q among H_J with no Fano-type seven, and the least w* at that q. That
  maximum is q = 1 at k = 5, 9 (complete families), q = 0 at k = 8 (FKW) and q < 0 otherwise. Theorem C2 already
  caps two-block families at q ≤ 7.
- Reading: P1's bound is never close, because its constant is −5. With P1′, FKW is tight, and the complete
  families are tight in the stuck case up to the O(1). The ratio w*/e is undefined at this scale, so **c is not
  constrained by any known family.**

## 2. Where the 4 comes from: a waste identity, and P1′ [proved by hand]
- Colour as in P1 (Z → p0, D_ij → Q_k, E_i → Q_{i±1}). Each U-point lies on exactly 2 of the 3 pencil R's and on
  exactly 2 of the 4 others; each Z-point lies on 0 and 4. A Z-point coloured q ≠ p0 only loses. So for every
  admissible colouring: Σ_{pencil}|R| = 2|U| = 3k + w, and Σ_{other 4}|R_g| ≤ 4n − 3k − w.
- **Waste identity.** 4n = Σ_ℓ|R_ℓ| = (3k + w) + 4(k + r) + slack, i.e. **4s = w + 4r + slack** (s = n − 7k/4).
  - The pencil lines waste exactly w: E-points sit in a second pencil R.
  - Each completing line wastes r: size-based covering needs |R_g| ≥ k + r.
  - So P1's condition is w ≤ 4(s − r) = q. The global Fano count (each point in 4 of 7 R's) adds nothing beyond
    this.
- **P1′ (exact optimum of the colouring).**
  - With class sizes c_i (E-assignment free) and splits α_i, the four |L_g| are the sums of one side of each class
    over the even-parity patterns.
  - min max_g |L_g| = ⌈|U|/2⌉ + [stuck]. Here "stuck" means that every class-parity pattern reachable by moving
    E-points has exactly two odd classes. Moving an E_3 point adds (1,1,0), and similarly for E_1 and E_2; so stuck
    forces at most one E_i ≠ ∅.
  - The four L's are equal iff all α_i = c_i/2. That gives the formula.
  - Hence a seven whenever |U| ≤ 2T (w ≤ q), or w ≤ q − 4 if stuck.
  - Checks:
    - brute force over all region sizes ≤ 3 (4096 vectors), 0 mismatches;
    - 300 explicit P1′ sevens built in H_Z (§3), each brute-force checked to have no 2-point transversal
      (`p1_prime.py 3 300`) [computed].
  - The weight-1 pencils of K_{(7k+1)/4}^{(k)} are stuck (d12 odd, d13 and d23 even), as P1′ requires.

## 3. Local sharpness: the family H_Z [proved by hand; ILP-checked]
**Proposition.** Fix any pencil P with w > q and z ≥ r. Let H_Z = {k-sets B : |B ∩ Z| ≤ z − r}. Then:
- H_Z ∋ x1, x2, x3; H_Z is T-covering, with τ(H_Z) = T + 1;
- no good seven of H_Z has x1, x2, x3 on three concurrent lines.

*Proof.*
- Covering: a (k+r)-set S has |S∩U| ≥ k + r − z, so S∩U plus ≤ z − r points of S∩Z gives a member.
- Hole Z ∪ (k − z + r − 1 points of U): size k + r − 1, so τ = T + 1.
- In a seven with P concurrent at p0, every U-point has its colour in some Q_i. So it lies in ≤ 2 of the four other
  members B_g.
- Each B_g has ≥ k − z + r points in U. So 4(k − z + r) ≤ 2|U|, which is w ≤ q. ∎

- **What this kills.**
  - Any choice of the four completing members: static, adaptive, best of several covering sets, or members taken
    from a second light pencil (x1, y2, y3) placed at p1 ∈ ℓ_1. The count bounds every member in every such seven.
  - So "two light pencils sharing a member" cannot help while the seven contains P concurrently.
- **Exact threshold.** `p1_local.py 8 22` solves a profile ILP over 187 cells (k = 8..22, all T with q ≥ 0, r ∈
  {0,1,2,3,5,8,12}): 6925 pencils, balanced and random region splits. The largest completable w in H_Z is **exactly
  q** in all 187 cells, with 0 violations of P1′ [computed]. So the best universal constant lies in [q−4, q], and
  equals q off the stuck case.
- **Other placements are worse.**
  - P on a triangle: Σ_{other 4}|R| ≤ 3w + 2|D| + 3z = 3n − 3k/2 + w/2. Size-based covering then needs
    w ≥ 2n + 3k − 8T ≈ k/2 + 2s − 8e: useless for w = O(εk).
  - P not in the seven at all: this is back to Theorem A / 3n/7.
- **H_Z has w* = k mod 2.** All k-subsets of U are members, and |U| ≥ ⌈3k/2⌉, so H_Z's own minimum pencil is perfect
  and completable. **The obstruction is entirely about not using minimality.**

## 4. What c > 4 needs: the blocked-pencil lemma [open], with partial facts
- **BPL(γ).** Let H be T-covering and P a pencil with 0 < θ ≤ γ·e that has no concurrent completion. Then H has a
  pencil of weight < w(P).
  - BPL(γ) ⇒ c ≥ 4 + γ ⇒ slope (1+η)/(5+γ+η): at η = 1/2, 3/(11+2γ). Conversely, H_Z shows that the argument must
    find a pencil (or a seven) elsewhere.
- **Fit criterion** [proved by hand]. Choose an E-assignment and y_i ≤ c_i with c_i − y_i + y_j + y_l ≤ T for all i.
  Then three of the R_g have size ≥ k + r. So P completes as soon as one member B fits the fourth, i.e.
  B ⊆ Z ∪ Y. The maximal choice is y_i = (c_i − θ/2)/2 up to rounding (|U| = 2T + θ/2).
  - Hence, if P is blocked, every member B with |B∩Z| ≥ k − T + θ/2 + O(1) = (z − r) + θ + O(1) is **class-heavy**:
    for every E-assignment, some i has |B ∩ C_i| > (c_i − θ/2)/2.
  - In H_Z this is vacuous: every member has |B∩Z| ≤ z − r. So BPL must find the light pencil among Z-poor
    members, i.e. members with > T − θ/2 points in U, |U| = 2T + θ/2.
- **Routes tried, each giving nothing** [proved by hand].
  - (a) Second-generation pencils x_1 + B_000 + B_011 from a colouring with only two big R's. The best union bound is
    k + z + |col(1,1)| with |col(1,1)| ≥ k/2 + r − z. That gives weight ≤ 2r: Lemma 8′, worse than PEN's 3r/2.
    (A balanced-colouring estimate 2s − 5w/6 was wrong: E_2 points lie outside x_1.)
  - (b) Members forced into Z ∪ Y with |Y| = |U|/2 + θ/4 = |U| − T. The adversary drops its r points in Z, where all
    four lines share them, so nothing is recovered. Making three such members a pencil needs triple-free Z-parts of
    size z − r, i.e. z ≤ 3r; but z ≈ k/4.
  - (c) Z-poor members alone (every member has ≥ |U|/2 + θ/4 points in U). Light pencils among them would need
    PEN or Lemma 8′ inside U (n_U = 3k/2 + w/2, radius r). The size conditions fail there: T_U = k/2 + w/2 − r
    < k/2 + 5r/4, and Lemma 8′ needs w ≥ 2r + 2. So minimality inside U is exactly as hard as PEN(η < 1/2).
    [heuristic: BPL looks no easier than PEN(η<1/2), the other agent's problem]
- **Small SAT tests are uninformative** [heuristic]. At sizes a solver reaches (n ≤ 16), covering already forces
  pencils of weight ≤ 3 (PROGRAMME3_LT §2: (12,5,2,3) UNSAT). So P is never a minimum pencil there, while q ≤ 4.

## 5. Reproduction (`compute/programme4/p1/`, `py -3.14`, single core)
- `p1_table.py 24 11`: §1 table and two-block scan (minutes; k = 11 is the slow step). It uses `programme2/C/twoblock.py`.
- `p1_local.py 8 22`: H_Z exact threshold (≈ 4 min), giving `logs/p1_local_8_22.log`.
- `p1_prime.py 3 300`: P1′ formula brute force plus 300 end-to-end sevens, giving `logs/p1_prime.log`.
