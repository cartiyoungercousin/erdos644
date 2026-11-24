# PROOFS — verified proofs of the hand lemmas (assembly/verification agent)

Sources checked: `notes/FRESH_C.md` §1, §6.1, §8, §9.3, §10; `notes/TWIN.md` §1, §3, §5, §7.
Each item: precise statement, complete proof, verification verdict, Lean status.
Lean files (new, not yet imported by `Lean644.lean`): `Lean644/FlatTuple.lean`,
`Lean644/FanoBlocks.lean`, `Lean644/Waste.lean`.

Conventions. H is a k-uniform family, tau(H) > T means no set of <= T points meets all edges.
*Request principle*: if tau(H) > T, every set S with |S| <= T is disjoint from some edge
(`exists_response`). "(7,2)" is used in the **at-most** convention (`HasPropertyAtMost H 7 2`:
every subfamily with at most 7 members has a 2-point transversal). This matters: see E1 below.
For a tuple A_1..A_m and a point x, J_x = {i : x in A_i} (type), deg x = |J_x|.

---------------------------------------------------------------------------------------------

## 0. Errors and imprecisions found (read first)

**E1 (Lemma 3 / Cor. 3a / Cor. 4: repetitions).** The seven edges produced by Lemma 3 need not be
distinct, and distinctness cannot be added: for k = 1, T = 1, H = two singletons we have tau > T,
4T >= 3k, and H has only two edges. So Lemma 3 gives a 7-*tuple* (multiset). Corollaries 3a and 4 are
therefore correct only if "(7;5)" resp. "(7,2)" are read for tuples with repetition, equivalently
for subfamilies with *at most* 7 members. (Same k = 1 example: H satisfies the exactly-7 forms of
(7;5) and (7,2) vacuously and has tau = 2 > ceil(3k/4) = 1, so Cor. 3a is false in the exactly-7
reading.) The repo's `HasPropertyAtMost` is the right hypothesis; nothing else changes.

**E2 (FRESH_C §6.1: wrong closure).** The text defines "U = up-closure of the realized types" and
"D = {points whose type J satisfies [6] \ J in U}". This is wrong as written: the condition
J_x ∪ J_y ⊇ [6] says that [6] \ J_y is *contained in* a realized type, i.e. [6] \ J lies in the
**down**-closure of the realized types (the nerve N of TWIN §1). Items (i)–(iii) of §6.1, TWIN §1
and the code (`endgame.py` header: "complement [6]\J is contained in some realized type") all use
the correct version; only the displayed definition is wrong.

**E3 (TWIN §1 and FRESH_C §6.1(ii): "every point of degree >= 4 is in D").** Not a property of
6-tuples: a degree-4 point is in D iff the complementary two replies intersect. "No reply can be
fully requested" only shows that the adversary *may* make every pair of replies meet (at the cost
of one point); he is not forced to, and Theorem 8's adversary keeps A_1 ∩ A_2 = ∅. Correct
statement: deg >= 5 points are always in D (edges are nonempty); deg-4 points are in D iff the
complementary pair meets. Also the nerve must contain ∅ by convention (a point of type [6] is in
D; and if [6] in N then every point is in D, matching the "type [6] not realized" proviso).

**E4 (Theorem 8, last line).** The proof answers the 7th request with "x plus k-1 fresh points",
but then claims all replies lie in {A_1} ∪ (k-subsets of V'). These are inconsistent. Fix: take
A_7 = any k-subset of V' \ S_7 containing x (exists: |V' \ S_7| >= k and x in V' \ S_7). Also the
argument divides by T, so it needs T >= 1 (for T = 0 the statement is trivial). The theorem is
correct.

**E5 (TWIN Cor. 5.2, first clause).** "Each rectangle has |A\E| + |A'\E| <= k + small ... five such
rectangles cannot cover for T < 4k/5" — with semi-perimeter k the area bound is 5k²/4 >= k², which
proves nothing. Only the second reading is a proof: under Theorem 8's confinement the relevant
grid is X × Y (area Tk) and the rectangles have semi-perimeter T, so five of them cover at most
5T²/4 < Tk when T < 4k/5. The conclusion of Cor. 5.2 is right for the confined adversary only.

**E6 (TWIN 7.4).** The window is [x, x + r] with r = N - 1 - t (the slack), for every N; "r = 1 - t"
is correct only for N = 2. With that reading the lemma is correct.

**E7 (STRATEGIST §2.3 normal form).** The pair property is true only in the rank-<=k class (not
for k-uniform point-minimal families), and the "three-part" normal form (criticality + saturation
+ pairs) is not justified: see §7.

No error was found in: Lemma 3's inequalities; Cor. 3b; Cor. 4 (shape of covers); TWIN §1 formula
(after E3's convention); TWIN §3; Lemma 5.1; TWIN 7.1, 7.2, 7.3(a)(b)(c), 7.5; FRESH_C §9.3
(including existence of the weighted Fano blow-up, checked below).

---------------------------------------------------------------------------------------------

## 1. Lemma 3 (flat tuples) and Corollary 4

**Lemma 3.** Let H be k-uniform, tau(H) > T, 3k <= 4T. Then there are edges A_1, …, A_7 of H
(repetitions allowed) such that every point lies in at most four of them.
**Lean:** `Erdos644.exists_flat_tuple` (`Lean644/FlatTuple.lean`).

*Proof.* Write d_i(x) for the degree of x in A_1..A_i. We maintain finite sets containing all
points of high degree. Two kinds of step, each one application of the request principle.

(Odd step, level j, `flat_odd_step`.) Suppose d_i <= j everywhere and P ⊇ {d_i >= j}, |P| <= p <= T.
Request S = P; let A_{i+1} be an edge disjoint from P. A point of A_{i+1} had degree <= j - 1, so
d_{i+1} <= j everywhere; and {d_{i+1} >= j} ⊆ P ∪ A_{i+1} =: Q, |Q| <= p + k.

(Even step, level j, `flat_even_step`.) Suppose d_i <= j everywhere and Q ⊇ {d_i >= j}, |Q| <= m.
Choose S ⊆ Q with |S| = min(T, |Q|) and an edge A_{i+1} disjoint from S. Then d_{i+1} <= j + 1, and
a point with d_{i+1} >= j + 1 has d_i >= j (so it is in Q) and lies in A_{i+1} (so it is not in S):
{d_{i+1} >= j+1} ⊆ Q \ S =: P, |P| = |Q| - min(T,|Q|) <= m ∸ T (truncated subtraction).

Chain (start: d_0 = 0, P = ∅):
1. odd, j = 1, p = 0:       d <= 1, |{d >= 1}| <= k.
2. even, j = 1, m = k:      d <= 2, |{d >= 2}| <= p_2 := k ∸ T.
3. odd, j = 2 (p_2 <= T):   d <= 2, |{d >= 2}| <= p_2 + k.
4. even, j = 2:             d <= 3, |{d >= 3}| <= p_4 := (p_2 + k) ∸ T.
5. odd, j = 3 (p_4 <= T):   d <= 3, |{d >= 3}| <= p_4 + k.
6. even, j = 3:             d <= 4, |{d >= 4}| <= p_6 := (p_4 + k) ∸ T.
7. odd, j = 4 (p_6 <= T):   d <= 4.
The three side conditions p_2, p_4, p_6 <= T follow from 3k <= 4T (p_6 <= 3(k - T) when T <= k,
and all p's vanish when T > k); no assumption T <= k is needed. ∎

Remarks. (a) The proof never needs a "top-T set" in general; only "all points of degree >= j" (odd
steps) and "T points of degree >= j" (even steps). (b) Repetitions: see E1.
(c) Tightness of the hypothesis: complete family on n = ceil(7k/4) - 1 points has
tau = ceil(3k/4) and every 7-tuple has a 5-fold point (7k > 4n).

**Corollary 4 (shape of covers).** If every point lies in at most 4 of A_1..A_7 and {x,y} meets all
seven, then J_x ∪ J_y = [7], so |J_x| + |J_y| >= 7; hence both degrees are in {3,4}, one of them is
exactly 4, and the other point lies in all three edges of the complementary triple.
**Lean:** `Erdos644.flat_cover_shape`; combined with Lemma 3 and property (7,2):
`Erdos644.flat_tuple_cover`. ∎

**Corollary 3b** (verified): if sum_i mu(A_i) > 4 mu(V) for some weight mu >= 0 then some point
has degree >= 5, because sum_i mu(A_i) = sum_x mu(x) deg(x).

---------------------------------------------------------------------------------------------

## 2. The dangerous set D (nerve formula, TWIN §1; corrected FRESH_C §6.1)

**Statement.** Let A_1..A_6 be sets, N = {I ⊆ [6] : some point lies in all A_i, i in I} ∪ {∅}.
For a set A_7 the 7-tuple has a 2-cover iff A_7 meets
  D = {y : [6] \ J_y in N} = ⋃_{J : [6]\J in N} ⋂_{j in J} A_j   (empty intersection = everything).
*Proof.* If {x,y} covers all seven, one of them, say y, is in A_7, and every i <= 6 with i not in
J_y has x in A_i; so [6] \ J_y ⊆ J_x, i.e. [6] \ J_y in N (if it is empty, by convention).
Conversely if y in A_7 and x lies in all A_i, i in [6] \ J_y (x := y if this set is empty), then
{x,y} is a cover. The second form of D: y is in the union iff some J ⊆ J_y has [6] \ J in N, and N is
down-closed. ∎
Consequences: deg >= 5 points are in D if all A_i are nonempty; a deg-4 point iff the complementary
pair meets (E3); a deg-3 (deg-2) point iff the complementary triple (4-set) has a common point.
The requester wins the six-edge endgame iff |D| <= T (then S_7 = D). Not formalized.

---------------------------------------------------------------------------------------------

## 3. Rectangle lemma and Theorem 8 (waste adversary)

**Lemma 5.1 (rectangles).** Let A ∩ A' = ∅ and E_1..E_n be sets. The sets A, A', E_1..E_n have a
2-cover iff some (x,y) in A × A' lies in no rectangle R_t = (A \ E_t) × (A' \ E_t). Hence if there
is no 2-cover, sum_t |A \ E_t| |A' \ E_t| >= |A| |A'|.
*Proof.* A 2-cover has one point in each of the disjoint sets A, A'; (x,y) in A × A' misses E_t
iff both x, y are outside E_t. The count is a union bound. ∎
**Lean:** `Erdos644.rect_cover_iff`, `Erdos644.rect_count` (`Lean644/Waste.lean`).

**Theorem 8 (seven-request game, no discards).** Game: for i = 1..7 the requester names S_i with
|S_i| <= T (adaptively), the adversary answers with a k-set A_i disjoint from S_i; the requester
wins iff A_1..A_7 have no 2-cover. Claim: if 1 <= T and 5T < 4k the adversary wins, and all his
replies can be taken in the family {A_1} ∪ (k-subsets of V'), |V'| = k + T, which has tau = T + 1.

*Proof.* A_1 any k-set avoiding S_1; A_2 = Y a k-set disjoint from A_1 ∪ S_2. Fix X ⊆ A_1 with
|X| = T, V' = X ∪ Y. For t = 3..6 answer with any k-set B_t ⊆ V' \ S_t (|V' \ S_t| >= k).
Put P_t = X \ B_t, Q_t = Y \ B_t; |P_t| + |Q_t| = |V' \ B_t| = T, so |P_t||Q_t| <= T²/4.
Call (x,y) in X × Y *good* if it is in no P_t × Q_t; a good pair covers A_1, A_2, B_3..B_6.
Let E_X, E_Y be the projections of the good pairs. Every pair of X × Y is good (hence in
E_X × E_Y) or in a rectangle, so
    Tk <= |E_X||E_Y| + sum_t |P_t||Q_t| <= |E_X||E_Y| + T².
If |E_X| + |E_Y| <= T then |E_X||E_Y| <= T²/4 and 4Tk <= 5T², i.e. 4k <= 5T: contradiction.
So |E_X ∪ E_Y| > T >= |S_7|; pick x in (E_X ∪ E_Y) \ S_7 with good partner y and answer with a
k-subset A_7 of V' \ S_7 containing x. Then {x,y} covers all seven replies.
tau of the reply family: a transversal of all k-subsets of V' must leave fewer than k points of
V', so it has >= T + 1 points; T + 1 points of V' including one of X also meet A_1. ∎

**Lean:** `Erdos644.waste_core` (counting core, any number n of rectangles with (n+1)T < 4k) and
`Erdos644.waste_adversary` (the six-edge position: for every S with |S| <= T there is x not in S,
x in X ∪ Y, and y with {x,y} meeting A_1, Y and all B_t). The game wrapper (quantification over
requester strategies) is NOT formalized; `waste_adversary` is exactly the statement "after these
six replies, whatever S_7 is, the adversary has a reply (any set containing x) completing a
2-coverable 7-tuple".

Scope remarks. (i) The theorem is about the *game*: the reply family is not (7,2), so it says
nothing about f(k,7); it shows the 7-request no-discard game cannot prove a bound below 4k/5.
(ii) The hand bound 4/5 is not the value against this adversary: 5/6 is [computed], see §6.
(iii) Same counting in the m-request discard game: replies 3..m-1 give n = m - 3 rectangles in the
T × k grid, so by `waste_core` all m replies get a common 2-cover when (m-2)T < 4k; for m = 8 this
is T < 2k/3 (TWIN §5, "sufficient condition for the adversary"), so the method yields no
8-request adversary above 3k/4.

---------------------------------------------------------------------------------------------

## 4. Confined game lemmas (TWIN §7) — all verified

Setting: V a ground set, replies B_1..B_7 ⊆ V, C_i = V \ B_i, I_x = {i : x in C_i}.

**7.1 (criterion).** B_1..B_7 have no 2-cover iff for all x, y in V (x = y allowed)
I_x ∩ I_y ≠ ∅, i.e. every pair of points lies in a common C_i.
*Proof.* Points outside V are in no reply, so covers may be taken in V; {x,y} is a cover iff no
B_i misses both iff no C_i contains both. (Points in no reply have I = [7]; they impose no
condition beyond I_y ≠ ∅.) ∎

**7.2.** Enlarging any C_i preserves the criterion. In particular, if the requests S_i ⊆ C_i alone
pair-cover V the requester has won (Fano blow-up: 7 classes of mass |V|/7, requests = lines, needs
3|V|/7 <= T). ∎

**7.3 (rigidity at |V| = 2k, |C_i| = k).** In a final position without 2-cover:
(a) every x in V has |I_x| >= 3: the C_i through x must cover V by 7.1, and two k-sets through x
    cover at most 2k - 1 points;
(b) sum_x (|I_x| - 3) = 7k - 3·2k = k exactly;
(c) no weights w >= 0 on [7] have w(I_x) > w([7])/2 for all x: summing over x would give
    sum_i w_i |C_i| > 2k · w([7])/2 = k w([7]) = sum_i w_i |C_i|. ∎

**7.4 (window).** Let |V| = Nk, slack r = N - 1 - t (units of k), Y ⊆ V. If the request has
mass(Y) - x - r inside Y and t - (mass(Y) - x - r) outside Y (both in range), every reply B ⊆ V \ S
of mass 1 has mass(B ∩ Y) in [x, x + r].
*Proof.* Upper: unrequested part of Y. Lower: 1 - (mass(V \ Y) - requested outside)
= 1 - N + t + x + r = x. ∎ For N = 2, Y = B_1: mass(C_1 ∩ C_2) = mass(B_1 ∩ B_2) >= x for any x <= t.

**7.5 (Fano-nerve criterion, mandatory blocks).** Label seven sets B_0..B_6 so that
012, 034, 056, 135, 146, 236, 245 are the lines of a Fano plane. If the three sets of each line
have empty intersection, there is no 2-cover. Sequential form: with
  M_2 = B_0∩B_1, M_4 = B_0∩B_3, M_5 = (B_1∩B_3) ∪ (B_2∩B_4), M_6 = (B_0∩B_5) ∪ (B_1∩B_4) ∪ (B_2∩B_3)
(M_0 = M_1 = M_3 = ∅), if B_c ∩ M_c = ∅ for all c then B_0..B_6 have no 2-cover. No ground set is
involved.
*Proof.* A cover {x,y} has J_x ∪ J_y = [7]; every 2-colouring of the Fano plane has a monochromatic
line, so one of x, y lies in the three sets of a line {a<b<c}, i.e. in B_c ∩ M_c. ∎
**Lean:** `Erdos644.fano_blocks` (from the existing `fano_criterion`) and the game consequence
`Erdos644.mandatory_block_large` (`Lean644/FanoBlocks.lean`): in a (7,2)-family with tau > T, six
edges with B_2 ∩ M_2 = B_4 ∩ M_4 = B_5 ∩ M_5 = ∅ have |M_6| > T.
(TWIN uses labels 1..7 with lines 123, 145, 167, 246, 257, 347, 356; the two labellings are
isomorphic. TWIN's "equivalent to requesting all of M_c" is one direction only: requesting M_c is
sufficient for B_c ∩ M_c = ∅; the adversary need not realize an unrequested intersection.)
Six-edge form (verified): with matching (16)(25)(34) in TWIN's labels, M_7 is the union of the three
matched intersections and the four lines avoiding 7 are the transversal triples 123, 145, 246, 356.

**FRESH_C §9.3 (one discard beats waste), verified including existence.** Keep A_1 (anchor),
discard A_2. On V' (mass 1 + T) take a Fano plane with line a of weight 1 (= Y), line b of weight
2 - 2T, five lines of weight T. Class masses w(p) = (L_p - (1+T))/2, L_p = total weight of lines
through p: a∩b: 1 - T; the two other points of a: T/2; of b: (1-T)/2; the two points on neither:
(2T-1)/2. All >= 0 for T >= 1/2, total 1 + T, and X = V' \ Y has mass T as required. The seventh
request is line b: possible iff 2 - 2T <= T iff T >= 2/3. (Against the forced adversary only.)

---------------------------------------------------------------------------------------------

## 5. Not verified in this pass

TWIN §2 (closed form of the last round), §4 (two clusters), §8 (re-cutting constraints), §11–12
(padding, hosting, spread lemma); FRESH_C §6–7 computations. The spread lemma 12.4 is a one-line
argument and looks correct (a point of degree 4 had degree 3 at the request of its fourth edge).

---------------------------------------------------------------------------------------------

## 6. The seven-request game and the numbers 5/6, 11/13, 7/8 (FRESH_C §10): proved vs computed

**Definitions.** G_m(T,k): the requester makes m adaptive requests (|S_i| <= T), the adversary
answers with k-sets A_i ∩ S_i = ∅; the requester wins iff some seven replies (as a tuple) have no
2-cover. An *adversary class* is a restriction on replies. t*_C(m) = inf of T/k (k → ∞, scale-free
model with "slivers" = O(1) points at zero mass) at which the requester beats every adversary of
class C. Classes used:
- W (waste, Theorem 8): A_1 arbitrary, A_2 disjoint, X ⊂ A_1 of mass T, later replies forced
  = V' \ S_t with V' = X ∪ A_2 (zero slack when |S_t| = T).
- W' (balanced waste): as W, but the pendant set Z of mass 1 - T is split between A_1 and A_2.
- K (complete, minimal overlap): complete family on (1+T)k points, |A_1 ∩ A_2| = k - T (so
  A_1 ∪ A_2 is the whole ground set), later replies forced.

**What is proved (by hand, checked here; core in Lean).**
1. t*_W(7) >= 4/5: Theorem 8 (§3 above). Lean: `waste_core`, `waste_adversary`.
2. For every m and every T < 3k/4 the adversary "complete family on k + T points" wins G_m: that
   family is (7,2) in the at-most sense (7 edges on n = k + T < 7k/4 points have a 5-fold point,
   and two k-sets on n < 2k points meet) and has tau = T + 1. So t*(m) >= 3/4 for all m, for any
   class containing it.
3. The requester needs at least the flat-tuple structure: Lemma 3 / Cor. 4 (§1), Lean-checked.
4. If all replies stay in a set of mass 1 + T + s, non-adaptive Fano requests win iff
   3(1+T+s)/7 <= T (TWIN 7.2). Against class W with 8 requests and one discard the requester wins
   for every T >= 2k/3 (§4, FRESH_C §9.3; "only if" is computed, not proved). This is consistent
   with item 2 because W's reply family is not (7,2).
5. Monotonicity in m (more requests never hurt the requester): trivial, proved.

**What is only computed (exact MILP in the scale-free model, float tolerance 1e-4, requester
free, adversary forced inside its class; not rational-certified, not re-run by me).**
- t*_W(7) = 5/6: requester's optimum mass(D) = 5/3 - T; sign change between T = 0.83 (+0.0067)
  and T = 0.8334 (-0.0002). The hand proof gives only 4/5; **no hand proof of 5/6 exists** in
  either direction (neither "adversary wins for T < 5/6" nor the requester's strategy at 5/6).
- t*_{W'}(7) ≈ 0.8461, identified with 11/13 = 0.84615… to four digits only. **The identification
  with 11/13 is numerical**, not a derivation.
- t*_K(7) = 7/8: sign change between 0.874 and 0.876, value 0 at 0.875. No hand proof. (A quick
  attempt via 7.1 — five requests of mass T must pair-cover C_1 × C_2 and cover every core point
  three times — gives only t >= 0.85 by convexity, not 7/8.)
- m = 8, one discard, classes W, W', K and the eight scripts: threshold 3/4 (control +0.04 at
  0.74, -0.04 at 0.76).

**What is NOT established.**
- No statement about the unrestricted adversary at any m: t*(7) >= 7/8 is computed for class K
  (a lower bound for the unrestricted value, since K is a legal adversary strategy — but resting
  on a float MILP); no upper bound on the unrestricted t*(7) below 1 other than what the
  literature's proofs imply, and those proofs are not seven-request strategies verified here.
- The coincidence "5/6, 11/13, 7/8 are the upper bounds appearing in the literature" is an
  observation about three computed numbers. Nothing proved links class W to the one-anchor bound
  (n-k)/3 + k/2 at n = 2k (FRESH_C §9.1 says the optimal requester pattern there is not the anchor
  template), class W' to the 11/13 argument, or class K to the FKW 7/8 proof.
- "Any proof below 7/8 must use more than seven requests": follows from t*_K(7) = 7/8 **if** that
  computed value is certified; currently [computed], so this is a conjecture-level remark with
  strong numerical support. The rigorous version available today is with 4/5 in place of 7/8
  (Theorem 8).

**Suggested certification order.** (1) rational LP certificates for the K-class value at
T = 0.87 (adversary side: fix the skeleton found by the MILP, verify the dual in exact
arithmetic); (2) a hand proof that W holds the requester to 5/6: sharpen the rectangle count of
Theorem 8 by also charging the requests needed for the pairs inside X ∪ Z and Y (the present
proof uses only cross pairs).

---------------------------------------------------------------------------------------------

## 7. STRATEGIST §2.3 "merge-irreducible normal form" — verdict: TRUE in the rank-<=k class, FALSE as a three-part normal form of a k-uniform family

**Setting that makes it true.** Class R(k,T): finite families H of nonempty sets of size <= k
(not necessarily uniform) with (7,2) and tau(H) >= T + 1. For u != v let H/uv be the image of H
under the map phi identifying u and v (to a point w).

**Lemma 7.1 (merge).** (a) H/uv has nonempty edges of size <= k and has (7,2) (either convention).
(b) tau(H) - 1 <= tau(H/uv) <= tau(H). (c) tau(H/uv) = tau(H) - 1 iff some minimum transversal of H
contains both u and v, iff the edges avoiding {u,v} can be met by tau(H) - 2 points.
*Proof.* (a) Choose a preimage for each of <= 7 edges of H/uv (distinct images have distinct
preimages); phi of a 2-cover of the preimages covers the images. (b) phi(D) is a transversal of
H/uv for every transversal D of H; phi^{-1}(D') is a transversal of H of size <= |D'| + 1.
(c) If a minimum transversal D contains u, v then |phi(D)| = tau - 1. Conversely let D' be a
transversal of H/uv of size tau - 1. If w not in D', then D' ⊆ V \ {u,v} meets every phi(E)
outside w, hence meets E: a transversal of H of size tau - 1, impossible. So w in D' and
phi^{-1}(D') is a transversal of size tau containing u and v. ∎

**Proposition 7.2 (pair property).** Let H in R(k,T) have the fewest points (>= 2 points). Then
tau(H) = T + 1 and every two points u != v lie in a common minimum transversal; equivalently there
is a set D of T - 1 points such that every edge avoiding D contains u or v.
*Proof.* H/uv has fewer points and is in R(k,T) unless tau(H/uv) <= T. By 7.1(b) this forces
tau(H) = T + 1 and tau(H/uv) = tau(H) - 1; apply 7.1(c). ∎

**Why R(k,T) is the right class (transfer to f(k,7)).** max tau over rank-<=k (7,2)-families equals
f(k,7): pad each short edge with private fresh points; a 2-cover of old edges still covers, and a
transversal using a fresh point of E can use an old point of E instead (E nonempty), so tau is
unchanged. So a k-uniform counterexample exists iff R(k,T) is nonempty. But the point-minimal member
of R(k,T) is in general **not k-uniform**, and padding it back destroys point-minimality.

**What is false / unjustified in STRATEGIST §2.3.**
(E7a) For a *k-uniform* counterexample with the fewest points among k-uniform ones, the argument
only gives: every pair u, v **not contained in a common edge** lies in a common minimum transversal
(merging such a pair keeps uniformity). For pairs inside an edge nothing follows — the merged
family leaves the class. The text's parenthesis ("sizes <= k are allowed") is therefore essential,
and every later use must be in the rank-<=k class.
(E7b) "tau unchanged iff ..." and "minimum transversal has T + 1 points, so D has T - 1 points"
need tau(H) = T + 1, which holds for the point-minimal H (7.2) but is not stated.
(E7c) The **three-part normal form is not established**. Point-minimality is compatible with
*either* extra extremal choice, not with both:
  - fewest points, then fewest edges ⇒ pair property + tau-criticality (deleting edges stays in
    R(k,T) on no more points; criticality in rank-<=k form: each edge E is the only edge missed by
    some T-set);
  - fewest points, then most edges (adding sets of size <= k on the same point set) ⇒ pair property
    + saturation (tau cannot rise above T + 1 by 7.2).
  Criticality is edge-minimality and saturation is edge-maximality; no single extremal choice
  yields both, and no argument is given that a family with both exists. Also "saturation: adding
  any k-set" must read "any nonempty set of size <= k on the point set" in this class.
  Candidate D uses (i) criticality, (ii) pairs, (iii) saturation simultaneously; as it stands only
  (i)+(ii) or (ii)+(iii) may be assumed, and in both cases for a non-uniform family (so lemmas
  proved for k-uniform families — Lemma 3, the Lean files with `IsUniform` — must be re-checked
  for rank <= k before being combined with it; Lemma 3's odd step uses |A| <= k only, so it
  survives; statements using |A| = k exactly do not automatically).
Not formalized.

---------------------------------------------------------------------------------------------

## 8. TWIN §13 (anchored reduction) — verdict: the lemma, Theorems A–D and Prop. E are correct; four statements need added hypotheses

Notation: anchors B_a, B_b, B_c with B_a ∩ B_b ∩ B_c = ∅, V their union, P_ab = B_a ∩ B_b
(pairwise disjoint), p = |P_12| + |P_13| + |P_23|, Q_c = B_c \ P, |V| = 3k - p.

**Errors / gaps (none affects Theorems A–D).**
(E8a) Theorem C needs |V| <= 2T - O(1), not |V| <= 2T: the six half-parts of P and twelve quarter
parts of Q are rounded, so a request can exceed |V|/2 by a bounded amount. (TWIN writes "+O(1)" on
the wrong side.)
(E8b) 13.5, third consequence ("three replies meeting pairwise only in O(1) points lose") and the
bold corollary of Prop. E ("a reply meeting the union of two earlier replies in only O(1) points
loses in four more requests") both need the triple to be an anchor triple, i.e. empty common
intersection. This holds if she requested B_i ∩ B_j when the third reply was made (her standard
S_3), but not for arbitrary earlier replies; the bold corollary also needs |B_i ∩ B_j| <=
T - k/3 - O(1) (true for her capped pair B_1, B_2 when T >= 2k/3 + O(1), not for "two earlier
replies" in general), and for a later reply B_j it costs more than seven requests in total.
(E8c) 13.6, last sentence: the reason given ("he controls every overlap from below: he may answer
with fresher points") is backwards — fresher points *reduce* overlaps and enlarge V. Correct
reason: he may choose every overlap anywhere between 0 and her cap; after S_2 (cap k - T on
P_12) and S_3 ⊇ P_12, at least k unrequested points of B_1 ∪ B_2 remain, so any p_13 + p_23 <= k is
available to him. Consequently |V| >= k + T > 2T always against her standard opening: **Theorem C
is never reachable unless the adversary cooperates**; the usable end case is Theorem D only, and
he avoids it with p > T - k/3. The conclusion (the window cannot be avoided) is right.
(E8d) 13.3, parenthesis: Lemma 5.1 is not literally a degenerate case of Theorem B (a disjoint
pair is not an anchor triple); it is an analogue. Harmless.

**Verified proofs.**
*Anchor lemma (13.1).* A point lies in at most two anchors, so if {x,y} meets all three then each
of x, y lies in at least one: x, y in V (x = y impossible). Creation: |S_2 ∩ B_1| >= k - T gives
|B_1 ∩ B_2| <= T; S_3 ⊇ B_1 ∩ B_2 gives empty triple intersection (needs T >= k/2). ✓
*Theorem A (13.2).* (i) For x, y in V: {x,y} meets E iff it meets E ∩ V; so coverability of
{anchors} ∪ {E_i} depends only on the traces and is monotone increasing in them. (ii) Real reply
E_i avoids S_i ⊆ V, so E_i ∩ V ⊆ V \ S_i has size <= min(k, |V \ S_i|) and can be padded inside
V \ S_i to that size; a confined strategy fed the padded traces ends with an uncoverable padded
tuple, hence (monotonicity) an uncoverable real tuple. Valid as long as the three anchors are
among the kept replies. (iii) is (i). ✓
**Lean:** `Lean644/Anchor.lean`: `anchor_cover_mem`, `anchor_trace_iff`, `anchor_mono`,
`anchor_coverable_mono`.
*Theorem B (13.3).* The 2-covers of the anchors are exactly the pairs (x,y) in P_ab × B_c over the
three splits (one point in two anchors, the other in the third); such a pair misses E_i iff it is
in (P_ab \ E_i) × (B_c \ E_i). |K_i| = |V| - min(k, |V| - T) = max(T, |V| - k). ✓
*Theorem C (13.4).* Types: P_12: {4,7},{5,6}; P_13: {4,6},{5,7}; P_23: {4,5},{6,7}; Q_c: the four
pairs other than the two types of the opposite P_ab. Checked: every type of B_3 = P_13 ∪ P_23 ∪ Q_3
meets both types of P_12 (and cyclically), since disjoint 2-subsets of a 4-set are complementary;
every round contains exactly half of each P_ab and two of the four parts of each Q_c, so
|S_i| = |V|/2 (+ rounding). Omissions only enlarge K_i. ✓ (with E8a)
*Theorem D (13.5).* All four requests contain P, so no later reply meets P; a cover is then x in P
and y in Q lying in E_1 ∩ … ∩ E_4. |X_1| <= k, |X_2| <= k - (T-p), |X_3| <= k - 2(T-p) <= T - p
iff p <= T - k/3; request 7 = P ∪ X_3. ✓ (|V| >= 10k/3 - T iff p <= T - k/3.)
*Prop. E.* With P_13 = P_23 = ∅ only the grid P_12 × B_3 remains; S_i = P_12 ∪ (quarter of B_3)
needs p_12 + k/4 <= T; the 2 × 2 cover needs p_12/2 + k/2 <= T. ✓
*13.6.* 2p <= 3k (each anchor contains two disjoint P's), so 3k/2 <= |V| <= 3k. ✓
*13.7(a).* If y in B_c is killed only at round i then every x in P_ab needs i in I_x. ✓
The "missing inequality" is a correct reformulation (by Theorem A), not a result.

**Direction of the reduction (coordinator's question) — CONFIRMED: requester-win(confined G(V)) ⇒
requester-win(open), with the same requests, budget and number of rounds.**
Setting: anchors fixed, V their union; G(V) = game starting from the anchors in which a reply to
S ⊆ V is any subset of V \ S of size exactly m(S) := min(k, |V \ S|). Let Σ be a requester strategy
winning every play of G(V) (keeping the anchors among her seven).
1. *Short traces.* An open reply E_i avoids S_i and may have any number of points outside V, so
   its trace t_i = E_i ∩ V ⊆ V \ S_i has size anywhere in [0, m(S_i)] (at most k and at most
   |V \ S_i|). It is never larger than a confined reply, only smaller.
2. *Padding.* She chooses t'_i with t_i ⊆ t'_i ⊆ V \ S_i, |t'_i| = m(S_i). This is a legal reply of
   G(V).
3. *Adaptivity.* Her next request is Σ applied to the padded history (S_1, t'_1, …, S_i, t'_i).
   The sequence of padded replies is a legal play of G(V) whatever rule produced it (real traces
   plus her own, arbitrary, padding choices), and Σ wins **every** legal play; no assumption that
   the virtual adversary is a fixed strategy is needed. The real requests are the same S_i, so
   the real adversary's replies are legal answers to them. Her padding choices influence her
   later requests, but only through a play that Σ is guaranteed to win.
4. *Transfer.* At the end the kept padded tuple (anchors + some t'_i) has no 2-cover. A 2-cover
   {x,y} of the kept real tuple (anchors + the same E_i) lies in V (anchor lemma), meets every
   t_i = E_i ∩ V (trace equivalence), hence every t'_i ⊇ t_i: contradiction. (Lean:
   `anchor_mono` with E := real replies, E' := padded traces.)
5. *Provisos.* (a) The three anchors must be among the kept replies in both games; a strategy
   that discards an anchor is outside the reduction (re-anchoring = a new V and a new game).
   (b) Only |E_i| <= k is used. (c) Discards among the non-anchor replies are allowed.
Converse: every confined adversary is an open adversary with the same traces (if |V \ S| < k, add
fresh outside points), so open-win ⇒ confined-win **for anchor-keeping strategies**. Hence the
two games have the same value among strategies that keep the anchors; the open game may have a
smaller value if dropping the anchors helps, so G(V) gives an upper bound on what she needs, not
a lower bound for the open game. An adversary certificate in G(V) therefore does NOT transfer to
the open game by itself (she might re-anchor); a requester certificate does.
