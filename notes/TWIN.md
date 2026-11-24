# TWIN — theory twin on the six-edge endgame claim (Erdős #644)

Scope: decide "the requester can always force |D| <= T after six replies when 4T >= 3k + O(1)", then
(after the coordinator's redirect, FRESH_C §8) the discard version. Code: `compute/twin/checks.py`.
Tags: [proved by hand] / [computed exact] / [heuristic].

**Bottom line.**
1. The claim as stated (seven requests, all replies used) is FALSE. I confirm FRESH_C Theorem 8
   line by line (§3) and found the same phenomenon independently by a different adversary
   ("two clusters", §4, specific lines only).
2. The discard version (m >= 8 requests, any 7 replies) is NOT settled here. With unbounded m it is
   the conjecture itself; no bounded-m strategy with a proof, and no adversary beating m = 8 above
   3k/4, was found. What is proved: an exact nerve description of D (§1), an exact closed form for
   the last round (§2), and the rectangle lemma for disjoint pairs (§5), which says precisely what
   "waste" is and why it must be discarded rather than played through.

Notation: masses in units of k, t = T/k, r = 1 - t. Type of a point = set of indices of replies
containing it. "Heavy" type = positive mass; "sliver" = O(1) points.

---------------------------------------------------------------------------------------------

## 1. Nerve form of the dangerous set [proved by hand; checked exact]

Let N = nerve of A_1..A_6 = { I ⊆ [6] : the A_i, i in I, have a common point } (down-closure of the
realized types). Then

    D = union over J with [6]∖J in N of  ∩_{j in J} A_j .

So D always contains every point of degree >= 4 (each pair of replies meets: no reply can be fully
requested), a degree-3 point of type J iff the complementary three replies have a common point, a
degree-2 point iff the complementary four have a common point.
*Proof.* A 2-cover {x,y} of A_1..A_7 has, say, y in A_7 and J_x ∪ J_y ⊇ [6], i.e. [6]∖J_y ⊆ J_x with
J_x realized; conversely such a y in A_7 gives a cover. ∎
`checks.py` check1: formula vs brute-force 2-cover on 3000 random 7-tuples, all agree.

Consequences used below.
- (Free slivers) [proved by hand]. At round i+1 a type J is *blocked* iff all its points are
  requested. For every unblocked J the adversary may put one point of J into A_{i+1} at cost O(1);
  this only enlarges N, hence D. Types with O(1) points can be blocked forever at total cost O(1).
  So up to O(1): N gains J ∪ {i+1} for every heavy unblocked J, and nothing else.
- (Monotonicity) [proved by hand]. Requesting more never hurts the requester (the adversary's option
  set shrinks, the terminal test depends only on the final configuration); so |S| = T w.l.o.g.
- A triple {a<b<c} enters N iff A_a ∩ A_b is not completely requested at round c; a 4-set
  {a<b<c<d} iff A_a ∩ A_b ∩ A_c is not completely requested at round d. The requester's only tool
  against a complementary realization is to request a whole intersection, at its full mass.

## 2. Exact last round [proved by hand; checked exact]

State after five replies: heavy types with masses m_J (J ⊆ [5]) and the nerve N_5.
Complementarity graph G on heavy types: J ~ J' iff J ∪ J' = [5].
W = { heavy J : [5]∖J in N_5 } (types that become dangerous if promoted into A_6).
For a set B of fully requested types (mass(B) <= t), U = heavy ∖ B, let
W'(U) = { J in W : some neighbour of J in G is in U }. Then the value of round 6 is

    min over B ⊆ W, mass(B) <= t of
        mass(W'(U)) + min( 1, max(0, mass(W ∖ W'(U) ∖ B) - (t - mass(B))) ).

*Proof.* Final type J ∪ {6} is in D iff [5]∖J in N_5 (J in W); final type J (6 not in J) is in D iff
some unblocked heavy J' ⊇ [5]∖J was slivered into A_6 (J in W'(U)). Types of W'(U) count whether or
not promoted; types of W∖W'(U) count only on their promoted part, which the adversary maximises
(cap 1) and the requester reduces with the leftover budget t - mass(B). Blocking a type outside W
changes nothing (it is neither promotable into D nor a neighbour of anything). ∎
`checks.py` check2: closed form vs brute-force min–max (unit model, free slivers) on 400 random
5-states, all agree.

Fano 5-state (classes P; Q1,Q2; Q3,Q4; Z1,Z2 of mass r, lines L6 = {P,Q1,Q2}, L7 = {P,Q3,Q4} still
unrequested): G is two triangles sharing P; B = L6 gives W'(U) = L7, value 3r. Any other B gives
>= 5r. So in the Fano play the last request is forced, and the value 3r is the whole of Lemma 3's
degree-4 mass — consistent with FRESH_C §8.1.

## 3. The stated claim is false: verification of FRESH_C Theorem 8 [proved by hand, re-derived]

Adversary: A_2 fresh and disjoint from A_1; Z ⊂ A_1, |Z| = k - T; X = A_1∖Z, Y = A_2, V' = X ∪ Y;
replies 3..6 any k-subset of V'∖S. I re-derived every step:
- a cross pair (x,y) in X × Y covers A_1, A_2, and fails on B_t iff (x,y) in P_t × Q_t with
  P_t = X∖B_t, Q_t = Y∖B_t, |P_t| + |Q_t| = |V'| - k = T, so area <= T²/4;
- the pairs not in any of the four rectangles number >= Tk - T²; both ends of such a pair have
  complementary-covering types, so they lie in D; their projections E_X, E_Y satisfy
  |E_X||E_Y| >= Tk - T², hence |E_X| + |E_Y| >= 2 sqrt(Tk - T²) > T iff 5T < 4k;
- then some x in D is unrequested at round 7 and A_7 ∋ x is covered with x's partner.
Correct. `checks.py` check4: the integer inequality "e_X e_Y >= Tk - T² implies e_X + e_Y > T" holds
for all 4 <= k <= 60, 5T < 4k [computed exact].

## 4. Independent mechanism: two clusters [proved by hand for the lines stated; not a full strategy]

Found before reading §8; kept because it shows the failure is not special to the confined region V'.
Facts: a type of mass > t can never be blocked; two heavy types of total mass > t cannot both be
blocked.
Line: A_1, A_2 disjoint. Round 3, request s_1 + s_2 = t, say s_1 <= t/2: A_3 takes c = 1 - s_1 >= 1 - t/2
of A_1 (rest fresh). Round 4, requester blocks 13 (cost c), leftover 3t/2 - 1 on A_2: A_4 takes
e = 2 - 3t/2 of type 2. Round 5: c + e = 3 - 2t > t for every t < 1, so 13 and 24 cannot both be
blocked; whichever is left open is promoted with mass 3 - 3t into a heavy triple (135 or 245) whose
complement in [5] is the other heavy pair. By §2 the last round then costs
min(5 - 5t, 7 - 15t/2) (triple 245) or the analogous value with 135, which exceeds t for t < 14/17.
At t = 4/5 in units of 1/5: values 5 and 6 against T = 4 (`checks.py` check3, [computed exact]).
Not covered: the requester's alternatives at rounds 3–4 (unbalanced round 3; leaving 13 open at
round 4, which I checked by hand only in one sub-line, value 4 - 7t/2 or 5 - 9t/2, worse for her).
So this is corroboration, not a second proof; Theorem 8 is the proof.

## 5. Discard version: what is proved and what is open

Game: m requests, replies A_1..A_m; requester wins iff some seven replies have no 2-cover
(equivalently, since supersets of uncoverable sets are uncoverable, iff the reply family is not
"(7,2)").

**Lemma 5.1 (rectangle lemma) [proved by hand].** Let A, A' be disjoint replies and E_1..E_5 five
more. The seven are 2-coverable iff the rectangles R_t = (A∖E_t) × (A'∖E_t) do not cover A × A'.
Hence an uncoverable 7-tuple containing a disjoint pair needs sum_t |A∖E_t||A'∖E_t| >= k².
*Proof.* A 2-cover needs one point in each of A, A'; (x,y) fails on E_t iff x, y both miss E_t. ∎

**Corollary 5.2 [proved by hand].** If the adversary keeps every later reply E with
|E ∩ (A ∪ A')| >= k - (small), each rectangle has |A∖E| + |A'∖E| <= k + (small) — and with
Theorem 8's confinement to V' it is T on the grid X × Y. Five such rectangles cannot cover for
T < 4k/5. So below 4k/5 a winning requester MUST discard one edge of that disjoint pair; the bad
7-tuple she finally keeps cannot contain it. "Waste" = a disjoint (or nearly disjoint) pair together
with confinement of later replies near its union.

**Remark 5.3 [proved by hand].** Which edge to drop is forced against Theorem 8's adversary: drop
A_1 (it carries the pendant Z). Then A_2 = Y is the complement in V' of X, |X| = T, a legal Fano
line; six further forced replies complete a Fano blow-up of V' iff T >= 3k/4 — total m = 8.
If A_2 is dropped instead, the Fano template is unavailable with m = 8: A_1 ∩ V' = X has T < k
points, so A_1 is not a line-complement of any blow-up of V' (I did not prove that no other
uncoverable configuration through A_1 exists).

**Why this does not yet give a strategy [first two sentences proved by hand; the rest heuristic].** The reply family is not confined unless
the adversary chooses so. After the drop the requester's Fano lines lie in V' and leave Z unrequested,
so the adversary may answer with points of Z (or fresh points) instead of V'∖S: a point z in Z placed
in all later replies covers them all, and with any y in A_2 covers the kept 7-tuple. Blocking this by
requesting Z each round costs up to r of the budget (she need not block every z every round, only
keep each z out of four kept replies whose complementary three share a point); in the worst case the
effective ground set is A_1 ∪ A_2 with slack r per reply, where non-adaptive Fano needs T >= 6k/7
(FRESH_C §7.1). So "detect waste, then Fano inside the
region" is a correct counter only to a confined adversary; against an adversary who alternates
between confinement and pivots it needs a genuinely adaptive rule, i.e. a solution of the
slack-r game on a 2k-point ground set, which I do not have.

**Sufficient condition for the adversary [proved by hand].** He wins the m-discard game if all m
replies have a common 2-cover. In Theorem 8's scheme this needs m - 2 rectangles of area <= T²/4 not
to cover T × k, guaranteed only for (m-2)T < 4k; for m = 8 that is T < 2k/3. So Theorem 8's method
gives no m = 8 adversary above 3k/4, and I found none by other means.

**Status of the discard claim: OPEN.** Unbounded m is equivalent to f(k,7) <= T (FRESH_C §8.4),
so a bounded-m strategy with proof at (3/4+eps)k would be the upper bound of the conjecture itself,
not a lemma on the way to it.

## 6. Decisive remaining gap

Decide the slack game on a bounded ground set with discards: adversary = all k-subsets of a
2k-point set V = A_1 ∪ A_2 (slack r = k - T per reply), requester has m = 8 or 9 requests and one
or two discards. If the requester wins at T = (3/4+eps)k, the winning rule (how the Fano classes are
re-cut after each omission) is the candidate lemma; if the adversary wins for all bounded m, his
omission rule is the seed of a counterexample and must be tested for coexistence in one (7,2)-family.
Tools ready for that: §1 (terminal test via the nerve), §2 (exact last round, no MILP needed),
Lemma 5.1 (prunes every kept tuple with a disjoint pair).

=============================================================================================
# Part II — the discard / confined game (second time box)

Code: `compute/twin/confined.py` (exact AND/OR solver of the confined game on atoms, with slivers).
**Status in one line: no strategy with proof and no counterexample.** The confined game is reduced to
a clean pair-covering game (§7), the Fano template is turned into "mandatory blocks" (§7.5), and
two natural re-cutting rules are shown NOT to work below 4/5 (§8), which pins down what the correct
rule must do.

## 7. The confined game is a pair-covering game [proved by hand]

Ground set V (mass N in units of k; N = 2 for V = A_1 ∪ A_2). Reply B_i ⊂ V∖S_i, complement
C_i = V∖B_i = S_i ⊔ O_i, where O_i ("omission") has mass N-1-t (= r when N = 2).
C-type of a point: I_x = { i : x in C_i }.

**7.1 Intersecting-types criterion.** Seven replies have no 2-cover iff the C-types of the points of
their union are pairwise intersecting (x = y included, i.e. no point lies in all seven replies).
*Proof.* {x,y} covers all replies iff no reply misses both iff no C_i contains both. ∎
Equivalently: the C_i cover every pair of points. This is §1 in complement language; it is symmetric
in the seven indices (no "last request" is singled out).

**7.2 Omissions never hurt on a fixed ground set.** C_i ⊇ S_i, and enlarging any C_i only adds covered
pairs. So if the requests alone cover all pairs she wins outright (non-adaptive Fano, lines of mass
3N/7 <= t). The adversary's only weapon inside a fixed ground set is to place his omissions where
they are useless; his only other weapon is fresh points, which enlarge the set of pairs.

**7.3 Rigidity at N = 2.**
(a) Every point must lie in at least 3 of the seven C_i (two sets of mass N/2 through x cannot
    cover V).
(b) Total membership is 7, so the excess ∫(|I_x| - 3) equals exactly 1 in every winning final
    position: the adversary cannot create more waste than 1, he only decides where it sits.
(c) No weighted-majority family can be the family of realized types: if w(I_x) > w([7])/2 for all x,
    then Σ_i w_i·mass(C_i) = ∫ w(I_x) > N·w([7])/2 = w([7]), contradicting mass(C_i) = 1.
    So at N = 2 the final type family is a non-threshold intersecting family; the Fano up-set (types
    containing a line) is the natural one. For N > 7/3 the majority family ("every point in at most
    3 replies") becomes available, which is why spread-out adversaries are easy.

**7.4 Window lemma.** For a set Y ⊂ V and a level x: requesting mass(Y) - x - r inside Y and the rest
of the budget outside Y (when these numbers are in range) forces mass(B_new ∩ Y) in [x, x + r]; the
adversary picks the point in the window. In particular on N = 2 she can force
mass(C_1 ∩ C_2) >= x for any x <= t, so a complementary ("wasted") pair cannot be forced on her
inside a fixed ground set. In the open game she has only the upper end of the window.

**7.5 Fano-nerve criterion and mandatory blocks.** Label seven kept replies by the points of a Fano
plane. If B_a ∩ B_b ∩ B_c = ∅ for each of the seven lines {a,b,c}, there is no 2-cover.
*Proof.* A cover gives reply-types J_x ∪ J_y = [7]; every 2-colouring of the Fano plane has a
monochromatic line, so J_x or J_y contains a line. ∎
This holds on any ground set, confined or not. By the free-sliver rule (§1) it is equivalent to:
at round c she requests ALL of

    M_c = union of B_a ∩ B_b over the lines {a,b,c} with a, b < c.

So a sufficient form of the whole game is "keep mass(M_c) <= t for every c"; the rest of each budget
is free and is used to shape later intersections. Standard labelling (lines 123, 145, 167, 246, 257,
347, 356): M_3 = B_1∩B_2, M_5 = B_1∩B_4, M_6 = (B_2∩B_4) ∪ (B_3∩B_5),
M_7 = (B_1∩B_6) ∪ (B_2∩B_5) ∪ (B_3∩B_4). The labelling may be chosen after seeing the replies.
Six-edge form: a perfect matching of six replies whose three pair-intersections have union <= t,
plus the four transversal triples of one parity having empty intersection (this is §2's Fano
5-state, and Lemma 3's 3r when the matched intersections are disjoint of mass r each).

**7.6 Slivers in complement language.** If the adversary omits a class of type I at round i he may
keep one point of it in the reply; she then requests that point for free in every later round, so it
ends with type I ∪ {i+1,…,7}. These types must be in the intersecting family too. Points neither
requested nor omitted are dominated by this sliver. (Used in `confined.py`.)

## 8. Re-cutting: constraints on the rule [proved by hand, within the Fano template]

Assign each point a class q (a point of the plane) all of whose past lines are in its type; its
*need* is the number of future lines through q. Re-cutting = re-assigning classes after each reply.

**8.1 Adaptivity is necessary, and how much.** After round 1 the total need is 2·1 + 3·1 = 5 and her
remaining budget is 6t. For t < 5/6 every winning play must turn at least 5 - 6t of the adversary's
omitted mass into needed memberships.

**8.2 A complementary pair cannot be completed (K4 leak).** If C_1 ⊔ C_2 = V are both kept, the class
L_1 ∩ L_2 is empty and the four lines not through it have total load 2·mass(V) = 4 > 4t. So one
member of a disjoint pair of replies must be discarded (agrees with Lemma 5.1); inside a fixed
ground set she avoids the situation by 7.4.

**8.3 "Pencil first" fails for t < 4/5.** Suppose rounds 1–3 are labelled as three lines through one
class, so she blocks B_1 ∩ B_2 (mass y) at round 3. After round 3 every point has type-size 1, 2
or 3, with masses satisfying 2κ + d = 1 (κ = type-size 3 = complete points, d = type-size 2). Every
non-complete point needs 2 of the 4 remaining lines: total need 4 - 2κ. At round 3 the singly
covered mass left unrequested is at least 2(1-y) - (t-y) >= r, so the adversary can make d >= r,
hence κ <= t/2. In rounds 4–7 he omits complete points while r of them are unrequested (pure
waste); if κ < r his useful contribution is at most 4(r - κ). Supply is therefore at most
max(4t, 4 - 4κ), and 4 - 2κ exceeds both when 0 < κ <= t/2 < 2r, i.e. t < 4/5. (κ = 0: every point
needs both of its two lines among four sets of mass 1; he omits off-line points and the unrequested
on-line mass r is lost.) ∎
Consequence: below 4/5 the labelling of round 3 must be decided AFTER his omission. If he completes
the sunflower (omits inside C_1 ∩ C_2): pencil. If he creates doubly covered points: they must become
the classes L_1∩L_4, L_2∩L_4 of a triangle labelling (where M_3 = ∅). In a transversal round an
omission landing on a non-complete point of the "wrong half" is useful after re-cutting (a point
of class {1,4,5} that receives 6 is re-cut to class {1,6,7}); only omissions on complete points are
certain waste.

**8.4 Candidate rule (NOT proved).** State after j rounds = masses of C-types. Choose the labelling
and class assignment minimising the largest future line load (a transportation LP: at most 2^j
types × 7 classes, 30 labellings); request the points whose class is on the current line, never a
complete point. Claim to prove: the LP value stays <= t under every omission when t >= 3/4 + eps.
I did not find the invariant. 8.1–8.3 are constraints it must respect. This LP rule is the concrete
object for agent C's solver to test against free adversaries.

## 9. Lifting to unconfined adversaries

- [proved] Criterion 7.5 and the blocks M_c do not refer to a ground set.
- [proved] What fresh points take from her is the lower end of the window (7.4): she can no longer
  force two replies to overlap, so the adversary can produce disjoint or nearly disjoint pairs,
  which by 8.2 / Lemma 5.1 must lose a member; each discard costs one request.
- [heuristic] Fresh mass in a reply is mass not spent inside old replies, so it tends to shrink the
  blocks M_c; an adversary using much fresh mass moves towards N > 7/3, where the majority family
  of 7.3(c) is available.
- [open] Whether boundedly many discards suffice. After a discard the adversary may answer
  disjointly again. Three pairwise disjoint replies lose at once, so among any three replies two
  meet, but "meet in O(1) points" is still waste. Missing: a potential showing that each wasted
  reply permanently reduces the mass he can keep away from her requests.

## 10. Computation [computed exact]

`confined.py k T` solves the 7-request confined game on 2k atoms exactly (both players exhaustive,
slivers as in 7.6). k = 3, T = 2 (t = 2/3 < 3/4): requester loses — sanity check, 5.6 s.
Runs for (k,T) = (4,3), (5,4), (6,5) hit the 9-minute limit without finishing (empty
`compute/twin/run_k*_T*.log`): NOTHING is claimed for those sizes. The solver needs round-symmetry
canonicalisation and a better request ordering (e.g. the LP rule of 8.4 first) before it is useful.
