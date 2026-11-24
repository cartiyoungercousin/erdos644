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

=============================================================================================
## 11. Is the confined adversary the worst case? (third time box)

**Answer: not provably, and not by any simulation argument. What is true is one-directional.**
- An ADVERSARY win on the 2k points A_1 ∪ A_2 transfers to the open game (11.1).
- A REQUESTER win there transfers only for 7-tuples that keep the disjoint pair (11.2), which is the
  mode she cannot use below 5k/6; in the mode she must use (drop one of A_1, A_2) I have no reduction,
  and the two obvious ones fail for stated reasons (11.3, 11.5).
- "Each disjoint pair costs one discard, and only boundedly many can be forced" is false as a
  mechanism (11.4).
I found neither a proof that fresh points are useless to the adversary nor an unconfined adversary
that provably beats what every confined one can do. So a certified requester win in agent C's
confined game would NOT by itself prove anything about general families.

Notation: conf(N) = adversaries all of whose replies lie in a fixed N-point set V known to the
requester; open = no restriction. "Fresh" = a point in no earlier reply.

### 11.1 Monotonicity [proved by hand]

Every conf(N) strategy is a conf(N') strategy for N' >= N (ignore the extra points), and in an
m-request game every open strategy uses at most mk points, so open = conf(mk) up to naming the fresh
points in advance. Hence the adversary's power is non-decreasing in N, and

    "confined to 2k is the worst case"  ⇔  the game value is constant in N for N >= 2k.

Consequences: an adversary strategy that beats every m-request requester on 2k points beats her in
the open game too; a requester win on 2k points says nothing about N > 2k.

### 11.2 Keep-mode: confinement is w.l.o.g. [proved by hand]

**Theorem.** Let A, A' be disjoint replies that are both among the seven kept, W = A ∪ A'. Replace
every other kept reply E by any k-set E' with E ∩ W ⊆ E' ⊆ W. If the original seven are 2-coverable,
so are the new seven. So in tuples that keep the pair, an adversary loses nothing by confining all
later replies to W, and fresh mass strictly helps her: a reply with mass f outside W has rectangle
(A∖E) × (A'∖E) of semi-perimeter exactly k + f (Lemma 5.1), against k for a confined reply.
*Proof.* A cover of a tuple containing A, A' is a pair (x,y) in A × A'; it covers E iff x or y is in
E ∩ W ⊆ E'. ∎
This is the only regime where "confined to A_1 ∪ A_2" is literally the worst case. It is the regime
of Theorem 8, whose adversary holds her to T >= 5k/6 [C, computed exact], so it is not the regime
in which 3k/4 can be reached.

### 11.3 Padding lemma: what a confined win does give [proved by hand]

**Lemma.** Let Σ be a requester strategy that beats every conf(V) adversary. Against an arbitrary
adversary let her feed Σ the padded replies B'_i = (B_i ∩ V) ∪ P_i, with P_i ⊂ V∖(S_i ∪ B_i) of her
choice, |B'_i| = k (possible since |V∖S_i| >= k). When Σ announces seven uncoverable padded replies,
every 2-cover of the corresponding REAL replies contains a point outside V.
*Proof.* B_i ∩ V ⊆ B'_i, so a real cover inside V covers the padded tuple. ∎
So the lift succeeds iff she can also exclude covers through outside points, i.e. pairs (x,y), x ∉ V,
with J_x ∪ J_y ⊇ kept. A sufficient condition is "points of V in at most 4 kept replies, outside
points in at most 2". That costs budget outside V: at each round she must request the outside points
already used twice. Σ is a black box using the whole budget T inside V, so the lift needs
T_open >= T_conf + (mass of twice-used outside points), and the adversary decides that mass. A
single fresh point placed in every reply already defeats the unpaid lift (cost O(1)); a fresh set F
of mass f that he re-uses whenever it is unrequested costs her on the order of f/2 per round [estimate: she must pair-cover F by
her requests, e.g. six sets of half its mass in K4 pattern], while costing him f of each reply's
mass inside V. Whether that exchange favours him is exactly the open game; the lemma
does not decide it.

### 11.4 Disjoint pairs are not "one discard each" [proved by hand]

**Proposition (two arenas).** Let V_X, V_Y be disjoint public sets of k + ⌈T/2⌉ points and let the
adversary always reply inside one arena (he can: one arena has at most T/2 requested points). Among
m replies with a in V_X there are a(m - a) disjoint pairs — every X-reply is disjoint from every
Y-reply, no three replies are pairwise disjoint — so no bounded number of discards removes them.
Nevertheless the requester wins with 7 requests and no discard when T >= 2k/3 + O(1).
*Proof.* Fix P_1..P_4 ⊂ V_X and Q_1..Q_4 ⊂ V_Y, each of at most T/2 points, covering their arena
(4·T/2 >= k + T/2). With x, y the numbers of X- and Y-replies so far, request P_{x+1} ∪ Q_{y+1}
(nothing from an arena that already has four replies). If before the last round one arena has no
reply, request more than T/2 points of the other arena, which forces a reply into the empty one.
After 7 rounds both arenas are used and one, say X, has four replies missing P_1,…,P_4, hence with
no common point. A 2-cover needs a point of V_Y for a Y-reply and then one point in all X-replies:
impossible. ∎
So a disjoint pair (A, A') is of two kinds, distinguished by the later replies E:
confined kind (E ⊂ A ∪ A', rectangle area <= k²/4: the pair must lose a member below 4k/5 [proved, Cor. 5.2];
below 5k/6 against Theorem 8's adversary [C, computed]) and
arena kind (E misses A or A', rectangle a full strip: the pair is kept and helps her). By 11.2 the
measure is the semi-perimeter k + f of the rectangle. An adversary may mix the kinds reply by reply,
and nothing I can prove bounds the number of confined-kind pairs he forces. The only general
constraint is that the disjointness graph is triangle-free, so 23 = R(3,7) replies always contain 7
pairwise intersecting ones — but not necessarily seven she can use, and "intersecting in O(1)
points" still behaves like disjoint.

### 11.5 Why compression does not work [proved by hand]

The natural reduction replaces each fresh point by an old unrequested point (a map φ from the open
ground set onto V). Covers survive (φ of a cover is a cover of the images), but requests do not:
one request of φ(u) in the confined game answers to requests of all preimages of φ(u) in the open
game, so the image adversary is weaker, not stronger. Fresh points are precisely extra copies that
she must pay for separately; this is the content of 11.3's budget term and the reason no
shifting-type argument can prove the reduction.

### 11.6 What would close it

(i) [open] Constancy of the value in N on the range 2k <= N <= 7k/3. The upper end is where the
majority template of 7.3(c) becomes available (seven replies with every point in at most three);
points of degree >= 3 in a kept 7-tuple have mass at most 7k/3, so I expect nothing new beyond it
[heuristic].
(ii) A requester strategy stated in ground-set-free terms. The Fano-nerve blocks M_c of 7.5 are
such terms: for a block strategy the open game IS the game "keep mass(M_c) <= T", and fresh points
enter only through twice-used fresh mass on the early pair of a line, whose labelling she chooses
afterwards. A certified win of agent C's solver transfers to general families only if the winning
strategy is of this form and its certificate bounds mass(M_c) for arbitrary replies, not only
for replies inside A_1 ∪ A_2.
(iii) Concretely for agent C: by 11.1 the informative direction on 2k points is an ADVERSARY
certificate. For the requester direction the same solver should be run on conf(N) with
N in {2.15k, 7k/3} (complete family, same omission scripts plus a "new territory" rule: omit the
highest-degree unrequested points), since those adversaries are at least as strong.

=============================================================================================
## 12. Does the value stabilise past N₀ ≈ 7k/3? (fourth time box)

**Outcome: job (1) is NOT proved; job (2) is answered with proved lemmas, and they show why
7k/3 is a threshold for the final 7-tuple but not (by any argument I have) for the game.**
- 12.1 gives the exact condition under which points beyond a ground set V can be merged into V
  (hosting theorem). Merging is free for points used once and for strategies that never cap or
  block at degree 2; it is not free in general, and the precise leak is identified (12.2).
- 12.3–12.6 are the lemmas behind 7k/3: forced 4-fold mass below it, the spread (majority) lemma
  above it, and the fact that every cover lives on at most 7k/3 points.
- I found no adversary whose power provably grows with N, so there is no counterexample lead either.

conf(N), open, fresh as in §11. Type J_u = set of replies containing u; image objects carry a prime.

### 12.1 Hosting theorem [proved by hand]

**Theorem.** Let Σ be a requester strategy that beats every adversary confined to a set V
(|V| >= k + T_Σ, budget T_Σ). In the open game let her run Σ against image replies B'_j ⊂ V∖S^Σ_j
that she constructs herself, and put I'_J = ∩_{i in J} B'_i. Suppose at every round j her real
request contains

    U_j = { real points u with J_u ≠ ∅ and I'_{J_u} ⊆ S^Σ_j }        (so she needs |U_j| <= T).

Then she can construct the B'_j so that at all times every real point u with J_u ≠ ∅ has a host
p in V with J'_p ⊇ J_u, and when Σ announces seven uncoverable image replies, the real replies with
the same indices are uncoverable.
*Proof.* Induction on j. A point u of the real reply B_j is not in U_j, so there is
p_u in I'_{J_u}∖S^Σ_j (for fresh u: any p_u in V∖S^Σ_j). Let B'_j consist of the p_u, u in B_j (at
most k points), padded to a k-subset of V∖S^Σ_j; this is a legal confined reply, and
J'_{p_u} ⊇ J_u ∪ {j}. Points outside B_j keep their hosts. A real 2-cover {x,y} of the kept replies
gives hosts with larger types, i.e. an image 2-cover. ∎
Hosts need not be distinct: arbitrarily many real points may share one host. The real request need
not contain S^Σ_j at all. The entire cost of ignoring the points outside V is |U_j|:

    cost_j = real mass of the types J whose image intersection I'_J is completely requested by Σ.

### 12.2 What the theorem gives and where it leaks [proved by hand]

(a) **Points used once are free.** |I'_{{a}}| = k > T_Σ, so a point lying in one reply is never in
    U_j. Fresh filler that is not re-used costs nothing, on any V, for any Σ.
(b) **Faithful case = monotonicity.** If the real ground set embeds injectively in V (hosts
    distinct, B'_j = image of B_j), then U_j is contained in the preimage of S^Σ_j and cost_j <= T_Σ:
    this is just 11.1.
(c) **Block-only strategies see only degree >= d.** If Σ only ever requests a whole I'_J with
    |J| >= d, then U_j consists of real points of degree >= d, whose mass among j replies is at
    most jk/d (7k/3 for d = 3 and seven replies). Only these points would need distinct hosts.
    [That they can always be given distinct hosts online is NOT proved.]
(d) **The leak.** She can make |I'_{ab}| no larger than |B'_a∖S^Σ_b|. When Σ caps a pair intersection
    by a partial request (most of B'_a at round b) and later requests the small I'_{ab} entirely,
    the real points of type ⊇ {a,b} are charged in full, and nothing in the hosting construction has
    capped THEIR mass: merged copies evade a cap that was paid for only once. The strategies known
    to reach 3k/4 on small ground sets (Fano blocks M_c of 7.5, matched pairs capped at r) are of
    this kind, with d = 2. In my construction, mirroring the caps needs distinct hosts for all
    points of degree >= 1, i.e. |V| >= the real ground set: no reduction.
So merging points beyond N₀ changes the winner unless the certified strategy is block-only at
degree >= 3. I could not prove stabilisation at any N₀ independent of m for general strategies.

### 12.3 Below 7k/3 high multiplicity is forced [proved by hand]

Seven replies inside an N-set have 4-fold mass at least (7k - 3N)/4, and at least 7k - 3N if no
point lies in five of them (count incidences: 7k <= 7y + 3(N - y), resp. 4y + 3(N - y)). So for
N < 7k/3 every 7-tuple has 4-fold points for free; she can never reach "every point in at most 3"
and must instead destroy every complementary (4,3)/(4,4) pair. This is forced mass that no request
can prevent. For N >= 7k/3 nothing is forced: every 4-fold point exists only because the adversary
re-used it against her requests.

### 12.4 Spread lemma (the majority family as a strategy) [proved by hand]

**Lemma.** On any ground set: if at each of the requests j = 4,…,7 the points lying in at least
three of the replies so far have mass at most T, she wins with seven requests and no discard.
*Proof.* She requests exactly those points. A point in four replies i_1 < … < i_4 lay in three
replies at request i_4 and was requested. So no point is 4-fold and two points cover at most six. ∎
Corollary: to survive, an adversary must at some request j <= 7 have 3-fold mass > T among at most
six replies. By 12.3 a confined adversary with N < 7k/3 never satisfies the hypothesis; an adversary
on more points satisfies it unless he concentrates on purpose.

### 12.5 Every cover lives on at most 7k/3 points [proved by hand]

If no point lies in five of the seven kept replies (free for her when 4T >= 3k, Lemma 3), a cover
{x,y} has both degrees in {3,4}. So coverability of the tuple depends only on the traces on
R = {points in >= 3 kept replies}, and 3·mass(R) <= 7k. All other points are *filler*.
With N points and maximum degree 4 the filler has mass at most 2N - 7k/2: none at 7k/4 (Fano
blow-up is rigid), k/2 at 2k, 7k/6 at 7k/3.

### 12.6 Why the threshold appears, and why it is not yet a theorem about the game

What fresh points give the adversary, exactly: filler. Up to N = 7k/3 more points mean more room
for replies that overlap little with the past (waste in the sense of Theorem 8, disjoint pairs) while
4-fold points are still forced (12.3). Past 7k/3 the relevant set R cannot grow (12.5), 4-fold
points are no longer forced (12.3), and an adversary who actually spreads over the extra points
loses to 12.4. That is the sense in which the gain stops. [the three facts are proved; the
conclusion "hence the game value is constant past 7k/3" is NOT]
What is missing: R is only determined at the end. During play she cannot tell filler from future
members of R, and by 12.2(d) she cannot treat them as merged without losing her caps. An adversary
on N > 7k/3 points is free to play any small-ground-set strategy and to decide reply by reply
which fresh points to re-use.
No growing adversary found: in every example I can analyse, fresh mass f in a reply shrinks the
core he plays on (replies of size k - f on R), and a smaller Fano-type core has smaller blocks, which
helps her [heuristic]. I have no adversary whose guaranteed level increases with N beyond 2k.

### 12.7 Consequence for the certification plan

A certified requester win on N₀ = 7k/3 points becomes a general bound if, in addition, the
certificate shows either
(i) the strategy is block-only at degree >= 3 (then by 12.2(c) only points of degree >= 3 matter;
    but 12.3 says such a strategy cannot win on N₀ < 7k/3, and at 7k/3 it is essentially 12.4), or
(ii) the bound mass(M_c) <= T on its blocks holds for arbitrary real replies, with caps paid on
    real points (the ground-set-free form of 11.6(ii)).
Without one of these the confined certificate does not transfer.

=============================================================================================
## 13. Reduction of the open game to a confined game on at most 3k points (fifth time box)

Code: `compute/twin/anchors.py`.
**Outcome: the reduction IS proved, in an anchored form, with no loss of budget and no extra
requests** (13.1–13.2). Its ground set is the union V of three replies with empty common
intersection, so |V| <= 3k. Two ends of the range of |V| are solved by hand (13.4, 13.5):
she wins when |V| <= 2T and when |V| >= 10k/3 - T (about 2.58k at T = 3k/4, matching the red team's
"N >= about 2.5k loses"). What is NOT proved is the window 2T < |V| < 10k/3 - T; there the game is a
concrete four-rectangle covering problem (13.3), stated as the missing inequality in 13.7.
This supersedes the negative conclusions of §11–§12: those concerned black-box simulation of an
arbitrary confined strategy; anchoring avoids simulation altogether.

### 13.1 Anchor lemma [proved by hand; checked exact]

**Lemma.** Let B_a, B_b, B_c be replies with B_a ∩ B_b ∩ B_c = ∅ and V = B_a ∪ B_b ∪ B_c. Every
2-cover of any family of replies containing these three consists of two points of V.
*Proof.* No point lies in all three, so each of the two covering points lies in at least one. ∎
She can always create such a triple: any S_2 with |S_2 ∩ B_1| >= k - T gives |B_1 ∩ B_2| <= T, and
S_3 ⊇ B_1 ∩ B_2 then gives B_1 ∩ B_2 ∩ B_3 = ∅ (single points included). More generally replies
i < j < l are anchors as soon as S_l ⊇ B_i ∩ B_j.
Write P_ab = B_a ∩ B_b (three pairwise disjoint sets), P = their union, p = mass(P),
Q_c = B_c∖P (points in exactly one anchor). Then |V| = 3k - p.

### 13.2 Exact reduction [proved by hand; checked exact]

**Theorem A.** For families of replies that contain the anchors:
(i) coverability depends only on the traces E ∩ V of the other replies, and is monotone in them
    (a larger trace can only create covers);
(ii) hence against an open adversary she may run verbatim any strategy for the *anchored confined
    game* G(V): requests inside V, adversary answers with a subset of V∖S of mass min(k, |V∖S|);
    same requests, same budget, same number of rounds; outside points never need to be requested;
(iii) conversely the adversary loses nothing by confining every later reply to V.
*Proof.* (i) By the lemma a cover is a pair in V, and it covers E iff it meets E ∩ V. (ii) Feed
the strategy the traces, padded inside V∖S when shorter than min(k, |V∖S|); by (i) padding can only
create covers, so an uncoverable padded tuple is uncoverable in reality. (iii) is (i). ∎
So every open adversary is, from the moment anchors exist, an adversary confined to at most 3k
points, as long as she keeps the anchors among her seven. She may discard and re-anchor on any
other triple; each re-anchoring costs at most three requests.
`anchors.py` check A: lemma, trace equivalence and 13.3 agree with brute force on 2000 random
7-tuples (ground sets with points outside the anchors).

### 13.3 The anchored game is a three-grid, four-rectangle covering game [proved by hand; checked]

**Theorem B.** Anchors plus four further replies E_1..E_4 have no 2-cover iff for each of the three
splits (ab|c)

    union over i of (P_ab∖E_i) × (B_c∖E_i)  =  P_ab × B_c .

*Proof.* A cover has one point x in two anchors (x in some P_ab) and the other point y in the third
(y in B_c); it covers E_i iff x or y is in E_i. ∎
With K_i = V∖E_i ⊇ S_i ("killed at round i") and I_x = {i : x in K_i}: she needs
I_x ∩ I_y ≠ ∅ for all x in P_ab, y in B_c = P_ac ∪ P_bc ∪ Q_c. Nothing is required between two points
of the same P_ab, between Q's, or between Q_c and P_ac. mass(K_i) = max(T, |V| - k) when she spends
her budget: for |V| > k + T the adversary must add omissions, for |V| <= k + T he adds none.
(The disjoint-pair Lemma 5.1 is the degenerate case P_ab = ∅ with five rectangles.)

### 13.4 Small union: |V| <= 2T [proved by hand; table checked]

**Theorem C.** If |V| <= 2T (+O(1)) she wins with four more requests, non-adaptively.
*Proof.* Rounds 4,5,6,7. Split P_12 into halves with request-types {4,7}, {5,6}; P_13 into {4,6},
{5,7}; P_23 into {4,5}, {6,7}; split Q_c into four equal parts carrying the four pairs that are not
the two types of the opposite P_ab. Two 2-subsets of a 4-set are disjoint only if complementary,
i.e. only inside one P_ab, so all required intersections hold already for the requests. Each round
requests half of every part: mass |V|/2 <= T. ∎
At T = 3k/4, |V| = 3k/2 this is the Fano blow-up with a pencil as anchors (classes of mass k/4).

### 13.5 Large union: |V| >= 10k/3 - T [proved by hand; checked exhaustively at k = 3]

**Theorem D.** If p <= T - k/3, i.e. |V| >= 10k/3 - T, she wins with four more requests and no
discard.
*Proof.* Every later request contains P; then points of P lie in no later reply. A cover needs
x in some P_ab and then y in Q_c lying in all four later replies. Let X_1 = E_1 ∩ Q (mass <= k),
X_2 = X_1 ∩ E_2, X_3 = X_2 ∩ E_3. Requests 5 and 6 contain T - p points of X_1, resp. X_2, so
mass(X_3) <= k - 2(T - p) <= T - p, and request 7 contains X_3. No such y exists. ∎
Consequences [proved]:
- an adversary whose first three replies (after her two blocking requests) span at least
  10k/3 - T points loses in seven requests; ground-set growth after the anchors is irrelevant by
  Theorem A, and growth before them only enlarges |V|;
- after a disjoint (or nearly disjoint) pair, the next reply must take more than T - k/3 from the
  pair's union or he loses in seven: "waste" cannot be repeated;
- three replies meeting pairwise only in O(1) points lose (p = O(1)), which is the rigorous form of
  "intersecting in slivers behaves like disjoint" (§11.4).
`anchors.py` check D: at k = 3, T = 2, p = 1 the strategy beats every reply sequence (all maximal
traces, four rounds; 310000 leaves each), for two anchor shapes [computed exact]. A k = 4 run was
too slow and is not claimed.

**Proposition E (shape matters) [proved by hand].** If the third anchor is exactly disjoint from the
other two (p_13 = p_23 = 0, no common point at all), the only grid is P_12 × B_3 and she wins when
p_12 <= max(T - k/4, 2T - k): request P_12 plus a quarter of B_3 four times, or use the 2×2 cover
(half of P_12 with half of B_3). So the constant T - k/3 of Theorem D is not optimal for every shape.
Caveat: a single common point of B_3 with B_1 or B_2 re-creates the grids P_13 × B_2, P_23 × B_1
(every point of B_2, B_1 must then be killed once), and the adversary gets such points for free; in
that case use Theorem D: with p_12 capped at k - T by S_2, p <= k - T + O(1) <= T - k/3 for
T >= 2k/3 + O(1). Hence **a reply meeting the union of two earlier replies in only O(1) points
loses in four more requests** [proved, via Theorem D].

### 13.6 What this says about N₀

With anchors the game lives on V with 3k/2 <= |V| <= 3k (each anchor contains two of the P_ab, so
2p <= 3k; in particular Theorem C applies to some anchors only when T >= 3k/4), and only

    2T  <  |V|  <  10k/3 - T        (1.5k < |V| < 2.58k at T = 3k/4)

is undecided. So N₀ = 10k/3 - T works in the following exact sense: **every adversary is, after
three requests, equivalent to one confined to the union V of the anchors; if |V| >= N₀ he has
already lost.** The red team's observations are instances: proportional adversaries on N >= 2.5k
give large |V|; growing ground sets only increase |V|; disjoint pairs are capped because the third
anchor must re-enter the pair's union.
The adversary can always place |V| inside the window (he controls every overlap from below: he may
always answer with fresher points), so the window cannot be avoided by her choice of S_2, S_3.

### 13.7 The exact missing statement

In the window she needs I_x ∩ I_y ≠ ∅ on the three grids with four kill-sets K_i ⊇ S_i,
mass(K_i) = max(T, |V| - k), where the adversary chooses K_i∖S_i. Two facts bound what a proof must
do [proved by hand]:
(a) Each point of P_ab must be killed at every round at which some y in B_c is killed for the only
    time; the adversary never omits a point of P voluntarily and re-includes a killed Q-point unless
    it is requested again. So freezing is forced, but only for the pair-part opposite to the Q_c
    being killed: she may specialise rounds by c (Proposition E is the extreme case, valid only without
    stray common points). I did not
    optimise this; T - k/3 in Theorem D is sufficient, not shown necessary, and the true lower end
    of the window depends on the shape (p_12, p_13, p_23).
(b) [heuristic] For |V| = 2k, p = k (e.g. a disjoint pair and a third reply inside its union, or
    §8.3's pencil) the natural template is K4 with zero slack: mass(K_i) = k = |V|/2 exactly, so
    redundant omissions should defeat it. This is the obstruction behind Theorem 8 and 8.3, now
    seen as a property of the anchors rather than of the ground set.
**Missing inequality.** Let val(p_12, p_13, p_23) be the smallest T/k at which she wins the
three-grid game for anchors of that shape, with re-anchoring allowed (m requests in total). The
general bound f(k,7) <= T + O(1) follows from

    for every adversary there is, within boundedly many requests, an anchor triple with
    val(p_12, p_13, p_23) <= T/k,

and 13.4–13.5 prove it outside the window. Inside the window I have neither a strategy nor an
adversary. The confined computation that would now transfer verbatim to general families (by
Theorem A) is: anchors of prescribed shape, adversary confined to V = their union, requester free
with re-anchoring — not the game on A_1 ∪ A_2 with a disjoint pair, which is the K4 point (b).

=============================================================================================
## 14. Near-copy region, steering lemma, and the limit of the three-anchor route (sixth time box)

Scaled units (k = 1, t = T/k). Anchors, P_ab, p_ab, V, B_c, K_i = V∖E_i as in §13.
**Outcome.**
- STEP 1 (partial): the near-copy region is quantified from the adversary's side: **max p_ab > t²
  is an adversary win of the anchored game** (Theorem F, proved; it reproduces the top of every
  table of FRESH_C §13). Proved requester wins remain Theorems C, D and Prop. E. The claim "balanced
  shapes are requester wins" is NOT true near 3/4: at (k,T) = (8,6) the balanced window shapes
  (3,3,3), (3,2,2), (4,3,3), (4,4,3) are adversary wins [computed with C's `anchor.js`].
- STEP 2: proved with "near-copy" := max p_ab > t². She obtains an anchor triple with all three
  pair-intersections <= t² in three requests **iff t >= t₁ = (√17 - 1)/4 ≈ 0.7808** (S1, S3).
  For 3/4 <= t < t₁ a two-arena adversary keeps every triple near-copy for every number J of replies
  (Theorem G), so the protocol "J replies, commit to three anchors, four more replies" fails there.
- Consequence: below t₁ a proof cannot have the form "steer to a good anchor triple, then play the
  anchored game". The same two-arena adversary is beaten by a certificate with FOUR replies having
  empty common intersection (§11.4), so the next object is a four-anchor version of §13.

### 14.1 Theorem F: one large pair-intersection loses the anchored game [proved by hand]

**Theorem F.** If p_12 > t² (any p_13, p_23), the adversary wins the anchored game: whatever the four
further requests, anchors plus the four replies have a 2-cover.
*Proof.* He replies with E_i ⊇ as much as possible of (P_12 ∪ B_3)∖S_i: all of it if its mass
1 + p_12 - s_i is at most 1 (s_i = mass of S_i inside P_12 ∪ B_3), otherwise a subset of mass 1.
Then K_i ∩ (P_12 ∪ B_3) has mass max(s_i, p_12) <= max(t, p_12), so the rectangle
(K_i ∩ P_12) × (K_i ∩ B_3) has area at most max(t, p_12)²/4. Four rectangles cover the grid
P_12 × B_3 (area p_12·1) only if max(t, p_12)² >= p_12, i.e. p_12 <= t² (for t < p_12 < 1 the inequality
p_12² >= p_12 fails; for p_12 = 1 he puts the whole omitted part on one side, so the four
rectangles cannot tile). By Theorem B an uncovered point of the grid is a 2-cover. ∎
The same holds for each pair. Discrete form: p_ab > T²/k. Check against FRESH_C §13 and my rerun:
every shape with p_12 >= 3, 4, 5, 6, 5, 7 at (k,T) = (4,3), (5,4), (6,5), (7,6), (8,6), (8,7) is in
the adversary lists (T²/k = 2.25, 3.2, 4.17, 5.14, 4.5, 6.125). It is necessary, not sufficient:
e.g. (5,1,0) at (8,7) and (3,3,3) at (8,6) are adversary wins with all pairs below T²/k.

**Obligations lemma [proved by hand].** In the anchored game the adversary can ensure
(a) every point of P is killed at least twice (if x in P_ab is killed only at round i, then
B_c ⊆ K_i; he keeps one unrequested point of B_c in E_i, possible as |B_c| > T), and
(b) if P_ab ≠ ∅ (one point suffices) every point of B_c is killed at least once.
So O(1) common points between anchors change the game: this is why (5,0,0) is a requester win and
(5,1,0) an adversary win at (8,7).

### 14.2 Steering lemma [proved by hand]

Let λ_t = 2 - 2t² - t (λ_t > 0 iff t < t₁; λ_{3/4} = 1/8).
**S1 (gap lemma).** If two replies satisfy λ_t <= p_ij <= t², one more request gives an anchor triple
(i, j, l) with all three pair-intersections <= t².
*Proof.* Request B_i ∩ B_j together with max(0, 1 - t² - p_ij) points of each of B_i∖B_j, B_j∖B_i.
Cost p_ij <= t if p_ij >= 1 - t², else 2 - 2t² - p_ij <= t. The reply meets B_i and B_j in at most
t² each and misses B_i ∩ B_j. ∎
**S2 (structure when no pair is in the gap), t >= 3/4.** Call i ~ j if p_ij > t². If no pair has
λ_t <= p_ij <= t², then ~ is an equivalence relation (p_il >= p_ij + p_jl - 1 > 2t² - 1 >= λ_t, because
4t² + t - 3 = (4t - 3)(t + 1) >= 0), classes are pairwise λ_t-disjoint, and if she always requests
B_i ∩ B_j for one fixed pair in different classes, a reply in a third class gives anchors with
p < 3λ_t <= t - 1/3 (true for t >= 0.747), a win by Theorem D. So the adversary is confined to at
most two classes of mutual near-copies with small cross-overlap: the "two clusters" of §4.
**S3.** For t >= t₁, λ_t <= 0, so S1 applies to B_1, B_2 (p_12 <= 1 - t <= t² after S_2 ⊂ B_1):
three requests give anchors outside the near-copy region.

### 14.3 Theorem G: below t₁ steering out of the near-copy region is impossible [proved by hand]

**Theorem G.** Let 3/4 <= t < t₁ and choose n with 1 + t/2 <= n < 2 - t² (possible exactly when
t² + t/2 < 1, i.e. t < t₁). The adversary answering inside one of two disjoint arenas of mass n
(the one with at most t/2 requested points) has, after any number of replies: same-arena pairs
with p >= 2 - n > t², cross-arena pairs disjoint. Every triple contains two replies of one arena,
so every anchor triple is near-copy and, once she commits to it, he wins by Theorem F.
The threshold is the same number t₁ from both sides: 2(1 - t²) <= t is the cost of capping one
member of each cluster at t², and n = 1 + t/2 < 2 - t² is the room for two arenas.
Note: the two-arena adversary is not a strong adversary — she beats it in seven requests with four
same-arena replies of empty common intersection plus one reply of the other arena (§11.4). What
fails is only the three-anchor certificate.

### 14.4 What the data say about STEP 1 near 3/4 [computed with C's anchor.js; reading is mine]

(8,6), t = 3/4: 17 requester shapes of 55: all shapes with p_12 <= 2, the shapes (3,0,0), (3,1,0),
(3,1,1), (3,2,0), (3,2,1), (4,0,0), and the Fano-end shape (4,4,4) (|V| = 2T). Every other window
shape is an adversary win, including balanced ones. (8,7), t = 7/8: 41 of 55, losing only near-copy
shapes and (4,4,0). So the requester region grows from "small p, plus the Fano point" at 3/4 to
"everything except near-copies" at 7/8; "balanced shapes win" is a statement about t well above
3/4. In the proved terms: Theorem D gives p <= t - 1/3 (3.3 of 8 at t = 3/4; the data show about
p <= 6 with p_12 <= 3), Theorem C gives the Fano point, Theorem F the region p_12 >= 5.

### 14.5 Exact gaps

1. STEP 1: the requester region between Theorem D and Theorem F as a function of t. The data
   suggest that at t = 3/4 + eps it is a small neighbourhood of the Theorem D region and of the Fano
   point; I have no proof of either inclusion beyond C, D, E, F.
2. STEP 2 is settled for the F-definition of near-copy: threshold t₁ ≈ 0.781. A steering lemma for
   t < t₁ needs a different certificate. The natural one, forced by Theorem G and S2: with two
   clusters, take FOUR replies of one cluster with empty common intersection and one reply
   of the other. Not worked out: the four-anchor analogue of the anchor lemma only confines covers
   to the union of the four, and the cross-overlaps < λ_t must be shown harmless.
3. For t >= t₁ what is missing for a full hand proof of f(k,7) <= t₁k + O(1)-type bounds is STEP 1
   on the region {all p_ab <= t²}: by 14.1 it is not all winning, so S1 must be strengthened to
   steer into the true requester region (the caps in S1 can be lowered: with t >= t₁ she can cap
   both new intersections at any level c with 2(1 - c) - p_12 <= t, i.e. c >= 1 - (t + p_12)/2).

=============================================================================================
## 15. Step 1 for the petal architecture near t = 3/4 (seventh time box)

Code: `compute/twin/petal22.py`. Reduction and steering for petals are the petal agent's
(notes/PETAL.md); this section only answers "which petal configurations does she win".
**Outcome.** (i) The petal game is the confined pair-cover game on the union U of the petals,
continued from the petals; when |U| <= k + T the adversary has no move and the question is a
finite design problem (15.1). (ii) Four petals from one cluster of near-copies are an adversary
win (15.3). (iii) **Triple-free four petals are the winning architecture**: only three grids of
complementary pair-cells remain, three rounds suffice, and for two pairs with cores a, b the
exact criterion is L*(a,b) <= T (15.4); e.g. a = b <= 4T/5, which at t = 3/4 covers near-copy pairs
(overlap between t² = 0.5625 and 0.6). (iv) Three petals of a cluster plus one outside petal are
not settled (15.5).

### 15.0 Parked: job (A), the record path [proved by hand]

**Theorem H.** For T < 4k/5 every anchor shape (0, b, k - b) with b <= T (a disjoint pair and a third
reply inside its union) is an adversary win of the anchored game: with Z ⊂ B_1∖B_3, |Z| = k - T,
X = B_1∖Z, Y = B_2, he answers inside X ∪ Y; B_3 and the four replies each kill a rectangle of
semi-perimeter T in X × Y, total area <= 5T²/4 < Tk (Theorem 8's count). After a disjoint opening he
can always choose such a third reply (her caps on p_13, p_23 sum to 2k - T >= k). So "all pairs
<= t²" is not a requester region, and three-anchor steering in seven requests gives nothing below
4k/5 (5k/6 by C's exact value for this adversary). The record path needs J >= 4 anchors-to-choose
and the true requester region; not pursued.

### 15.1 The petal game is a confined pair-cover continuation [proved by hand]

Petals P_1..P_m (m <= 4) with empty common intersection, U their union, N = |U|/k. For x in U let
M_x = {i : x not in P_i} (nonempty). Later replies E_1..E_q (q = 7 - m), K_r = U∖E_r ⊇ S_r ∩ U,
I_x = {r : x in K_r}. A pair {x,y} ⊂ U covers the petals iff M_x ∩ M_y = ∅ ("covering pair").
**The tuple is uncoverable iff I_x ∩ I_y ≠ ∅ for every covering pair**, i.e. iff the 7-round types
M_x ⊔ I_x are pairwise intersecting: this is the game of §7 on the ground set U, started after m
rounds whose complements U∖P_i cover U. (m = 3 is §13.)
**No-adversary range.** If N <= 1 + t, then |U∖S| <= k for a full request inside U: the adversary's
best reply contains all unrequested points of U and K_r = S_r. The continuation is then a
one-player design problem: choose kill-types I_x ⊆ [q] with all round loads <= T. In general a
design with loads <= T is sufficient, and it is also necessary whenever the adversary can place his
forced omissions (mass N - 1 - t per round) on points that are in no covering pair.
**Cost lemma.** A point missing exactly one petal needs two kills (otherwise that whole petal,
mass k > T, would have to be killed in one round; he keeps one of its points). A point x with
|I_x| = 1 forces all its partners into that round.

### 15.2 Notation for four petals

Cells by membership J ⊆ [4] (J = [4]∖M). Triple-free = no point in three petals; then cells are
singles and the six pair-cells c_ij = |P_i ∩ P_j|, and the covering pairs are exactly
c_12 × c_34, c_13 × c_24, c_14 × c_23 (the three perfect matchings of K4). Singles are in no
covering pair. She makes petals triple-free by requesting, when a petal is created, all pairwise
intersections of the earlier petals (cost: their total mass, must be <= T).

### 15.3 Four petals from one cluster lose [proved by hand]

**Proposition.** If every point of U misses exactly one petal (N = 4/3: the four complements
partition U into parts of mass k/3; pairwise overlaps 2k/3), every point needs two kills in three
rounds: 8k/3 <= 3T, so the adversary wins for T < 8k/9. In the symmetric family with pair-missing
cells (each point misses one or two petals, overlaps 2k/3 - π) the same count gives: adversary win
whenever the pairwise overlap exceeds 3T/2 - 2k/3 (0.458k at t = 3/4), in particular for all
near-copy clusters (overlap > t²k). So "four same-arena replies with empty common intersection"
is a certificate only together with a reply almost disjoint from U (as against the two-arena
adversary, who is forced to supply one); a careful adversary never supplies it.

### 15.4 Triple-free four petals: exact criteria [proved by hand; checked exact]

**(a) Uniform K4.** Six pair-cells of mass k/3, no singles (N = 2): round r requests one
complementary pair of cells, load 2k/3. Requester win for T >= 2k/3 (+O(1)). This is the Fano
blow-up with the class of the line {5,6,7} empty.
**(b) Two pairs.** Petals x, x', y, y' with cores a = |x ∩ x'|, b = |y ∩ y'|, the four cross
intersections of O(1) points, triple-free. Let

    L*(a,b) = min( a + b/3,  b + a/3,  2(a+b)/3,  3a/4 + b/2 [if b >= a/2],  3b/4 + a/2 [if a >= b/2] ).

**Theorem I.** She wins with three more requests iff L*(a,b) <= T + O(1).
*Proof.* Only the grid core_X × core_Y and two pairs of single points have to be killed. A kill-type
assignment is a pair of cross-intersecting families on [3]; up to symmetry the maximal pairs are
({123}, singletons), (2-sets, 2-sets), ({12},{13} ; {1},{23}) and its mirror, giving the five
loads. Necessity: he puts every unrequested core point into his reply (they fit while she requests at
least a + b - k core points) and omits singles (there are 4k - 2a - 2b >= 3k - a - b - T of them), so the kill sets in the cores are
her requests, or sets of mass a + b - k <= T of his choosing if she requests less. ∎
`petal22.py`: the covering pairs are as stated (brute force); design 3 leaves no 2-cover against
random replies with fresh and re-used outside points at (k,T,a,b) = (5,4,2,2), (8,6,4,4); and the
exact atom optimum of the 3-round design equals ceil(L*(a,b)) for all 1 <= a <= b <= 6 [computed exact].
Consequences: a = b wins iff a <= 4T/5. At T = 3k/4: a, b <= 0.6k; or a <= 0.75k with b = O(1);
generally L* is increasing in a and b, so **smaller overlaps are always better for her, and she
controls every overlap from above** (caps). With cross-cells of positive mass add
max(c_13 + c_24, c_14 + c_23) to the load of two different rounds (sufficient; exact value = an LP).
**(c) General triple-free.** Three grids, three rounds; sufficient: one complementary pair per
round, loads c_12 + c_34, c_13 + c_24, c_14 + c_23 <= T. The exact value is a small LP (request C1).

### 15.5 Three cluster petals plus one outside petal [partly proved]

x, x', x'' with common core c_3 = |x ∩ x' ∩ x''| and y outside. Covering pairs: core × y (grid
c_3 × k) and, for each cross point of y with one x, the cell of the other two x's only. The grid
alone needs L*(c_3, k) <= T, i.e. c_3 <= T - k/3 (freeze the core, thirds of y) [proved: necessary].
The cross points cannot be prevented (a petal cannot be requested entirely), so the pair-only
cells carry "kill once" obligations as in 14.1; with them I have neither a strategy nor an
adversary. Since she can lower c_3 by requests but the pair-only cells then grow, I expect this
configuration to be worse for her than 15.4(b). Not settled.

### 15.6 What to steer to (for the petal agent)

Target: four replies, triple-free, with L* of each complementary pair of pair-cells within T, the
three grids fitting in three rounds. Against two clusters this means one pair from each cluster
with both cores capped near 0.6k (at t = 3/4), cross-overlaps O(1), and the triple intersections
requested away when the third and fourth petals are created (cost = core of the first pair + O(1)).
What I did not prove: that she can force both caps simultaneously (the cap on a core costs
k - 0.6k = 0.4k per cluster, and the triple-free block of the first core costs up to 0.6k more at
the fourth petal).

### 15.7 Requests for C (exact, real sets)

C1. Four-petal confined game, triple-free configurations (c_12, c_13, c_14, c_23, c_24, c_34) plus
    singles, three further requests: table of requester/adversary shapes at (k,T) = (8,6), (9,7),
    (12,9), (12,10). Prediction for two pairs with O(1) cross points: R iff ceil(L*(a,b)) <= T up to
    the cost of the cross points.
C2. Same game for one-cluster configurations (every point missing one or two petals) at (8,6),
    (9,7), (12,9): prediction A for every near-copy configuration.
C3. Configuration 15.5 (three cluster petals, common core c_3, pair-only cells, one outside petal
    with one point in each x) at (8,6), (9,7), (12,9), over c_3 and the pair-only masses.
C4. Selection game: four replies, she wins iff they are triple-free with L*-feasible grids (C1's
    table); can she force it at (8,6), (9,7), (12,9), (12,10), and with five or six replies choosing
    four?

=============================================================================================
## 16. The concentrated case (eighth time box)

**Outcome: the concentrated-case lemma is NOT proved.** Proved: an exact block form of the Fano
six-state (16.1), that with unboundedly many requests the lemma is the conjecture for families on
fewer than 3k - T points (16.2), the lemma for ground sets of at most 3T - k/2 points (16.3), exact
win conditions and a necessary count for the quadrangle-first labelling (16.4), and the reason the
line-first labelling stops at 3T - k/2 (16.5). The missing inequality is stated in 16.6. Units:
k = 1, t = T/k, r = 1 - t; ground set V of mass N, 1 + t <= N < 3 - t, ω = N - 1 - t.

### 16.1 Block form of the six-state [proved by hand]

Label the seven kept rounds by the points of a Fano plane; J_x = set of replies containing x.
The Fano criterion (7.5) says every J_x must be line-free. For a line-free J put
T(J) = { c not in J : c is the third point of a line through two points of J }.
**A point of type J must be requested at every later round c in T(J), and nowhere else.** So the game
is: at round c request M_c = { x : c in T(J_x) }; she wins iff mass(M_c) <= t at every round; the rest
of each budget is free. |J| <= 1: never blocked. |J| = 2: blocked once, at the third point of its
line. A non-collinear triple: blocked at the three third-points of its sides and free at one round
(it can grow to a quadrangle). A quadrangle: blocked at the three remaining rounds.
Up to isomorphism the labelling of the first four rounds is one of:
(L) 1,2,3 collinear (M_3 = B_1∩B_2; the first three replies are anchors);
(T) 1,2,3 a triangle and 4 on one of its sides (M_3 = ∅, M_4 = B_a∩B_b);
(Q) 1,2,3,4 a quadrangle (M_3 = M_4 = ∅). Then 5,6,7 are the diagonal points and

    M_5 = B(m_1),  M_6 = B(m_2),  M_7 = B(m_3) ∪ (B_5 ∩ B_6),

where m_1, m_2, m_3 are the three perfect matchings of {1,2,3,4} in an order of her choice and
B(m) = union of B_a ∩ B_b over the two pairs of m.
The labelling may be decided after seeing the replies, as long as it is consistent with the blocks
already made (none before round 3; in (Q) none before round 5).

### 16.2 Stationary adversaries [proved by hand]

If she may repeat requests, a reply that differs from an earlier reply to the same request only adds
a reply to the pool, and the winning condition (some seven replies uncoverable) is monotone in the
pool. So with unboundedly many requests the adversary is w.l.o.g. a fixed map S ↦ B(S), i.e. a
family, and the concentrated-case lemma becomes: *a (7,2)-family on fewer than 3k - T points has
tau <= T*. With a bound m(eps) it is formally stronger. I know no argument special to bounded
ground sets beyond those below; in particular the fractional relaxation is useless (the complete
family on 2k points has fractional transversal number 2).

### 16.3 The lemma for N <= 3t - 1/2 [proved by hand]

**Proposition 16.A.** If all replies lie in a known set V with |V| <= 3T - k/2 - O(1), she wins with
seven requests and no discard.
*Proof.* B_1 arbitrary. Fix a_0 ⊂ V∖B_1 of mass α = N - 2t. S_2 = a_0 ∪ (t - α points of B_1), so
|B_1 ∩ B_2| <= r + α. S_3 = a_0 ∪ (B_1 ∩ B_2), of mass at most 2α + r = 2N + 1 - 5t <= t. Now
B_1, B_2, B_3 are anchors and none of them meets a_0, so their union has mass <= N - α = 2t, and
Theorem C finishes with four non-adaptive requests. ∎
(This is the "first edge arbitrary, then Fano" range of FRESH_C §7.1, now as a seven-request proof.)
Above 3t - 1/2 the kernel a_0 cannot be both large enough and affordable twice.

### 16.4 Quadrangle-first: exact conditions after four replies [proved by hand]

Let, after four replies, n_3, n_4 = mass of points in exactly three / four of them, c(m) = mass of
points whose type is exactly a pair of m, σ_0, σ_1 = mass in no / exactly one reply, and
L(m) = n_3 + n_4 + c(m) = mass of B(m). The certificate of labelling (Q) is completed iff, for some
order of the matchings,
    L(m_1) <= t,   L(m_2) <= t,   L(m_3) + e <= t,
where e = mass of B_5 ∩ B_6 on points in at most one of the first four replies; she caps e with the
spare budget t - L(m_2) of round 6 (and shapes B_5 with t - L(m_1) at round 5).
**Count.** Σ_m L(m) = 8 - 3N + 3σ_0 + σ_1 - 2n_4 (from 4 = σ_1 + 2c + 3n_3 + 4n_4 and
N = σ_0 + σ_1 + c + n_3 + n_4). Hence against an adversary whose fourth reply avoids the common
points of the first three (n_4 = 0), **labelling (Q) needs N >= 8/3 - t** (1.917 at t = 3/4), with
equality only if every point lies in two or three of the four replies and the three loads are
exactly balanced. For N >= 2 no triple points are forced and (Q) is the K4 pattern of §15.4.
*Example* (N = 2): anchors of shape (r, t/2, t/2) and B_4 = the three single parts give pair-cells
c_12 = c_34 = r, c_13 = c_24 = c_14 = c_23 = t/2, matching loads (2r, t, t), e = 0: she wins. If
instead he puts unrequested points of B_1 ∩ B_2 into B_4, triple points appear, the loads can
become infeasible in (Q), and she has to fall back on labelling (L) with these anchors.

### 16.5 Why (L) stops at 3t - 1/2 and what is left between [proved where stated]

In (L) the first three replies are anchors and the rest is the anchored game on their union.
Near t = 3/4 the requester region of that game is, by C's exact tables, a neighbourhood of the
Fano point |U_3| <= 2t together with small-overlap shapes p <= about t (which the concentrated
hypothesis p > t excludes) [computed, (8,6)]. She controls |U_3| only through the kernel a_0 of
16.3. So:

| N (units of k, t = 3/4 + eps) | status |
|---|---|
| <= 3t - 1/2 ≈ 1.75 + 3eps | proved (16.A) |
| (3t - 1/2, 8/3 - t) ≈ (1.75, 1.917) | open; (Q) is excluded by the count, (L) needs anchors off the Fano point, (T) not analysed |
| [8/3 - t, 3 - t) ≈ [1.917, 2.25) | open; (Q) available, needs the inequality below |
| >= 3 - t | spread case (petals / Theorem D) |

The red team's computed wins at t = 0.76 on N = 1.9 (just below 8/3 - t = 1.907) therefore cannot
be pure (Q); they must be (T) or (L) with adaptive continuation. Worth reading off their lines.

### 16.6 The exact missing inequality

For N in [8/3 - t, 3 - t): **she can choose S_2, S_3, S_4 so that, whatever the replies, some order of
the three matchings satisfies L(m_1), L(m_2) <= t and L(m_3) + e <= t.** Equivalent form with
Φ(state) = min over orders of max(L(m_1), L(m_2), L(m_3) + e*): she forces Φ <= t after four replies,
where e* is the adversary's best value of e against her caps. Her tools are the window lemma (each
overlap with one chosen set in a window of width ω) and top-degree requests (n_3 <= p - t, n_4 = 0);
the adversary's are the choice inside each window and the triple points he creates in B_4. The
count leaves her total slack 3t - (8 - 3N) - 3σ_0 - σ_1, which is 3eps at N = 23/12; so near the
lower end she must also keep σ_0 = σ_1 = 0 and the loads balanced to within eps, with windows of
width ω ≈ 1/6. I do not see how, and I expect the true statement to need the fourth labelling (T)
there.
For N in (3t - 1/2, 8/3 - t): the analogous statement for labelling (T) — after three free replies
and S_4 ⊇ B_a ∩ B_b for a pair of her choice — is not even formulated as a count yet.

### 16.7 Requests for C (exact)

D1. Confined game on N = 1.8k, 1.85k, 1.9k, 2.0k at T = 0.76k-type sizes (e.g. (k,T,N) = (12,9,22),
    (12,9,23), (12,9,24), (12,10,24), (16,13,30)): for each winning requester line record which of
    (L), (T), (Q) the kept seven realise (which triples of kept replies have empty intersection).
D2. Four-reply states: on the same sizes, the set of 4-states from which (Q) wins (16.4) and whether
    she can force one; this is a 4-round game plus a closed form, far smaller than the 7-round game.
D3. The same for (T): states after four replies with one blocked pair.
