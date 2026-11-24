# PETAL — the petal (four-anchor) architecture for 3/4 < t < t₁ (Erdős #644)

Scope (after the coordinator's redirect): (1) the reduction for petal anchors, (2) steering into a
petal configuration for t slightly above 3/4. Part (3), "which petal shapes win the confined game",
is the twin's (TWIN §15); it is used here, not redone. Code: `compute/petal/petal_checks.py`.
Units: k = 1, t = T/k. Tags: [proved by hand] / [computed exact] / [simulated] / [heuristic].

**Bottom line.**
1. **Reduction: done, for any 2 <= q <= 6 petals, and sharper than §13** (§1). Every 2-cover of a
   tuple containing the petals is an edge of an explicit "dangerous graph" Γ(P) on the *active set*
   U*(P) ⊆ U; coverability depends only on traces on U*, is monotone, and confined wins transfer to
   the open game verbatim. One centre wins iff it misses U*; three centres with pairwise disjoint
   traces on U* win (Lean `three_centres` with U replaced by U*).
2. **Steering below t₁: a dichotomy, not a full lemma** (§3, Theorem J). For t >= 3/4 and
   c = 4t/5, λ = (9t/5 - 1)/7 (c = 0.6, λ = 0.05 at t = 3/4): within 14 requests she either wins
   outright (four same-class petals + three forced centres with disjoint traces, or Theorem D), or
   two replies have overlap in the band [λ, c]. This beats the two-arena adversary of Theorem G and
   all "leaky" two-arena adversaries with leak <= about 0.03, for every t >= 3/4.
3. **Decisive gap** (§5): a banded pair (λ <= overlap <= 4t/5). It is exactly a legal *core* of the
   twin's winning shape (Theorem I, a <= 4T/5), but I cannot complete it to a winning triple-free
   four-petal configuration against an adversary who keeps overlapping the pair's union: adding a
   triple-free petal costs the total pair mass p of the earlier petals, and he can push p above t.

---------------------------------------------------------------------------------------------

## 1. Petal reduction [proved by hand; checked exact]

Petals P = {B_1..B_q}, 2 <= q <= 6, replies with **empty common intersection** (single points
included); U = their union. For x in U: J_x = {a : x in B_a} (nonempty, proper),
M_x = [q]∖J_x (co-type, nonempty). Centres C_1..C_r, r <= 7 - q: any further replies.

**Dangerous graph.** Γ(P) = graph on U with x ~ y iff M_x ∩ M_y = ∅ (every petal contains x or y).
**Active set.** U*(P) = non-isolated vertices of Γ. Formula: x is active iff the petals missing x
have a common point, ∩_{a in M_x} B_a ≠ ∅. (q = 3: Γ is the three grids P_ab × B_c of Theorem B, and
U* = P ∪ ⋃{B_c : P_ab ≠ ∅}; q = 2: the grid B_1 × B_2 of Lemma 5.1; q = 4, no point in three petals:
the three grids of TWIN 15.2, singles inactive.)

**P1 (petal lemma).** Every 2-cover of any family containing P is an edge {x,y} of Γ(P); in
particular x ≠ y and x, y in U*(P).
*Proof.* Each petal contains x or y, so M_x ∩ M_y = ∅ once both are in U. If x were outside U, y would
lie in every petal; so x, y in U. x = y would be a common point. ∎

**P2 (centre criterion; Theorem B for petals).** P ∪ {C_1..C_r} has no 2-cover iff every edge
{x,y} of Γ(P) is missed entirely by some centre (x, y both outside C_i). With K_i = U*∖C_i,
I_x = {i : x in K_i}: iff I_x ∩ I_y ≠ ∅ for all edges; i.e. the kill sets K_i cover Γ by induced
subgraphs. *Proof.* P1, and {x,y} meets C_i iff not both are missed. ∎

**P3 (reduction; Theorem A for petals).** For families containing P:
(i) coverability depends only on the traces C_i ∩ U*(P), and is monotone in them (a larger trace
only creates covers);
(ii) any requester strategy for the *petal game* G(P) — requests inside U*, adversary answers with
a subset of U*∖S of mass min(1, |U*∖S|), r rounds — can be run verbatim in the open game: feed it
the traces, padded inside U*∖S; same requests, same budget, same rounds;
(iii) the adversary loses nothing by confining every later reply to U* (plus irrelevant points).
*Proof.* (i) is P2: the condition mentions only C_i ∩ U*. (ii) Padding enlarges traces, so by (i) an
uncoverable padded tuple is uncoverable in reality. (iii) is (i). ∎
So W = U*(P) is the set "determined by the anchors". It can be much smaller than U: singles of
triple-free four petals are inactive; in Prop. E's shape U* = P_12 ∪ B_3.

**P4 (certificates).**
(a) *One centre:* P + C has no 2-cover iff C ∩ U*(P) = ∅. Hence **|U*(P)| <= t for some petal set
    (q <= 6) is a win in one more request**, and in any (7,2)-family with τ > T every edge meets
    U*(P) for every such P ⊆ H. (q = 6: this is Cor. 4's set D; Lemma 2's "6+1 star" is the case
    C ∩ U = ∅.)
(b) *Residual graph:* after centres C_1..C_j the surviving edges are those meeting every C_i.
    The last request wins iff it contains all vertices of the surviving graph (the adversary can
    put any single unrequested point into his reply).
(c) *Three centres:* if C_i ∩ C_j ∩ U*(P) = ∅ for i ≠ j, then P + C_1 + C_2 + C_3 has no 2-cover
    (each centre contains x or y, so one of them lies in two centres). This is `three_centres`
    with U* in place of U; she obtains it by S(C_2) ⊇ Z_1, S(C_3) ⊇ Z_1 ∪ Z_2, Z_i = C_i ∩ U*.
`petal_checks.py A`: activity formula, P1, P2, trace equivalence and monotonicity, P4(a), P4(c)
agree with brute force on 2063 random systems (q = 2..6, ground sets of 6–12 points)
[computed exact].

Not Lean-formalised (no Lean edits in this box). The statements are one-line extensions of
`Anchor.lean` (`anchor_cover_mem` with a finite petal family) and `ThreeCentres.lean`.

## 2. Steering tools [proved by hand]

**F (forcing).** Requesting a subset of mass 1 - c of a reply B forces |E ∩ B| <= c for the next
reply E. Cost 1 - c.
**RI (running intersection).** Let a class of replies be built so that each new member E answered
a request containing min(b, |I|) points of the current common intersection I of the class. Then
|I| <= 1 - (j-1)b after j members, and if 1 - 2b <= b (i.e. b >= 1/3) the first four
members have empty common intersection. With two classes served simultaneously (b each) she does
not need to know in advance which class the reply joins.
**DT (disjoint traces).** P4(c): cost of the third centre's request is |Z_1 ∪ Z_2| plus whatever
is needed to make the reply a centre of the intended kind.

## 3. Theorem J: two-class adversaries lose; in general a banded pair appears [proved by hand; simulated]

Fix t >= 3/4 and numbers c, λ with

    (J1) λ <= 2c - 1,   (J2) 3λ <= t - 1/3,   (J3) 1 - c + 7λ <= t,   (J4) 2λ <= 1 - c,  t - λ >= 2/3.

Example: c = 4t/5, λ = (9t/5 - 1)/7; at t = 3/4: c = 0.6, λ = 0.05. (Other choices trade the two ends
of the band: c = t² gives λ = (t + t² - 1)/7 = 0.0446 at 3/4.)

**Theorem J.** There is a requester strategy of at most 14 requests such that either seven of the
replies have no 2-cover, or at some moment two replies have overlap in the band [λ, c].

*Proof.* Assume no pair of replies ever has overlap in [λ, c]. Write i ~ j if p_ij > c. By (J1),
p_il >= p_ij + p_jl - 1 > 2c - 1 >= λ, so ~ is an equivalence relation; different classes overlap
in less than λ.
*Standing request.* As soon as two classes exist, with first members X_1, Y_1, every request
contains X_1 ∩ Y_1 (mass < λ). If a reply E falls in a third class, (X_1, Y_1, E) are anchors with
p < 3λ <= t - 1/3 (J2), and she wins by Theorem D in four more requests.
*Step 1 (petals; at most 7 requests).* Request min(b, |I^X|) points of I^X and min(b, |I^Y|) of I^Y,
b = (t - λ)/2, where I^c is the common intersection of the first (up to four) members of class c.
By RI a class with j <= 3 members has |I| <= 1 - (j-1)b, and 1 - 2b = 1 - t + λ <= b by (J4), so the
fourth member misses all of I. Among seven replies one class, call it X, has four members
X_1..X_4 with empty common intersection. U = their union.
*Step 2 (three centres; 3 requests).* For j = 1, 2, 3 request
S = F_j ∪ (Z_{<j}∖X_1) ∪ (X_1 ∩ Y_1), where Z_i = C_i ∩ U are the traces of the centres obtained so
far, F_j ⊂ X_1 has mass 1 - c and contains Z_{<j} ∩ X_1 (mass < 2λ <= 1 - c by (J4)).
By F the reply C_j has |C_j ∩ X_1| <= c, hence < λ (no band), hence C_j is not in class X and meets
each petal in less than λ. So |Z_i∖X_1| < 3λ and |S| < 1 - c + 6λ + λ <= t (J3). The traces
Z_1, Z_2, Z_3 are pairwise disjoint, so by P4(c) the seven replies X_1..X_4, C_1, C_2, C_3 have no
2-cover. (If C_j is in a third class she wins by Theorem D instead.) Total 7 + 3 (+4). ∎

Remarks.
- Theorem G's two-arena adversary (same-arena overlaps >= 2 - n > t², cross overlaps 0) has no
  banded pair unless he chooses to create one; so he loses to Theorem J at every t >= 3/4, with the
  certificate "four same-class petals + three centres". This is the dynamic, arena-free form of
  §11.4: she needs no public arenas, and she *can* force the far reply (cost 1 - c), contrary to
  the reading "a careful adversary never supplies it" (TWIN 15.3) — he avoids supplying it only by
  answering in the band.
- Leaky two arenas (X-edges: >= 1 - δ inside arena X, the rest anywhere; arenas of mass
  1 + t/2 - δ; this is FRESH_C §3's "two interval types" family with α = 1 - δ): same-class overlaps
  >= 1 - t/2 - δ, cross overlaps <= 2δ. Theorem J applies when t/2 + δ + 14δ <= t, i.e.
  **δ <= t/30** (0.025 at 3/4); a direct count (no third class possible, 6λ instead of 7λ) gives
  δ <= t/26.
- `petal_checks.py B` [simulated, not a proof]: the strategy of Steps 1–2 against randomized leaky
  two-arena adversaries (leaks re-used, aimed at earlier replies or random; class chosen to
  frustrate or at random): 400 games at (k,T,leak) = (40,30,1), (80,60,2), (80,62,2), (60,46,1),
  all end with seven replies verified uncoverable by brute force, at most 10 requests.
- What a banded pair gives by S1-type capping: with p_ij >= λ, the request B_i ∩ B_j plus
  1 - c' - p_ij of each private part costs <= t for c' = 1 - (t + λ)/2 (= 0.6 at t = 3/4). So the
  unconditional output of Theorem J + one request is: **a win, or an anchor triple with
  λ <= p_ij <= c and p_il, p_jl <= c'** (c = c' = 0.6 at t = 3/4). By Theorem F and TWIN 15.0 such triples are not all
  three-anchor wins, which is why the petal continuation of §4 is needed.

## 4. Interface with TWIN §15 (winning shapes) [proved by hand unless tagged]

TWIN 15.3: four same-cluster petals are an adversary win *of the confined game on U*. Consistent
with §3: there the centres are not confined to U; the forcing request F makes them nearly disjoint
from U, and by P3 that only helps her. The confined adversary corresponds to answering her forcing
request inside the band.

TWIN 15.4 (Theorem I): triple-free four petals in two pairs with cores a, b win iff L*(a,b) <= T; in
particular a = b <= 4T/5. This is why c = 4t/5 is the natural upper band end in Theorem J: **a
banded pair is a legal core.**

**Matching-load lemma (general triple-free petals).** Four petals, no point in three of them, pair
cells c_ij. If c_12 + c_34 <= t, c_13 + c_24 <= t and c_14 + c_23 <= t, three more requests win
(round r requests both cells of the r-th perfect matching; U* is the union of the six cells and Γ
the three grids, P2). Non-adaptive; the adversary's replies are irrelevant.

**Where 3/4 shows up.** Build petals greedily: S_2 ⊂ B_1 of mass t (c_12 <= 1 - t); S_3 ⊇ B_1 ∩ B_2;
S_4 = P ∪ (t - p further points of B_3), p = p_12 + p_13 + p_23 (legal iff p <= t; this is what makes
the four petals triple-free). Then c_34 <= 1 - p_13 - p_23 - (t - p) = 1 - t + p_12, so

    c_12 + c_34 <= 1 - t + 2 p_12 <= 3(1 - t) <= t   iff   t >= 3/4.

So the first matching is always affordable exactly from 3/4 on. The other two matchings
(c_13 + c_24, c_14 + c_23) and the legality p <= t are not controlled: see §5.

## 5. What prevents steering, and the decisive gap

**Adversaries that escape Theorem J** [proved that they escape; not proved that they win]:
anything that answers in the band. Concretely
(a) leaky two arenas with leak δ > t/26: cross overlaps up to 2δ >= λ. As a *family* this is not
    (7,2) (FRESH_C §3: broken by 6+1 stars and 5+2 splits), but no request strategy is known that
    extracts those tuples from a sub-family chosen by the adversary;
(b) "inside the union": after a banded or small pair (B_1, B_2) the third reply takes p_13 + p_23
    close to 1 from B_1 ∪ B_2 (she can only cap p_13 + p_23 <= 2 - t - p_12). Then p > t, the fourth
    petal cannot be made triple-free with these three, and the three-anchor game on them is an
    adversary win below 4/5 when p_12 = 0 (TWIN 15.0). This is the same adversary that defeats
    the three-anchor route; the petal architecture does not remove it, it only changes what she
    needs: not "all pairs <= t²" but "total pair mass of three petals <= t, and the two uncontrolled
    matchings light".

**Decisive gap (steering).** Prove or refute, for t = 3/4 + ε:

    from a banded pair (λ <= |B_i ∩ B_j| <= 4t/5) the requester reaches, in boundedly many further
    requests and with discards, four petals with no point in three of them whose three matching
    loads are <= t (or which satisfy the twin's exact criterion once it exists for six positive
    cells).

Known: the first matching is free at t >= 3/4 (§4); two-class adversaries are beaten without it
(§3). Unknown: (i) keeping the pair mass of three chosen petals <= t against adversary (b) — she
must discard and re-select, and each re-selection meets (b) again; (ii) a winning criterion for
triple-free petals with all six cells of positive mass (TWIN 15.4 covers only "two pairs with O(1)
cross cells" and uniform K4); (iii) whether petals with triple points (q = 4 with cells of
co-type size 1, or q = 5, 6) are ever needed — the family-level witnesses of FRESH_C §3 (6+1,
5+2, non-Fano) suggest yes for adversaries of type (a).

**Suggested next computation.** Extend `anchor_select.js` from "three anchors + four replies" to
"choose q in {3,4} petals among J replies, then 7 - q centres" using P3 (continuation confined to
U*), at (k,T) = (8,6), (9,7), (12,9): by P3 this is exact for the open game with m = J + 7 - q
requests and would show directly whether adversary (b) survives the petal architecture.

## 6. Checks

`py compute/petal/petal_checks.py A` — §1 statements vs brute force [computed exact].
`py compute/petal/petal_checks.py B 100` — Theorem J strategy vs leaky two-arena adversaries
[simulated].
Hand proofs re-read once: P1–P4, Theorem J (budget (J3) uses |Z_i∖X_1| < 3λ for two earlier
centres plus the standing λ; (J4) is used twice), matching-load lemma, the 3(1-t) computation.

=============================================================================================
# Part II — the spread side (second time box)

Brief from the coordinator: assume some three replies with empty common intersection have union
>= 3 - t, i.e. pair mass p = p_12 + p_13 + p_23 <= t ("spread triple"); the concentrated side is the
twin's (Fano six-state). Code: `compute/petal/design.py`, logs `table_12_9.log`, `table_16_12.log`.

**Outcome.**
- Gap (2) is closed: the exact criterion for triple-free four petals is a finite design problem
  with no adversary (Theorem K, §7), value L(a,b) computed by a 42-binary MILP; it specialises to
  the twin's L* for one grid. [proved by hand; MILP checked against L* and uniform K4]
- Gap (1) is closed for spread triples **without a dominant pair** and stays open with one.
  The fourth petal costs exactly p <= t (that is what "spread" buys), the cells then always fit the
  no-adversary range, and she wins in four more requests when max p_ab <= t - 1/2 and
  p_ab + p_ac - p_bc <= 3t - 2 [proved by hand, Theorem L], and on a much larger computed region,
  roughly max p_ab <= 3/8 at t = 3/4 [computed, grids k/12 and k/16]. With a dominant pair
  (max p_ab >= about 0.44) this fourth-petal architecture is an adversary win at t = 3/4, by margins
  that close near t ≈ 0.78–0.80 [computed].
- Interface (§9): good spread triples are *stateless* wins, so alternation cannot hurt there. The
  adversary's only way to sit between the two cases is a spread triple with a dominant pair
  (two near-copies plus a far reply). That is the remaining hole; it is the two-class picture of
  Theorem J again, and it is closed only when the play is band-free.

## 7. Theorem K: exact criterion for triple-free four petals [proved by hand; computed]

Four petals, no point in three of them. Grids r = 1, 2, 3 (the perfect matchings of K4):
A_r × A'_r with masses a_r, b_r; σ = total mass of the six cells = |U*|. Kill types are nonempty
subsets of the three remaining rounds.

**Theorem K.** (i) She wins with three more requests if there are, for each grid r, families
𝓕_r, 𝓖_r of nonempty subsets of [3] with F ∩ G ≠ ∅ for all F in 𝓕_r, G in 𝓖_r, and distributions of
A_r over 𝓕_r and of A'_r over 𝓖_r, such that every round load (mass of points whose type contains
the round) is <= t. Let L(a,b) be the least achievable maximum load.
(ii) If σ <= 1 + t this is also necessary: she wins iff L(a,b) <= t.
(iii) Zero cells: a cell of O(1) points opposite a cell of positive mass still forces one kill of
every point of the latter (the adversary gets the sliver for free); in L a zero cell is a cell of
mass ε.
*Proof.* (i) Request the round loads; every reply misses its request, so K_i contains the design's
round i and P2 applies (Γ is the three grids). (ii) His reply to a request S ⊆ U* with |U*∖S| <= 1
contains all unrequested active points (worst for her by P3(i)), so K_i = S_i ∩ U*; if she requests
fewer than σ - 1 active points he chooses the missing kills himself, which is no better for her
than requesting them (σ - 1 <= t). Replies carry no information, so the game is the design
problem; I_x ∩ I_y ≠ ∅ on a grid says exactly that the supports are cross-intersecting. ∎
Single grid: the maximal cross-intersecting pairs give L = L*(a,b) of TWIN 15.4. Closed forms
worth recording: matching design, loads a_r + b_r (one grid per round); all-pairs design, load
2σ/3 (every point killed twice); freeze design, load Σa + Σb/3 (Theorem D's count). No closed form
for general six positive cells: the optimum mixes these per grid, which is why it is left as a
MILP (`design.py`: binaries = allowed types per side and grid, u_F + v_G <= 1 for disjoint F, G).
Checks [computed]: uniform K4 (1/3 each) gives 2/3; one grid (1/2, 1/2) gives 0.625 = L*;
(1/3, 2/3) gives 0.556 = L*.

## 8. The fourth petal on a spread triple [proved by hand; computed]

Spread triple B_1, B_2, B_3 (empty common intersection, p <= t), singles Q_i of mass
q_i = 1 - p + p_jl. Request S_4 = P ∪ R, R inside the singles, r_i = |R ∩ Q_i|, Σ r_i = t - p.
Any reply B_4 gives four triple-free petals with cells
a = (p_12, p_13, p_23) and b = (c_34, c_24, c_14), c_i4 = |B_4 ∩ Q_i| <= q_i - r_i, Σ c_i4 <= 1.
**Cost control:** the fourth petal costs exactly p, affordable iff the triple is spread; and
σ = p + Σ c_i4 <= 1 + t, so Theorem K(ii) applies: **after the fourth petal there is no adversary.**
The whole continuation is the minimax  min_r max_b L(a, b).

**Theorem L (matching design).** Let t >= 3/4. If every p_ab <= t - 1/2 and
p_ab + p_ac - p_bc <= 3t - 2 for all labellings, she wins in four more requests.
*Proof.* Loads a_i + c_i4 <= a_i + q_i - r_i; she needs r_i >= ρ_i := 1 - t - p + 2a_i. A choice
r >= max(ρ, 0) with Σ r = t - p exists iff every sub-sum of the ρ_i is <= t - p: three terms give
3(1-t) - p <= t - p (t >= 3/4), two terms give a_i + a_j - a_l <= 3t - 2, one term gives
a_i <= t - 1/2. ∎
At t = 3/4: p_ab <= 1/4 and p_ab + p_ac - p_bc <= 1/4; e.g. every balanced spread triple.

**Computed region** (`design.py table K T`: shapes on the grid 1/K with t - 1/3 < p <= t — below
that Theorem D wins —, her r and his b on the same grid, L exact at each grid point, slivers as in
K(iii)). R = she wins with this architecture, A = the adversary's best fourth petal beats every
design. [computed; grid-restricted on both sides, so boundary shapes are indicative only]

| K, T | shapes | A shapes (p_12 p_13 p_23 in units 1/K) |
|---|---|---|
| 12, 9 | 39 | 600; 700 610; 800 710 620 611 530 440; 900 810 720 711 630 621 540 522 441 |
| 16, 12 | 79 | 800 710; 900 810 720 711; (10)00 910 820 811 730 721; (11)00 (10)10 920 911 830 821 740 731 722 650 551; at p = 12: all with p_12 >= 7, and 660 651 633 552 |

Reading: she wins whenever max p_ab <= 3/8, except for a few shapes with p = t exactly (no spare
request) or two heavy cells; she loses with a dominant pair, max p_ab >= 7/16. The adversary's
winning margin is small (values 12.25–13 of 16 except near-copies): this architecture alone
handles dominant pairs only from about t ≈ 0.78–0.80.
What the fourth petal looks like when he wins: B_4 is a near-copy of the far reply B_3
(c_34 large) that also takes a block from one single part of the dominant pair, e.g.
a = (7,1,0), b = (7,4,1) at K = 12: the cross grid 1 × 4 costs one kill of the block of 4, and
there is no room left beside the core grid 7 × 7.

## 9. Interface between the spread and the concentrated side

**9.1 Good spread triples are stateless wins [proved].** Theorems D, L (and the computed region)
use only the triple and four fresh requests; other replies, earlier or later, are irrelevant
(P3). So she can run any other strategy and switch the moment such a triple exists; alternating
between "concentrated" and "good spread" behaviour does not help the adversary.

**9.2 Committed play cannot be escaped [proved].** Once she has committed to a petal set P (any q)
and plays a strategy of the petal game G(P), replies leaving U*(P) only help her (P3(iii)). So if
the concentrated-side strategy has the form "select six petals, then one request" or "select
anchors, then confined play", the adversary cannot break its endgame by going spread. Alternation
can only attack the *selection* phase.

**9.3 The invariant the adversary must keep.** Combining 9.1 with REDTEAM 7.2: at every moment,
every triple of replies with empty common intersection is either concentrated (p > t) or spread
with a dominant pair (outside the R region of §8; in particular max p_ab > 3/8 up to the boundary
shapes, and p > t - 1/3). So the two cases do not partition the adversaries: the Fano six-state
lemma is stated under "every such triple has p > t", and a single far reply F violates that
hypothesis without giving a good triple, provided the replies that meet F little are pairwise
near-copies. Consequences of a far reply [proved by hand, from Theorem D]:
- if A ∩ A' ∩ F = ∅, |A ∩ A'| = a and F meets A ∪ A' in mass f, then a + f > t - 1/3 or he has lost;
  so after a reply disjoint from everything, all earlier replies must pairwise overlap in more
  than t - 1/3, and every later reply E must satisfy |E ∩ A| + |E ∩ F| > t - 1/3 for every earlier A
  (given E ∩ A ∩ F = ∅). She can cap |E ∩ A| at 1 - t for one chosen A, forcing |E ∩ F| > 2t - 4/3;
- hence a far reply splits the play into two families of mutual near-copies: the two-class
  picture. If no pair is banded, Theorem J wins. If a pair is banded, see 9.4.

**9.4 The hole.** A spread triple with a dominant pair, in a play that also has banded pairs:
neither Theorem J (needs band-free), nor Theorems D/L (need no dominant pair), nor — as far as it
is stated — the six-state lemma (needs all triples concentrated) applies. Candidate adversary:
a self-sufficient arena (N < 3 - t, replies pairwise overlapping in the band or above) plus rare
far replies. I did not show that this adversary survives: against it she can ignore the far
replies and play the concentrated strategy *if* that strategy tolerates replies outside the
arena. By 9.2 it does once it is committed; whether its selection phase does is a question about
the twin's proof, not about petals.
**Request to the twin:** state the six-state lemma with the hypothesis "every triple with empty
common intersection has p > t **or contains a pair with overlap > 3/8**" (far replies allowed), or
show that a far reply can be discarded at no cost. The natural argument for the latter: the
request was the one the concentrated strategy wanted, and in any committed continuation a
trace-poor reply is the best possible reply for her (P3(i)); what has to be checked is only the
bookkeeping of the selection phase.

## 10. Status of the two gaps and what is left

1. Fourth-petal cost: controlled exactly on the spread side (cost p <= t, no adversary afterwards).
   Banded pair → four winning petals: done when the pair sits in a spread triple without a
   dominant pair; open when the triple's largest pair exceeds about 3/8–7/16.
2. Criterion for six positive cells: Theorem K (exact, MILP); no closed form.
3. Decisive gap now: **dominant-pair spread triples at 3/4 < t < about 0.79** — equivalently the
   tolerance of the concentrated-side selection phase to far replies (9.4). A direct attack on
   the spread side would need petals with triple points (q = 4 keeping part of P_12 unrequested,
   or q = 5): by §8 the triple-free family is exhausted there.

Checks: `py compute/petal/design.py design a1 a2 a3 b1 b2 b3`; `py compute/petal/design.py table 12 9`
(about 1 min), `table 16 12` (about 8 min). Hand proofs re-read: Theorem K(ii) (the under-request
step), Theorem L (sub-sum condition), 9.3 bullets.

=============================================================================================
# Part III — Barrier F: the petal re-selection minimax (third time box)

Brief: decide the 2+2 triple-free petal re-selection minimax (TWIN 19.5, §8, §10.3).
Code: `compute/petal3/` (`lstar.py`, `quadmin.py`, `sim_arena.py`, `lpw.py`; logs in `compute/petal3/logs/`).
Units k = 1. Tags as before.

**Verdict.** The minimax, as posed, is an **adversary win**, by an explicit adversary, and re-selection
does not change that. It is NOT a counterexample to the conjecture: the same adversary loses to the
4+3 certificate of Theorem J when the requests are tailored to it. So Barrier F is not closed; it is
re-located from "re-select a 2+2 quadruple" to "make the 4+3 certificate tolerate bands".
1. [proved] **Serving lemma (11.2).** Against an adversary who plants one point of every
   unrequested pair-intersection in his reply, a triple-free quadruple exists only as T + E where
   the request answered by E contained all of P(T). One request serves only triples whose pair
   masses fit into t together; discards and re-selection give nothing else.
2. [proved] **Copy bound (11.3).** If E re-uses the unrequested part of the member of T opposite
   its heaviest pair a, the quadruple has a grid (a, b) with b >= 1 - t + a. Hence a single-served
   quadruple can win only if **a <= θ(t) = (6t - 2)/5** (0.5 at t = 3/4). This is TWIN 19.C made
   two-sided, with the exact constant for t >= 3/4.
3. [proved] **Theorem N (§12).** Two disjoint arenas of mass 1 + t/2 - δ, replies with leak δ,
   slivers, proportional replies: every triple-free quadruple that ever appears, for any number of
   requests, discards and simultaneous servings, has design value > t, whenever
   L*(1 - t/2 - δ, β(t,δ)) > t, β = (1-δ)(2 - 3t/2 - 2δ)/(2 - t - 2δ). At t = 3/4: all δ <= 0.0510;
   for δ = 0 (pure arenas plus O(1) leak): all t < 0.7903, which contains (3/4, t₁].
4. [proved] Theorem J as stated beats this adversary only for δ <= t/26 (0.0288 at 3/4). So for
   3/4 <= t < 0.7670 and t/26 < δ <= δ_N(t) the adversary escapes Theorem J's dichotomy AND every
   2+2 quadruple. A 4+3 certificate with arena-aware requests beats him for all δ < t/8 (12.3).
5. Remaining gap, exact form (§13): a **structure-agnostic** 4+3 strategy for two-class adversaries
   with within-class overlap > c and cross overlap <= μ in the region
   c > θ(t), μ > (t - 1 + c)/7. Not solved here.

## 11. The game, restated and checked against §8 / TWIN 19.5

**11.1 Game 𝓡(t, m).** Open request game, m requests. A *quad certificate* is a set of four replies,
no point in three of them, with design value L(a,b) <= t (Theorem K(i); zero cells opposite positive
cells count as slivers, K(iii)); she then wins with three more requests. The re-selection minimax
is: does she have a strategy producing a quad certificate among the m replies, against every
adversary? ("Discard" = she may choose the four afterwards.) §8 is the special case "the four are
a fixed triple T plus the next reply"; TWIN 19.5 asks whether choosing the four afterwards, or
combining replies obtained with complementary caps, changes the outcome. Check of the
restatement: for a fixed triple and one more reply, 11.2 gives S ⊇ P(T), so S = P ∪ R, |R| <= t - p,
and the cells of E are bounded by q_i - r_i: this is §8's min_r max_b L(a,b). ✓
Conventions used: masses are real; O(1) points are free for both players (the adversary may add
them to a reply, she may add them to a request); this is the convention of K(iii), P4(b), 19.1.

**11.2 Serving lemma [proved by hand].** *Sliver rule:* the reply to S contains one point of
(u ∩ v)∖S for every pair u, v of earlier replies with u ∩ v ⊄ S (boundedly many points).
Against any adversary obeying the sliver rule: if four replies are triple-free, T is the set of the
first three in time order and E the last, then P(T) ⊆ S_E, in particular p(T) <= t, and T has empty
common intersection. *Proof.* If u, v in T and u ∩ v ⊄ S_E, E contains a point of u ∩ v: a point in
three of the four. ∎
Consequences. (a) Each request serves the set 𝒯(S) = {T : P(T) ⊆ S}; a quad certificate is
T + E with T in 𝒯(S_E). (b) "Two replies obtained with complementary caps" (19.5) cannot be combined
into one quadruple unless the later of them was itself the reply to a request containing all
three pair-intersections of the other three. (c) A member of T that arrived after the other two
needed its own sealing at that time.
I did not prove that the sliver rule is free for the adversary in general; it is not needed: the
rule is part of the explicit adversary of §12, which is analysed as a whole.

**11.3 Copy bound [proved by hand].** Let T = (B_1, B_2, B_3) be served by S (P(T) ⊆ S, |S| <= t),
a = p_12, Q_3 = B_3∖(B_1 ∪ B_2). Then |Q_3∖S| >= 1 - (p_13 + p_23) - (t - p) = 1 - t + a. If the reply E
contains Q_3∖S, the quadruple has the grid (c_12, c_34) with c_34 >= 1 - t + a, so its design value is
at least L*(a, 1 - t + a) (restrict the design to one grid; L* of TWIN 15.4, increasing in both
arguments). With s = 1 - t: L*(a, a + s) = min(4a/3 + s/3, 5a/4 + s/2), so

    L*(a, 1 - t + a) <= t   iff   a <= t - 1/4   or   a <= (6t - 2)/5,

and for t >= 3/4 the second is the weaker requirement: **θ(t) = (6t - 2)/5**. (19.C is the first
branch, the freeze design; at t = 3/4 both give 1/2.) So against "sliver rule + copy the member
opposite the heaviest pair", a triple served alone yields a certificate only if all three of its
pairs are <= θ(t). L* formula re-checked against the MILP design on 7 grids (`logs/lstar.log`)
[computed].
Reading: §8's table (dominant pair >= 7/16–1/2 loses at t = 3/4) is this bound plus cross cells.
What re-selection could add is only simultaneous serving: several triples with a common heavy
pair and different third members, so that one reply cannot copy all of them. Theorem N shows this
fails against arenas, because all third members of one class overlap heavily anyway.

## 12. Theorem N: an explicit adversary beats every 2+2 quadruple [proved by hand; simulated]

**Adversary 𝒜(t, δ)**, 0 <= δ < 1 - t. Disjoint arenas V_A, V_F of mass n = 1 + t/2 - δ.
A reply of colour c has mass 1 - δ in V_c∖S, mass δ in the other arena outside S, plus slivers.
- Colour: c = F if |S ∩ V_A| > t/2, else c = A if |S ∩ V_F| > t/2, else either. Always possible:
  the chosen arena keeps at least n - t/2 = 1 - δ points and the other at least n - t >= δ.
- Own part: proportional, i.e. a fraction (1-δ)/|V_c∖S| of every atom of V_c∖S (atoms with respect
  to the earlier replies).
- Sliver rule of 11.2.
Write a_0 = 1 - t/2 - δ (two own parts in one arena meet in at least 2(1-δ) - n = a_0).

**Theorem N.** Against 𝒜(t, δ), every triple-free quadruple of replies, at any time, has a grid
(a, b) with a >= a_0 and b >= β(t, δ) = (1-δ)(2 - 3t/2 - 2δ)/(2 - t - 2δ). Hence if

    (N)   L*(a_0, β(t, δ)) > t,

no quad certificate ever exists: 𝓡(t, m) is an adversary win for every m.
*Proof.* (i) Same-colour triples always have a common point: when he answers in colour c at most
t/2 < a_0 of V_c is requested (δ < 1 - t), so no same-colour pair-intersection is inside S and
the sliver rule applies. (ii) So a triple-free quadruple is T + E (11.2) with T = (X, X', Y), X, X'
of one colour, say A, and Y of colour F. P(T) ⊆ S gives |S ∩ V_A| >= |X ∩ X' ∩ V_A| >= a_0 > t/2, so E has
colour F and y := |S ∩ V_F| <= t - a_0. (iii) Proportional own part:
|E ∩ Y| >= (1-δ) |(Y ∩ V_F)∖S| / |V_F∖S| >= (1-δ)(1 - δ - y)/(n - y), decreasing in y (1 - δ < n); at
y = t - a_0 this is β. (iv) In a triple-free quadruple |X ∩ X'| and |Y ∩ E| are the two cells of one
grid; L >= L*(a, b) >= L*(a_0, β). The case of a heavy pair of colour F is symmetric. ∎
The bound does not depend on how many triples the request serves, on m, or on which four she
selects: re-selection is covered.

**Range of (N)** (`lstar.py`, exact rational bisection) [computed exact]:

| t | δ_N(t) = sup{δ : (N)} | t/26 (Thm J) | single-serve bound 7/5 - 17t/10 (11.3 with a = a_0) |
|---|---|---|---|
| 0.75 | 0.0510 | 0.0288 | 0.125 |
| 0.76 | 0.0383 | 0.0292 | 0.108 |
| 0.77 | 0.0257 | 0.0296 | 0.091 |
| 0.78 | 0.0130 | 0.0300 | 0.074 |
| 0.79 | 0.0004 | 0.0304 | 0.057 |

(N) holds at δ = 0 iff t < 0.7903; δ_N(t) > t/26 iff t < 0.7670. For δ between δ_N(t) and
7/5 - 17t/10 a quadruple from a triple served alone still fails (11.3, with the copy reply in place
of the proportional one); whether simultaneous serving wins there is **not decided**
[heuristic: no — serving m third members costs her their m bands, mδ, in the heavy arena].
Corollary: pure two arenas with O(1) leak (δ = 0) defeat the 2+2 architecture on all of (3/4, t₁].
Theorem I's "a = b <= 4t/5" is a statement about shapes; the shape a = b = 1 - t/2 is not reachable
once he may leak O(1) points, because sealing the first core leaves only 3t/2 - 1 for the second.

**12.1 Simulation** (`sim_arena.py`, `logs/sim_arena.log`) [simulated, not a proof]. Point sets,
k = 800; the adversary's own part maximises the minimum overlap with all earlier same-colour
replies (small ILP; at least the proportional value); requester: randomised targeted lines (colour
forcing with shaped complements, sealing a pair plus the bands of 1–3 opposite replies, remainder
aimed at the served replies), 9 requests, 400 games per row; every quadruple tested, design MILP
with exact zero cells (favourable to her) whenever the L* bound is within one point of T.
(T, d) = (600,20), (600,32), (600,40), (608,20), (616,16): 3228 triple-free quadruples in total,
none with L <= T; smallest L - T = 47, 31, 21, 31, 19 points (theory: >= 28, 12, 1, 14, 6 minus O(1)).
The random requester is far from the bound, so this checks the mechanism (11.2, colours, cells),
not the constant. Rows with δ = 0.08, 0.13 (outside (N)) also show no good quadruple; that is not
evidence about that range. (The last row of the log, δ = 0.17, has 11 triple-free quadruples and
no recorded margin: a reporting defect I did not chase; it is outside every claim here.)

**12.2 Family level without slivers** (`quadmin.py`: one MILP over quadruple shapes and designs)
[computed, float MILP]. In the exact-leak family (no slivers, empty cells really empty) the best
2+2 quadruple has value (5/4)(1 - t/2) - (3/4)δ (fits the scanned points with δ <= 0.15 at
t = 0.75, 0.76, 0.78, `logs/quadmin_scan.log`), i.e. good quadruples *exist* iff
δ >= 5/3 - 13t/6 (0.0417 at 3/4). So below that leak there is not even a good quadruple to select;
between 0.0417 and 0.0510 (t = 3/4) they exist in the family and the adversary's play (slivers,
proportional replies) keeps her from them.

**12.3 The same adversary loses to 4+3 with arena-aware requests** [proved by hand]. Let δ < t/8
and let the adversary answer in any way inside the family (colour c: at least 1 - δ in V_c).
Requests 1–4: t/2 + ε in V_F, containing the V_F-parts of the earlier replies (<= 3δ + O(1)); the reply
has colour A; her t/2 - ε in V_A are chosen so that the four requests cover V_A (4·t/2 >= n). The four
petals have empty common intersection. Requests 5–7: t/2 + ε in V_A, containing the V_A-parts of the
earlier centres (<= 2δ + O(1)); in V_F the V_F-parts of the four petals (<= 4δ + O(1) < t/2). The replies
have colour F, miss U ∩ V_F, and are pairwise disjoint on V_A: P4(c). Seven requests. ∎
So 𝒜(t, δ) is not a (7,2) obstruction; it is an obstruction to the 2+2 architecture and to
Theorem J's present constants only. Theorem J loses here because it pays 1 - c + 7λ with worst-case
traces (3λ outside X_1 per centre); the real traces are δ per centre.

## 13. What is dead, what is left

Dead [proved]:
- Re-selection of triple-free quadruples as the tool against two-class adversaries with small
  bands: Theorem N. In particular "combine a small-core reply with a small-band reply" (19.5)
  is impossible by 11.2(b).
- G2/G3 as specified in TWIN 19.6 as a test of this barrier: the restricted mixed adversary
  (replies inside F ∪ (A Δ A'), disjoint far reply, no second arena) cannot plant a point of A ∩ A', so
  she never has to seal the core and caps b for free; that is why `g2_restricted.log` shows
  immediate requester wins at t = 3/4. The band-start runs that timed out test the same class. I
  did not re-run them: no outcome would bear on 𝓡. The informative finite check would be
  𝒜(t, δ) itself on point sets, and FAST Parts 3–4 show that at reachable k (<= 12) the O(1) terms
  (slivers cost one point per pair) swamp a margin of 0.02k–0.07k.

Not decided:
- 𝒜(t, δ) for δ_N(t) < δ < 7/5 - 17t/10 against simultaneous serving (irrelevant for the conjecture
  when δ < t/8, by 12.3; relevant only as a statement about the 2+2 architecture).
- Quadruples with unsealed pair cells (a sliver triple point makes one whole petal active, at the
  price of one kill of its single part): not covered by 11.2. Not needed against 𝒜 (12.3).
- No potential-function or LP-duality proof of a requester win was found, and by Theorem N none
  exists for the 2+2 certificate alone.

**Exact remaining gap (Barrier F, re-posed).** Two-class adversaries: an equivalence on replies
with same-class overlaps > c and cross overlaps <= μ, not given as arenas. Known:
Theorem J wins if 1 - c + 7μ <= t (and (J1), (J2), (J4)); a single-served 2+2 quadruple needs
c <= θ(t) = (6t - 2)/5 (11.3); arenas are beaten for μ = 2δ < t/4 when she knows them (12.3). Open:

    c > θ(t)  and  μ > (t - 1 + c)/7:   a 4+3 strategy that does not know the arenas.

Two concrete sub-questions: (i) in Step 2 of Theorem J replace the worst-case trace bound 3λ per
centre by the observed traces, and pairwise disjointness by P2 (only edges of Γ(P) with an
endpoint in two traces survive); (ii) force the far reply at cost about t/2 (as in an arena)
instead of 1 - c, by requesting inside the common part of two same-class petals.
RI in Step 1 already tolerates μ <= t - 2/3 (0.083 at 3/4, i.e. δ <= 0.042), so Step 2 is the only
place where the constant t/26 arises.

Checks: `py compute/petal3/lstar.py` (L* vs MILP, table of §12); `py compute/petal3/quadmin.py t δ`;
`py compute/petal3/sim_arena.py 800 600 20 400 7` (about 15 s per row). Hand proofs re-read once:
11.2, 11.3 (the count |Q_3∖S| >= 1 - t + a), Theorem N steps (i)–(iv), 12.3 (budgets: 3δ <= t/2 + ε,
4δ < t/2 - ε, 4(t/2 - ε) >= n).
