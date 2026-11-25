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

---------------------------------------------------------------------------------------------
## 14. Rework of Theorem J, Step 2 (fourth time box) — outcome first

Brief: observed traces and P2 in place of worst-case 3λ and pairwise disjointness; forcing at about
t/2 instead of 1 - c; target: two-class adversaries with same-class overlap > c > θ(t), cross overlap
<= μ, all 3/4 < t <= t₁. No new code; everything below is by hand.

**Outcome: the gap is NOT closed in the abstract (c, μ) model, and I have no explicit adversary
for it either.** What is proved:
1. Theorem J′ (14.1): for strict two-class adversaries the condition improves from
   1 - c + 7λ <= t to **1 - c + 6μ <= t**, and to a condition on the *observed* traces,
   1 - c + |(Z_1 ∪ Z_2)∖X_a| <= t. With small singles the 6μ becomes 3μ + 2σ (14.2).
2. One fixed, arena-blind strategy (c = 1 - 7t/12, b = t/2) beats the Part III adversary 𝒜(t, δ)
   for **every δ < t/12** (14.3). Since δ_N(t) <= 0.0510 < t/12, the explicit window of Part III
   (t/26 < δ <= δ_N(t)) is closed without knowledge of the arenas.
3. P2 gives nothing over pairwise disjoint traces in the worst case (15.1), and forcing below
   1 - c is not available in general (15.2). Both proposed levers are dead as worst-case gains.
4. The worst case of J′ (traces 3μ outside every petal) needs single parts of mass >= 3μ in the
   petals. The natural realisation, arenas with private parts (𝓑, 15.3), then has
   c <= 1 - t/2 - 3μ and loses to J′ whenever c > θ(t) and t >= 3/4. So I could not build a two-class
   adversary in the open region; I also could not prove none exists.
Remaining gap, exact (§16): abstract two-class adversaries with c > θ(t) and 6μ > t - 1 + c whose
replies are not of arena-plus-private form.

### 14.1 Theorem J′ [proved by hand]

Setting 𝒞(c, μ): at all times the replies fall into at most two classes; same-class overlaps > c,
cross overlaps <= μ < c. (A third class costs the standing request λ and (J2) as in §3; omitted.)
Necessarily c < 1 - t/2: otherwise 1 - c of X_1 plus 1 - c of Y_1 is a legal request with no reply.

*Forcing.* If S contains 1 - c of some X-class reply, the reply is of class Y.
*Step 1 (7 requests).* Request min(t/2, |I^X|) points of I^X and min(t/2, |I^Y|) of I^Y. A class with
j <= 3 members has |I| <= 1 - (j-1)t/2, and 1 - t <= t/2, so its fourth member misses I: one class, X,
has four members X_1..X_4 with empty common intersection. No λ is needed. U = their union.
*Step 2 (3 requests).* For j = 1, 2, 3 let Z_{<j} be the union of the traces C_i ∩ U of the centres so
far, choose a petal X_a, and request S_j = F_j ∪ (Z_{<j}∖X_a), F_j ⊂ X_a of mass 1 - c containing
Z_{<j} ∩ X_a (mass <= 2μ <= 1 - c). The reply is of class Y and misses Z_{<j}, so the traces are pairwise
disjoint and P4(c) applies.

**Theorem J′.** She wins in 10 requests provided, on the line actually played,

    (J′)   1 - c + min_a |(Z_1 ∪ Z_2)∖X_a| <= t.

Worst case: |C_i ∩ X_b| <= μ gives |Z_i∖X_a| <= 3μ, so **1 - c + 6μ <= t suffices**. ∎
At t = 3/4: μ <= (c - 1/4)/6, i.e. μ <= 0.042 at c = 1/2 and 0.0625 at c = 5/8.

### 14.2 Multiplicity refinement [proved by hand]

Let s_b be the mass of the single part of X_b (points of U in no other petal). Points of U∖X_a of
multiplicity >= 2 lie in two of the other three petals, so a centre has at most 3μ/2 of them; on
single parts it has at most Σ_{b≠a} min(μ, s_b). Hence

    |(Z_1 ∪ Z_2)∖X_a| <= 3μ + 2 Σ_{b≠a} min(μ, s_b).

With negligible singles the requirement is 1 - c + 3μ <= t. The factor 6 is reached only when
each centre puts μ into the single part of each of three petals.

### 14.3 The arena adversary 𝒜(t, δ) is beaten arena-blind for δ < t/12 [proved by hand]

Fix c = 1 - 7t/12 (0.5625 at 3/4). In 𝒜(t, δ) with δ < t/12: same-colour overlaps are >= a_0 =
1 - t/2 - δ > c and cross overlaps are <= 2δ + O(1) < t/6 < c, so the classes are visible and 𝒞 holds.
Step 1 as above. Step 2 with a = 1: a centre's trace has at most δ + O(1) in V_A, and in V_F it lies
in the V_F-parts of the petals; outside X_1 those have mass <= 3δ + O(1). So
|(Z_1 ∪ Z_2)∖X_1| <= 2δ + 3δ, and (J′) reads 7t/12 + 5δ <= t, i.e. δ <= t/12. ∎
The strategy uses t and the threshold c only. δ_N(t) < t/12 for all t >= 3/4 (table in §12), so
every 𝒜(t, δ) that Theorem N protects from 2+2 quadruples loses to J′.
(12.3 reaches t/8 with arena-aware requests; the difference is the forcing set, which there may
sit anywhere in V_A.)

## 15. The two proposed levers, and the attempt at an adversary

### 15.1 P2 does not beat pairwise disjointness in the worst case [proved by hand]

Four petals with empty common intersection, T_d = points in all petals except X_d. From
|X_a ∩ X_b| > c: |T_d| > 2c - 1 for each d, so no T_d is empty. A point y of T_d has co-type {d}, so
x ~ y iff x is in X_d; every x of U lies in some X_d.
**Lemma.** Suppose each of the three centres contains a point of every T_d (he can arrange this
unless a request contains a whole T_d). Then P2 holds iff the traces are pairwise disjoint on U.
*Proof.* P2 fails iff some edge {x, y} has every centre containing x or y. Let x lie in two
traces, Z_i and Z_j, and let x be in X_d. The third centre contains some y in T_d, and x ~ y. So
no point may lie in two traces; the converse is P4(c). ∎
What P2 does give: a centre that misses T_d entirely frees the other two to overlap on points
whose only relevant neighbours are in T_d. That costs |T_d| > 2c - 1 per request; in arenas
|T_d| is about t/2, the size of the forcing set. Not pursued: no gain when c is near 1 - t/2.

### 15.2 Forcing below 1 - c [dead; proved for arenas]

In 𝒜(t, δ) any request with at most t/2 points in V_A admits a reply of colour A. So forcing costs
at least t/2 = 1 - a_0 - δ: the possible gain over 1 - c is δ, and to collect it she must know that
the forcing points lie in V_A. In the abstract model the only certificate of exclusion is
"1 - c of one petal". The count via four petals (a class-X reply E has Σ_a |E ∩ X_a| > 4c, hence more
than 4c - 2 in ∪T_d) gives cost |∪T_d| - (4c - 2), which is larger than 1 - c in arenas.

### 15.3 Attempt at an adversary realising 6μ: arenas with private parts [proved that it fails]

𝓑(t, ρ, μ): arenas of mass 1 + t/2 - ρ; a reply has 1 - ρ in its own arena and ρ elsewhere. X-type
replies put the ρ into fresh points (a private single part). A forced centre puts μ into the
unrequested private part of each of three petals outside X_a. Needs ρ >= 3μ. Then
c = 1 - t/2 - ρ and the J′ cost is t/2 + ρ + 6μ <= t/2 + 3ρ.
If c > θ(t) then ρ < 7/5 - 17t/10, so the cost is below 4.2 - 4.6t, which is <= t exactly when t >= 3/4.
**So 𝓑 loses to J′ in the whole region c > θ(t), t >= 3/4.** Outside it (c <= θ) the 2+2 single-serve
bound 11.3 no longer protects him. The mechanism: private parts that make traces large also
lower c, i.e. raise her forcing cost by ρ but his exposure by 3ρ.
I did not find another construction. A targeting adversary must also know the quadruple; in J′
it is determined (first four of a class), so that is not the obstacle.

## 16. Status after the rework

Closed [proved]: 𝒜(t, δ) for δ < t/12 arena-blind (all of Theorem N's range); 𝓑 in the region
c > θ(t); abstract two-class adversaries with 1 - c + 6μ <= t, or with small singles and
1 - c + 3μ + 2σ <= t.

Dead [proved]: P2 as a worst-case improvement (15.1); cheaper forcing in general (15.2).

**Exact remaining gap.** Abstract class 𝒞(c, μ) with

    θ(t) < c < 1 - t/2   and   6μ > t - 1 + c,

realised by replies whose petals have single parts >= 3μ *without* the arena-plus-private
relation c <= 1 - t/2 - 3μ. I have neither a strategy nor an adversary there. At t = 3/4 this is
1/2 < c < 5/8, μ > (c - 1/4)/6, up to μ <= (t - 1/3)/3 = 0.139 (above that he needs a third class
and Theorem D applies).

**Best next step.** Prove or refute the structural lemma behind 15.3 in general:

    if every class-X reply has single mass >= σ relative to three others of its class, then some
    request of mass <= 1 - c - σ + o(1) excludes class X (the exclusion cost e_X, not 1 - c, is the
    true forcing price), and e_X + e_Y > t is forced on him.

With it, J′'s cost becomes e_X + 3μ + 2·min(3μ, σ) against e_X + e_Y > t, and the region above
should close by the 𝓑 computation. Without it, the adversary to look for is a two-class family
that is not a pair of arenas: same-class overlaps > θ(t) spread over many small common parts
rather than one core.

Hand proofs re-read once: 14.1 (Step 1 budget 2·t/2; (J′)), 14.2 (3μ/2 count), 14.3 (5δ; c < a_0 iff
δ < t/12), 15.1, 15.3 (4.2 - 4.6t <= t iff t >= 3/4).

---------------------------------------------------------------------------------------------
## 17. The single-mass exclusion lemma (fifth time box) — outcome first

Brief: prove or refute "single mass σ in a class gives exclusion cost about 1 - c - σ", redo 15.3 for
general two-class adversaries, otherwise build the counterexample class and replay.
Code: `compute/petal3/replay_q.py`, `replay43.py`; logs `logs/replay_q.log`, `logs/replay43.log`.

**Outcome.**
1. The lemma is **false in the form she can use** (17.1) and true only as a statement about a
   family she is told (17.2). So it cannot be the tool.
2. Something better is true: singles are bounded by c alone (17.3), and rotating the forcing petal
   removes one single part per centre. **Theorem J″: 1 - c + 4μ <= t suffices** (18.1) [proved];
   replayed exactly on the extremal configuration (18.2) [computed exact].
3. **Correction to §16.** The cap "μ <= (t - 1/3)/3" there is wrong for strict two-class adversaries
   (it is the condition for opening a third class). The arena adversary 𝒜(t, δ) of §12 with larger
   δ lies in the open region. It is the explicit counterexample class asked for (19.1): for
   **t/8 <= δ < 7/5 - 17t/10** (0.094 <= δ < 0.125 at t = 3/4; nonempty iff t < 0.767) every strategy in these
   notes fails against it, by exact replay. Whether he wins there is not decided.
Remaining gap, exact: θ(t) < c < 1 - t/2 and 4μ > t - 1 + c; sharpest instance 𝒜(3/4, 0.1).

### 17.1 The certified form is false [proved by hand]

From the hypothesis of 𝒞(c, μ) she can conclude that S excludes class X only if no set E of mass 1
outside S meets every X-class reply in more than c ("certified exclusion").
**Configuration 𝒬(c)**, 1/2 < c <= 2/3: V = four blocks of mass c/2; X_i = (V minus block i) plus a
private part of mass ρ = 1 - 3c/2. Then |X_i ∩ X_j| = c, the four have empty common intersection, each
has single mass ρ.
Claim: a request of mass 1 - c - ρ + ε inside X_1 ∩ V does not exclude class X in the certified sense.
*Proof.* Spread S over blocks 2, 3, 4. Take E = (X_1 ∩ V)∖S (mass c - ε), plus c/3 + 2ε of block 1, plus
2ε of the private part of X_1. Mass 4c/3 + 3ε <= 1. |E ∩ X_1| = c + ε; for i = 2, 3, 4:
|E ∩ X_i| = (2/3)(c - ε) + c/3 + 2ε > c. ∎ (c = 0.6: ρ = 0.1, S of mass 0.3, E of mass 0.8.)
So singles of mass ρ do not lower the price she can rely on below 1 - c.

### 17.2 The true form holds in arena-with-pool families [proved by hand]

Family 𝓖: all sets with 1 - ρ in an arena of mass n and ρ in a large pool. Then c = 2(1 - ρ) - n,
τ(𝓖) = n - 1 + ρ = 1 - c - ρ, and replies with fresh pool points have single mass ρ. Same for a kernel
family (at least κ_0 in a kernel, rest anywhere). In these the lemma is an identity, and it is
what made 𝓑 lose in 15.3. In 17.1 the set E is not a member of 𝓖 (it has 4c/3 < 1 - ρ in V): the
exclusion is real but she cannot know it from overlaps. I have no proof and no counterexample
for the true form in general; by 18.1 it is no longer needed for the constant 6.

### 17.3 Singles are bounded by c [proved by hand]

Four petals, empty common intersection, pairwise overlaps > c; s = total single mass, p = total
mass of the six pair cells, T = total mass of the four triple cells. Then s + 2p + 3T = 4 and
p + 3T > 6c, hence **s + p < 4 - 6c**. 𝒬(c) is extremal (p = 0, s = 4 - 6c).
Also each single part has mass < 1 - c, so a forcing set can contain a whole single part.

## 18. Theorem J″ and its replay

### 18.1 Theorem J″ [proved by hand]

Setting 𝒞(c, μ), petals X_1..X_4 from Step 1 of 14.1. Step 2 with **rotation**: centre j is forced
inside a different petal a_j (a_1, a_2, a_3 distinct), and F_j, of mass at least 1 - c inside X_{a_j},
contains the whole single part of X_{a_j} and Z_{<j} ∩ X_{a_j}; S_j = F_j ∪ (Z_{<j}∖X_{a_j}).
Then C_j has no point in the single part of X_{a_j}. For i < j every point of Z_i outside X_{a_j} lies
in one of the two petals other than a_i, a_j (the only remaining possibility, the single part of
X_{a_i}, is excluded), so |Z_i∖X_{a_j}| <= 2μ.
Cost of the third request: at most max(1 - c + 4μ, s_{a_3} + |Z_1| + |Z_2|) with |Z_i| <= 3μ; taking a_3
with the smallest single part, s_{a_3} < 1 - 3c/2 (17.3), and 1 - 3c/2 + 6μ <= 1 - c + 4μ since μ <= c/4.

**Theorem J″.** In 𝒞(c, μ) she wins in 10 requests if **1 - c + 4μ <= t**. ∎
At t = 3/4: μ <= (c - 1/4)/4, i.e. 0.0625 at c = 1/2 and 0.094 at c = 5/8 (J′: 0.042 and 0.0625).
Redo of 15.3: 𝓑 and every arena-with-pool class were already beaten by J′ in the region c > θ(t);
J″ covers them with room and needs no information about the family.

### 18.2 Exact replay on 𝒬(c) (`replay_q.py`) [computed exact]

Point sets, k = 400; petals 𝒬(c); scripted centres: a fixed core, μ unrequested points from every
private part (re-using earlier trace points when not sealed), one unrequested point of every block
(the slivers of 15.1). Requester: Step 2 with the forcing petal chosen to minimise the outside
trace and its private part put into F (this is the rotation). Exact 2-cover test of the seven sets.
| T | c | μ | 1 - c + 4μ (points) | result |
|---|---|---|---|---|
| 300 | 216 | 10, 19, 20 | 224, 260, 264 | no 2-cover (she wins) |
| 300 | 216 | 38 (= ρ/2) | 336 | third request 38 over; 2-cover exists |
| 308 | 216 | 38 | 336 | 30 over; 2-cover exists |
| 300 | 232 | 26 (= ρ/2) | 272 | no 2-cover |
| 300 | 240 | 10, 20 | 200, 240 | no 2-cover |
The wins are verified wins of those seven sets. The two failures are failures of J″ against a
scripted line, not adversary wins: on 𝒬(c) J″ fails iff 3 - 4c > t (μ = ρ/2), i.e. c < 0.5625 at 3/4.
The centres there are not produced by a validated adversary (I did not check that a class
containing them can answer every request), so 𝒬 is a configuration, not a counterexample class.

## 19. The counterexample class, and status

### 19.1 𝒜(t, δ) with t/8 <= δ < 7/5 - 17t/10 [computed exact for the two 4+3 strategies; 2+2 by 11.3]

𝒜 is strict two-class with c = 1 - t/2 - δ and μ = 2δ; c > θ(t) iff δ < 7/5 - 17t/10. Replay on point sets
(`replay43.py`, k = 480, T = 360, 20 seeds per row; adversary as in §12 with trace-maximising own
parts and bands placed outside as many petals as possible; exact 2-cover test):
| δ | J′ arena-blind (c = a_0 known) | 12.3 arena-aware |
|---|---|---|
| 0.050 – 0.083 | wins 20/20 | wins 20/20 |
| 0.092 | fails 20/20 (third request 15 points over) | wins 20/20 |
| 0.100 – 0.125 | fails 20/20 | fails 20/20 (13–61 points over) |
"Fails" = the strategy's request does not fit, and with the truncated request the seven replies
have a 2-cover. The blind strategy does better than its bound t/12 because the realised traces
outside the forcing petal are about 4δ, not 5δ. Rotation (J″) does not help here: the single parts
are the petals' bands, δ each, and the cost is dominated by t/2 + δ plus the bands of the other
petals.
So for t/8 <= δ < 7/5 - 17t/10:
- every 2+2 quadruple from a triple served alone fails (11.3, exact inequality
  1 - t/2 - δ > (6t - 2)/5);
- 4+3 with pairwise disjoint traces fails for both request schemes (exact inequality
  t/2 + 4δ > t for the aware scheme, 12.3);
- not excluded: simultaneous serving in 2+2; 4+3 with a whole triple cell T_d in the request
  (15.1; my count gives a gain up to about δ = 0.095 only) [heuristic]; choosing the four petals among
  many replies so that their bands overlap (he can keep bands of different covering types disjoint
  for about n/δ replies) [heuristic]; certificates with triple points.
I do not claim he wins. An adversary win here for all request numbers would defeat the request
game itself at that t, which is a far stronger statement than anything checked.

### 19.2 Status

Proved: J″ (1 - c + 4μ <= t); singles bound; certified exclusion lemma false.
Dead: the exclusion lemma as a tool; 𝓑-type (arena with pool) adversaries.
Corrected: §16's upper limit on μ.
**Exact remaining gap:** 𝒞(c, μ) with θ(t) < c < 1 - t/2 and 4μ > t - 1 + c. One explicit member, with all
constants fixed: 𝒜(3/4, 0.1) (arenas of mass 1.275, c = 0.525, μ = 0.2).
**Best next step:** decide 𝒜(3/4, 0.1) alone. Requester side: a 4+3 line that requests one triple cell
T_d (mass about 0.26) inside the forcing set, so that the band of petal d need not be sealed, and
picks petals whose bands overlap. Adversary side: show that with bands kept disjoint across the
four covering types every seven replies keep a 2-cover; the replay harness `replay43.py` takes a
new strategy as one function.

Checks: `py compute/petal3/replay_q.py 400 300 216 38`; `py compute/petal3/replay43.py 480 360 48 20`.
Hand proofs re-read once: 17.1 (masses of E), 17.3, 18.1 (the 2μ count and the max).

---------------------------------------------------------------------------------------------
## 20. 𝒜(3/4, 0.1) decided: requester win (sixth time box)

**Outcome: 𝒜(t, δ) loses for every δ < t/6, in seven requests** [proved by hand; replayed exactly].
At t = 3/4 that is δ < 0.125, the whole class of 19.1; for t > 3/4 the class (δ < 7/5 - 17t/10) is inside
it too. So 𝒜 is dead as an obstruction on the whole range where c > θ(t). The reason is an error of
economy in 12.3, not a new idea: pairwise disjoint traces need every band point in **at most one**
centre, not in none.

### 20.1 Family test [computed exact]

H = all replies of 𝒜 at k = 40, T = 30, d = 4 (arenas of 51 points). H does **not** have property
(7,2): `replay43.py 40 30 4` (mode aware2) produces seven members with no 2-point cover (exact test
over all pairs of membership types, common points included), 20/20 seeds; same at k = 80 and
k = 480. No SAT search was needed, the construction below gives the seven sets.
A caution on the brief: non-(7,2) of H alone is not decisive, since he chooses the bands and she
cannot force two bands to coincide (12.2 already had good configurations she could not reach).
What decides the instance is that the seven sets below are forced against every choice of his.

### 20.2 Theorem DS: double sealing [proved by hand]

Let δ < t/6 and let the adversary answer in any way inside the family (colour c: at least 1 - δ in
V_c, the rest in the other arena, slivers included in "the rest").
*Requests 1–4 (petals), as in 12.3:* t/2 + ε in V_F, containing the V_F-parts of the earlier petals
(<= 3δ + O(1) <= t/2); t/2 - ε in V_A, the four chunks covering V_A. Replies have colour A; empty common
intersection. Let B = the union of the V_F-parts of the four petals, |B| <= 4δ + O(1).
*Requests 5–7 (centres):* split B into three parts B_0, B_1, B_2 of equal mass. Request j contains
B minus B_j (mass 8δ/3 <= t/2 - ε, since δ < 3t/16), and in V_A the V_A-parts of the earlier centres
(<= 2δ + O(1)) filled up to t/2 + ε. Replies have colour F.
Every point of B is requested in two of the three requests, so it lies in at most one centre; the
V_A-parts of the centres are pairwise disjoint. So the traces on U are pairwise disjoint and P4(c)
gives seven replies with no 2-cover. ∎
The binding condition is 3δ <= t/2 in the petal phase as written; sealing only the common part of
the earlier V_F-parts there would extend the range to δ < 3t/16 [not checked, not needed].

### 20.3 Exact replay (`replay43.py`, mode aware2; `logs/replay43_aware2.log`) [computed exact]

Adversary of 19.1 (trace-maximising own parts, bands never re-used and placed outside as many
petals as possible). 20 seeds per row; exact 2-cover test of the seven replies.
| k, T | δ | blind J′ | aware (12.3) | aware2 (20.2) |
|---|---|---|---|---|
| 40, 30 | 0.100 | 0/20 | 0/20 | **20/20** |
| 80, 60 | 0.100 | 0/20 | 0/20 | **20/20** |
| 480, 360 | 0.092 | 0/20 | 20/20 | 20/20 |
| 480, 360 | 0.100, 0.108, 0.117, 0.125 | 0/20 | 0/20 | **20/20** each |
| 480, 372 | 0.100, 0.117 | 0/20 | 0/20 | **20/20** each |
In every aware2 game no request exceeds T and the three traces are pairwise disjoint. The replay
uses one adversary; the claim for all adversaries in the family is 20.2.
Limits: the strategy places requests by arena. She can read the arenas off the replies (own
parts of one colour overlap in more than c, bands do not), but I did not write the blind version.

### 20.4 Consequences and status

- Corrections: 12.3's range t/8 becomes t/6; the "counterexample class" of 19.1 is withdrawn.
  Theorem N (2+2 fails against 𝒜 for δ <= δ_N) stands; it now says only that the 2+2 architecture is
  the wrong tool there.
- **𝒜(t, δ): closed for all δ < t/6**, hence wherever c > θ(t), for every t >= 3/4.
- Abstract class 𝒞(c, μ): J″ (1 - c + 4μ <= t) is the best general statement. The region
  θ(t) < c < 1 - t/2, 4μ > t - 1 + c has **no explicit member left**: 𝒜, 𝓑 (15.3) and arena-with-pool
  classes are all beaten; 𝒬(c) (18.2) is a configuration without a validated adversary.
- What 20.2 uses beyond J″: (a) traces of centres on the petals' union are confined to a set she
  knows in advance (the bands), so she can seal by design, each point twice in three requests,
  instead of sealing observed traces sequentially; (b) forcing costs t/2, placed anywhere in the
  arena.

**Exact remaining gap.** 𝒞(c, μ) with θ(t) < c < 1 - t/2 and 4μ > t - 1 + c, for adversaries whose
centres' traces are not confined to a set she can identify in advance (the abstract analogue of
(a)). I have no inequality for a design-sealing scheme in the abstract class: sealing every single
point in two of three requests costs up to (2/3)(4 - 6c) per request (17.3), which beats J″ only when
the singles are small [heuristic, not worked out].
**Best next step:** write the arena-blind version of 20.2 (classes and bands read off the replies)
and state it as a theorem about adversaries whose same-class replies share a common region of
mass >= 1 - δ each (the natural hypothesis under which (a) holds); then look for a two-class
adversary violating that hypothesis, starting from 𝒬(c) with c < (3 - t)/4.

Checks: `py compute/petal3/replay43.py 40 30 4 20`; `py compute/petal3/replay43.py 480 360 48 20`.
Hand proof re-read once: 20.2 (budgets 3δ <= t/2, 8δ/3 <= t/2 - ε, 2δ <= t/2; each band point in at most
one centre).

---------------------------------------------------------------------------------------------
## 21. Arena-blind Theorem DS, and a candidate adversary outside its hypothesis (seventh time box)

Naming: the double-sealing theorem of 20.2 is **Theorem DS** (renamed; "Theorem P" is CORE.md's pool
theorem). Code: `compute/petal3/exclusion.py`, log `logs/exclusion.log`.

**Outcome.**
1. Blind DS: **not obtained at the aware range.** What is proved blind, for classes with a common
   region, is n - 1 + 7δ <= t (21.1), i.e. δ <= t/12 for tight arenas, against t/6 aware. I say exactly
   which three terms are lost and why my attempt to recover them fails (21.2).
2. A candidate two-class adversary 𝒦₂(c), θ(t) < c < (3 - t)/4, built on 𝒬(c), survives every attack
   analysed here: J″ (exact replay, 18.2), double sealing of the single parts, role swap, and
   certified double exclusion (computed, 21.4). It is **not validated** as a strategy: its
   out-of-family ("closure") replies are not shown to be sustainable. No adversary win is claimed.

### 21.1 Blind statement for common-region classes [proved by hand]

Hypothesis CR(n, δ): two classes; disjoint regions R_X, R_Y of mass n; every reply of a class has
at least 1 - δ in its region; she knows t, and a number c below 2(1 - δ) - n and above 2δ (so classes are
read off overlaps), nothing else.
**Theorem DS-b.** Under CR(n, δ) she wins in 10 requests if **n - 1 + 7δ <= t**, placing requests only
from observed replies.
*Proof.* Step 1 of 14.1 (running intersections) gives four petals of one class, X. Step 2 of 14.1
with a fixed forcing petal X_a and c just below 2(1 - δ) - n: forcing costs 1 - c = n - 1 + 2δ. A centre
meets U∖X_a in (i) its part outside R_Y, at most δ, and (ii) points of U ∩ R_Y outside X_a, which lie
in the parts of the three other petals outside R_X: at most 3δ in total, and once sealed they
are gone. So |(Z_1 ∪ Z_2)∖X_a| <= 3δ + 2δ, and (J′) holds. ∎
Tight arenas (n = 1 + t/2 - δ): δ <= t/12. Replay (19.1): realised threshold between 0.083 and 0.092 at
t = 3/4, because the parts (i) of two centres cannot both avoid the best petal.

### 21.2 Why the aware range t/6 is not reached blind [the three terms are proved; the diagnosis is heuristic]

Aware cost t/2 + 8δ/3; blind cost t/2 + 6δ. The difference:
- forcing: +δ. The only certificate she has is "1 - c of one petal"; in an arena t/2 anywhere
  suffices, but she cannot certify that a point lies in R_X (a band point re-used by r of m
  replies looks the same; mass-level certainty costs mδ/r, never below about δ).
- centre parts outside R_Y: +2δ (aware: inside the forcing set, which may sit anywhere in V_A).
- bands: 3δ against 8δ/3 for four bands, or 2δ for three: double sealing needs the band set in
  advance. Attempt: probe centres, record hits, double-seal the recorded set, restart when new
  hits exceed ξ. It fails as written: recorded hits mix band points (bounded by 3δ in total) with
  the centres' own stray parts (δ per probe, unbounded in total), and she cannot tell them apart,
  so the recorded set grows without bound. Hiding bands from probes does not help him (a probe
  with no band hits is a good centre), so some version may work; I do not have it.
So against 𝒜(t, δ) with t/12 < δ < t/6 the proved win is arena-aware only. The arenas are learnable in
principle (own parts recur, bands do not), but that is exactly the unproved step.

### 21.3 The candidate 𝒦₂(c) [explicit; not validated]

Fix θ(t) < c < (3 - t)/4 (nonempty for t < 23/29 = 0.793; at t = 3/4: 0.5 < c < 0.5625),
ρ = 1 - 3c/2, μ = ρ/2.
- Class X: region R_X of mass 2c. Honest reply: 3c/2 in R_X∖S and ρ fresh points. Four replies
  whose missing blocks partition R_X are exactly 𝒬(c): overlaps c, single parts ρ.
- Class Y: region R_Y of mass 1 - 3μ + q, 0 <= q <= 1 - 3μ - c. Honest reply: 1 - 3μ in R_Y∖S and a hit part of
  mass 3μ: μ unrequested points in the single part of each of three X-petals, re-using the hit
  part of an earlier centre whenever it is not requested, otherwise new points. Roles swap when
  she takes petals in class Y.
- A request containing the traces of two centres but no certified exclusion of class X is
  answered in class X (a class-Y reply would be a third centre with a disjoint trace).
- If no honest member of either class avoids S, he answers with any set that still meets every
  earlier reply of one class in more than c ("closure reply", as E in 17.1).
It violates CR with small leak: the honest leaks are ρ and 3μ = 3ρ/2 (0.19 and 0.285 at c = 0.54), and
the honest families alone have τ = c/2 + q < t, so the closure replies are essential.

### 21.4 Attacks checked against 𝒦₂

| attack | outcome | tag |
|---|---|---|
| J″ (rotation, observed traces) | third request costs 1 - c + 4μ = 3 - 4c > t; replay at c = 0.54: 38 points over at k = 400, 2-cover exists | computed exact (18.2) |
| double sealing of all single parts outside the forcing petal | 1 - c + (2/3)·3ρ = 3 - 4c > t, same inequality | proved |
| role swap (Y petals, X centres with leak ρ = 2μ into the Y petals' hit parts) | same count, 1 - c + 4μ | heuristic (count only; not replayed) |
| third centre without forcing (request = traces of two centres) | he answers in class X | by definition of 𝒦₂ |
| certified double exclusion, e_X + e_Y <= t | fails: e_X = 1 - c on 𝒬(c); e_Y = 1 - c with two hit types for 2–4 members and every block size q; sums 0.88–0.96 at c = 0.52–0.56 | computed, float, LP duality over a weight grid (`exclusion.py`) |
| same with three or four hit types | e_Y drops to 0.30–0.42, sums 0.77–0.88, still > t; and a third hit type needs the unaffordable request | computed |
| many X members with spread blocks | e_X tends to 2c/3 (uniform weights); 2c/3 + 1 - c > t for c < 3(1 - t) | proved for uniform weights only |
`exclusion.py` gives, for every weight vector, a request that really excludes, so its values are
rigorous upper bounds on the certified cost at the grid's best point; the claim "fails" rests on
the grid minimum and is [computed], not proved.

Not checked: whether closure replies can be iterated without lowering some overlap below c or
opening a good triple; 2+2 with simultaneous serving; petals with triple points; any strategy
that learns R_X and R_Y first. So 𝒦₂ is a **candidate**, not a counterexample.

### 21.5 Status

Proved: Theorem DS-b (blind, n - 1 + 7δ <= t). Not proved: blind DS at t/6.
Open, exact:
(a) blind play against 𝒜(t, δ), t/12 < δ < t/6 (aware play wins; blind proof missing);
(b) 𝒞(c, μ) with θ(t) < c < (3 - t)/4 and μ = (2 - 3c)/4: the candidate 𝒦₂(c). J″ covers c >= (3 - t)/4 for this μ.
**Best next step:** validate or kill 𝒦₂(0.54) at t = 3/4 by a mass-level game solver: states are
atom masses, his move is an LP (honest reply if one exists, else closure reply maximising the
minimum overlap), her moves are the finitely many request types used above plus exclusion
requests from `exclusion.py`; depth 10. If every line ends in a certificate, (b) closes; if a
line survives, it is the first explicit non-arena obstruction and should be replayed on points.

Checks: `py compute/petal3/exclusion.py` (about 1 min). Hand proofs re-read once: 21.1 (3δ + 2δ),
the two inequalities 3 - 4c > t in 21.4.

---------------------------------------------------------------------------------------------
## 22. Family test on 𝒦₂(0.54), and its death by a mixed sealing plan (eighth time box)

Code: `compute/petal3/family_k2.py`, `seal_plan.py`, `replay_q.py` (function `run_plan`); logs
`logs/family_k2.log`, `logs/seal_plan.log`, `logs/replay_q_plan.log`.

**Outcome.**
1. Family test: 𝒦₂ is **not a consistent family** in the sense required. Its honest replies form a
   family with τ = c/2 + q < T (47 against 75 at k = 100) [proved; computed]. The smallest threshold
   family that contains every closure reply has τ > T but is no longer two-class, and fails (7,2)
   by six explicit edges that he is not obliged to give. So the test neither kills nor confirms
   𝒦₂ by itself (22.1).
2. Direct kill: **𝒦₂(0.54) as defined (hits μ = ρ/2) loses.** A mixed plan, designed sealing plus
   observed traces, costs 1 - c + 2.5μ <= t at the third request (22.2) [proved for the plan's
   accounting; exact replay]. In general 𝒦₂(c) with hits ρ/2 loses for
   c >= (2.25 - t)/2.875 = 0.5217 at t = 3/4.
3. Not killed: 𝒦₂(c) for θ(t) < c < 0.5217, and variants with larger hits (ν up to 0.8ρ) at
   c = 0.54, where the best plan found misses by 0.003 (22.3). The mass-level solver was not
   built: the instance it was meant for is dead, and the survivors need a statement first.

### 22.1 Family test [proved by hand; computed exact at k = 100]

k = 100, T = 75, c = 54; R_X of 108 points, R_Y of 89 points (q = 0.175), fresh points unlimited.
(b) Honest family (X-edges with at least 81 points in R_X, Y-edges with at least 71 in R_Y): a
request of 28 points of R_X and 19 of R_Y meets every edge, so **τ = 47 < T**. As a fixed family the
honest part of 𝒦₂ is not an obstruction at all: with H known she simply makes that request.
Every reply of 𝒦₂ that matters is therefore a closure reply.
(a) A fixed family containing every closure reply must contain every set with more than c in
R_X (such a set is a legal closure reply after one honest reply whose R_X-part contains it), and
likewise for Y. That threshold family H* has τ = 54 + 35 = 89 > T. It fails (7,2), in fact (6,2):
three X-edges whose R_X-parts have empty common intersection, three such Y-edges, leaks fresh;
no point lies in three of the six, and no X-edge meets a Y-edge (`family_k2.py`: overlaps
2, 27, 28 and 21, 28, 27, exact test: no 2-cover).
Can she force them? Not by anything I can show: inside H* he may answer with near-copies. The six
edges have same-class overlaps down to 2 points, which the two-class adversary never gives.
Reading. For 𝒜 the family test was decisive because the family was the adversary. For 𝒦₂ the
family H* is much larger than the adversary, and 𝒦₂ proper is a path-dependent sub-strategy of
it, not a family. That is itself a finding: **a two-class adversary with c > θ(t) and big hits is
never a fixed family with τ > T unless its classes are arenas of the 𝒜 type** — I state this as
the reading of (b), not as a theorem; the general statement would need the true exclusion
lemma of 17.2.

### 22.2 The mixed sealing plan [proved for the stated accounting; exact replay]

Setting: petals with single parts of mass ρ; a centre meets each single part in at most ν and
meets U outside the single parts only in O(1) points (this is 𝒦₂; ν = μ = ρ/2 there). Rotation:
centre j is forced inside X_{a_j}, and F_j contains the single part of X_{a_j}; b is the fourth petal.
Plan for ν = ρ/2:
- request 1: F_1 and the whole single part of X_{a_2} (ρ);
- request 2: F_2, the observed trace of C_1 (in the single parts of X_{a_3} and X_b: 2ν), and ρ/4
  further points of the single part of X_b;
- request 3: F_3 and the observed traces outside X_{a_3}: C_1 in b (ν), C_2 in a_1 (ν) and in b (at most
  ρ - ν - ρ/4 = ρ/4).
Surpluses over 1 - c: ρ, 1.25ρ, 1.25ρ. Traces are pairwise disjoint by construction, so P4(c) applies.
**She wins if 1 - c + 1.25ρ <= t** (ν = ρ/2), i.e. 1 - c + 2.5μ <= t. On 𝒬(c), ρ = 1 - 3c/2:
c >= (2.25 - t)/2.875. At c = 0.54, t = 3/4: 0.46 + 0.2375 = 0.6975. ∎
`seal_plan.py` minimises the largest surplus over this plan family (grid 1/40) for other hit
sizes [computed]: ν/ρ = 0.2: 0.80ρ; 1/3: 1.00ρ; 0.5: 1.25ρ; 0.6: 1.40ρ; 0.8: 1.54ρ; 1: 1.675ρ
(J″ pays 4ν).

Exact replay (`replay_q.run_plan`, scripted centres as in 18.2, exact 2-cover test) [computed exact]:
| k, T | c | ν | request sizes | result |
|---|---|---|---|---|
| 400, 300 | 216 (0.54) | 38 = ρ/2 | 260, 260, 300 | no 2-cover: she wins |
| 800, 600 | 432 | 76 | 520, 520, 598 | no 2-cover |
| 400, 300 | 212 (0.53) | 41 | 270, 283, 300 | no 2-cover |
| 400, 300 | 210 (0.525) | 42 | 275, 293, 300 | no 2-cover |
| 400, 300 | 208 (0.52) | 44 | second request 2 over | plan fails |
| 400, 300 | 204 (0.51) | 47 | 13 over | plan fails |
| 400, 300 | 216 | 57, 60 (0.75ρ, 0.79ρ) | 17, 20 over with this plan | plan fails |
(The replay takes the smallest extra sealing in request 2 that works; at c = 0.54 that is 0, the
third request then sits exactly at T; with ρ/4 extra the sizes are 260, 279, 281.)
Scope: the centres are scripted (hit ν in every unrequested single part, re-using unsealed
trace points, one point per block). The accounting in the proof covers any centre obeying the
setting; it does not cover closure replies that meet U elsewhere in positive mass.

### 22.3 What survives

- 𝒦₂(c), hits ρ/2, for θ(t) < c < (2.25 - t)/2.875 (0.5 < c < 0.5217 at t = 3/4).
- At c = 0.54: hits ν with 0.75ρ <= ν < (1 - c)/3 = 0.807ρ (the upper limit keeps two centres with
  disjoint hits in one class). Best plan found: surplus 1.54ρ, cost 0.7526 > 0.75. The margin is
  inside what a better plan or P2 could recover; I do not count this as an obstruction.
- Blind play against 𝒜 (21.5(a)): unchanged.

### 22.4 Status

Dead: 𝒦₂(0.54) as defined in 21.3. The family test as a decision procedure for path-dependent
adversaries (it is decisive only when the family is the adversary).
**Exact remaining gap:** two-class adversaries with θ(t) < c < 1 - t/2 whose centres' hits ν and
petals' single parts ρ satisfy 1 - c + s(ν/ρ)·ρ > t, s the plan value above (s(1/2) = 1.25); on 𝒬-type
petals this is c < 0.5217 for ν = ρ/2. Every such adversary known to me needs closure replies, i.e.
is not a fixed family.
**Best next step.** Two cheap things before any solver: (1) prove the reading of 22.1(b) as a
lemma: a fixed family with τ > T whose edges fall into two classes with pairwise overlaps > c has,
in each class, true exclusion cost at most 1 - c - (single mass available to centres); with it the
plan of 22.2 pays e_X instead of 1 - c and the window 0.5 < c < 0.5217 should close; (2) solve the
plan game exactly (it is a small LP per ν once the plan family is written as mixtures) to replace
the grid values of `seal_plan.py`.

Checks: `py compute/petal3/family_k2.py`; `py compute/petal3/seal_plan.py` (about 2 min);
`py -c "import replay_q as r; print(r.run_plan(400,300,216,38,19))"` from `compute/petal3`.
Hand proofs re-read once: 22.1(b) (28 + 19), 22.2 (the three surpluses).

---------------------------------------------------------------------------------------------
## 23. Fixed-family exclusion, Theorem AP, and the exact plan game (ninth time box)

Code: `compute/petal3/plan_lp.py`, `replay43.py` (mode `ap`, optional arena size); logs
`logs/plan_lp.log`, `logs/replay43_ap.log`.

**Outcome.**
1. Exclusion lemma for a fixed family: **true for private mass, false for single mass of a
   quadruple** (23.1) [both proved].
2. Consistency does the work one level up. **Theorem AP:** a fixed family made of two
   arena-with-pool classes with same-class overlaps > θ(t) and τ > t is beaten in at most 10
   requests, for every t >= 112/151 = 0.742 (23.2) [proved by hand; exact replay]. It contains 𝒜, 𝓑
   and the honest part of 𝒦₂, and closes the whole region c > θ(t) for such families.
3. Plan game solved exactly (23.3) [computed exact, LP]: rotation-only value
   s(x) = min(4x, 1/2 + 3x/2, 1 + 2x/3), x = ν/ρ. The grid values of §22 were exact at x = 1/2. The
   path-dependent survivors stay: hits ρ/2 for c < 0.5217, large hits for c < (40 - 18t)/49 = 0.5408.
   Private forcing lowers the value only for x <= 1/2 (to 1 at x = 1/2).
4. The survivors are not fixed families (22.1). A fixed counterexample would have to be a
   two-class family that is not arena-with-pool; none is known, and none is excluded.

### 23.1 Lemma FF [proved by hand]

𝓕: a family of sets of mass 1 with all pairwise overlaps > c. For X in 𝓕 let π(X) be the mass of the
points of X lying in no other member.
**Lemma FF.** τ(𝓕) <= 1 - c - π(X) + ε for every member X.
*Proof.* Request 1 - c - π(X) + ε points of X outside its private part. Another member avoiding the
request meets X in at most c - ε. ∎
**The single-mass form is false.** Complete family on a ground set of mass 2 - c: all overlaps >= c
and τ = 1 - c exactly, yet four members whose complements (mass 1 - c each) cover the ground set
with triple overlaps have single parts of total mass up to (2 - 3c)/2 (c = 0.54: 0.19 in total).
There the single part of one member lies in other members of the family, so π = 0.
So "single mass available to centres" lowers the true exclusion cost only when it is private in
the family. What consistency gives for a two-class family H: τ(H) <= τ_X + τ_Y <= 2 - c_X - c_Y - π_X - π_Y, so
**π_X + π_Y < 2 - c_X - c_Y - t** for all members; with c near θ(3/4) = 1/2 this allows up to 0.25 in
total, with c = 0.54 only 0.17, less than the 0.19 that one 𝒬(0.54) petal carries.

### 23.2 Theorem AP: fixed arena-with-pool families [proved by hand; exact replay]

H = H_X ∪ H_Y; disjoint regions R_X, R_Y of masses n_X, n_Y; H_c = all sets with at least 1 - ρ_c in
R_c, the rest anywhere. Then the least same-class overlap is c_c = 2(1 - ρ_c) - n_c and
τ_c = n_c - 1 + ρ_c = 1 - c_c - ρ_c (Lemma FF with equality). She knows H.
**Theorem AP.** If c_X, c_Y > θ(t), τ(H) > t and t >= 112/151, she obtains seven edges with no 2-cover in
at most 10 requests.
*Proof.* τ_X + τ_Y >= τ(H) > t. Petals: if both τ_c >= t/2, running intersections as in 14.1 (unforced),
and X is the class that reaches four members; otherwise τ_Y < t/2 <= τ_X and she forces class X with
τ_Y + ε in R_Y plus min(1/3, |I|) of the running intersection (t/2 + 1/3 <= t). Either way the petals'
class has τ_X >= t/2. B = the parts of the petals outside R_X, |B| <= 4ρ_X, split into three equal parts
B_0, B_1, B_2.
Centre request j: a set G_j ⊂ R_X of mass max(τ_X + ε, |Z_{<j} ∩ R_X|) containing Z_{<j} ∩ R_X, and B∖B_j. The
reply has class Y (no member of H_X avoids G_j). A centre has at most ρ_Y outside R_Y, so
|Z_{<j} ∩ R_X| <= 2ρ_Y. Every point of B is in at most one centre, the centres are pairwise disjoint on
R_X, and U ⊂ R_X ∪ B: P4(c).
Cost <= max(τ_X, 2ρ_Y) + (8/3)ρ_X + ε. From c_c > θ: ρ_c < 1 - θ - τ_c. Then
τ_X + (8/3)ρ_X < (8/3)(1 - θ) - (5/3)τ_X <= (8/3)(1 - θ) - (5/6)t, which is <= t iff 1 - θ <= (11/16)t; and
2ρ_Y + (8/3)ρ_X < (14/3)(1 - θ) - 2(τ_X + τ_Y) - (2/3)τ_X < (14/3)(1 - θ) - (7/3)t, which is <= t iff
1 - θ <= (5/7)t. With θ = (6t - 2)/5 the first reads t >= 112/151. ∎
At t = 3/4: 1 - θ = 0.5 <= 0.5156. Special cases: 𝒜(t, δ) (Theorem DS), 𝓑 (15.3), the honest families of
𝒦₂ (where τ(H) < t anyway).
Replay (`replay43.py`, mode `ap`, symmetric arenas of n points, leak into the other arena, the
adversary of 19.1; the harness now refuses any request above T; exact 2-cover test), k = 400,
T = 300, 20 seeds each [computed exact]:
| ρ | n | τ per class | c | τ + 8ρ/3 | wins |
|---|---|---|---|---|---|
| 40 | 516 | 156 | 204 | 263 | 20/20 |
| 48 | 503 | 151 | 201 | 279 | 20/20 |
| 44 | 510 | 154 | 202 | 271 | 20/20 |
| 45 | 507 | 152 | 203 | 272 | 20/20 |
| 30 | 530 | 160 | 210 | 240 | 20/20 |
| 20 | 555 | 175 | 205 | 228 | 20/20 |
| 10 | 570 | 180 | 210 | 207 | 20/20 |
Not replayed: unequal arenas, leak into a pool (the proof does not distinguish).

### 23.3 The plan game, exactly (`plan_lp.py`) [computed exact up to LP tolerance]

Model as in 22.2, single parts of mass ρ = 1, hits at most ν = x per single part. Hitting the
maximum is dominant for him (every later cost is nondecreasing in the hits), so the game is a
minimisation with min() terms; each of the 4^4 resolutions is an LP, per mode triple.
Mode R = rotation (forcing 1 - c inside the petal, its single part included); mode P = private
forcing (1 - c - ρ, Lemma FF; the centre may then enter that single part).
| x = ν/ρ | 0.2 | 0.25 | 0.3 | 1/3 | 0.4 | 0.5 | 0.6 | 0.7 | 0.75 | 0.8 | 0.9 | 1 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| R only | 0.800 | 0.875 | 0.950 | 1.000 | 1.100 | 1.250 | 1.400 | 1.467 | 1.500 | 1.533 | 1.600 | 1.667 |
| R or P | 0.300 | 0.500 | 0.750 | 0.833 | 0.900 | 1.000 | 1.400 | 1.467 | 1.500 | 1.533 | 1.600 | 1.667 |
R only fits **s(x) = min(4x, 1/2 + 3x/2, 1 + 2x/3)** at all twelve points [computed; not proved as a
formula]. She wins the plan game iff 1 - c + s·ρ <= t.
Survivors of §22, re-examined on 𝒬-type petals (ρ = 1 - 3c/2):
- hits ρ/2, 0.5 < c < 0.5217: s = 1.25 is exact, so rotation alone does not close it. If the single
  parts are private in a fixed family, s = 1 and the cost is 2 - 5c/2 <= t for c >= (4 - 2t)/5, which is
  below θ(t) for t >= 3/4: **closed in the fixed-family setting**, open for path-dependent 𝒦₂.
- large hits at c = 0.54: s(0.8) = 1.5333, cost 0.7513 > 0.75; exact, so the miss of 0.0013 is real for
  this plan family. Over all admissible hits (ν < (1 - c)/3) rotation alone wins iff
  c >= (40 - 18t)/49 (0.5408 at 3/4). Private forcing does not help for x >= 0.6.
Limits of the model: three centres, pairwise disjoint traces, fixed order; no P2 gain, no
re-selection of petals.

### 23.4 Status

Proved: Lemma FF; Theorem AP; (computed) the plan game.
Refuted: exclusion lemma with quadruple-single mass, also for fixed families.
Reading for the actual problem: H is a fixed family there, so a path-dependent adversary such
as 𝒦₂ is relevant only if it lives inside a fixed two-class family with τ > t. For arena-with-pool
classes that is impossible when c > θ(t) (Theorem AP).
**Exact remaining gap (Barrier F).** A fixed family whose edges fall into two classes with
same-class overlaps > c > θ(t), cross overlaps <= μ, τ > t, and whose classes are **not** of the form
"at least 1 - ρ in a region". Constraints already forced on it: τ_X, τ_Y <= 1 - c - (private mass)
(Lemma FF), and it must defeat the plan game: 1 - c + s(ν/ρ)ρ > t with rotation forcing, where the
single parts used are not private (else mode P applies).
**Best next step.** A structure lemma. For a family with pairwise overlaps > c >= 1/2 and τ >= t/2,
let β be the least number such that some set R contains all but β of every member. Theorem AP's
proof uses only: members have at most β outside R, and some request of mass about τ inside R
meets every member. If β < 1 - θ - τ always holds, Barrier F closes for fixed families. The two
extremes I know are the complete family (β = 0) and "at least 1 - ρ in R" (β = ρ). First test: search
for a pairwise->c family with τ >= 3/8 far from both, on small ground sets (k <= 16, MILP).

Checks: `py compute/petal3/plan_lp.py` (6 s);
`py -c "import replay43 as r; print(r.game(400,300,48,'ap',0,n=503))"` from `compute/petal3`.
Hand proofs re-read once: Lemma FF, Theorem AP (both chains of inequalities; the forced petal
phase), the two closed-form thresholds in 23.3.

---------------------------------------------------------------------------------------------
## 24. Spec for the small-ground-set search (handover; self-contained)

**Goal.** Find, or fail to find, a fixed two-class family that Theorem AP (23.2) does not beat.
**Objects.** k-uniform family H on a finite ground set, T = 3k/4 (k = 12, T = 9; k = 16, T = 12). τ(H) = least size of a point
set meeting every edge. H is *two-class with parameters (c, μ)* if H = H_X ∪ H_Y (disjoint), any two edges of the same class
share at least c points, any two edges of different classes share at most μ points, μ < c.
**Range.** θ = (6t - 2)/5 = 1/2 at t = 3/4. Required: c > k/2, c < k - T/2, τ(H) >= T + 1. Integers: k = 12: c = 7; k = 16: c
= 9. (Then τ(H_X) + τ(H_Y) >= T + 1 and each τ(H_c) <= k - c.)
**Arena-with-pool form, parameter ρ.** H_c has it w.r.t. a point set R if every edge of H_c has at most ρ points outside R.
Always true for ρ = 0, R = everything, so regions must be disjoint: for disjoint R_X, R_Y put β_c = max over edges E of H_c of
|E∖R_c| and h_c = least size of a set inside R_c meeting every edge of H_c (h_c = infinity if none).
**AP cost.** cost(X; R_X, R_Y) = max(h_X, 2β_Y) + ceil(8β_X/3) + 2; AP(H) = min over disjoint (R_X, R_Y) and over the two
roles (X or Y as petal class) of that cost. Theorem AP's proof beats H whenever AP(H) <= T (the +2 covers its ε terms; treat T
- 1 <= AP <= T + 1 as borderline, not as a hit).
**Structure lemma under test.** "Every two-class family in the range has AP(H) <= T", i.e. each class sits, up to β, in its
own region and is hit cheaply inside it. Known extremes: complete family on 2k - c points (β = 0, h = k - c); all sets with >=
k - ρ points in a region of 2(k - ρ) - c points (β = ρ, h = k - c - ρ).
**A hit** = a family in the range with AP(H) >= T + 2.
**Search space (blow-up families; keeps the MILP small).** Ground set = m <= 8 atoms of integer sizes s_1..s_m. An edge type
is a vector e with 0 <= e_i <= s_i, Σ e_i = k; a family is given by a list of types per class and contains ALL k-sets of those
types. Then, exactly:
- two edges of types a, b share at least Σ_i max(0, a_i + b_i - s_i) points (two edges of the same type a: use b = a); they
  can share at most Σ_i min(a_i, b_i);
- same-class condition: the first quantity >= c for all pairs of types in a class (including a type with itself); cross-class
  condition: Σ_i min(a_i, b_i) <= μ;
- a request removing x_i points from atom i (0 <= x_i <= s_i) meets every edge of type e iff e_i > s_i - x_i for some i; τ =
  least Σ x_i killing all types; h_c: same with x_i = 0 outside R_c;
- regions are unions of atoms; β_c = max over types of Σ_{i not in R_c} e_i. Variables: sizes, a 0/1 choice of types per class
  from the enumerated list (prune: types that violate the self-overlap condition). τ >= T + 1 is a "for all requests"
  condition: enumerate the requests x with Σ x_i = T (they are few after symmetry) and require a surviving type for each, or
  solve by cut generation. AP(H) >= T + 2 is checked after the fact by enumerating region pairs. Start with m <= 6, at most 4
  types per class, k = 12; then k = 16.
**Exact verification of any hit (mandatory, on actual point sets, not types).** (1) rebuild H as a list of k-sets (or sample
all type pairs) and recheck both overlap conditions; (2) τ(H) by an exact hitting-set ILP; (3) AP(H) by exhaustive region
pairs; (4) report whether each class is "non-arena": β_c > k - c - τ(H_c) for every region (Lemma FF says private mass is at
most that).
**Then, for a verified hit only:** (5) search for 7 edges with no 2-point cover (SAT). Caution: at these k genuine (7,2)
families with τ > T exist for integrality reasons alone (complete 12-uniform family on 21 points has τ = 10), so (7,2) of a
hit is not news by itself; the news would be a hit whose blow-up keeps τ/k > 3/4 and (7,2) as k grows. Report that at once.
**Files to reuse:** `compute/petal3/lpw.py` (HiGHS wrapper), `replay43.py` (exact 2-cover test, request-game harness),
`exclusion.py` (certified exclusion by weights).

---------------------------------------------------------------------------------------------
## 26. Pooled 𝒜 in the strip 7/5 - 17t/10 <= δ < t/6: closed (tenth time box)

(§25 is left to the structure search of §24.) Code: `compute/petal5/` (`pool_strip.py`, `family72.py`, `run_ps.py`; logs
`logs/family72.log`, `logs/run_ps.log`). Nothing imported from `compute/verify` or `compute/petal3`.

**Outcome.** The strip is **closed**: pooled 𝒜(t, δ) loses in seven requests for every δ < 3t/16, any pool, any
leak placement (Theorem PS, 26.2) [proved by hand; exact replay]. The obstruction was not in the family but in AP's
hypothesis: AP's strategy, accounted directly instead of through c > θ(t), already wins. This also replaces DS
(the pool-free case) and extends its t/6 to 3t/16.

### 26.1 Family test [computed exact]

H(k; n_A, n_F, d_A, d_F, m) = all k-sets with >= k - d_c points in R_c (|R_c| = n_c), the rest anywhere in
R_A ∪ R_F ∪ O, |O| = m; variant "pool only": the rest in R_c ∪ O; variant "exact pool": exactly d_c points in O.
- τ: H is invariant under Sym(R_A) × Sym(R_F) × Sym(O), and "some member avoids S" depends only on the profile
  (|S ∩ R_A|, |S ∩ R_F|, |S ∩ O|), so τ is the least profile sum with no avoiding member (exhaustive over profiles).
  Result τ(H) = τ_A + τ_F, τ_c = n_c - k + d_c + 1 points, in every instance; with n_A = k + T/2 - d, n_F = n_A - 1 this is
  T + 1. (k, T) = (12, 10), d = 1; (20, 16), d = 1, 2; (40, 32), d = 5; all in the strip.
- (7, 2): **fails**. SAT (CaDiCaL, seven distinct members, pattern 4 of class A + 3 of class F, leaks forced into own
  arena or pool; with `EXACT_POOL=1` exactly d_c pool points each) finds seven members in < 1 s in every instance;
  brute-force pair test (all x <= y in the union) confirms no 2-point cover. Without distinctness three equal centres
  already do it (four petals with empty common intersection + one F-set).
- As 20.1 warned, this is not decisive alone: every subfamily with τ > T is a legal adversary. Hence 26.2.

### 26.2 Theorem PS (pooled sealing) [proved by hand]

Setting: disjoint regions R_X, R_Y (masses n_X, n_Y), everything else is "pool" (any size). The adversary answers
request S with any set of mass 1 avoiding S that has >= 1 - ρ_c in R_c for some c (class c); so every subfamily of the
pooled family is covered. Put τ_c = n_c - 1 + ρ_c (a subset of R_c of mass > τ_c meets every class-c set). Assume
τ_X + τ_Y > t (else τ(H) <= t) and

    (a) t - τ_Y >= 1/3 + ε,        (b) max(τ_X, 2ρ_Y) + (8/3)ρ_X + ε <= t.

**Theorem PS.** Then seven requests give seven replies with no 2-point cover. No hypothesis on overlaps (no c > θ).
*Proof.* Petals (requests 1–4). b = t - τ_Y - ε; I_i = common intersection of the first i petals. Request i+1 =
F ∪ J: F ⊂ R_Y of mass τ_Y + ε containing I_i ∩ R_Y (|I_i ∩ R_Y| <= ρ_X, and ρ_X < τ_Y because (b) gives
τ_X <= t - 8ρ_X/3 and τ_X + τ_Y > t); J = min(b, |I_i ∖ R_Y|) of I_i ∖ R_Y (pool points included). R_Y ∖ F has mass
1 - ρ_Y - ε, so the reply is class X. |I_1| <= 1, |I_2 ∖ R_Y| <= 1 - b, |I_3 ∖ R_Y| <= 1 - 2b <= b by (a), so request 4
contains I_3 and the four petals have empty common intersection. Mass <= τ_Y + ε + b = t.
Centres (requests 5–7). U = union of petals, B = U ∖ R_X (other arena AND pool), |B| <= 4ρ_X, split into thirds
B_0, B_1, B_2. Request j = G_j ∪ (B ∖ B_j), G_j ⊂ R_X of mass max(τ_X + ε, |Z_<j ∩ R_X|) containing Z_<j ∩ R_X
(Z_i = trace of centre i on U). R_X ∖ G_j has mass < 1 - ρ_X, so the reply is class Y, and it has <= ρ_Y outside R_Y,
so |Z_<j ∩ R_X| <= 2ρ_Y. U ⊂ R_X ∪ B; on R_X the traces are pairwise disjoint (sealed), on B every point is requested
twice, so lies in at most one centre. P4(c). Mass <= max(τ_X, 2ρ_Y) + ε + (2/3)|B| <= t by (b). ∎

**Corollary (pooled 𝒜).** ρ = δ, τ = t/2 (+ε to have τ(H) > t): (a) is t >= 2/3, (b) is t/2 + 8δ/3 < t, i.e.
**δ < 3t/16**. Since t/6 < 3t/16, the strip 7/5 - 17t/10 <= δ < t/6 is closed for every t > 3/4, with or without
pool, symmetric or not as long as (a), (b) hold for one choice of X. [proved by hand]
- Why AP stopped at c > θ: its last paragraph turns (b) into a condition on c through ρ_c < 1 - θ - τ_c. For 𝒜,
  (b) holds directly far beyond that. The strategy is AP's forced branch with b = t - τ_Y in place of 1/3.
- Why DS failed with a pool (DS_FF_AP addendum): DS empties the petals' intersection by arena chunks and seals only
  V_F-parts, so pool points were never sealed and centres could share them. PS seals the running intersection itself
  (any region) and puts all of B, pool part included, into the double-seal design. The extra cost is in the centre
  phase only: (2/3)|B| on top of τ_X, instead of DS's free V_F filler.
- Not used: arena chunks, overlap thresholds, knowledge of the pool (B and I are read off the replies; she needs R_X,
  R_Y, as in DS and AP).

### 26.3 Exact replay (`run_ps.py`, 300 adversary games per row) [computed exact]

Adversary: per-reply priority genomes (features: multiplicity in earlier replies, same-class multiplicity, common
point of all earlier replies / same-class replies, requested before, pool, other arena; class choice when free;
extra own-arena points), random + hill climbing on (max pair coverage of the seven, request size), plus hand-made
extremes (petal leaks into fresh pool or other-arena points, maximising |B|; centres on earlier replies' points).
Harness checks every reply is in H and avoids S, flags any petal of the wrong class, non-empty petal intersection,
centre of the wrong class, intersecting traces. Independent pair test (all x <= y) on the seven replies.
| k, T | n_A, n_F | d_A, d_F | pool m (only?) | t | 3t/16·k | τ(H) | X | bound | covers | over-T | centre max |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 40, 32 | 54, 53 | 2, 2 | 12 | 0.800 | 6.0 | 33 | F | 22 | 0/300 | 0 | 22 |
| 40, 32 | 53, 52 | 3, 3 | 12 | 0.800 | 6.0 | 33 | F | 24 | 0/300 | 0 | 24 |
| 40, 32 | 52, 51 | 4, 4 | 12 | 0.800 | 6.0 | 33 | F | 27 | 0/300 | 0 | 27 |
| 40, 32 | 51, 50 | 5, 5 | 0 | 0.800 | 6.0 | 33 | F | 30 | 0/300 | 0 | 30 |
| 40, 32 | 51, 50 | 5, 5 | 12 | 0.800 | 6.0 | 33 | F | 30 | 0/300 | 0 | 30 |
| 40, 32 | 51, 50 | 5, 5 | 40 | 0.800 | 6.0 | 33 | F | 30 | 0/300 | 0 | 30 |
| 40, 32 | 51, 50 | 5, 5 | 40 (pool only) | 0.800 | 6.0 | 33 | F | 30 | 0/300 | 0 | 30 |
| 40, 32 | 50, 49 | 6, 6 | 40 | 0.800 | 6.0 | 33 | F | 32 | 0/300 | 0 | 32 |
| 60, 47 | 78, 78 | 5, 5 | 30 | 0.783 | 8.8 | 48 | A | 38 | 0/300 | 0 | 38 |
| 60, 47 | 77, 77 | 6, 6 | 30 | 0.783 | 8.8 | 48 | A | 40 | 0/300 | 0 | 40 |
| 60, 47 | 76, 76 | 7, 7 | 30 (pool only) | 0.783 | 8.8 | 48 | A | 43 | 0/300 | 0 | 43 |
| 100, 80 | 136, 135 | 4, 4 | 60 | 0.800 | 15.0 | 81 | F | 51 | 0/300 | 0 | 51 |
| 100, 80 | 132, 131 | 8, 8 | 60 | 0.800 | 15.0 | 81 | F | 62 | 0/300 | 0 | 62 |
| 100, 80 | 127, 126 | 13, 13 | 60 | 0.800 | 15.0 | 81 | F | 75 | 0/300 | 0 | 75 |
| 100, 80 | 127, 126 | 13, 13 | 120 (pool only) | 0.800 | 15.0 | 81 | F | 75 | 0/300 | 0 | 75 |
| 40, 34 | 52, 51 | 5, 5 | 30 | 0.850 | 6.4 | 35 | F | 31 | 0/300 | 0 | 31 |
| 60, 48 | 76, 81 | 3, 7 | 40 | 0.800 | 9.0 | 49 | F | 48 | 0/300 | 0 | 48 |
| 60, 48 | 76, 78 | 9, 4 | 40 | 0.800 | 9.0 | 49 | F | 34 | 0/300 | 0 | 34 |
| 80, 64 | 103, 104 | 6, 10 | 60 (pool only) | 0.800 | 12.0 | 65 | A | 46 | 0/300 | 0 | 46 |
| 100, 80 | 132, 128 | 12, 7 | 80 | 0.800 | 15.0 | 81 | F | 55 | 0/300 | 0 | 55 |
| 40, 32 | 49, 48 | 7, 7 | 40 | 0.800 | 6.0 | 33 | F | 35 | 0/300 | 154 | 35 |
| 100, 80 | 124, 123 | 16, 16 | 80 | 0.800 | 15.0 | 81 | F | 83 | 0/300 | 171 | 83 |
Row d = 6 at (40, 32) is δ = 3t/16 exactly (fits by integer rounding). Last two rows: controls with δ > 3t/16.

Every in-strip row: 0 covers, 0 budget violations, no flags; the largest centre request equals the predicted bound
(the adversary reaches it), so the accounting is tight. Control rows above 3t/16 overrun exactly as predicted
(no reply exists to an over-budget request).

### 26.4 Status

- **Closed:** pooled 𝒜(t, δ), δ < 3t/16, all t > 3/4 (the strip and DS's range). With 𝒜's own condition δ < 1 - t, this
  is all of pooled 𝒜 for t >= 16/19 = 0.842.
- **Open (pooled 𝒜 only):** 3t/16 <= δ < 1 - t for 3/4 < t < 16/19. PS is sharp there [computed]; the cost is the
  (2/3)·4δ of the double seal on B. Not examined (outside the brief): sealing only B ∩ U*, or more
  than three centres.
- Dead routes: "(7,2) of the fixed pooled family as an obstruction" (fails, 26.1); "AP needs c > θ for 𝒜" (artefact).
- Barrier F as in 23.4 is unchanged: the remaining question is families that are not arena-with-pool.
Hand proof re-read once: petal class forcing, ρ_X < τ_Y, the 1 - 2b <= b step, the double seal on B including pool points.
Checks: `py compute/petal5/family72.py 20 26 25 2 2 10 0`; `py compute/petal5/run_ps.py 30` (fast version).

---------------------------------------------------------------------------------------------
## 25. Result of the §24 small-ground-set search (code: `compute/petal4/search.py`, `verify.py`; logs: `compute/petal4/logs/`)

**Model (exact, no MILP).** Atom-size multisets s_1>=...>=s_m (sorted = symmetry breaking, each s_i <= 2k, n >= T+k since
tau <= n-k+1). For each size vector: SAT (Glucose4) over ALL type subsets (no cap on types per class; strictly more generous
than "<= 4"): types e<=s, sum k, self-overlap sum max(0,2e_i-s_i) >= c; same-class pair clause if min-overlap < c; cross clause
if sum min(a_i,b_i) > mu; one clause per request x (sum x = T, x<=s) demanding a surviving type (e<=s-x); both classes
nonempty; smallest-index chosen type lies in X (X/Y symmetry). Then CEGAR on the AP condition: a model is accepted only if
AP >= T+2; otherwise a sound no-good (monotone in the chosen set: allowed = types with out-mass <= current bounds and killed
by the witness request) is added and the SAT is re-solved. So "NO_HIT" for a size vector is a PROOF (SAT UNSAT after cuts).
**Readings chosen (generous to the adversary).** mu = c-1 (k=12: c=7, mu=6; k=16: c=9, mu=8); no cap on #types; the
spec's "each tau(H_c) <= k-c" is NOT imposed (the true bound is k-c+1, e.g. complete family on 2k-c points; only tau(H) >= T+1 is
imposed). AP uses TRUE point-set regions: regions may split atoms; by symmetry only counts matter and larger regions only help
the petal class, so it suffices to range over partitions r^X+r^Y=s (exact). The atom-union reading of the search space gives
a strictly larger AP and produced one false hit, see below.
**Pseudo-hit (rejected by the mandatory verification).** s=(13,13,2,2), k=12: X = types (0,9,2,1),(0,10,0,2),(0,10,1,1),(0,10,2,0),
(0,11,0,1),(0,11,1,0),(0,12,0,0),(1,10,1,0),(1,11,0,0); Y = same with atoms 1,2 swapped. `verify.py` on actual point sets
(11921+11921 edges): overlaps X-X min 7, Y-Y min 7, cross max 2; tau(H)=10=T+1 (ILP), tau_X=tau_Y=5. Atom-union AP = 11
(= T+2, would be a hit) but splitting an atom gives AP = 10 (witness recomputed on the explicit edges: cost 10) = T+1,
borderline, NOT a hit. Not an arena violation.

| k | atoms m | n range | size vectors | range-feasible (tau>=T+1 and overlaps OK) | hit (AP>=T+2) | status |
|---|---|---|---|---|---|---|
| 12 | <=4 | 21-48 | 9780 | 2002 | 0 | PROVED none (all solved) |
| 12 | <=4 | 49-72 | 8855 | 1974 (1550+424) | 0 | PROVED none |
| 12 | <=4 | 73-96 | 1123 | 147 | 0 | PROVED none (96 = 4*24, so m<=4 with s_i<=24 is COMPLETE) |
| 12 | 5-6 | 21-34, first 4925 of 10070 vectors | 4925 | 655 | 0 | partial: remaining vectors not run (time) |
| 16 | <=4 | 28-44 | 8111 | 1683 | 0 | PROVED none for n<=44; n>44 (to 128) not run |

(the single TIMEOUT line in each of three chunked runs was re-solved from that index in the resume log.)
**Verdict.** No hit found at k=12 (m<=4 exhaustive over all sizes <=24: PROVED none; m=5,6 only partly covered, NOT proved) and
none at k=16 (m<=4, n<=44, PROVED within those bounds; larger n and m>4 not run). Nothing reached steps (5)-(7); the only
candidate was killed by exact verification. Many range-feasible families exist (e.g. two disjoint complete families) but
every one has AP <= T+1: the structure lemma holds on all searched blow-up families.

---------------------------------------------------------------------------------------------
## 27. Pooled 𝒜 above 3t/16: Theorem PS2 (δ < t/4), and the subfamily lever (eleventh time box)

Code: `compute/petal5/ps2.py`, `bload_lp.py`, `intload.py`, `minimal.py`; logs `logs/ps2.log`, `logs/bload.log`,
`logs/min_k12.log`.

**Outcome.**
1. The open range [3t/16, 1 - t) shrinks to **[t/4, 1 - t), and it is empty for t >= 4/5** (Theorem PS2, 27.2)
   [proved by hand, with one LP step computed exactly; exact replay]. At t = 3/4 the range left is [0.1875, 0.25).
2. Double sealing is dead above 3t/16 [proved by hand, 27.1]. The gain comes from P2 instead of P4(c): a single point of a
   petal needs sealing only once, provided its whole neighbourhood (one triple cell) is sealed in that request, and the
   petal requests can be designed so that two triple cells fit into the free part of the centres' forcing sets.
3. Subfamily lever (27.4): at k = 12, d = 2 (t = 3/4, δ = 1/6) **every** subfamily with τ > T fails (7,2), and the
   failure is forced (PS2 fits the integer budget exactly) [proved by hand + computed exact]. Enumerating minimal τ > T
   subfamilies directly is not feasible: they are large (27.4). For k = 20, d = 4 (δ = 0.2, inside [t/4, 1 - t)) nothing
   was decided.

### 27.1 Why PS stops at 3t/16 [proved by hand]

Petals of class X, centres of class Y (a centre has to avoid a set of mass > τ_X = t/2 inside R_X). Let every petal put
its leak on fresh points outside R_X, so B = U ∖ R_X has mass 4δ. A centre may contain any unrequested point of B: points in
R_Y have no capacity limit, and a single pool point is a free sliver. For P4(c), every point of B must be requested in at
least two of the three centre requests. So the three requests together hold 3·(t/2) + 8δ, and one of them holds at least
t/2 + 8δ/3. This is the PS bound, so the **P4(c) route is dead for δ > 3t/16 whatever the petal phase does**. (The pool is
not the issue: with no pool the adversary puts the leaks into R_Y and gets the same 8δ/3; 26.2 and the §20 DS case agree.)

### 27.2 Theorem PS2 [proved by hand; the B-load step computed exactly]

Pooled 𝒜(t, δ) (or any arena-with-pool family with τ_X = τ_Y = t/2, leak δ), 3/4 <= t, δ < min(t/4, 1 - t).
*Petals (requests 1–4).* Request i = F_i ∪ W_i. F_i ⊂ R_Y has mass max(t/2 + ε, |R_Y-parts of earlier petals|) and contains
those parts. W_1, W_2, W_3 are pairwise disjoint blocks of R_X of mass t/2 - ε, and W_4 = R_X ∖ (W_1 ∪ W_2 ∪ W_3), of mass
w = 1 - t - δ + 3ε. Request 4 also contains the points of P_1 ∩ P_2 ∩ P_3 outside R_X ∪ R_Y (pool common points).
- Class X is forced (|F_i| > τ_Y). For i <= 3, P_i ∩ R_X = R_X ∖ W_i exactly, since 1 - δ is all that is left there. The
  R_Y-parts of different petals are disjoint. ∪W = R_X. So the common intersection is empty.
- Budgets. Requests 1–3: t/2 + t/2 (2δ <= t/2 since δ < t/4). Request 4: with s = mass of pool common points, the R_Y-parts of
  petals 1–3 have mass <= 3δ - 3s, so request 4 <= max(t/2 + s, 3δ - 2s) + w <= max(1 - t/2, 1 - t + 2δ) <= t, using
  δ <= t - 1/2.
- Triple cells: T_a = the points of U in every petal but a. Then T_a ∩ R_X ⊂ W_a (mass <= t/2) for a <= 3, and T_4 ∩ R_X = W_4
  (mass w).
*Centres (requests 5–7).* G_j ⊂ R_X has mass >= t/2 + ε and contains the R_X-traces on U of the earlier centres (<= (j-1)δ),
so the centres are class Y with pairwise disjoint traces on R_X. Pick an S-petal a ∈ {1,2,3}: G_5 ⊇ T_a ∩ R_X. Petal 4 is
the second S-petal: G_6 ⊇ T_4 ∩ R_X, and δ + w = 1 - t <= t/2. Each B point gets a pattern P ⊆ {5,6,7}, the requests that
contain it. Singles of petal a (resp. 4) may have P = {5} (resp. {6}). All other B points get |P| >= 2. B points of type
[4] ∖ {a} (resp. [4] ∖ {4}) must have 5 ∈ P (resp. 6 ∈ P).
- P2 holds. Edges are pairs {x, y} with J_x ∪ J_y = [4]. R_X points and points with |P| >= 2 lie in at most one centre, so
  such pairs meet at most two centres. B singles of different petals are never adjacent. A single x of petal a with
  P = {5} has N(x) = T_a, and request 5 contains x and all of T_a (R_X part in G_5, B part by its pattern), so centre 5
  misses both. The same holds for petal 4 with request 6. No point lies in all four petals.
- Cost of request j: |G_j| + (B-load of j) = t/2 + ε + B-load_j (G_j stays at t/2: 2δ <= t/2, and δ + w <= t/2).
  **B-load <= 2δ** for every leak structure. Fix the S-choice (S_1 = petal 1, S_2 = petal 4). Then the least max load is
  a convex function of the masses of B by petal type (singles and multi-types, with petal budgets <= δ), so its maximum
  sits at a vertex of that polytope. All 93 vertices were solved as LPs [computed exact]: max = 2δ, attained by all
  singles. (Correction, §28: an earlier draft minimised over the S-choice before taking the vertex maximum. A minimum of
  convex functions is not convex, so that version did not justify the vertex step. With the choice fixed the maximum is
  2δ for every s1 ∈ {1,2,3} with s2 = 4.) By hand at that vertex: loads δ + δ, δ + δ, 2δ (singles of petals 2 and 3 double-sealed as {5,7}, {6,7}).
  With double seal only, the max is 8/3 δ, as in 27.1.
So every centre request is <= t/2 + 2δ + ε <= t iff **δ < t/4**. ∎ For t >= 4/5, t/4 >= 1 - t, so pooled 𝒜 is closed on its
whole range δ < 1 - t.

### 27.3 Exact replay (`ps2.py`, 200 adversary games per row; harness and adversary of 26.3) [computed exact]

The S-petals and pattern design are chosen in-game by an integer MIP on the actual B points. Brute-force pair test on the
seven replies.
| k, T | d (δ) | pool m (only?) | t/4·k | τ(H) | covers | over-T | centre max |
|---|---|---|---|---|---|---|---|
| 40, 30 | 6 (0.150) | 0 | 7.5 | 31 | 0/200 | 0 | 27 |
| 40, 30 | 6 (0.150) | 40 | 7.5 | 31 | 0/200 | 0 | 27 |
| 40, 30 | 7 (0.175) | 0 | 7.5 | 31 | 0/200 | 0 | 29 |
| 40, 30 | 7 (0.175) | 40 | 7.5 | 31 | 0/200 | 0 | 29 |
| 40, 30 | 7 (0.175) | 40 (pool only) | 7.5 | 31 | 0/200 | 0 | 29 |
| 80, 60 | 12 (0.150) | 60 | 15.0 | 61 | 0/200 | 0 | 54 |
| 80, 60 | 14 (0.175) | 60 | 15.0 | 61 | 0/200 | 0 | 58 |
| 80, 60 | 15 (0.188) | 0 | 15.0 | 61 | 0/200 | 0 | 60 |
| 80, 60 | 15 (0.188) | 80 | 15.0 | 61 | 0/200 | 0 | 60 |
| 80, 60 | 15 (0.188) | 80 (pool only) | 15.0 | 61 | 0/200 | 0 | 60 |
| 100, 78 | 16 (0.160) | 80 | 19.5 | 79 | 0/200 | 0 | 71 |
| 100, 78 | 19 (0.190) | 0 | 19.5 | 79 | 0/200 | 0 | 77 |
| 100, 78 | 19 (0.190) | 100 | 19.5 | 79 | 0/200 | 0 | 77 |
| 50, 40 | 8 (0.160) | 40 | 10.0 | 41 | 0/200 | 0 | 36 |
| 50, 40 | 9 (0.180) | 40 | 10.0 | 41 | 0/200 | 0 | 38 |
| 50, 40 | 9 (0.180) | 40 (pool only) | 10.0 | 41 | 0/200 | 0 | 38 |
| 80, 60 | 15/12 (0.188) | 60 | 15.0 | 61 | 0/200 | 0 | 60 |
| 80, 60 | 12/15 (0.188) | 60 | 15.0 | 61 | 0/200 | 0 | 54 |
| 40, 30 | 8 (0.200) | 40 | 7.5 | 31 | 0/200 | 125 | 32 |
| 80, 60 | 16 (0.200) | 80 | 15.0 | 61 | 0/200 | 141 | 64 |
| 80, 60 | 18 (0.225) | 80 | 15.0 | 61 | 0/200 | 147 | 72 |

Every row with δ <= t/4 (δ = t/4 exactly at k = 80, d = 15, which fits by rounding): 0 covers, 0 over budget, no flags; the
largest centre request equals τ_X + 2d (bound attained). The last three rows (δ > t/4) overrun as predicted. Small k:
(12, 9), d = 2, m = 6 and m = 12 pool only: 300 games each, 0 covers, max request 9 = T. (16, 12), d = 3 (δ = t/4) overruns by
one point in the petal phase (integer rounding), so it is not covered at k = 16.

### 27.4 The subfamily lever

- **Logic** [proved by hand]. (7,2)-failure passes to superfamilies, and every τ > T subfamily contains an inclusion-minimal
  one. So "every minimal τ > T subfamily fails (7,2)" ⟺ "no subfamily is a counterexample at this k". The game is
  stronger: a requester strategy that works against the whole family works against every subfamily. Forcing is
  sufficient, not necessary.
- **k = 12, T = 9, d = 2, any pool: settled** [proved by hand + computed exact]. PS2's integer budget: petal requests
  5 + 4 = 9, request 4 <= max(5 + s, 6 - s) + 2 <= 9. G_j = 5 (blocks 4, W_4 = 2, traces <= 4). B-load <= 4, by exhaustive
  MIP over all 987 integer leak structures (`intload.py 2`: worst 4 = 2d). Each centre request <= 9. So every subfamily with
  τ > 9 yields seven forced members with no 2-cover. Replay agrees (27.3).
- **Direct enumeration of minimal subfamilies: dead at this scale** [computed]. The fractional cover number of the full
  family is 2.8 while τ = 10 (k = 12). So τ > T is purely integral, and cut generation needs very many members:
  LP-guided integer cuts reached τ = 7 after 1244 members (`logs/min_k12.log`, stopped), and minimalisation would cost one ILP
  per member on top. Random cuts are worse (τ = 6 after 700). No minimal subfamily was obtained, so none was tested.
- **k = 20, T = 15, d = 4** (δ = 0.2 ∈ [t/4, 1 - t)): PS2 overruns (max centre request 16), so no forcing statement. Not
  decided.

### 27.5 Status and next steps

- Closed: pooled 𝒜, δ < t/4, all t >= 3/4; all of pooled 𝒜 for t >= 4/5.
- Open: pooled 𝒜 with t/4 <= δ < 1 - t, 3/4 < t < 4/5 (t = 3/4: [0.1875, 0.25)).
- Limits of PS2 [heuristic, counting]: a third S-petal would need T_c ∩ R_X <= t/2 - 2δ, or two S-petals in one request
  would need T_a + T_b <= t/2. With W_4 <= t/2 - δ (petal-4 budget), Σ_a |T_a ∩ R_X| >= 2n - Σ|W| >= 2 - t - δ, and both
  options need t >= 4/5 or δ <= (3t - 2)/2. So within 4 + 3 with this window design, t/4 looks like the end.
- Most promising next route [heuristic]: 2+2 in the range. There a_0 = 1 - t/2 - δ <= θ(t), so the copy bound 11.3 no longer
  blocks a triple served alone (L*(a_0, 1 - t + a_0) <= t). But an A-pair with overlap a_0 needs an unforced request
  (forcing class A costs t/2 and leaves overlap 1 - t/2 > θ), so the adversary's class choice has to be handled. Cross cells
  (<= 2δ) are not yet in the account. Not attempted.
Hand proofs re-read once: 27.1 counting; 27.2 petal budgets (request 4 with the pool trade-off s), the P2 case list, G_j
sizes. Checks: `py compute/petal5/bload_lp.py`; `py compute/petal5/intload.py 2`; `py compute/petal5/ps2.py 20`.

---------------------------------------------------------------------------------------------
## 28. The limit of window-and-seal: δ* = t/2 - 1/6; pooled 𝒜 closed for t >= 7/9 (twelfth time box)

Code: `compute/petal5/window_lp.py` (exact LP of the method), `window_int.py` (integer version), `ps3.py` (strategy PS3,
replay); logs `logs/window_lp.log`, `logs/ps3.log`.

**Outcome.**
1. **Limit of the method** [computed exact, LP; plan and value proved by hand for the all-singles leak]. "4 forced class-X
   petals with designed windows + 3 forced class-Y centres, P2 sealing by patterns" beats pooled 𝒜 iff
   **δ < δ*(t) = t/2 - 1/6** (on 3/4 <= t <= 7/9). δ* is t/4 + (t/4 - 1/6): it beats PS2 for every t > 2/3.
2. **δ* reaches 1 - t at t = 7/9 = 0.7778.** So pooled 𝒜 is closed for all t >= 7/9 (PS3, 28.2) [proved by hand + computed
   exact LP over all leak structures; exact replay]. Open: **t/2 - 1/6 <= δ < 1 - t for 3/4 < t < 7/9** (t = 3/4:
   [0.2083, 0.25)).
3. The obstruction just below 1 - t (28.3) is the third centre request. It has to seal the R_X-traces of both earlier
   centres (2δ) and one triple cell (1 - t - δ), on top of the singles. The three requests together need 1 + 6δ > 3t.
4. **k = 20, d = 4 is not decided.** The method's best integer plan needs 16 > T = 15 even against all-singles leaks
   (`window_int.py`). An exact solution of the game itself is out of reach at this size (28.4).
5. 2+2 in the open range: dead for single-serve triples against a copying adversary [heuristic; argument in 28.5].
   Theorem T/Q′ needs confinement (g = ∅ or a bounded ground set), which a pool breaks [proved: CORE §3 remark]. No other
   certificate was found.

### 28.1 The LP of the method [computed exact]

Variables (mass units): atoms μ_M of R_X by the set M of petals missing them (M ≠ ∅; Σ μ_M = n = 1 + t/2 - δ; window
|W_a| = Σ_{M∋a} μ_M <= t/2, and <= t/2 - s for petal 4, where s = the common points of petals 1–3 outside R_X, sealed by
request 4). Triple cell T_a ∩ R_X = μ_{a}. Assignment: each petal is D (singles sealed twice) or an S-petal of one centre
request j (singles sealed once in j, with T_a in j). G_j >= t/2 and G_j >= (j - 1)δ + Σ_{S-petals of j} μ_{a}. Load_j =
seals in j. Value = least max_j (G_j + load_j).
- Upper bound for the method: the adversary plays all singles (s = 0), and we minimise over all 256 assignments and all
  windows. Lower bound: fix the best assignment, make the windows of petals 1–3 robust (shared), and let W_4, G and the design
  adapt to each of the 94 vertices of the leak polytope (petal budgets δ, singles + 6 pair types + 4 triple types). With the
  assignment fixed, the value is an LP value in the leak masses (they enter the RHS), hence convex, so vertices suffice.
- Result (bisection, `logs/window_lp.log`): the upper and lower bounds coincide at every t scanned:
  | t | 0.75 | 0.76 | 0.77 | 0.775 | 0.78 | 0.79 | 0.80 |
  |---|---|---|---|---|---|---|---|
  | δ*(t) | 0.20833 | 0.21333 | 0.21833 | 0.22083 | = 1 - t | = 1 - t | = 1 - t |
  | 1 - t | 0.25 | 0.24 | 0.23 | 0.225 | 0.22 | 0.21 | 0.20 |
  i.e. δ* = t/2 - 1/6 until it meets 1 - t at t = 7/9. Optimal assignment at every t: one D-petal and three S-petals, one
  per centre request.

### 28.2 Strategy PS3 [plan proved by hand for all-singles leaks; general leaks computed exact (28.1)]

Petals 1–4, class X forced by F_i ⊂ R_Y of mass t/2 + ε (F_4 also contains the common points of petals 1–3 in R_Y). Windows:
W_1, W_2 disjoint and private, mass t/2. W_3 = P ∪ Σ_0, W_4 = P' ∪ Σ_0, where P, P' are private of mass p = 1 - t - δ,
Σ_0 is shared, of mass σ = t/2 - p = 3t/2 - 1 + δ, and ∪W = R_X (check: t + 2p + σ = n). Request 4 also holds the pool common
points (mass s, with W_4 shrunk by s; covered by the LP). Triple cells: T_1 = W_1, T_2 = W_2 (t/2 each), T_3 = P,
T_4 = P' (mass p).
Centres: petal 1 is D; petal 2 is S in request 5 (G_5 = t/2 ⊇ T_2); petal 3 is S in request 6 (G_6 ⊇ z ∪ T_3, mass
<= δ + p = 1 - t <= t/2); petal 4 is S in request 7 (G_7 ⊇ z ∪ T_4, mass 2δ + p = 1 - t + δ). The singles of petal 1 are
split l_5 + l_6 + l_7 = 2δ over pairs of requests. Costs: t/2 + δ + l_5, t/2 + δ + l_6, 1 - t + 2δ + l_7. Balanced at
L = (1 + 6δ)/3 with l_7 = t - 2/3 >= 0 and l_5 = l_6 = 1/3 + δ - t/2 ∈ [0, δ] (needs δ >= t/2 - 1/3). **L <= t iff
δ <= t/2 - 1/6.** P2: as in 27.2 (every S-single's neighbourhood is its triple cell, sealed with it; everything else is
in at most one centre). ∎ For δ < t/2 - 1/3 the windows are relaxed (PS2 already covers δ < t/4).
Petal budgets: requests 1–3: t/2 + t/2; request 4: t/2 + (t/2 - s) + s.
Replay (`ps3.py`; S-assignment and patterns chosen in-game by MIP on the actual points; harness and adversary of 26.3):
| k, T | d (δ) | pool m (only?) | δ*·k | τ(H) | covers | over-T | centre max |
|---|---|---|---|---|---|---|---|
| 40, 30 | 8 (0.200) | 0 | 8.3 | 31 | 0/80 | 0 | 30 |
| 40, 30 | 8 (0.200) | 40 | 8.3 | 31 | 0/80 | 0 | 30 |
| 40, 30 | 8 (0.200) | 40 (pool only) | 8.3 | 31 | 0/80 | 0 | 30 |
| 80, 60 | 16 (0.200) | 80 | 16.7 | 61 | 0/80 | 0 | 60 |
| 80, 60 | 16 (0.200) | 0 | 16.7 | 61 | 0/80 | 0 | 60 |
| 120, 90 | 24 (0.200) | 100 | 25.0 | 91 | 0/80 | 0 | 89 |
| 120, 90 | 24 (0.200) | 100 (pool only) | 25.0 | 91 | 0/80 | 0 | 89 |
| 80, 62 | 17 (0.212) | 80 | 17.7 | 63 | 0/80 | 0 | 62 |
| 100, 78 | 21 (0.210) | 80 | 22.3 | 79 | 0/80 | 0 | 76 |
| 100, 78 | 21 (0.210) | 100 (pool only) | 22.3 | 79 | 0/80 | 0 | 76 |
| 40, 30 | 9 (0.225) | 40 | 8.3 | 31 | 0/80 | 45 | 32 |
| 80, 60 | 17 (0.212) | 80 | 16.7 | 61 | 0/80 | 48 | 62 |
| 20, 15 | 4 (0.200) | 10 | 4.2 | 16 | 0/80 | 44 | 16 |
Last three rows: controls above δ* (k = 20, d = 4 among them). In-range rows: 0 covers, 0 over budget, no flags, centre max <= T (= T where the bound is tight).

### 28.3 The obstruction just below 1 - t [computed exact; heuristic reading]

At δ = 1 - t - η: n = 3t/2 + η, so the windows can barely cover R_X. Σ_a |T_a ∩ R_X| >= 2n - Σ|W| >= 2 - t - 2δ (= t at
δ = 1 - t). Costs of the method, all of which the LP makes tight:
- every centre request has a forcing set of mass >= t/2 in R_X;
- the second and third requests seal the R_X-traces of the earlier centres (δ, 2δ). That is forced: an R_X point in two
  centres has a whole petal as neighbourhood;
- each petal's singles are sealed once (S, with their triple cell in the same forcing set) or twice (D). At most one
  S-petal fits per request, because a triple cell is as big as a window or larger than the free room.
The three requests add up to 1 + 6δ, against a budget of 3t: 1 + 6(1 - t) <= 3t iff t >= 7/9. Below 7/9 this
architecture cannot reach 1 - t. Changes outside the model (petals of both classes, adaptive release of R_X-trace seals
when the third centre is known to miss the neighbourhood, more than 7 replies with re-selection) are **not examined**. The
adaptive release looks useless [heuristic]: the adversary's second centre can always contain singles of every petal,
which are neighbours of any triple-cell point.

### 28.4 k = 20, T = 15, d = 4

- The method at integer level (`window_int.py`, all-singles leaks, all 256 assignments, both role choices): the best plan
  needs **16 > 15**. Continuous value 1/3 + 2δ = 14.67 points; rounding (windows <= τ_X - 1 = 7, triple cell p = 2, G_7 =
  8 + 2) costs the margin. PS3 overruns there (control row of 28.2).
- Exact game: the requester's choice is a 15-subset of a ground set of 46 + m points at each of 7 rounds, and the adversary
  has comparable choice. No exact solver is feasible. **Undecided.**
- Larger k at the same δ = 0.2 (t = 3/4): k = 40, d = 8 and k = 80, d = 16 fit exactly (centre max = T; replay above).

### 28.5 2+2 in the open range [heuristic]

There a_0 = 1 - t/2 - δ < θ(t) and L*(a_0, 1 - t + a_0) <= t, so the copy bound 11.3 alone no longer blocks. But:
- a class-A pair produced by a request that forces class A has overlap >= 1 - t/2 against a copying adversary: the request
  has at most t/2 outside R_F, so the second member can copy the rest of the first, pool leak included [proved by hand];
- an unforced request aimed at a member of class A is answered in class F (refusal). Serving one member of each class splits
  the budget, and leaves overlap >= 1 - t/2 on whichever class answers.
So every reachable same-class pair seems to have overlap >= 1 - t/2, and 1 - t/2 <= θ(t) iff t >= 14/17 = 0.82: outside the
range. Making this a theorem needs an adversary that copies every served member at once (the Theorem N issue). Not done.

### 28.6 Status

- Closed: pooled 𝒜 for δ < t/2 - 1/6 (all t >= 3/4), hence **for all δ when t >= 7/9**.
- Open: t/2 - 1/6 <= δ < 1 - t, 3/4 < t < 7/9. This is the limit of the 4 + 3 window-and-seal method [computed exact].
- Dead: improving 4 + 3 sealing further inside the model (the LP is tight); single-serve 2+2 [heuristic]; Theorem T/Q′
  without confinement.
- Correction to 27.2: the vertex argument needs a fixed S-choice (done; max 2δ).
Hand proofs re-read once: 28.2 window arithmetic and the balancing; 28.3 sum. Checks: `py compute/petal5/window_lp.py scan2`
(about 5 min); `py compute/petal5/window_int.py 20 15 4`; `py compute/petal5/ps3.py 20`.

---------------------------------------------------------------------------------------------
## 29. HANDOVER: pooled 𝒜 on the strip 3/4 < t < 7/9, t/2 - 1/6 <= δ < 1 - t (self-contained)

**Why it matters.** The strip reaches t → 3/4, the asymptotic case (t = 3/4: δ ∈ [5/24, 1/4)).
**Object.** k = 1, t = T/k. Disjoint arenas R_A, R_F of mass n = 1 + t/2 - δ (+ε), pool O of any size. H = all mass-1 sets
with >= 1 - δ in R_A (class A) or in R_F (class F), the rest anywhere; τ_c = n - 1 + δ = t/2 (mass > t/2 inside R_c meets
all of class c); τ(H) = τ_A + τ_F. Game: request |S| <= t, the adversary answers with any member avoiding S (so every
τ > t subfamily is a legal adversary); win = 7 replies with no 2-point cover, certified by P1/P2 (§1: 4 petals with empty
common intersection + 3 centres missing every edge of Γ).
**Closed** (§26–§28): δ < 3t/16 (PS), δ < t/4 (PS2), δ < t/2 - 1/6 (PS3). Code `compute/petal5/`: `ps3.py` (strategy +
replay), `window_lp.py` (exact LP of the method), `pool_strip.py` (adversary search, brute-force 2-cover).
**PS3** (§28.2). Class-A petals forced by t/2 + ε in R_F. Windows W_a = S_a ∩ R_A: W_1, W_2 private (t/2); W_3, W_4 (t/2)
share σ = 3t/2 - 1 + δ, privates p = 1 - t - δ; ∪W = R_A. T_a = points in all petals but a. Class-F centres forced by
G_j ⊂ R_A (>= t/2), which also seals the earlier centres' R_A-traces (δ, 2δ). Petal 1's singles (its δ outside R_A) are
sealed twice. Petals 2, 3, 4 are sealed once, in requests 5, 6, 7, each together with its triple cell. Costs
t/2 + δ + l_5, t/2 + δ + l_6, 1 - t + 2δ + l_7, Σl = 2δ.
**Why maxed** (§28.1, §28.3). The LP over all windows, assignments and patterns, robust over all 94 leak vertices, gives
exactly δ* = t/2 - 1/6. Forcing costs t/2 per centre; requests 6 and 7 must seal the R_A-traces (an R_A point in two centres
has a whole petal as neighbourhood); one triple cell fits per forcing set; Σ triple cells >= 2 - t - 2δ. Total
1 + 6δ <= 3t, which meets 1 - t only at t = 7/9.
**Dead** (do not redo): P4(c) double seal above 3t/16 [proved, §27.1]; further 4+3 refinements inside the window model [LP
exact]; single-serve 2+2 [heuristic, §28.5: forced same-class pairs overlap >= 1 - t/2 by copying, unforced requests get
the other class; needs 1 - t/2 <= θ = (6t - 2)/5, i.e. t >= 14/17]; Theorem T/Q′ (needs g = ∅ or a bounded ground set,
which the pool breaks); enumerating minimal τ > T subfamilies (τ* = 2.8 vs τ = 10 at k = 12); k = 20, d = 4 (best integer
plan 16 > 15, the game is too large to solve exactly).
**Ideas, ranked.**
1. Kill the 2δ trace seal of request 7 (largest term near δ = 1 - t): (a) force centre 2 to miss all petal singles, so an
   R_A point in centres 1 and 3 is harmless once its neighbourhood avoids centre 2; (b) petals of both classes (2A + 2F),
   so the centres' traces land in cells with small neighbourhoods. Test by adding the option to `window_lp.py`: the
   request sum shows at once whether 1 - t is reachable.
2. More than 7 replies with re-selection: 5–6 class-A replies, then choose the 4 petals with the cheapest triple cells and
   singles (he must spoil every 4-subset). Model as a selection LP over the window design.
3. If both fail: prove an adversary (fresh-pool leaks, trace-maximising centres, copy pairs) beats every 4+3 and 2+2
   certificate on the strip (a Theorem-N analogue). Then the strip is a real obstruction at t → 3/4 for Barrier F.

---------------------------------------------------------------------------------------------
## 30. Ideas from §29: split singles, what trace release must save, and dead routes (thirteenth time box)

Code: `compute/petal5/window_lp.py`. New in it: the global `ZFAC` (how many multiples of δ of earlier centre traces each
centre request seals), `build_split`, and the mode `py window_lp.py split`. Log: `logs/window_split.log`. Nothing committed.
Scope (coordinator; notes/verify/PS3.md): the verified δ* = t/2 - 1/6 covers only single-class 4+3 window-and-seal, with best
assignment (D, S5, S6, S7). Ideas 1(b), 2 and adaptive trace release lie outside that scope. Below, each one's own coverage is
stated.

**Outcome.**
1. **Trace relief on its own is dead for t < 10/13** [computed exact, LP; proved by hand in 30.1]. With every trace seal
   removed (ZFAC = (0,0,0)), the §28 LP gives δ_max = 3t/10 (t = .75/.76/.77: .225/.228/.231), and 3t/10 < 1 - t iff
   t < 10/13 = 0.769.
2. **New lever: split S-petals.** The singles of one petal are sealed once each, spread over several requests, and each of
   those requests holds that petal's triple cell. This is P2-legal [proved by hand]. With the standard trace seals (0, δ, 2δ)
   it gains **nothing**: δ_max = t/2 - 1/6 at t = .75, .76, .77 [computed exact]. So the verified limit also holds for this
   wider sealing model.
3. **Split singles plus trace release is exactly enough, with no margin** [computed exact, all-singles adversary]. Suppose
   request 7 seals only δ of the earlier traces (ZFAC = (0,1,1)). Then split plans reach 1 - t at t = .75, .76, .77, which is
   the whole strip. At the corner t = 3/4, δ → 1/4, take ZFAC = (0,1,c) with c = 1, 1.25, 1.5, 1.75, 2. The max request is
   then 0.7500, 0.7708, 0.7917, 0.8125, 0.8333 against T = 0.75. So **request 7 must save one full δ** (c = 1, zero margin).
   The corner plans are Y = ({1},{2},{0},{0,1}) and ({0},{1},{2},{0,1,2}): one petal's tiny triple cell goes into every
   request, and its singles are spread across them.
4. Idea 1(a) as stated is dead [proved by hand, 30.2]. Whether some adaptive release saves δ is open; the corner looks
   negative [heuristic]. Idea 1(b), 2A+2F petals, is dead for t < 4/5 [heuristic, 30.3]. Idea 2, petal re-selection, gives no
   gain against all-singles [proved by hand, in the model, 30.4]. 6+1 with class-A petals is dead on the strip [proved by
   hand, 30.4]. Idea 3, a Theorem-N analogue: **not proved** (30.5).

### 30.1 The sum bound behind item 1 [proved by hand; the LP agrees]

The all-singles adversary puts the leaks on fresh R_F points. Its replies are legal:
- a forced class-A reply takes 1 - δ of R_A ∖ S (mass >= n - t/2 = 1 - δ) plus δ of R_F ∖ S;
- a forced class-F centre takes 1 - δ of R_F ∖ S, including every unrequested single, plus its R_A-trace.

Each centre is forced class F by |G_j| >= t/2 in R_A, and G_j is disjoint from the singles, which lie in R_F.

Every single is sealed at least once. Otherwise it lies in all three centres and has a neighbour in T_a. T_a is nonempty:
T_a ∩ R_X ⊇ R_X ∖ ∪_{b≠a} W_b, of mass >= 1 - t - δ > 0 on the strip. A single sealed twice counts its mass twice.
- Some petal is D: Σ cost >= 3t/2 + 5δ, so the max is >= t/2 + 5δ/3.
- No petal is D and the S-petals are not split: some request holds the singles of two petals, so it costs >= t/2 + 2δ.

These bounds exceed t iff δ > 3t/10 (resp. δ > t/4). They hold whatever the traces cost. So no trace treatment rescues the
unsplit model for t < 10/13. Split plans escape this bound (item 3).

### 30.2 Idea 1: trace release

- (a), "make centre 2 miss all petal singles", does not make an R_X point of C_1 ∩ C_3 harmless [proved by hand]:
  - x in a triple cell T_a: N(x) ⊇ P_a ∩ R_X, of mass >= 1 - δ > t, so C_2 always takes an ε of it outside request 6.
  - x in a pair cell (missing petals a, b): N(x) ∩ R_X ⊇ R_X ∖ (W_a ∪ W_b), of mass >= 1 - t/2 - δ > t/2. Holding it in
    request 6 makes that request cost >= 1 - t/2, and the sum bound then gives δ <= t/2 - 1/5 < δ*.
  - Light cells (points in one petal only; N = one triple cell) have total mass <= (3t/2 - 1 + δ)/2. That is too little to
    absorb z_1, so the adversary can always put z_1 and z_2 into heavy cells.
- What item 3 actually needs: request 7's trace overhead, beyond cells it holds anyway, must be <= δ. The only free room is
  traces overlapping triple cells sealed in the same request, plus the t/2 floor.
- The corner t = 3/4, δ = 1/4: n = 9/8, non-triple mass <= 3/8, and the all-S budget forces ΣG <= 5/4. Put T_1, T_2 into
  requests (5,6), (5,7) or (6,7). In every case ΣG >= 13/8, because the adversary puts z_1 into the pair cell or into the
  triple cell that the next request does not hold [heuristic: hand case analysis for PS3-type and symmetric windows only,
  not all windows].
- **Not built:** an exact adaptive LP, in which the adversary allocates traces cell by cell and the requester re-optimises
  after each centre. It is the computation that decides idea 1.

### 30.3 Idea 1(b): petals 2A + 2F [heuristic]

Main grid X × Y, with X = A1 ∩ A2 ∩ R_A and Y = F1 ∩ F2 ∩ R_F. Both have mass >= 1 - t/2 - δ, which is > t/2 exactly on the
strip, so X by itself is a class-F forcing set. For each y, the traces of the centres from requests holding y must have
empty common part on X. Designs and their sums:
- (β) every centre request ⊇ X, and request 7 ⊇ Y ∖ (r_5 ∪ r_6): Σ >= 3|X| + |Y| + cross;
- (α) every y sealed twice: Σ >= 3t/2 + 2|Y| + cross;
- mixed (one class-A centre): Σ >= |X| + |Y| + t + cross.

The second pair of petals can always leak into cross cells (types {A_i, F_j}; complementary pairs are adjacent) or into worse
places (X or Y, where the neighbourhood is a whole petal). For the leak placements checked, cross >= 4δ. Then (β) needs
4 - 2t <= 3t, i.e. t >= 4/5, while (α) and mixed fail outright. The capacity limit of class-F centres on R_A cross points was
not fully accounted for, so this stays heuristic.

### 30.4 Idea 2: more replies

- **Petal re-selection** [proved by hand, in the model]. Against the all-singles adversary every class-A reply has a window of
  mass exactly t/2, and any four windows of mass <= t/2 can be requested directly (t/2 forcing + t/2 window). So re-selection
  only reaches plans the window model already contains. It can matter only against structured leaks, and the robust LP already
  covers those for the chosen four.
- **Using the extra petals instead** (q > 4 petals; P1-P4 allow q <= 6):
  - 6 class-A petals + 1 centre is **dead on the strip** [proved by hand]. R_X points in <= 3 windows are active, since any
    three class-A sets meet in R_X in mass >= 1 - t - δ > 0. Points in >= 4 windows have mass <= (3t - n)/3. Hence
    |U* ∩ R_X| >= (4 - t - 4δ)/3, which is > t iff δ < 1 - t, and every reply meets U*.
  - 5 petals + 2 centres: not settled. With two centres every edge must lie inside one kill set, which looks expensive
    [heuristic].

### 30.5 Idea 3: an adversary [not proved]

Not achieved.
- Proved parts: the sum bound of 30.1 (forced 4+3, unsplit), 6+1 (30.4), 30.2(a).
- Missing: unforced centre requests (the adversary's class choice; the Theorem N issue), split plans with adaptive trace
  release, 2A+2F with capacity, and q = 5.

If an adversary beating every 4+3 and 2+2 certificate on the strip were proved, the strip would be a real obstruction for
Barrier F at t → 3/4. That is **not** established here.

### 30.6 Status

- **Open:** the strip 3/4 < t < 7/9, t/2 - 1/6 <= δ < 1 - t. The decisive question is now sharp: **can request 7 avoid
  sealing one full δ of earlier centre traces?** If yes, split singles close the strip in the model. If no, 4+3 stays at δ*.
- **Dead:**
  - trace relief without split, for t < 10/13 [LP + hand];
  - split without trace relief [LP];
  - 1(a) as stated [hand];
  - 6+1 with class-A petals [hand];
  - petal re-selection against all-singles [hand];
  - 2A+2F below 4/5 [heuristic].
- No win is claimed, so no replay was run. The split result is a model value against all-singles leaks. A win would also need
  the robust 94-vertex version, an adaptive trace model, and a ps3-style exact replay.
- **Next:** build the adaptive trace LP of 30.2, starting at the corner t = 3/4.

Checks: `py compute/petal5/window_lp.py split` (about 10 min). Oracle: set `window_lp.ZFAC` and call `build`.

---------------------------------------------------------------------------------------------
## 31. Adaptive trace release decided for forced centres; class choice is the remaining gap (fourteenth time box)

Code: `compute/petal5/adaptive_trace.py` (the deciding game as a MIP), `trace_adversary.py` (the adversary A_T on point sets,
with a legality harness), `window_lp.py` mode `cap`. Logs: `logs/adaptive_two.log`, `adaptive_two_nofloor.log`,
`adaptive_corner_*.log`, `adaptive_ccg_077.log`, `window_cap.log`, `trace_adversary.log`, `ps3_k100_T77_d22.log`.
Nothing committed.

**Outcome.**
1. **For forced centres the answer is no at t = 0.75 and 0.76. Adaptive release saves about δ/2, not δ** [computed exact:
   MIP solved to optimality, gap 0]. The game (31.2) is solved at δ = 1 - t - 10^-4. Its value is the least achievable max
   request, with the adversary restricted and the requester given extra power:

   | t | 0.75 | 0.76 | 0.77 |
   |---|---|---|---|
   | value | 0.79157 | 0.77990 | 0.76725 |
   | budget t | 0.75 | 0.76 | 0.77 |
   | verdict | adversary wins | adversary wins | not certified (undecided, 31.2) |

   The non-adaptive model (§30, c = 2) gives 0.8333 at t = 3/4, and c = 1.5 would give 0.7917. So adaptivity is worth half a
   trace seal.
2. **The threshold of this model is δ = 3t/10** [computed exact at these points]:
   - t = 0.75: value 0.70417, 0.75000, 0.75250, 0.77917, 0.79157 at δ = 0.2, 0.225, 0.226, 0.2375, 0.2499;
   - t = 0.76: value 0.76000, 0.76250 at δ = 0.228, 0.229.

   So at the sampled t, forced 4+3 with split singles and any adaptive release loses on (3t/10, 1 - t). That interval is
   nonempty iff t < 10/13, which explains why t = 0.77 is not certified. On [t/2 - 1/6, 3t/10] the model certifies nothing in
   either direction. A gain there over PS3 would need a real strategy and a replay; none is claimed. That the value is
   monotone in δ between the sampled points is [heuristic].
3. **Unforced centre requests reopen the question** [computed exact]. Drop the floor |G_j| >= t/2 and let the adversary still
   answer class F (A_T's choice). The model value is then 0.74970, 0.71970, 0.68970 at t = .75, .76, .77 near 1 - t, all
   <= t, so no loss is certified. **Any obstruction must therefore use class choice**: answering class A to an unforced
   centre request (31.4). That is exactly the Theorem N issue, now isolated.
4. **Legal trace mass** [computed exact; proved by hand at the corner]. A class-F centre that keeps every unrequested single
   has only θ_j = min(δ, 1 - 4δ + ℓ_j) left for its R_X-trace, where ℓ_j is its request's single load. So the §28/§30
   adversary (θ = δ always) is illegal when ℓ_j < 5δ - 1.
   - With the legal θ (`window_lp.py cap`), δ_max is still t/2 - 1/6 at t = .75, .76, .77, so the verified limit stands.
   - At δ = 1 - t, θ = δ is forced: the other two requests carry <= t loads, so ℓ_j >= 4δ - t = 5δ - 1.
5. **The adversary A_T is legal** [computed exact]. Six strip instances (k = 40, 80, 100; with and without pool), each with
   400 random games over all request profiles (unforced ones included), plus PS3 plays: every reply is a member avoiding S,
   and no answerable request goes unanswered.
6. Integer side note [computed exact]. At k = 100, T = 77, d = 22 (δ = 0.22, just above δ* k = 21.83), PS3 stays within T
   with no pool (40 games, 0 covers). With pool m = 60 it overruns by one point. This is a rounding effect, not a closure.

### 31.1 Necessary conditions used (all [proved by hand]; only necessary conditions enter, so a value > t is a real loss)

All-singles leaks on fresh R_F points. Centre j keeps every unrequested single. Its R_X-trace z_j (mass θ_j) also carries an
ε-point of every cell outside G_j. Then:
- (H1) A heavy point x of z_1 (triple or pair cell) lies in request 6. The only alternative, for a pair cell, is a "skip":
  request 7 holds x and the whole neighbourhood N(x). For a triple cell, N(x) ⊇ P_a ∩ R_X has mass >= 1 - δ > t, so no
  skip is possible.
- (H2) z_1 lies in request 7 unless G_6 ⊇ N(x) (release; pair cells only).
- (H3) z_2 lies in request 7 unless G_5 ⊇ N(x) (release; pair cells only).
- (H5) A single of petal a sealed only in request j forces T_a ⊂ G_j.
- (H6) Every single is sealed at least once.

N(x) for a pair cell missing {a,b} is the union of the cells disjoint from {a,b}, and it has no B part.

### 31.2 The game (`adaptive_trace.py`) [computed exact]

The stages follow the play.
1. The requester picks windows (15 cell masses), G_5, which triple cells G_5 hosts, which releases G_5 enables, and ℓ_5.
2. The adversary picks z_1 by greedy fill of the heavy cells outside G_5, in one of two orders: pairs first, or triples
   first.
3. The requester picks G_6 (holding z_1 except skips), its hostings and releases, and ℓ_6.
4. The adversary picks z_2 outside G_6, again by greedy fill in one of the two orders.
5. The requester picks G_7, its hostings, releases and skips, and every single's pattern.

The objective is the max over j of |G_j| + ℓ_j.

How the model leans:
- In the requester's favour: she knows which single is which with hindsight; the adversary never uses light cells; skipped
  points cannot be reused by z_2.
- Against the requester: none. Every constraint is one of H1–H6, the capacity rule θ, or the window rules.

Hence value > t means this adversary beats every adaptive plan in the forced 4+3 window-and-seal model, split singles
included. The scenario tree has 4 leaves, about 560 variables, and is solved in 2–6 min.
- Control: δ = 0.2 gives 0.70417 <= 0.7333 = PS3, as it must.
- Richer adversary families make the MIP intractable at this size. With 4 orders per stage it stopped at the time limit
  (incumbent 0.83320, bound 0.70820); with 10 orders it stopped too. They are not needed for the "adversary wins" rows.
- At t = 0.77 a column-and-constraint loop (`ccg`) was run. The 2-order optimum (0.76725) fails against the 10-order family
  (bound 0.80608 > t). With 5 orders the master stopped at the time limit (incumbent 0.76730, bound 0.69153), and its plan
  fails again (0.80610). The run was stopped there. **t = 0.77 stays undecided** (it lies above 10/13, outside the t → 3/4
  question).

### 31.3 The adversary A_T, explicitly

Class choice:
- class A while fewer than 4 class-A replies exist (or class F is infeasible); class F after that;
- class A only if class F is infeasible.

Replies:
- **Class-A reply:** k - d points of R_A ∖ S plus d fresh R_F points (fresh pool points as fallback).
- **Class-F reply:** every unrequested single; R_X-trace of size θ = min(d, k - #unrequested singles), placed by the better
  of the two greedy orders (the code fills pairs first); plus ε-points of every cell outside S, then R_F filler.

Legality is checked in `trace_adversary.py` (outcome 5). Against forced centres A_T wins on (3t/10, 1 - t) at the sampled t.
Against unforced centre requests the always-F rule certifies nothing (outcome 3).

### 31.4 Toward a Theorem-N analogue: what is proved and what is missing

Proved or computed exact:
- the model loss on (3t/10, 1 - t) for forced 4+3 at the sampled t (31.2);
- 6+1 with class-A petals dead (30.4);
- trace relief and split alone (§30);
- legality of A_T.

Missing, and each would be needed before the strip is called a real obstruction for Barrier F:
1. **Unforced centre requests.** The natural rule: answer class A with a near-copy of an earlier petal (P' = P ∖ S plus fresh
   replacements; legal because |R_A ∖ S| >= 1 - δ when the request is unforced in R_F). Then show that near-copies never
   complete a certificate (q = 5 petals + 2 centres, or a class-A centre). Not done; the 5+2 case of 30.4 is the core.
2. Two-class petals (30.3, heuristic) and 2+2 (§28.5, heuristic).
3. A proof, rather than samples, of the threshold 3t/10 in the forced model. It matches the §30.1 sum bound, which suggests a
   hand proof along the same lines [heuristic].

**Status.** For t < 10/13, the strip part 3t/10 < δ < 1 - t resists every forced 4+3 certificate in the model, adaptive or
not [computed exact at t = .75, .76]. This includes t → 3/4, where 3t/10 = 0.225 and 1 - t = 0.25. The strip is **not** yet
shown to be a real obstruction: unforced requests, with the adversary's class choice, are the open door.

Checks:
- `py compute/petal5/adaptive_trace.py 0.75 1e-4 two` (about 8 min; `... 1500 cap 0` for the unforced version);
- `py compute/petal5/trace_adversary.py`;
- `py compute/petal5/window_lp.py cap`.
