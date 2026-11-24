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
