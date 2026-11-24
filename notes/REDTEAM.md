# REDTEAM — strongest opponents against the discard-game route (Erdős #644)

Time box ~90 min. Code: `compute/redteam/prop.py` (exact requester vs mixed-reply adversaries, one MILP,
plus an independent re-simulation `replay`), `compute/redteam/sim.py` (top-degree requester vs the same
adversaries). Logs: `compute/redteam/prop_*.log`. Nothing of agent C's was edited.
Tags: [proved by hand] / [computed exact] / [numerical] / [heuristic].
Units of k throughout: t = T/k, r = 1 - t, N = mass of the ground set, "conf(N)" as in TWIN §11.

## 0. Bottom line

- **No adversary found that beats the 8-request requester at any t > 3/4.** Every opponent I built either
  loses outright to a requester line that I can exhibit (rigorous: the line is re-simulated), or is
  undecided because the MILP did not close (one case: mixed replies on exactly 2k points, t = 0.76, where
  the requester's best found line misses by 0.0012).
- **No counterexample lead.** Every adversary here answers from the complete family on N points, which
  is not (7,2) for N >= 7k/4; none of them is a family, and none survives, so there is nothing to test
  for coexistence. §4 says exactly what a surviving adversary would have had to look like.
- New information for the proof side: (i) the adversary's useful range of ground sets is narrow,
  N in (1+t, about 2.5]; beyond that he loses in 7 requests to plain top-degree requests; growing the
  ground set during play does not help him; (ii) *mixed* (non-vertex) omissions are a gift to the
  requester because she sees them before her next request — the dangerous omissions are the
  concentrated, redundant ones (C's vertex scripts), not the spread ones; (iii) the "many disjoint pairs"
  idea is capped at m <= 22 and cannot be forced past round 4.

## 1. Adversaries designed

### 1.1 Mixed-reply ("proportional") adversary on N points, constant or growing N

Rule: at round e the active ground set has mass N_e (N_1 <= N_2 <= ...; a growing schedule = fresh
territory opened round by round); the reply takes the same fraction lam_e = 1/(N_e - t) of every
unrequested active point class, pool included. This is the extreme non-vertex reply (the coordinator's
"mixing two replies can hurt more than either"), it is legal in the real game (a generic k-subset of
the unrequested points), and N_e = 1 + t is the forced complete family (the control).
Because the unrequested active mass is exactly N_e - t when she spends her whole budget, the dynamics
are linear and the requester's exact optimum is one MILP (`prop.py`): 7 replies, she discards one,
terminal test mass(D) <= t for the remaining six (same test as `fresh_c/pivot.py`).
Restrictions, all on the requester's side (so her wins are rigorous): full budget every round; the win
"first seven replies already uncoverable" is not modelled in the MILP.

Results, m = 8 (z = min over requesters of mass(D) - t; negative = requester wins; every incumbent was
re-simulated by `replay`, which agrees to 1e-6):

| t | ground-set schedule N_1..N_7 | z incumbent | MILP bound | verdict |
|---|---|---|---|---|
| 0.76 | 1.76 constant (control) | -0.0400 | (not closed) | requester wins, = 3r - t as in FRESH_C §9.2 |
| 0.74 | 1.74 constant (control) | +0.353 | -0.74 (not closed, 200 s) | uninformative (known adversary win, value +0.04) |
| 0.76 | 2.0 constant | **+0.0012** | -1.06 (240 s) | **UNDECIDED** — see PENDING below |
| 0.76 | 7/3 constant | -0.3315 | -0.90 | requester wins [computed exact line] |
| 0.76 | 3.0 constant | -0.7600 | -0.76 (optimal) | requester wins with D = empty |
| 0.76 | 1.76, 2.0, 2.2, 2.4, 2.6, 2.8, 3.0 (growing) | -0.5827 | -0.88 | requester wins |
PENDING_ROWS

Top-degree requester alone (`sim.py`, no optimisation, [computed exact for the stated rule]): against the
constant-N proportional adversary the seven replies are already uncoverable (7-request win, no discard)
for N >= 2.75 at t = 0.76 and N >= 2.5 at t = 0.80; max degree is 4 for every N (Lemma 3). For
N in [1+t, 2.5] the top-degree rule fails badly (mass(D) - t up to +1.06 at N = 1.9..2.0): in that
range she needs the adaptive lines the MILP finds.

Threshold vs N for this adversary [computed, from the table]: the requester's margin at t = 0.76 is
-0.04 (N = 1.76), about 0 (N = 2.0, undecided sign), -0.33 (N = 7/3), -0.76 (N = 3). So the
adversary's power is NOT monotone in N for a fixed rule (monotonicity, TWIN 11.1, is about the best
adversary on N points): the hardest ground set for her is N close to 2, exactly where the twin's rigidity
7.3 says the final type family has no slack. Threshold vs m: only m = 8 was computed.

### 1.2 Why spread omissions help her — template calculus [proved by hand]

By TWIN 7.1 a kept tuple is uncoverable iff the complement types I_x = {i : x not in B_i} are pairwise
intersecting. On conf(N) each complement C_i = S_i + O_i has mass N - 1, so a terminal position is a
measure on an intersecting family with every marginal equal to (N-1)/N; the mean type size is
7(N-1)/N: 3 at N = 7/4, 3.5 at N = 2, 4 at N = 7/3.
- Fano lines: marginal 3/7. Requests alone suffice iff t >= 3N/7 (non-adaptive Fano).
- 2-(6,3,2) blocks (coordinator's second template): six indices, every index in exactly half of the
  blocks, so each of the six complements must contain half of the kept points: possible only for
  N - 1 >= N/2, i.e. N >= 2 (at N = 2 with every omitted point landing exactly in a block).
  Requests alone would need t >= N/2 >= (1+t)/2, i.e. t >= 1: **never**. The six-edge template
  is reachable only through the adversary's omissions.
- [heuristic from here on] Hence the six-edge template is a weapon exactly against adversaries whose
  omissions she can *use*: she sees O_i before choosing S_{i+1}, and spends her next requests only on
  the points that were not omitted. Against the proportional adversary every unrequested class is split
  by each omission, so she can try to complete pairwise intersection class by class; the incidence
  count 7(N-1) >= 3N permits it for N >= 7/4, with room at N = 7/3 (9.33 against 7). (Note the
  non-adaptive count 7t >= 3N fails at N = 7/3, t = 0.76, yet she wins there by -0.33 [computed]: the
  win necessarily uses his omissions.) A vertex adversary (C's rules L / PF) puts each omission on
  points that are already in many complements; my reading is that this is why C's scripts hold her to
  exactly 3r - t = -0.04 while the proportional rule gives her -0.33 at N = 7/3. I did not inspect
  which template her winning lines end in.
- Consequence for adversary design: mixing replies is useful to him only if the mixture is over
  *redundant* omissions. "Mix Fano-type and 2-(6,3,2)-type structure" on the adversary side means: keep
  the final type family off both templates, i.e. keep some class in at least 4 replies whose
  complementary triple still has a common point, for every 6- and 7-subset. On N = 2 the excess
  incidence is exactly 1 (TWIN 7.3(b)); the design template uses excess 0 on six replies and the Fano
  template excess 1 on seven, so an adversary on 2k points must make her waste strictly more than one
  unit of complement incidence over the kept replies. I did not find a rule that does so against an
  adaptive requester; rule L is the natural candidate and loses [C, computed exact].

### 1.3 "Every kept 7-tuple contains a disjoint pair" (multi-waste adversary)

Idea: by the rectangle lemma (TWIN 5.1/5.2) a kept tuple containing a disjoint pair A, A' whose other
members are confined to A + A' is coverable below 4/5. So let the disjointness graph of the m replies
have independence number <= 6: then every 7-subset contains a disjoint pair and a single discard is
useless. For m = 8 two disjoint pairs {A_1,A_2}, {A_3,A_4} suffice (grid: rows / columns of a 2x2
array of cells of mass 1/2).
- [proved by hand] Cap on m: the disjointness graph is triangle-free (three pairwise disjoint replies
  are uncoverable), so alpha <= 6 forces m <= R(3,7) - 1 = 22. This adversary type cannot beat every
  bounded m; it could at best shift t*(m) for m <= 22.
- [proved by hand] It cannot be forced even at m = 8. Both pairs must be of confined kind with respect
  to each other, which forces A_1 + A_2 = A_3 + A_4 = V and A_4 = V - A_3. If she puts mass sigma of
  S_4 inside V - A_3, any reply disjoint from A_3 has mass >= sigma outside V; then the rectangle of A_4
  in A_1 x A_2 has semi-perimeter >= 1 + sigma (TWIN 11.2), i.e. the pair {A_1,A_2} becomes arena-kind
  and may be kept. If instead he stays inside V, A_4 meets A_3 in mass >= sigma and there is no second
  disjoint pair: the play is the ordinary conf(2) pivot game with one disjoint pair, which is agent C's
  open case and not a new adversary.
- [heuristic] With sigma = t the reply A_4 = (r inside V) + (t fresh) leaves a rectangle covering all
  of A_1 x A_2 except a strip of width <= r; I did not compute the continuation, so "she wins after
  that" is not proved.

### 1.4 Common 2-cover for all m replies; two arenas; fresh re-use

- Common cover for all m replies: Theorem 8's method guarantees it only for (m-2)t < 4, i.e. t < 2/3
  at m = 8 (TWIN §5). Open-game version [proved by hand for the bound per reply; the conclusion is a
  count, not a strategy proof]: with A_1, A_2 disjoint and a request taking t/2 of each, any reply
  inside A_1 + A_2 kills at least (t/2)(1 - t/2) = 0.234 (at t = 3/4) of the pair square A_1 x A_2,
  and a reply with fresh mass kills more; the candidate pairs cannot outlast a bounded number of
  replies. Not growing in m.
- Two arenas: TWIN 11.4, loses at 2/3.
- Growing ground set (fresh territory each round): the proportional version loses by -0.58 (table).
  Mechanism [proved by hand, spread lemma TWIN 12.4]: fresh mass lowers the 3-fold mass, and once it is
  <= t at requests 4..7 she wins without a discard.

## 2. Threshold of the best adversary found, vs m and N

| m | N | best adversary I have | level he holds | status |
|---|---|---|---|---|
| 8 | 1+t | forced complete family (control) | 3/4 exactly | [computed exact], reproduces C |
| 8 | 2 | proportional omissions | >= 3/4; at 0.76 her best found line misses by 0.0012 | UNDECIDED (see PENDING) |
| 8 | 7/3 | proportional | < 0.76 | [computed exact line] |
| 8 | >= 2.75 | proportional | < 0.76, already at m = 7 | [computed exact, top-degree rule] |
| 8 | growing to 3 | proportional | < 0.76 | [computed exact line] |
| 9..22 | any | disjoint-pair graph with alpha <= 6 | not forceable (1.3) | [proved by hand] |
| >= 23 | any | — | that mechanism is void | [proved by hand] |

I have no adversary whose guaranteed level exceeds 3/4 for any m >= 8, and none whose level increases
with N. The m-dependence was not computed beyond m = 8 (each extra reply doubles the type space).

## 3. Realizability

Nothing to realise: no adversary above won. For the record, the test that would have applied:
all replies of every adversary in §1 are k-subsets of one N-set avoiding the request, i.e. members of
the complete family on N points, which has tau = N - k + 1 > T but contains uncoverable 7-tuples as
soon as N >= 7k/4 (Fano blow-up). A bounded-m win in the scale-free model would therefore be a statement
about the *depth* of the bad 7-tuples (how many requests are needed to force one), not a family; to
become a family the reply rule would have to be a function of the request alone, consistent over all
C(N,T) requests — the proportional rule is as far from that as possible (it depends on the whole
history through the types).

## 4. Why these adversaries fail — the statement the proof side needs

Two facts are proved, one is the missing lemma.
1. [proved by hand] (Lemma 3 + TWIN 12.4) An adversary survives only if at some request j <= 7 the
   points in at least three of his replies have mass > t; with spread replies that forces N < about 2.6
   ([computed] for the proportional rule: N <= 2.5 at t = 0.76).
2. [counts proved by hand, interpretation heuristic] (§1.2) On conf(N) his omissions have total mass
   7(N-1-t), and every omitted point she can see is complement incidence she did not pay for. To gain
   from them he must place them on points whose complement type is already large ("redundant
   omissions"); how much he can hide this way is what decides the game. On N = 2 the total excess
   incidence is exactly 1 (TWIN 7.3(b)).
3. **Missing lemma (my proposed form; not proved, not tested beyond the table).** *For every eps > 0 there is m(eps) such that for all N in
   [1+t, 5/2] and t >= 3/4 + eps, against any adversary confined to N points the requester can, within
   m(eps) requests, find seven replies whose complement types are pairwise intersecting, using the
   adversary's visible omissions: i.e. the mass of omissions that are redundant for every admissible
   template (Fano on 7, 2-(6,3,2) on 6, and their mixtures of mean type size 7(N-1)/N) is at most
   (4t - 3) + o(1) per kept tuple.* The forced family (N = 1+t, no omissions), the vertex scripts of C
   (all omissions redundant, value exactly 3r - t) and the proportional rule (no omission redundant,
   value far below) are the three corners; the open case is an adversary who chooses adaptively between
   redundant and non-redundant omissions on N close to 2.

## 5. Not done

- The N = 2, t = 0.76 proportional MILP did not close (bound -1.06); neither side is certified there.
- No m >= 9 computation; no certified lower bounds for any adversary win (the MILP bounds are weak).
- No run with partial budgets, and the 7-reply direct win is not in the MILP (both only weaken her).
- The continuation after round 4 in §1.3 is heuristic.
