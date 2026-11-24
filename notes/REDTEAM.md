# REDTEAM — strongest opponents against the discard-game route (Erdős #644)

Code (all in `compute/redteam/`, nothing of agent C's was edited):
`prop.py` (requester's exact MILP vs the proportional adversary), `mix.py` (same, adversary = round-by-round
mixture of proportional and vertex replies, requester's discard can be fixed), `exact.py` (exact rational
re-simulation of a requester line), `nb.py` (neighbourhood driver), `show.py` (terminal position of a line),
`sim.py` (top-degree requester). Logs `prop_*.log`, `mix_a.log`, `nb_0.log`, `nb_1.log`, `nb_long.log`;
certified line `cert_N2_T076.json`.
Tags: [proved by hand] / [computed exact] (exact rational arithmetic) / [numerical] (float MILP) / [heuristic].
Units of k: t = T/k, r = 1 - t, N = mass of the ground set, conf(N) as in TWIN §11.

## 0. Bottom line

- **No adversary found that beats the 8-request requester at any t > 3/4, and no counterexample lead.**
- The one case that looked close (mixed replies on exactly 2k points, t = 0.76, first run: requester's best
  line missing by 0.0012) **is settled for the requester in exact rational arithmetic**: the miss was an
  unconverged MILP, not rounding. With her discard fixed to reply 5 the MILP closes in 57 s and the line,
  re-simulated with fractions at T = 19/25, gives mass(D) - T = -0.0670 exactly negative (§1.1).
- Neighbourhood of that adversary (N = 1.9, 2.1, 2.15, 2.2; a single concentrated omission at reply
  2, 4, 6 or 7; alternating proportional / vertex rounds; constant mixing fractions 0, 0.25, 0.5, 0.8, 0.9
  with three vertex orders; one irregular round-by-round schedule): **all 21 opponents tested lose at
  T = 19/25 (N = 2.15 at T = 0.761), each to an explicit requester line verified in exact rational arithmetic** (§1.2). Three
  fractional mixtures were out of reach of the plain MILP and were settled by transferring her "plan"
  (which types she requests completely) from a neighbouring line. No single plan beats all of them: the
  plan must follow the adversary's mixing schedule.
- Every adversary here answers from the complete family on N points; none wins, so there is nothing to
  realise (§3).

## 1. Adversaries built and what happened to them

### 1.1 Mixed-reply ("proportional") adversary on N points

Rule: at round e the active ground set has mass N_e (non-decreasing; a growing schedule opens fresh
territory round by round); the reply takes the same fraction lam_e = 1/(N_e - |S_e|) of every unrequested
active point class, pool included. This is the extreme non-vertex reply; it is legal in the real game (a
generic k-subset of the unrequested points); N_e = 1 + t is the forced complete family (control).
With full budget the dynamics are linear, so the requester's optimum is one MILP: 7 replies, she discards
one, terminal test mass(D) <= t on the remaining six (same test as `fresh_c/pivot.py`).
Restrictions are all on her side: full budget each round in the MILP; the win "the first seven replies are
already uncoverable" is not modelled.

Certification method. MILP lines are knife-edge (several late requests are unions of whole types of mass
exactly the budget), so a rounded line cannot be replayed at the same budget. I solve the MILP at budget
T - 0.001, snap the line to rationals, and replay it with `fractions` at T, the adversary's rule being
applied with the true unrequested mass. The replayed line is a legal line at T and its value is exact.

| t (exact T) | ground set | mass(D) - T of her line | status |
|---|---|---|---|
| 0.76 | 1.76 (control) | -0.040 = 3r - t | [numerical], reproduces FRESH_C §9.2 |
| **0.76 (19/25)** | **2.0** | **-0.0670** (discard reply 5; MILP for that discard optimal, -0.0660 at budget 0.759) | **[computed exact]** requester wins |
| 0.76 | 1.9 | -0.0341 | [computed exact] requester wins |
| 0.76 | 2.1 | -0.1278 | [computed exact] requester wins |
| 0.761 | 2.15 | -0.0496 (discard 1; other discards not optimised) | [computed exact] requester wins |
| 0.76 | 2.2 | -0.2723 (optimal for discard 5) | [computed exact] requester wins |
| 0.76 | 7/3 | -0.33 | [numerical] requester wins |
| 0.76 | 3.0 | -0.76 (D empty, MILP optimal) | [numerical] requester wins |
| 0.76 | growing 1.76, 2.0, 2.2, 2.4, 2.6, 2.8, 3.0 | -0.58 | [numerical] requester wins |
| 0.801 | 2.0 | -0.2178 | [computed exact] requester wins |

(First all-discards run at N = 2: incumbent +0.0012 after 240 s, -0.057 after 480 s, bound never better
than -0.82: the monolithic MILP is the problem. Fixing the discard makes it close.)

What her winning line looks like at N = 2 (`show.py cert_N2_T076.json`) [numerical]: kept replies
1,2,3,4,6,7; four heavy triples 246, 147, 237, 136 (0.24-0.25 each: the transversal triples of one parity
for the matching (12)(34)(67)), three 4-types 1234, 1267, 3467 (0.11-0.13 each), degree-2 filler 0.34,
no 5-fold point, 13 of 20 triples realised, mass(D) = 0.693. This is the **Fano six-state** of FRESH_C
§8.1 with noise, not the 2-(6,3,2) template (which would have no 4-fold type and exactly ten triples).
Same shape at N = 2.15 and at t = 0.80. So against spread omissions she still plays Fano; I saw no line
ending in the six-edge template.

Top-degree requester alone (`sim.py`) [numerical, exact rule]: against constant-N proportional replies the
seven replies are already uncoverable (7 requests, no discard) for N >= 2.75 at t = 0.76 and N >= 2.5 at
t = 0.80; for N in [1+t, 2.5] the top-degree rule fails (mass(D) - t up to +1.06) and the adaptive lines
above are needed.

Threshold vs N (this adversary, m = 8, t = 0.76): margins -0.040, -0.034, -0.067, -0.128, -0.272, -0.33,
-0.76 at N = 1.76, 1.9, 2.0, 2.1, 2.2, 7/3, 3. The requester's margin is smallest near N = 1.76-1.9 and
grows steadily with N: a spread adversary gets weaker, not stronger, with more room. (The margins at
1.9, 2.1 are incumbents, not optima; the true margins can only be larger.)

### 1.2 Neighbourhood: mixtures of proportional and vertex replies (N = 2, t = 0.76)

Reply at round e = alpha_e x proportional + (1 - alpha_e) x vertex reply (omit the slack greedily in a fixed
order: LOW = lowest degree first, pool first; HIGH = highest degree first; GIFT = pool last, then lowest
degree). alpha = 1 is §1.1; alpha = 0 is C's scripts L / H / G. Requester's MILP per fixed discard at
budget 0.759, each winning line verified exactly at T = 19/25.

| alphas for replies 2..7 | vertex order | result (mass(D) - T, exact) |
|---|---|---|
| 0,1,1,1,1,1 (concentrated omission at reply 2) | LOW | -0.0670 requester wins |
| 1,1,0,1,1,1 (at reply 4) | LOW | -0.2516 requester wins |
| 1,1,1,1,0,1 (at reply 6) | LOW | -0.2203 requester wins |
| 1,1,1,1,1,0 (at reply 7) | LOW | -0.1648 requester wins |
| 1,0,1,0,1,0 (alternating) | LOW | -0.2920 requester wins |
| 0.5 every round | HIGH | -0.0605 requester wins |
| 0,1,0,1,0,1 (alternating) | LOW | -0.3314 requester wins |
| 1,1,0,1,1,1 | HIGH | -0.2262 requester wins |
| 1,1,0.5,1,0.5,1 | GIFT | -0.1311 requester wins |
| 0.9 every round | LOW | -0.0637 requester wins (plan transfer; plain MILP: no line in 335 s) |
| 0.5 every round | LOW | -0.0594 requester wins (plan transfer; plain MILP: no line in 420 s, incumbent +0.24) |
| 0.25 every round | LOW | -0.0572 requester wins (plan transfer) |
| 0.8 every round | GIFT | -0.1064 requester wins (plan transfer, and plain MILP with discard 7) |
| 0 every round (= C's vertex rules) | LOW / HIGH | -0.0370 = 3r - t at budget 0.759 (plan transfer); plain MILP at 0.76, discard 1: -0.0400 optimal, = C's value |
| 0 every round | GIFT | -0.2780 requester wins (plan transfer) |
| 0.7,0.2,0.9,0.4,0.6,0.1 (irregular) | LOW | -0.1841 requester wins, with the plan of the alternating line; the plan of the pure proportional line FAILS here by +0.0061 (optimal for that plan) |

Plan transfer (`plan.py`, `planall.py`): take a logged winning line, record at each round the set of types
she requests completely and her discard, impose "request these types completely" as constraints against
the new adversary and let the MILP re-optimise the rest. This restricts only her, the model closes in
seconds, and the resulting line is verified exactly as before.

Reading.
- A concentrated omission at rounds 4, 6 or 7 inside otherwise proportional play *helps* her (margins
  0.16-0.25 against 0.067).
- Along the constant-alpha LOW family her margin with one fixed plan is 0.037, 0.057, 0.059, 0.064, 0.067
  at alpha = 0, 0.25, 0.5, 0.9, 1: monotone, smallest at the pure vertex rule, where it equals the control
  value 3r - t. In this family mixing does NOT hurt her more than the pure vertex reply; the worst
  opponent is still C's rule L / the forced family. (These are margins of one plan, i.e. lower bounds on
  her true margin.)
- The irregular schedule is the only place where a plan broke (+0.006): an adversary who changes his
  mixing fraction from round to round forces her to change plan, and an adversary who chooses the fraction
  *after seeing her request* (not a fixed schedule) is outside everything computed here. That adaptive
  choice of alpha_e is the natural refinement; with six rounds and a few alpha levels it is a small game
  tree over plans, and it is what I would hand to C's certified solver next.

### 1.3 Templates [counts proved by hand; interpretation heuristic]

A kept tuple is uncoverable iff the complement types I_x = {i : x not in B_i} are pairwise intersecting
(TWIN 7.1). On conf(N) each complement has mass N - 1, so a terminal position is a measure on an
intersecting family with all marginals (N-1)/N; mean type size 7(N-1)/N.
- Fano lines: marginal 3/7; requests alone suffice iff t >= 3N/7.
- 2-(6,3,2) blocks: six replies, each complement must contain exactly half of the kept points, so it
  needs N - 1 >= N/2, i.e. N >= 2; requests alone would need t >= N/2 >= (1+t)/2, i.e. t >= 1 — never.
  **The six-edge template can only be completed with the adversary's omissions**, at least N/2 - t of
  each complement; at N = 2 that is all of his slack r, every round, landing exactly on blocks. It
  has zero tolerance for misplaced omissions, so presumably he can avoid it cheaply [heuristic, not
  proved]; in any case it is not what her optimal lines use (§1.1).
- At N = 7/3, t = 0.76 the non-adaptive count 7t >= 3N fails, yet she wins by 0.33: her wins on larger
  ground sets necessarily use his omissions, which she sees before the next request. Spread omissions
  are usable; omissions on points already in many complements are not. That is the only sense in which
  "mixing" helps him, and it points at low-degree-biased mixtures (the undecided rows above).

### 1.4 "Every kept 7-tuple contains a disjoint pair"

Idea: a kept tuple containing a disjoint pair with all other members confined to its union is coverable
below 4/5 (TWIN 5.2); so make the disjointness graph of the replies have independence number <= 6 — for
m = 8 two disjoint pairs {A_1,A_2}, {A_3,A_4} (rows and columns of a 2x2 grid of cells of mass 1/2).
- [proved by hand] Three pairwise disjoint replies are uncoverable, so the graph is triangle-free and
  alpha <= 6 forces m <= R(3,7) - 1 = 22. The mechanism cannot work for every bounded m.
- [proved by hand] It cannot be forced at m = 8 either: both pairs confined with respect to each other
  means A_1 + A_2 = A_3 + A_4 = V, so A_4 = V - A_3. If S_4 has mass sigma inside V - A_3, a reply
  disjoint from A_3 has mass >= sigma outside V and its rectangle in A_1 x A_2 has semi-perimeter
  >= 1 + sigma (TWIN 11.2: the pair {A_1,A_2} becomes arena-kind and can be kept); if he stays inside V
  there is no second disjoint pair and the play is C's ordinary conf(2) pivot game.
- [heuristic] The continuation after sigma = t was not computed.

### 1.5 Other opponents

- Common 2-cover for all m replies: guaranteed only for (m-2)t < 4 (TWIN §5), t < 2/3 at m = 8. With
  A_1, A_2 disjoint and a request taking t/2 of each, every reply kills at least (t/2)(1 - t/2) = 0.234
  of the pair square at t = 3/4, more if it uses fresh points [proved by hand]; not growing in m.
- Two arenas: TWIN 11.4, loses at 2/3.
- Growing ground set: loses by 0.58 in the proportional version (table); by the spread lemma (TWIN 12.4)
  fresh mass lowers the 3-fold mass and she wins without a discard once it is <= t.

## 2. Threshold vs m and N

| m | N | strongest adversary I have | level he holds | status |
|---|---|---|---|---|
| 8 | 1+t | forced complete family | exactly 3/4 | reproduces C |
| 8 | 1.9 - 2.2 | proportional | below 0.76 | [computed exact] |
| 8 | 2.0 | 17 fixed mixing schedules proportional / vertex (§1.2) | below 0.76; weakest margin 3r - t at the pure vertex end | [computed exact] |
| 8 | 2.0 | mixing fraction chosen after seeing the request | unknown | not computed |
| 8 | 7/3, 3, growing | proportional | below 0.76 | [numerical] |
| 7 | >= 2.75 | proportional | below 0.76 | [numerical], top-degree rule |
| 9..22 | any | disjoint-pair graph | not forceable | [proved by hand] |

No adversary of mine holds a level above 3/4 at m = 8, none gains from larger N, and m >= 9 was not
computed (more requests can only help her against a fixed rule).

## 3. Realizability

No adversary won, so no coexistence test was run. All replies of all adversaries here are k-subsets of one
N-set, i.e. members of the complete family on N points, which contains uncoverable 7-tuples for
N >= 7k/4. A bounded-m win in this model would have been a statement about how many requests are needed to
force a bad 7-tuple, not a family; to be a family the reply would have to depend on the request alone.

## 4. Why these opponents fail — what the proof side can use

1. [proved by hand] (Lemma 3 + TWIN 12.4) He survives only if at some request j <= 7 the points in at
   least three replies have mass > t; for spread replies this confines him to N below about 2.6
   ([numerical]: 2.5-2.75 for the proportional rule).
2. [computed exact, for the listed rules] Against spread omissions on N in [1.9, 2.2] she wins at 0.76 with
   the Fano six-state reached adaptively, with a margin that grows with N; a concentrated omission at one
   round does not help him.
3. **Missing statement** (not proved, not refuted): *on conf(N), N in [1+t, 5/2], for an adversary who
   may bias each omission towards points already lying in many complements, the requester still reaches a
   Fano six-state with mass(D) <= t within a bounded number of requests when t >= 3/4 + eps.* The three
   solved corners are: no omissions (N = 1+t, margin 3r - t), all omissions on lowest-degree points
   (C's rule L, margin exactly 3r - t), all omissions spread (margin larger). The unsolved region is the
   interior with *adaptive* choice of the bias: every fixed schedule I tried loses, but to different
   plans, so the open question is exactly whether she can choose her plan before knowing his next bias.

## 5. Not done / caveats

- No adversary win occurred. Every opponent is a fixed (request-independent) mixing schedule; schedules
  that react to her request were not computed. The plain MILP cannot certify an adversary win (its bounds
  stay near -0.6 unless all seven fixed-discard models close), so "no win found" for a future opponent
  would need C's solver.
- Rows tagged [numerical] rest on float MILP incumbents re-simulated in floats, not on `exact.py`.
- "Exact" means: exact value of an explicit rational requester line against the stated deterministic rule,
  in the scale-free model with free slivers. It is not a statement about finite k.
- m = 8 only; partial budgets and the direct 7-reply win are not in the MILP (both only weaken her).

=============================================================================================
# Part II — red team on the PETAL architecture (second job)

Read: TWIN §13–§14, PETAL.md (its §1–§6), `Lean644/ThreeCentres.lean`. Code:
`compute/redteam/petal_room.py` (SAT, exact), `petal_touch.py` (exhaustive). Outputs `petal_room.out`,
`petal_touch.out`. Units of k; t = T/k.

## 6. Bottom line

- **The adversary that defeats the four-petal certificates is not an arena construction; it is the
  single self-sufficient arena: any adversary confined to N points with k + T <= N < 2k.** On such a
  ground set neither four-petal certificate of PETAL.md exists or can be forced: triple-free four petals
  do not exist at all (they need N >= 2k), and "four petals + three centres with pairwise disjoint
  traces" does not exist for N < 17k/9 and cannot be closed for N < 11k/3 - 2T [proved by hand, §7; both
  existence thresholds confirmed by SAT / exhaustion]. For 2k <= N < 3k - T a one-line adversary rule
  ("touch every triple") still prevents every triple-free four-petal set [proved by hand]. This is
  PETAL §5's adversary (b) in exact form, and it is a route (i) defeat: no good four-petal configuration
  is ever reachable, for any number of requests.
- **Every arena-type variant I tried loses to PETAL's Theorem J or to Theorem D** (§8): two disjoint
  arenas of any sizes, overlapped arenas with small overlap, three or more arenas, nested arenas,
  near-copy chains. The reason is uniform: an arena that is not self-sufficient (mass < 1 + t) can be
  emptied by a request, so she can force far centres; a self-sufficient arena makes the others
  irrelevant and is the single-arena case.
- **It is not a counterexample.** The single arena is a sub-family of the complete family K_N,
  N >= k + T, which is not (7,2) (N >= 7k/4). In Part I she beat every such opponent I tried, but with
  *six* petals (the Fano six-state, mass(D) = |U*| <= T), never four. So Part II shows that the
  four-petal layer is empty exactly on the ground sets where Part I's opponents live, and that the proof
  needs the q = 6 lemma there (§9).

## 7. Room lemmas [proved by hand; checked exact]

**7.1 (triple-free four petals need 2k points).** Four k-sets with no point in three of them have union
>= 2k. Hence on N < 2k points the matching-load certificate and the Theorem I shapes (TWIN 15.4) do not
exist. [count; exhaustive check k = 3, 4: they exist iff N >= 2k]

**7.2 (touch every triple).** Let all replies lie in N < 3k - T points (or, in the open game, let every
three replies with empty common intersection have union < 3k - T). Three replies with empty common
intersection have a pair set P of size exactly 3k - |union| > T, so no request contains P, and the
adversary may put one unrequested point of P into his reply — for every such earlier triple at once
(O(1) points per reply). Then no reply is ever the latest member of a triple-free petal set: among four
triple-free petals the three earliest have empty common intersection and the latest would have to avoid
their pair set. So **triple-free four-petal configurations never arise, for any number of requests.**
[`petal_touch.py`: the minimum pair-set size over triples with empty common intersection equals 3k - N,
all k-subsets, (k,N) = (3,6), (4,7), (4,8), (5,9), (5,10). Without "empty common intersection" the bound
is only (3k - N)/2; the first version of my check caught that slip.]
This is the exact form of PETAL §5(b): "he pushes p above t" is automatic below 3k - T = 2.25k.

**7.3 (three centres with disjoint traces need room).** Petals (at most four, empty common
intersection, union U, |U| = u >= 4k/3) and centres C_1, C_2, C_3 with C_i ∩ C_j ∩ U = ∅, all inside an
N-set: the traces are disjoint in U and each centre has at most N - u points outside U, so
3k <= u + 3(N - u), i.e. u <= 3(N - k)/2 and **N >= 17k/9**. Integer form N >= k + ceil(2·ceil(4k/3)/3).
[`petal_room.py`, SAT, k = 3..9: a configuration exists iff N >= 6, 8, 10, 12, 14, 16, 17 — equal to the
formula in every case.] I did not redo the count with the active set U* in place of U (PETAL P4(c)).

**7.4 (forcing the centres needs more room).** To force the second and third centre she requests the
traces: she needs |C_1 ∩ U| + |C_2 ∩ U| <= T, and the adversary chooses C_2 with the largest trace
available. On N points every k-set has trace >= k - (N - u), and after a request of T points of U he can
still take min(k, u - T). So the closure needs u + (k - N + u) <= 2T, i.e. N >= k + 2u - 2T
**>= 11k/3 - 2T** (2.17k at t = 3/4). [SAT: a configuration with |U| + |G ∩ U| <= 2T exists iff
N >= max(ceil(4k/3), k + 2ceil(4k/3) - 2T), k = 3..9, T near 3k/4 and T = k - 1; no mismatch.]
In the open game the same defence is the invariant "every reply meets the union of any four earlier
replies with empty common intersection in more than 2T - |U| points". A single arena gives it for
free. It is exactly what Theorem J's forcing request F (cost 1 - c) is meant to break; on a
self-sufficient arena the reply to F cannot be far (overlap >= 2k - N), so it lands in the band and
Theorem J returns "banded pair", not a win.

**7.5 Summary by ground-set size (t = 3/4 + eps, units of k).**

| N | triple-free four petals | four petals + three centres | what is left for her |
|---|---|---|---|
| [1+t, 17/9) | do not exist | do not exist | q = 6 (Fano six-state); three anchors at the Fano point |
| [17/9, 2) | do not exist | exist, cannot be closed | same |
| [2, 11/3 - 2t) ≈ [2, 2.17) | exist, never reachable (7.2) | cannot be closed | same |
| [2.17, 3 - t) ≈ [2.17, 2.25) | never reachable (7.2) | closable only if he lets a trace drop | same |
| >= 10/3 - t ≈ 2.58 | — | — | she wins by Theorem D / spread lemma |

## 8. Arena-type adversaries: all lose [proved by hand, using PETAL Thm J and TWIN Thm D as stated there]

- **Two disjoint arenas, any sizes.** Direct argument, 7 requests: request T/2 of the current common
  intersection of the replies of each arena; every reply removes T/2 > k/3 from its arena's core, so the
  fourth reply of an arena has empty common intersection with the first three; seven replies contain
  four from one arena and at least one from the other; a cover would need a point in all four. Arena
  sizes never enter. (If he never uses the second arena he is a single-arena adversary.)
- **Different sizes / an arena that is not self-sufficient.** She can force him out of an arena of mass
  n < 1 + t by requesting n - 1 of it; this only adds options for her.
- **Overlapped arenas with overlap o.** Cross overlaps are at most o. If o < λ (PETAL: λ = 0.05 at
  t = 3/4) Theorem J applies verbatim. If o is in the band, the pair is banded and we are in PETAL §5;
  to stop triple-free petals he must then keep every three replies inside 3k - T points (7.2), i.e. the
  two arenas together form one ground set of fewer than 2.25k points: the single-arena case with extra
  restrictions on him.
- **Three or more arenas with small cross overlaps.** A reply in a third class gives anchors with
  p < 3λ <= t - 1/3 and loses to Theorem D; an arena he never uses does not exist.
- **Nested arenas.** A reply in the inner arena is a reply in the outer one: single arena.
- **Near-copy chains** (each reply a near-copy of the previous one, drifting). Either the chain stays
  inside 2.25k points (single-arena case), or three members with empty common intersection have union
  >= 3k - T, hence pair mass <= T, and a fourth triple-free petal becomes affordable; if it drifts to
  union >= 10k/3 - T she wins by Theorem D outright. [the middle case is "affordable", not "won":
  the matching loads are still his to fight — PETAL §5(i),(ii)]
So arenas are not the weapon. The structure that defeats the four-petal layer is concentration of ALL
replies on fewer than about 2.2k points.

## 9. Why it is not a counterexample, and the lemma the proof needs

Part I: at t = 0.76 on N = 1.9k, 2.0k, 2.1k, 2.2k she beats every mixing schedule I tried with eight
requests, ending in six kept replies whose active set D = U* has mass <= T [computed exact]. In PETAL's
language that is the one-centre certificate P4(a) with q = 6.
**Lemma needed.** *For t >= 3/4 + eps: if every three replies with empty common intersection have pair
mass > T (in particular if all replies lie in fewer than 3k - T points), then within m(eps) requests the
requester obtains six replies with |U*(P)| <= T — the Fano six-state: a perfect matching of the six
whose three pair-intersections have total mass <= T, and the four transversal triples of one parity with
empty intersection (TWIN 7.5).* The case split that makes the architecture exhaustive is by the size of
three-reply unions: below 3k - T (this lemma; no four-petal certificate is available), or at least
3k - T (a fourth triple-free petal is affordable and PETAL §4–§5 applies).
Not done: a proof of the lemma, or an adaptive concentrated adversary beating the q = 6 requester
(Part I §1.2: every fixed schedule loses; request-dependent schedules were not computed).

## 10. Realizability and caveats

- No winning adversary, so no (7,2) coexistence test. K_N is (7,2) only for N < 7k/4, where
  tau = N - k + 1 <= 3k/4: consistent with the conjecture.
- 7.3–7.4 concern the certificate "three centres with pairwise disjoint traces on U"; four petals with
  triple points under the general criterion P2, and q = 5, were not analysed.
- §8 relies on PETAL Theorem J and TWIN Theorem D as stated; only the disjoint-arena case was re-derived.
- `node ../fresh_c/anchor.js 9 7` (read-only use of C's solver, to list the winning anchor shapes at
  t = 0.778) did not finish in the time box; nothing is claimed from it.

## 11. What the certified winning lines realise at the end (for TWIN §16–§17, request E3)

Analysis only: the saved lines were re-simulated (`compute/redteam/fano_read.py`; outputs `fano_read.out`,
`fano_classes.out`, `fano_nonfano.out`, `fano_requests.out`). Seven = the six kept replies plus the eighth
reply (any k-set avoiding D). A type is "realised" if one point has it (slivers included, tolerance 2e-6).
For each line all 30 labelled Fano planes on the seven were tested for "every realised type is line-free".
Classes as in TWIN 16.1, by the first four kept rounds. Masses are float re-simulations at budget 0.759
(the lines themselves are the exactly verified ones). [computed; classification exhaustive over labellings]

**Answer in one line.** N = 1.9k: a Fano labelling of class **(T)** (triangle + point on a side), unique.
N = 2.0k (`cert_N2_T076.json`): a Fano labelling of class **(Q)** (quadrangle-first), unique. In both the
discarded reply is the fifth. No line realises the 2-(6,3,2) pattern (every line has realised 4-fold types).
Lines at N = 2.1k, 2.2k and two mixture lines at 2.0k are **not Fano** (no labelling), see 11.3.

### 11.1 N = 1.9k, t = 0.76, proportional adversary — class (T)

Kept replies 1,2,3,4,6,7 and the final reply 8; reply 5 discarded; mass(D) = 0.726 at budget 0.759.
Unique labelling, lines: **234, 146, 137, 267, 128, 368, 478** (these are exactly the seven empty triples).
So 1,2,3 is a triangle, 4 lies on its side 23, then 6 on 14, 7 = 13 ∩ 26, 8 = 12 ∩ 36 ∩ 47.

| round | block she must pay (16.1) | mass | rest of the request |
|---|---|---|---|
| 2 | none | 0 | 0.556 of B_1, 0.203 of the pool |
| 3 | none (triangle) | 0 | 0.269 of B_1 only, 0.277 of B_2 only, 0.212 of B_1∩B_2 (not sealed: 123 is realised) |
| 4 | B_2 ∩ B_3 (line 234) | 0.447 (23: 0.292, 123: 0.155) | 0.312 = all points lying only in B_1 |
| 5 (discarded) | — | — | all of 1-only (0.312), all of 24 (0.279), small singles, part of 34 |
| 6 | B_1 ∩ B_4 (line 146) | 0.467 (134: 0.262, 124: 0.205) | 0.292, spent on points of B_5 (types 235, 23) |
| 7 | (B_1∩B_3) ∪ (B_2∩B_6) (lines 137, 267) | **0.759 = whole budget** (134: 0.262, 246: 0.245, 1236: 0.136, …) | 0 |
| 8 | (B_1∩B_2) ∪ (B_3∩B_6) ∪ (B_4∩B_7) = D | 0.726 | 0.034 spare |

Final types on the six kept replies (mass; * = in D): triples 134 0.262, 237 0.256, 246 0.245, 167 0.239
(the four heavy classes), 136* 0.032, 247* 0.030, 124* 0.025, 126* 0.025, 347* 346* 467* 367* 0.024 each,
123* 0.019; 4-fold 1247* 0.180, 3467* 0.171, 1236* 0.136; pairs 23 0.036, 26 0.035, 17 0.034, 16 0.034 and
dust; no 5-fold type. Degree masses: 1.234 in triples, 0.487 in 4-fold, 0.172 in pairs.
Reading: the heavy part is the Fano six-state of FRESH_C §8.1 (four transversal triples about 1/4 each,
three 4-types of total 0.49), but the *order* is (T): the first three replies are NOT anchors (B_1∩B_2 is
only partly requested at round 3), the first paid block comes at round 4, and the two tight rounds are 7
and 8. Reply 5 is a real spare: its request strips B_1-only and the 24-cell, and the reply is then used
only as a place to spend the free budget of round 6.

### 11.2 N = 2.0k, t = 0.76, proportional adversary — class (Q)

Kept 1,2,3,4,6,7 + 8; reply 5 discarded; mass(D) = 0.693. Unique labelling, lines
**128, 348, 137, 247, 146, 236, 678**: 1,2,3,4 a quadrangle; 6, 7, 8 its diagonal points for the matchings
(14)(23), (13)(24), (12)(34); 678 the diagonal line.

| round | block | mass | rest of the request |
|---|---|---|---|
| 2 | none | 0 | 0.606 of B_1, 0.153 of the pool |
| 3 | none | 0 | 0.315 each of 1-only, 2-only; 0.130 of B_1∩B_2 |
| 4 | none | 0 | whole budget on the pair cells 23 (0.296), 13 (0.296), 12 (0.166); 123 is left unrequested |
| 5 (discarded) | — | — | cells 14 (0.311), 34 (0.206), singles, part of 24 |
| 6 | B(m_1) = (B_1∩B_4) ∪ (B_2∩B_3) | **0.759 = whole budget** (14: 0.311, 23: 0.296, 1234: 0.122, 123: 0.029) | 0 |
| 7 | B(m_2) = (B_1∩B_3) ∪ (B_2∩B_4) | **0.759 = whole budget** (246: 0.251, 136: 0.239, 1234: 0.122, 24: 0.060, 13: 0.058, 123: 0.029) | 0 |
| 8 | B(m_3) ∪ (B_6∩B_7) = D | 0.693 | 0.066 spare |

Final types: triples 246 0.251, 147 0.251, 237 0.239, 136 0.239, 167* 267* 0.049, 467* 367* 347* 346* 0.032,
123* 0.029, 127* 126* 0.026; 4-fold 3467* 0.134, 1234* 0.122, 1267* 0.108; pairs 14, 24 0.060, 13, 23 0.058,
small others; degree masses 1.287 / 0.364 / 0.336. So this is TWIN 16.4's labelling with loads
(L(m_1), L(m_2), L(m_3)+e) = (0.759, 0.759, 0.693) and n_4 = 0.122 > 0: the adversary's rule does put
common points of the first three replies into B_4 (type 1234), and she still fits, with two loads exactly
at the budget. Another run at the same (N, t) (`prop_c.log`, all discards free) ends in class (T): both
labellings are available at 2.0k.

### 11.3 All saved lines

| line | class |
|---|---|
| N = 1.9k proportional | (T) |
| N = 2.0k proportional (cert, budget 0.759, discard fixed) | (Q) |
| N = 2.0k proportional (prop_c, budget 0.76) and t = 0.80 | (T) |
| N = 2.15k proportional (discard reply 1) | (Q) |
| N = 2.0k, concentrated omission at reply 2 or 6; mixture 1,1,.5,1,.5,1 GIFT; all plan-transfer lines (alpha = 0, .25, .5, .8, .9) | (Q) (plan transfer inherits the certificate's plan) |
| N = 2.0k, concentrated omission at reply 4 or 7; alternating 0,1,0,1,0,1 | (T) |
| N = 2.0k, alternating 1,0,1,0,1,0 | (L) line-first |
| N = 2.1k, 2.2k proportional; N = 2.0k half-HIGH mixture; N = 2.0k 1,1,0,1,1,1 HIGH | **no Fano labelling** |

Non-Fano lines (e.g. N = 2.1k, mass(D) = 0.632): nine empty triples instead of seven
(123, 124, 234, 236, 146, 137, 247, 128, 348), only two realised 4-fold types among the six kept
(1267 0.124, 3467 0.100), four heavy triples 237, 246, 147, 136 as before, and a heavy triple inside D
(134 0.166). It is the (Q) picture with the 4-type 1234 absent (three of the four triples of the
quadrangle are empty) and its mass sitting in a triple that she pays for at the last round; the realised
types are an intersecting-complement family, but no Fano plane contains it. With more room she is not
forced onto a Fano labelling, which is consistent with TWIN 17.1 ("D <= t is more general").

### 11.4 What this gives the twin

- At N = 1.9k the pattern is exactly the unanalysed labelling (T) with one discard, not (L) with an
  adaptive finish and not a non-Fano family. The candidate for the window (3t - 1/2, 8/3 - t) is
  therefore: **triangle first with nothing sealed; S_4 = (B_a∩B_b) + all points lying only in the third
  triangle reply; one spare reply; then blocks B_1∩B_4, (B_1∩B_3)∪(B_2∩B_6), and D.** Loads in the
  realised line: 0.447, 0.467, 0.759, 0.726 at budget 0.759 — rounds 7 and 8 are the binding ones, so the
  inequality to prove for (T) is about those two blocks.
- This is one line against one fixed rule (proportional omissions); it shows (T) is feasible at 1.9k for
  that opponent, not that (T) is forced or sufficient against an adaptive one. The classification was
  done on float re-simulations of the saved lines; the lines' values are the exactly verified ones, the
  list of realised types is not separately certified in rationals.
