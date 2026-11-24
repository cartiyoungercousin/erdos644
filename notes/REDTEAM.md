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
