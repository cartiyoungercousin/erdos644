# R2-core results: the adaptive Fano-template game on n = 7k/4 + c points, T = 3k/4 + g

Written 2026-11-23. Code and outputs: `compute/r2core/` (`template_lp.py`, `candidate.py`,
`out/`). Milestones: `notes/R2CORE_PROGRESS.md`. Nothing committed, no Lean file touched.
Tags: **[E]** exact rational arithmetic, **[P]** hand argument, **[C]** floating point.

## 0. Verdict

| c/g | result | status |
|---|---|---|
| ≤ 3 | requester wins (static: Theorem A) | **[E]** LP feasible at 2 and 3 |
| 4 | adversary wins | **[E]** LP infeasible |
| 6 | adversary wins | **[E]** LP infeasible |
| 10 | adversary wins | **[E]** LP infeasible |
| threshold | exactly 3 (feasible at 3, infeasible at 3.01) | **[E]** |

Adaptivity, the rule "no shown good triple is tight" and the other proven constraints give the
requester **nothing** in this game beyond Theorem A, because the adversary can make all of his
6(c − g) forced omissions useless. There is one non-trivial phenomenon: against an adversary who
commits in advance to how he answers the *first* request, the requester wins up to c/g = 5
exactly **[E]**; the adaptive choice at that single response brings the threshold back to 3.
The adversary's answers do not define a counterexample candidate (Section 4).

Scope of the exact statement (Section 1): requests in the order 1A, 1B, 2A, 2B, 3A, 3B with the
template labelling; requester otherwise arbitrary; k large compared with c.

## 1. Model

s := c − g. Since n − T = k + s, the response to a request of size T − y is the offered set
minus exactly s + y points ("drops"), chosen by the adversary.
Lines: E = {b1,b2,b3}; 1A = {b1,a1,a2}, 1B = {b1,a3,a4}, 2A = {b2,a1,a3}, 2B = {b2,a2,a4},
3A = {b3,a1,a4}, 3B = {b3,a2,a3}. By the Fano criterion (NEW_PATHS §8.1) the requester wins iff
every point is absent (requested or dropped) from all lines of a star: an E-point from the three
response lines through some a_p; a non-E point from both lines of a group, or from an a-star.
(If some point is not covered, it forms a 2-cover with a bulk point of a suitable class, so the
criterion is exact here.)

Requester in the LP: for each point, any set R of lines that request it; any request sizes
T − y_L. This is fully general: points with the same history are interchangeable, and the first
move is just (amount of E, amount outside E, y) at 1A.

Adversary policy PI:
- 1A: after seeing the first request, either all drops on E-points (scenario E) or all outside
  E (scenario N);
- 1B: drops E-points that were requested at 1A (a second absence in the same group: useless);
- 2A, 2B, 3A, 3B: drops non-E points already absent from 1A and 1B (complete: useless).

Assumption used for the last item: at each of these four responses at least s + y complete
points are on offer. **[P]**: the number of complete points after 1B is at least k/4 − O(c) in
any play that can still win (the other two groups and all a-star points together can absorb at
most k/2 + O(c) non-E points), and requesting them wastes budget, so this holds for k large
compared with c.

LP (`template_lp.py`): two scenarios sharing the first move; variables = amounts of each point
type (minimal request sets only) and the y_L; rows = totals, six request sizes, drop amounts,
non-anticipativity. 51 variables, 46 rows, solved by an exact two-phase simplex over Fractions
(`compute/r1/exact_infeasible.py`). Infeasible means: no requester play beats PI.

## 2. The constraints, one by one **[P]**

- *No shown good triple is tight*: a concurrent triple that is good must leave fewer than
  n − 2T = k/4 + c − 2g points outside its union. PI respects it: the points absent from E, jA,
  jB are the class b_j (at most k/4 + g, and c > 3g), since PI never drops the same non-E point
  in both lines of a group; its useless drops are spread over distinct complete points, so no
  point becomes absent from a second full star. The requester cannot force tightness either:
  that needs k/4 + c − 2g points absent from both lines of a group, and a request has room for
  k/4 + g.
- *Lemma B*: unions of good triples have more than 2T points and every edge misses at most
  n − 2T of them: far from binding.
- *Cor 6.2 / three_centres*: two template edges share two bulk classes and a concurrent union
  misses only one class, so no two shown edges are disjoint inside such a union: vacuous.
- *Min-S rigidity 11.1(c)*: it bounds the part of a response outside A∪B for sparse pairs; here
  the whole ground set has only s − ν points outside such a union: vacuous.
- *Pair gap*: needs a lex-min anchor; not applicable to the template game.
- *Tight-triple lemma as a three-response closure*: three requests covering V have a common
  part of at most k/4 + (3g − c)/2 < k/4 + c − 2g when c > 7g/3, and the adversary never drops
  a point that is already in two of the three requests.

## 3. Why the threshold is 3, and where 5 comes from **[P]**, numbers **[E]**

Requests supply 6T = 9k/2 + 6g incidences; needs are 3 per E-point and 2 per non-E point,
9k/2 + 2c in all; the deficit 2c − 6g has to come from useful drops.
- From the second response on every drop of PI is useless.
- First response, drops outside E: each dropped point can be completed at 1B with one request,
  but only if 1B has room, i.e. only if the first request was E-heavy.
- First response, drops on E: each saves one E-request at 1B, but the freed room at 1B helps
  only points already absent from 1A, i.e. only if the first request was not E-heavy.
- The requester must fix the E-share of the first request before seeing which it is. Against a
  scenario known in advance he gains enough for c ≤ 5g (LP: feasible at 5, infeasible at 5.01,
  for either scenario); against the adaptive choice he gains nothing (infeasible at 3.01).

So the defect accounting goes the adversary's way: under PI the non-E points that can be
covered number at most 3(k/4 + g), hence c ≤ 3g.

The adversary's line of play, explicitly: answer 1A with "everything offered except c − g
points of E" if the first request contains at most k/2 points of E, and "everything offered
except c − g points outside E" otherwise; answer 1B with everything offered except c − g points
of E that were in the first request; answer 2A, 2B, 3A, 3B with everything offered except
c − g points (distinct each time) that are outside E and were in neither group-1 response.

## 4. Candidate family from the adversary's answers (`candidate.py`, typefam) **[C]**

- Closure of PI ("offered set minus s points of E, or minus s points outside E"): on the blocks
  (E, V∖E) this is essentially the complete family. k = 8, g = 1, c = 4 (n = 18, T = 7):
  tau = 11, and a bad 7-tuple exists (ILP, re-verified by brute force). Not a (7,2)-family.
- The 7-type block family of one concrete line of play (k = 16, n = 32, eight blocks) is (7,2),
  but has tau = 2.
- So nothing between "too small to have tau > T" and "too big to be (7,2)" comes out of the
  game: which subfamily of K_n, if any, has both properties is exactly the core conjecture.
  A genuine (7,2)-family with tau > 3k/4 + 1 was **not** found.

## 5. Soundness
Complete families K_N with N < 7k/4 correspond to c < 0 with g < c; the LP is infeasible there
(tested (c,g) = (−0.01,−0.02) and (−0.02,−0.05)): the requester stays stuck, as he must **[E]**.

## 6. Limitations
- The exact certificate covers the order 1A,1B,2A,2B,3A,3B and the template labelling of the
  six requests. Other orders (for instance the three "first" lines before the three "second"
  ones) were examined by hand only: the useless drops are then points with one pending absence;
  I expect the same threshold but did not run it.
- The availability assumption of Section 1 is a hand argument, for k large compared with c.
- "Exact" refers to the LP. The reduction of the game to the LP (policy PI, interchangeability
  of points with the same history, Fano criterion) is a hand argument.
- Closures other than the Fano template (three_centres, a tight triple from three responses)
  were only checked by hand to be unavailable.
- The (1/2)-threshold in the explicit line of play of Section 3 is my reading of the LP's two
  scenarios; the LP itself only certifies that for every first request one of the two answers
  wins.

## 7. What this means for the core conjecture
The decisive test of NEW_PATHS §12.5 comes out negative for the requester at every ratio: in the
near-complete instance the template game cannot tell a (7,2)-family from "K_n answering
adaptively", and the rule "no tight triple" does not separate them. A proof has to use a
property of genuine families that survives when each single request is answered like a complete
family, that is, a statement about many responses to overlapping requests (a density or
Turán-type input), not a better line of six requests.

## 8. Part 2 (all closure shapes / all request orders): PAUSED, state at the pause

Paused on a priority change from the coordinator. Code: `compute/r2core/orders_lp.py`,
`orders_milp.py`, `orders_tree.py`, `orders_modes.py`, `two_stage.py`; outputs in `out/`.

- **Shapes [P, resting on the floating MILP of ROADMAP 2.2].** For n < 11k/6 every bad 7-tuple
  carries a full Fano plane of miss-patterns, and a set of Fano lines meeting every line contains
  a line. So every closure shape is the Fano shape; 2 or 3 kept edges are sub-cases of one anchor
  plus six requests. What is left to vary is the ORDER of the six requests (first = 1A by symmetry;
  second = 1B, or 2A up to symmetry).
- **Orders whose second request is the partner of the first (24 of 120): threshold exactly 3
  [E]** (`out/orders_3.01.txt`: exact LP infeasible at c/g = 3.01 for all 24).
- **The other 96 orders: NOT SETTLED.** No adversary certificate. Against the restricted
  adversaries I could encode, the requester survives up to c/g = 11/3 (1B third) or 5 (1B later)
  **[C]** (`out/orders_milp.txt`, `out/orders_tree_D2.txt`: adaptive modes at the first two
  responses, a weak rule afterwards). These are upper bounds for the requester, NOT requester
  wins. In the other direction, a requester strategy that is static after the second response
  reaches exactly 3 and no more **[C]** (`two_stage.py`). So the true threshold of these orders
  lies in [3, 11/3] resp. [3, 5]. The depth-3 tree was still running when I stopped (no result).
  Hand analysis: with 2A second there are no complete points to drop at the 2nd to 4th
  responses, which is why the part-1 policy PI does not transfer; on the other hand the freed
  slots are rigidly placed (2B and 3B freed, 3A consumed), which is why I expect 3. Unproven.
- **Correction to part 1:** "adversary wins above 3" is certified only for the orders with
  partner second; Section 6 already flagged the other orders as unchecked.
- Coexistence check: not written up (hand notes only: the first answer of PI is memoryless, its
  later answers are history dependent; the closure of PI is K_n-like and not (7,2), Section 4).
