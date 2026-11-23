# R1 results: the looseness-constrained request game (one adaptive round), and the sparsest anchor

Written 2026-11-23. Code: `compute/r1/` (raw outputs in `compute/r1/out/`). Status tags:
**[E]** re-verified in exact integer/rational arithmetic (stuck certificates: relative to the
pattern tables of Section 1.2; contradiction wins: unconditionally), **[C]** floating-point
computation (evidence, not proof), **[P]** short hand proof, **[H]** heuristic reading of the data.
Normalization k = 1, budget t = T/k. Everything is a statement about the continuous relaxation
(cell sizes are reals); for the requester this is the favourable direction (integer rounding only
costs O(1/k)), so "stuck" below means stuck up to O(1/k) and "wins" means wins up to O(1/k).

## 0. Bottom line

**(A) The question as posed: does the looseness constraint beat 6/7 with one adaptive round?
No.**

1. *The tight-triple looseness inequality does nothing in this game.* At t = 0.85 the set of
   profiles the requester cannot win is the same with and without it (27 of 278 grid profiles
   with all pair cells ≤ 1/2; the certificates of the run with the inequality are **[E]**). Two reasons. (i) Honesty: a response K makes (E,F,K) a
   good triple only if it avoids E∩F completely, and the adversary destroys that with one point
   unless E∩F is entirely inside the request; so the inequality is available only for "sealed"
   cells. (ii) The winning responses are sparse (a third to a half of K is new points) and sit
   far below the bound S' ≤ 3 − 2t (median slack 0.45).
2. *Re-anchoring by maximality of S (the R1 proposal) does not help either.* In its sound form
   (anchor = max-S good triple among those with all pair cells ≤ 1/2) 24 of the 27 profiles stay
   stuck; in the optimistic global form 17 do, and the 6/7 corner neighbourhood (0.425)³ is
   stuck in both the `loose` and the `maxS` game **[E]**. The obstruction is on the sparse
   side, where an upper bound on S is the wrong kind of constraint.
3. *The game itself is weaker than the 6/7 manuscript*: with no extremal rule it is still stuck
   at t = 6/7 (profiles with two pair cells near 1/2) and first wins everywhere at 0.875.
   At t = 0.82 and 0.80 the complete family's answer beats every request at the diagonal
   profiles (a,a,a), 0.42 ≤ a ≤ 0.45 (a certificate over the continuum of requests,
   Section 2.3), while for t ≥ 5/6 it never does: the 5/6 barrier, reproduced inside the game.

**(B) Unplanned positive result: the opposite extremal principle works.** Choose the anchor as
the *sparsest* good triple: among good triples with all pair cells ≤ k/2, one minimizing
c·s1 + s2 (s1 ≥ s2 its two largest pair cells; c = 3 or 4). Then every response that creates a
good triple of that class must be at least as dense, and the same one-round game is **won at
every profile tested at t = 6/7 and t = 0.85** **[C]**:
- c = 3: t = 6/7 (281 profiles, grid 1/21) and t = 0.85 (278 profiles on the 1/20 grid, 1739 on
  the 1/40 grid, which includes the corner neighbourhood);
- c = 4: the same at 6/7 and 0.85 (coarse grids), and at t = 0.84 all 450 profiles of the 1/25
  grid; but on the 1/50 grid (3234 profiles, which unlike the 1/25 grid contains x = 1/2) six profiles are stuck: (0.38,0.38,0.22), (0.40,0.38,0.24), (0.5,0.18,0.18), (0.5,0.2,0.16), (0.5,0.2,0.18), (0.5,0.2,0.2). So 0.84 is **not** supported.
About 40–50% of the non-static wins are *pure contradictions*: for the chosen request no
response at all is compatible with the minimality of the anchor; these are re-proved in exact
rational arithmetic without any solver **[E]**. The simplest instance is a two-line lemma
(Lemma A, Section 4.4, **[P]**): the minimizer of s1 + s2 satisfies x + 2y ≤ 2k − T + O(1),
which already removes the 6/7 corner and every "two large cells" profile.
This is evidence that **a bound of 0.85·k, below 6/7 ≈ 0.857, is provable with one adaptive
response from a sparsest anchor**. It is not a proof (Section 5): the profiles are a grid, the
closure wins are floating-point, and one needs the existence of a good triple with all pair
cells ≤ k/2 (the manuscript's small-M regime has to be treated separately). Whether the same
works at 0.84 (which would also be below the 11/13 ≈ 0.846 of the third-party repository) is
open: the coarse grid says yes, the fine grid finds six stuck profiles for c = 4, and only the
potentials c·s1 + s2 with c ≤ 5 were tried there. At t = 5/6 these potentials leave 2–10 of 447 profiles
stuck, at t = 0.825 (c = 3) 26 of 281. Nothing known caps the approach at 5/6.

**(C) R3.** The stuck adversary of part (A) at (0.45,0.45,0.1), t = 0.85 is not realizable as a
block-type family on its own Venn cells: the family built from its 136 integral response types
(k = 40) has tau = 35 > T = 34 but contains bad 7-tuples made of response edges only, and loses
tau > T after five rounds of removing the offending types. The test is weak (a block-type
family contains every placement of each response profile), see Section 3.

**(D) Single most promising next step.** Make (B) a theorem and push it down in t: (1) prove
the contradiction lemmas (Lemma A and its c·s1 + s2 analogues) in Lean, they are linear
arithmetic over cell counts; (2) replace the grid by a certified cover of the profile region
that survives them, {x ≤ 1/2, static value > t, no contradiction}; (3) treat families with no
good triple with all pair cells ≤ k/2; (4) search the anchor potential systematically at
t ≤ 5/6 (the engine solves a full grid in under three minutes). Details in Section 6.


---------------------------------------------------------------------------------------------

## 1. Exact definitions (what was computed)

### 1.1 The game
The requester holds a good triple E,F,G (E∩F∩G = ∅) with pair cells X = E∩F, Y = E∩G, Z = F∩G
of sizes x ≥ y ≥ z and private parts PE, PF, PG of sizes 1−x−y, 1−x−z, 1−y−z ("profile").

1. *Static win.* If φ(x,y,z) ≤ t (four static requests close the triple) the requester wins.
2. *First request.* Otherwise he chooses D: d_c points of each of the six cells, Σ d_c = t.
3. *Response.* The adversary chooses K: k_c ≤ (size of c) − d_c points of each cell and k_N new
   points, total 1, subject to the *rules* of Section 1.4.
4. *Closure.* The requester wins against K if one of the following static closures has all
   request loads ≤ t:
   - **Q**: keep E,F,G,K and make 3 static requests. The points are cut into 13 regions
     (c+ = c∩K, c− = c∖K for the six cells, N = new points of K). Every point gets a label
     ⊆ [3] (the requests containing it). Two points form a *candidate pair* if their membership
     sets cover {E,F,G,K}; candidate pairs must have intersecting labels (some response then
     misses both). New points of the three final responses are harmless: they lie in none of
     E,F,G,K and no point lies in all four.
   - **T_c** (c ∈ {X,Y,Z}), *re-anchoring*: drop the edge opposite to c, keep K and the two edges
     through c, and close that triple by 4 static requests (labels ⊆ [4]). Only available when
     that triple is good, i.e. when c is *sealed* (c ⊆ D), see 1.3.
   (Dropping K and closing E,F,G is item 1.)

"Stuck profile" = for every first request D (of the grid, see 1.5) some admissible response
defeats Q and all available T_c.

### 1.2 Closure values: exact pattern tables (`tables.py`)
For a closure with r requests, group the points into classes with the same candidate partners.
A *pattern* assigns to each class c an up-closed family F_c of non-empty subsets of [r] (the
labels it may use); candidate classes must have cross-intersecting families (for up-closed
families: no label of one has its complement in the other). For a fixed pattern the best split
of the classes among their labels is an LP, and LP duality gives the closed form

    cost(pattern; masses) = max over λ in the simplex of  Σ_c mass_c · min_{L ∈ F_c} λ(L).

The function of λ is concave and piecewise linear on the cells of the arrangement
{λ(A) = λ(B) : A, B disjoint}, so the maximum is attained at one of finitely many rational
points Λ_r (|Λ_3| = 10, |Λ_4| = 101; denominators divide 12, resp. 840). Hence

    closure value = min over patterns  max over λ ∈ Λ_r   W[pattern, λ] · masses,

a finite min–max of linear forms with rational coefficients. A private class only has pair-cell
classes as candidate partners, so its optimal family is the *blocker* of the union of their
families; the free choices are the families of X,Y,Z (triple: 15 889 patterns up to label
permutation) or of X±,Y±,Z± (four edges: 33 103 patterns up to label permutation, after removing
options of the classes c− that are dominated pointwise on Λ_3). `check_tables.py` compares the
tables with an independent MILP formulation (labels on the 13 regions, candidate pairs from the
membership-union criterion, 0/1 support variables) on random instances including boundary
profiles: agreement to 4·10⁻⁵, the MILP's own gap **[C]**. On the diagonal the triple table
reproduces φ(a,a,a) = (3+3a)/5 for a ≤ 3/7 and (3−3a)/2 above. On faces y = 0 or z = 0 the table
value is *smaller* than `roadmap/static_phi.py` (e.g. φ(0.5,0.3,0) = 0.8333 vs 0.875), as the
caveat in ROADMAP §2.4 predicted: a private part whose opposite pair cell is empty needs no label.

### 1.3 Honest treatment of empty regions ("sealing")
A region is *structurally empty* only if its cell is empty, or it is c+ with c ⊆ D. Every other
region is treated as present even when K gives it mass 0, because the adversary can put one point
there for free (and the requester can put O(1) points into all requests for free). Consequences:

- (E,F,K) is a good triple only if K∩X = ∅, and the adversary can always destroy this with one
  point of X unless **X ⊆ D** ("X is sealed"). So both the looseness inequality for (E,F,K) and
  the re-anchoring closure T_X are available **only when X is sealed**; same for Y, Z.
- There is no cheap robust version: with a one-point core q, a point outside E∪F∪G that lies in
  all four responses forms a 2-cover with q, so neither the tight-triple lemma nor a static
  triple closure survives a non-empty core. (This is why every existing proof seals E∩F.)

The task statement's "looseness inequalities for every good triple among E,F,G,K" is therefore
implemented as: for every sealed pair cell. A model that applies them unconditionally would be
unsound.

### 1.4 Rules for the adversary (variants)
For a sealed cell c = A1∩A2 the new good triple (A1,A2,K) has S' = |c| + |K∩A1| + |K∩A2|.

| variant | rule | justification |
|---|---|---|
| `none`  | no constraint | baseline: one adaptive round against an unconstrained adversary |
| `loose` | S' ≤ 3 − 2t | tight-triple lemma (`Lean644/TightTriple.lean`) |
| `maxS`  | S' ≤ min(S, 3 − 2t), S = x+y+z | the anchor is a good triple of maximum S in the family ("re-anchoring by maximality": a response creating a larger-S good triple contradicts the choice) |
| `pot:a,b,c` | `loose` and Φ' ≤ Φ, Φ = a·s1 + b·s2 + c·s3 of the sorted pair cells | the anchor maximizes Φ over **all** good triples (`maxS` = 1,1,1) |
| `poth:a,b,c` | the same, but only when all three pair cells of the new triple are ≤ 1/2 | the anchor maximizes Φ over the good triples **with all pair cells ≤ 1/2** |

The rule inequalities are closed (the adversary may sit on the boundary). `game.py` also contains
a pair rule (`M`, `MS`: |K∩A| ≤ x or ≥ 1/2 when x is FKW's largest pair intersection ≤ k/2); it
was implemented but its runs were not completed and nothing below uses it.

Profiles: x ≥ y ≥ z ≥ 0, x + y ≤ 1, x + y + z ≤ 3 − 2t, on a grid; the main runs are restricted
to x ≤ 1/2 (all pair cells at most half an edge). This matters for the extremal rules: `maxS`
and `pot` are sound only if anchors with a pair cell > 1/2 are handled as well, and those are
almost all stuck (Section 2.1); `poth` is the sound version for the grid x ≤ 1/2.

### 1.5 Algorithm and what it certifies (`game.py`, `outer.py`, `run_grid.py`)
*Inner problem (fixed D).* Constraint generation with **exact pattern cuts**: a pattern beats K
iff all its |Λ_r| linear forms are ≤ t at K, so "K defeats every pattern of a finite pool" is a
MILP (one binary per pattern and λ). Loop: solve it (maximizing the margin); evaluate all
patterns at the K found; if the true value is > t the adversary wins this D, otherwise add the
best patterns and repeat. It terminates because there are finitely many patterns.
*Outer problem (choice of D).* All requests of a grid (d_c multiples of 1/dden, Σ = t, with
"c sealed" = the grid event d_c = |c|) are kept in a boolean table. Pick a live request, play the
inner game; if the requester wins, done; otherwise shrink the winning response (move mass to new
points while it still wins, so that it fits outside more requests), record for which seal
patterns it wins, and delete every request it answers. If the table empties, the profile is stuck.

What is certified:
- **Requester win at a profile** = an explicit D and a finite pool of patterns such that the
  adversary MILP has optimum ≤ 10⁻⁶ **[C]**. Additionally `check_wins.py` samples 20 000
  admissible responses per win and checks them against the pool without any MILP (no failure).
  It is a win against *all* real responses to that D, not only grid ones.
- **Stuck profile** = a finite list of responses such that every *grid* request is answered by
  one of them. `exact_check.py` re-verifies this with integers only: all grid requests are
  enumerated, capacities and rules are checked in rationals, and for every (response, seal
  pattern) used, all patterns of all available closures are evaluated in int64 **[E]**. This
  proves "no grid request wins" given the completeness of the pattern tables (Section 1.2; the
  argument is short but not machine-checked). It does **not** exclude a winning off-grid request,
  although the requester's best requests found are robustly on the grid (they seal cells).
- For speed the search uses sampled sub-tables (about 8% of the patterns); adversary wins are
  confirmed with the complete tables, and stuck certificates that fail the exact check are
  re-solved with complete tables only (`repair.py`).
- For dense profiles `complement.py` gives a certificate over the **continuum** of requests for
  the specific response rule "answer like the complete family" (Section 2.3).

---------------------------------------------------------------------------------------------

## 2. Results

### 2.1 Overview table
Profile grid: x ≥ y ≥ z multiples of 1/pden, x ≤ 1/2 unless stated; request grid step 1/dden.
"adaptive" = won by a first request plus Q / T_c closures; "stuck" = no grid request wins.

| t | variant | profiles (grid) | # | static | adaptive | stuck | new points in the recorded winning responses (median) | responses meeting an old edge in > 1/2 |
|---|---|---|---|---|---|---|---|---|
| 0.9 | `loose` | 1/20, x ≤ 1/2; requests 1/40 | 269 | 269 | 0 | 0 | – | – |
| 0.9 | `maxS` (global, optimistic) | 1/20, x ≤ 1/2; requests 1/40 | 269 | 269 | 0 | 0 | – | – |
| 0.875 | `loose` | 1/20, x ≤ 1/2; requests 1/40 | 274 | 268 | 6 | 0 | – | – |
| 0.875 | `maxS` (global, optimistic) | 1/20, x ≤ 1/2; requests 1/40 | 274 | 268 | 6 | 0 | – | – |
| 6/7 | `loose` | 1/21, x ≤ 1/2; requests 1/42 | 281 | 236 | 36 | 8 (+1 unresolved) | 0.33 | 1011/2105 |
| 6/7 | `maxS` (global, optimistic) | 1/21, x ≤ 1/2; requests 1/42 | 281 | 236 | 40 | 5 | 0.28 | 981/2129 |
| 0.85 | `none` | 1/20, x ≤ 1/2; requests 1/40 | 278 | 201 | 50 | 27 | 0.33 | 3127/6934 |
| 0.85 | `loose` | 1/20, x ≤ 1/2; requests 1/40 | 278 | 201 | 50 | 27 | 0.31 | 3115/7186 |
| 0.85 | `maxS` (global, optimistic) | 1/20, x ≤ 1/2; requests 1/40 | 278 | 201 | 60 | 17 | 0.32 | 1852/3992 |
| 0.85 | `loose` | the single profile (0.425)³; requests 1/40 | 1 | 0 | 0 | 1 | 0.17 | 3806/4954 |
| 0.85 | `maxS` (global, optimistic) | the single profile (0.425)³; requests 1/40 | 1 | 0 | 0 | 1 | 0.17 | 3767/4912 |
| 0.85 | `loose` | 1/20, 0.55 ≤ x ≤ 1; requests 1/40 | 213 | 13 | 49 | 151 | 0.37 | 3173/8798 |
| 0.85 | `maxS` (global, optimistic) | 1/20, 0.55 ≤ x ≤ 1; requests 1/40 | 213 | 13 | 95 | 105 | 0.39 | 1940/5455 |
| 0.80 | `loose` | 1/20, x ≤ 1/2; requests 1/40 | 283 | 107 | 56 | 120 | 0.46 | 1261/12324 |
| 0.80 | `maxS` (global, optimistic) | 1/20, x ≤ 1/2; requests 1/40 | 283 | 107 | 82 | 94 | 0.47 | 1098/9637 |

Readings:
- **The tight-triple looseness inequality is inert in this game.** At t = 0.85 the stuck sets of
  `none` and `loose` coincide (27 profiles). The recorded winning responses are sparse: over all
  (response, avoided cell) pairs of the `loose` run at t = 0.85 the slack 3 − 2t − S' has median
  0.445 and 5%-quantile 0.24 (`looseness_slack.py`); the bound S' ≤ 1.3 is reached by a handful of
  about 5700 pairs.
  The adversary wins with responses that use many *new* points (median 0.32 of an edge), not with
  tight ones.
- **The game is weaker than the 6/7 manuscript.** It is still stuck at t = 6/7 (9 profiles for
  `loose`: the 8 of the table and (10,10,4)/21, whose grid run ended with a solver error and
  which a separate run found stuck with 828 responses; 5 for `maxS`; all have two pair cells
  ≥ 8/21 and one equal to 10/21), has no stuck
  profile at t = 0.875 and is purely static at t = 0.9. So on anchors with all cells ≤ 1/2 the
  value of "one adaptive response, then static closure or static re-anchoring" lies in
  (6/7, 0.875]. The manuscript closes exactly these profiles (largest cell M > t/2 next to a
  medium cell) with several adaptive requests and pair-gap information; one response is not
  enough, in agreement with its Section 8 ("one-response constructions ... required a budget
  above 0.855").
- **Anchors with a pair cell > 1/2 are hopeless for this game**: at t = 0.85, 151 of 213 such
  grid profiles are stuck (105 under `maxS`), and essentially all with x ≥ 0.7. Any extremal
  anchor rule has to keep the anchor's cells ≤ 1/2, and then (Section 4) the adversary can escape
  the rule by meeting an old edge in slightly more than k/2 points.

### 2.2 Stuck profiles
**t = 0.85, `none` and `loose`** (27, identical): (0.45,0.4,0.25) (0.45,0.45,0) (0.45,0.45,0.05) (0.45,0.45,0.1) (0.45,0.45,0.15) (0.45,0.45,0.2) (0.45,0.45,0.25) (0.5,0.2,0.2) (0.5,0.25,0.25) (0.5,0.4,0) (0.5,0.4,0.05) (0.5,0.4,0.1) (0.5,0.4,0.15) (0.5,0.4,0.2) (0.5,0.4,0.25) (0.5,0.45,0) (0.5,0.45,0.05) (0.5,0.45,0.1) (0.5,0.45,0.15) (0.5,0.45,0.2) (0.5,0.45,0.25) (0.5,0.5,0) (0.5,0.5,0.05) (0.5,0.5,0.1) (0.5,0.5,0.15) (0.5,0.5,0.2) (0.5,0.5,0.25)

**t = 0.85, `maxS`** (17): (0.45,0.45,0.05) (0.45,0.45,0.1) (0.45,0.45,0.15) (0.45,0.45,0.2) (0.5,0.4,0.1) (0.5,0.45,0) (0.5,0.45,0.05) (0.5,0.45,0.1) (0.5,0.45,0.15) (0.5,0.45,0.2) (0.5,0.45,0.25) (0.5,0.5,0) (0.5,0.5,0.05) (0.5,0.5,0.1) (0.5,0.5,0.15) (0.5,0.5,0.2) (0.5,0.5,0.25)

**t = 6/7, `loose`** (grid 1/21): (0.476,0.381,0.048) (0.476,0.381,0.095) (0.476,0.381,0.143) (0.476,0.476,0) (0.476,0.476,0.048) (0.476,0.476,0.095) (0.476,0.476,0.143) (0.476,0.476,0.238)

**t = 6/7, `maxS`**: (0.476,0.476,0.048) (0.476,0.476,0.095) (0.476,0.476,0.143) (0.476,0.476,0.19) (0.476,0.476,0.238)

**t = 0.80**: 120 stuck profiles for `loose`, 94 for `maxS` (lists in `out/grid_loose_0.80_20_0.5.jsonl`, `out/grid_maxS_0.80_20_0.5.jsonl`; `py summarize.py` prints them).

**t = 0.85, profiles with 0.55 ≤ x ≤ 1**: 151 of 213 stuck for `loose`, 105 for `maxS` (`out/grid_*_0.85x0.55_20_1.0.jsonl`).

Shape of the stuck region at t = 0.85 (x ≤ 1/2): two pair cells ≥ 0.45 (or 0.5 and 0.4) and a
third cell ≤ 0.25, plus (0.5,0.2,0.2), (0.5,0.25,0.25); i.e. a largest cell above
t/2 = 0.425 next to a medium or large second cell. These are the manuscript's configurations of
the "second kind". As t decreases the region grows towards the diagonal and at t = 0.80 it
contains most profiles with x ≥ 0.35 and S ≥ 1.

### 2.3 The 6/7 corner and the complete-family response
The corner (3/7,3/7,3/7) is not on the 1/20 grid; the nearest non-static profile on the 1/40
grid is (0.425,0.425,0.425) (φ = 0.855, S = 1.275 ≤ 3 − 2t = 1.3).

- **(0.425,0.425,0.425) is stuck at t = 0.85** for `loose` (4954 recorded responses answer all
  79 233 grid requests, **[E]**) and for `maxS` (4912 responses, **[E]**). So neither
  looseness nor max-S anchoring moves the corner in one round.
- `complement.py` tests the response rule of the complete family, K(D) = (E∪F∪G)∖D plus the
  missing 1 − (U − t) new points, against **all** requests (a continuum; LP infeasibility for every
  closure pattern on every face "exactly these pair cells sealed") **[C]**. At the exact corner
  (3/7,3/7,3/7) with t = 0.85 or 0.855:
  - no cell sealed, or two cells sealed: the complete-family response beats every request;
  - exactly one cell sealed: the requester **beats** it by re-anchoring, with margin 0.02–0.026:
    e.g. D = X ∪ (0.24 of Y) ∪ (0.18 of Z); the complete response gives the good triple (E,F,K)
    with cells (0.429, 0.33, 0.39), whose static value is 0.83. The looseness bound is satisfied
    on these faces with slack 0.007 (it is nearly tight there, as it should be: this is the
    tight-triple lemma at work).
  - the adversary therefore answers one-sealed requests differently: it leaves part of E∖D or
    F∖D unused and takes more new points (0.24 instead of 0.125 in the example
    D = X ∪ 0.25 Y ∪ 0.175 Z at (0.425)³: K∩E = 0.21 instead of 0.325; T_X = Q = 0.871).
  So at the corner the one-round adversary is a **mixture**: complete-family answers to unsealed
  requests, sparse answers to requests that seal one cell. A complete family cannot give the
  sparse answers (it has only 1 + t − U = 0.125 new points), and a sparse family cannot give the
  complete ones; whether one family can do both is exactly what one adaptive round cannot see.
- Diagonal scan (`diag_complement.py`, `out/diag_complement.txt`): for which (a,a,a) does the
  complete-family rule beat every request?

  | t | a with φ(a,a,a) > t, 2 − t ≤ 3a ≤ 3 − 2t | complete-family rule |
  |---|---|---|
  | 0.85 | 0.42, 0.43 | not admissible after one seal (looseness; 0.42) / beaten by T_c after one seal (0.43) |
  | 0.84 | 0.41 – 0.43 | not admissible (0.41) / beaten by T_c (0.42, 0.43) |
  | 5/6  | 0.39 – 0.44 | not admissible (0.39–0.41) / beaten by T_c (0.42–0.44) |
  | 0.82 | 0.40 – 0.45 | not admissible (0.40), beaten (0.41), **beats every request for 0.42 – 0.45** |
  | 0.80 | 0.40 – 0.46 | beaten (0.40), **beats every request for 0.41 – 0.46** |

  This reproduces the 5/6 barrier of ROADMAP §2.3 inside the game: below 5/6 the complete family
  (which is not loose, but whose answers satisfy every looseness inequality the one-round game
  can state) defeats "request containing E∩F, then close"; above 5/6 it does not, and the
  adversary must leave the complete family.

### 2.4 The strategies that win
At t = 0.85 (`loose`), the 50 adaptive wins use three request types:

| sealed cells | closures in the certificate | profiles | where |
|---|---|---|---|
| X, Y, Z (possible iff S ≤ t) | Q only | 26 | x ∈ {0.45, 0.5}, y + z ≤ 0.4: one large cell, S ≤ 0.85 |
| Y, Z | Q and T_Y | 21 | x ≥ 0.4, medium y, S > t or XYZ-sealing fails |
| Z | Q and T_Z | 3 | (0.45,0.45,0.3), (0.5,0.4,0.3), (0.5,0.45,0.3) |

The rest of D is spread over the remaining cells; the certificates contain 3–18 patterns.
Typical example: (0.45,0.35,0.2), φ = 0.8625: D = Y ∪ Z ∪ (0.1 of X) ∪ (0.15 of PE) ∪ (0.05 of PG);
every response avoids Y and Z, and either three static requests on E,F,G,K or the static closure
of the good triple (E,G,K) wins (18 patterns in the certificate).
If such wins were all that is needed they would turn into integer lemmas routinely: each
certificate is a finite list of patterns (label families) with rational weights, i.e. a finite
system of linear inequalities in the cell counts, of the same form as the manuscript's Hall /
symmetric allocations (or as LP certificates in the style of the 11/13 repository), and the
exhaustive integer audit of `compute/audit_cases.py` applies. Since the game does not win
everywhere, this was not pursued.

### 2.5 What the adversary does at stuck profiles
Representative answers at (0.5,0.5,0.1), t = 0.85 (`maxS`; K listed as amounts in
X,Y,Z,PE,PF,PG and new points):

| K avoids (so it answers requests sealing) | response K | \|K∩E\|, \|K∩F\|, \|K∩G\| | comment |
|---|---|---|---|
| X | (0, .102, .075, 0, 0, .325; .498 new) | .10, .08, .50 | half of K is new; K meets G in just over 1/2 |
| X | (0, .406, .041, 0, 0, .1; .453) | .41, .04, .55 | takes most of Y |
| Y | (.469, 0, .047, 0, .034, 0; .45) | .47, .55, .05 | takes most of X, meets F in > 1/2 |
| X, Z | (0, .328, 0, 0, 0, .075; .597) | .33, 0, .40 | sparse |
| Y, Z | (.406, 0, 0, 0, 0, 0; .594) | .41, .41, 0 | 0.4 of X plus new points |

Two features recur in all stuck runs: (i) 0.3–0.6 of the response is new; (ii) in over 40% of the
recorded responses at t = 0.85 (last column of the table in 2.1) one of |K∩E|, |K∩F|, |K∩G|
exceeds 1/2, often by a hair (0.502–0.56). Feature (ii) is the escape route discussed in
Section 4: against "max" rules restricted to anchors with cells ≤ 1/2 it is free.

---------------------------------------------------------------------------------------------

## 3. R3 realizability test (`r3_family.py`)

Configuration: (0.45,0.45,0.1) at t = 0.85, `loose`, scaled to k = 40, T = 34: cells
X,Y,Z,PE,PF,PG = 18,18,4,4,18,18.

1. The outer loop was rerun with responses restricted to integer vectors. Result: **136 integral
   response types answer all 99 000 integral requests** (`out/r3_loose_0.85_9_9_2_20_k40.json`,
   exact check **[E]**). This is an honest finite statement at k = 40: for every 34-subset D of
   E∪F∪G there is a response type that defeats Q and the available T_c (the closures are the
   continuous relaxation, which only helps the requester).
2. Block-type family: blocks X,Y,Z,PE,PF,PG and a block O of new points; types = E, F, G and all
   k-sets with one of the 136 response profiles. With |O| = T + 23 = 57 (n = 137): tau = 35 > T.
   (Smallest O with tau > T: 38.)
3. `typefam.find_bad_tuple`: **a bad 7-tuple exists** for O = 57 and for O = 38 (both witnesses
   re-verified by brute force). The witnesses consist of seven response-type edges and **no
   anchor edge**; one response type occurs three times in different positions.
4. Refinement loop (delete the type used most often in the witness, recompute tau, search again;
   `out/r3_prune_9_9_2.txt`): five rounds, each witness again made of response types only; after
   the fifth deletion tau = 34 = T. So no sub-collection of the recorded response types found by
   this loop is both (7,2) and has tau > T.

Interpretation, honestly:
- The stuck adversary is **not** a counterexample candidate in this form.
- The test is much weaker than it looks. A block-type family contains *every* placement of each
  response profile, far more edges than an adversary has to commit to; the bad tuples use three
  differently placed copies of one profile. Whether a real family could place its responses
  consistently is not decided by cell counts over the Venn cells of E,F,G.
- What the witnesses do tell the requester: the missing strategy is not another closure of
  E,F,G,K. It is "collect several responses to different first requests and drop the anchor".
  This cannot be "added to the menu" of the present game, because whether two responses overlap
  as in the witness is the adversary's choice; it requires a game state that carries the Venn
  diagram of at least two responses, i.e. a second adaptive round (Section 6).

---------------------------------------------------------------------------------------------

## 4. Re-anchoring over several rounds, and extremal anchors

### 4.1 Maximality of S (the R1 proposal)
- `maxS` (anchor has maximum S among **all** good triples; responses to sealed requests have
  S' ≤ S): at t = 0.85 the stuck set drops from 27 to 17 profiles, at t = 0.80 from 120 to 94,
  at 6/7 from 9 to 5. The core survives: (0.45,0.45,0.05–0.2), (0.5,0.45,·), (0.5,0.5,·) and the
  corner neighbourhood. There the adversary's answers already have S' < S (in the `maxS` run at
  t = 0.85 the gap S − S' has median 0.27), so maximality of S costs it nothing: **the
  obstruction is on the sparse side, where an upper bound on S is the wrong kind of constraint.**
- This variant is optimistic: the max-S triple of a family may have a pair cell > 1/2, and such
  anchors are almost all stuck (Section 2.1). The honest version restricts the anchor to good
  triples with all cells ≤ 1/2; then a response that creates a good triple with a cell > 1/2 is
  not constrained. See 4.3.

### 4.2 A second re-anchoring round (diagnostic only) **[H]**
`reanchor_stats.py` classifies, for every recorded winning response to a sealed request, the new
good triple p' by the status of the nearest grid profile. In the `maxS` run at t = 0.85
(`out/reanchor_maxS_0.85.txt`): at the 17 stuck profiles between 49% and 91% of these triples
are near profiles where the requester wins the one-round game, at most 6% are near stuck
profiles, and the rest (5%–51%) are **outside the grid because one of their cells exceeds 1/2**.
For 26%–100% of the sealed requests every recorded answer has a re-anchor triple near a winning
profile. So a second
adaptive round started from p' would probably remove part of the stuck set, but the adversary
has an evident escape: answer so that K meets one of the two kept edges in more than k/2 points.
Triples with a cell > 1/2 are where this game fails almost everywhere. I did not compute the
two-round re-anchoring game exactly (the second-round anchor is off-grid; see Section 5).

### 4.3 Other extremal anchors ("potentials")
The requester may choose the anchor to maximize any function Φ of the sorted pair cells
(s1 ≥ s2 ≥ s3) over the good triples of the family (of a class); every response that creates a
good triple of the class then satisfies Φ' ≤ Φ. `maxS` is Φ = s1+s2+s3, minimum S is Φ = −S.
Rules only restrict the adversary, so it suffices to re-solve the 27 profiles stuck for `none`.
`potential_scan.py` does this for Φ = a·s1 + b·s2 + c·s3 in the sound form `poth` (class = good
triples with all cells ≤ 1/2; responses creating a cell > 1/2 are unconstrained; in the MILP
"> 1/2" is ≥ 1/2 + 10⁻⁵, in the exact checks it is ≥ 1/2, which favours the adversary).

Scan at t = 0.85 over the 27 profiles stuck for `none` (`out/pothscan_0.85*.jsonl`); "+" marks a
potential whose run was interrupted (count = lower bound):

| anchor chosen to | solved | still stuck (of 27) | which (if ≤ 6) |
|---|---|---|---|
| **min 3·s1+s2** | 27/27 | 0 |  |
| min 3·s1+2·s2 | 27/27 | 2 | (0.5,0.2,0.2) (0.5,0.25,0.25) |
| min 2·s1+s2 | 27/27 | 2 | (0.5,0.2,0.2) (0.5,0.25,0.25) |
| min s1+s2 | 27/27 | 2 | (0.5,0.2,0.2) (0.5,0.25,0.25) |
| min s2 | 27/27 | 2 | (0.5,0.2,0.2) (0.5,0.25,0.25) |
| max s1−2·s2 | 27/27 | 2 | (0.5,0.2,0.2) (0.5,0.25,0.25) |
| max s1−s2 | 27/27 | 2 | (0.5,0.2,0.2) (0.5,0.25,0.25) |
| max 2·s1−3·s2 | 27/27 | 2 | (0.5,0.2,0.2) (0.5,0.25,0.25) |
| max s1−s3 | 6/27 | 5+ |  |
| min s1 | 27/27 | 10 |  |
| min S | 27/27 | 11 |  |
| min s2+s3 | 26/27 | 13+ |  |
| min s1−s2 | 22/27 | 13+ |  |
| min s3 | 27/27 | 17 |  |
| max s2+s3 | 24/27 | 18+ |  |
| max s3 | 27/27 | 22 |  |
| max s2 | 27/27 | 24 |  |
| max s1+s2 | 27/27 | 24 |  |
| max S | 27/27 | 24 |  |
| max s1 (largest cell) | 27/27 | 26 |  |

Readings:
- Every "max" principle is useless once it is restricted to the sound class: max S, max largest
  cell (the analogue of FKW's M), max s1 + s2 leave 24–26 of 27 profiles stuck. The adversary
  simply answers sparsely, or with a triple that has a cell > 1/2.
- "Min" principles on the two largest cells remove almost everything: with min s1 + s2,
  min s2, max s1 − s2, min 2·s1 + s2 only (0.5,0.2,0.2) and (0.5,0.25,0.25) remain; min s1
  alone wins these two but loses ten others; **min 3·s1 + s2 wins all 27**.

### 4.4 The sparsest anchor: one adaptive round wins at t = 0.85 (not yet at 0.84) **[C]**, partly **[E]**
Rule `poth:-c,-1,0` (c = 2,…,5): the anchor minimizes c·s1 + s2 over the good triples with all
pair cells ≤ 1/2; a response to a request sealing a cell creates the good triple (A1,A2,K); if
its cells are all ≤ 1/2, then c·s1' + s2' ≥ c·x + y, otherwise nothing is assumed (looseness
S' ≤ 3 − 2t is kept). Full grids (every profile with x ≤ 1/2 solved under the rule):

| anchor minimizes | t | profile grid / request grid | profiles | static | adaptive: contradiction | adaptive: closures | stuck |
|---|---|---|---|---|---|---|---|
| 3·s1 + s2 | 6/7 | 1/14 / 1/42 | 115 | 93 | 12 | 10 | 0 |
| 3·s1 + s2 | 6/7 | 1/21 / 1/42 | 281 | 236 | 22 | 23 | 0 |
| 3·s1 + s2 | 0.85 | 1/20 / 1/40 | 278 | 201 | 40 | 37 | 0 |
| 3·s1 + s2 | 0.85 | 1/40 / 1/40 | 1739 | 1176 | 244 | 319 | 0 |
| 3·s1 + s2 | 0.84 | 1/25 / 1/50 | 450 | 292 | 66 | 91 | 1 |
| 3·s1 + s2 | 5/6 | 1/24 / 1/48 | 447 | 248 | 92 | 102 | 5 |
| 3·s1 + s2 | 0.825 | 1/20 / 1/40 | 281 | 130 | 68 | 57 | 26 |
| 3·s1 + s2 | 0.80 | 1/20 / 1/40 | 283 | 107 | 62 | 58 | 56 |
| 4·s1 + s2 | 6/7 | 1/14 / 1/42 | 115 | 93 | 13 | 9 | 0 |
| 4·s1 + s2 | 6/7 | 1/21 / 1/42 | 281 | 236 | 22 | 23 | 0 |
| 4·s1 + s2 | 0.85 | 1/20 / 1/40 | 278 | 201 | 41 | 36 | 0 |
| 4·s1 + s2 | 0.84 | 1/25 / 1/50 | 450 | 292 | 67 | 91 | 0 |
| 4·s1 + s2 | 0.84 | 1/50 / 1/50 | 3234 | 1793 | 610 | 825 | 6 |
| 4·s1 + s2 | 5/6 | 1/24 / 1/48 | 447 | 248 | 100 | 96 | 3 |
| 5·s1 + s2 | 0.84 | 1/25 / 1/50 | 450 | 292 | 70 | 88 | 0 |
| 5·s1 + s2 | 5/6 | 1/24 / 1/48 | 447 | 248 | 99 | 98 | 2 |
| 2·s1 + s2 | 0.84 | 1/25 / 1/50 | 450 | 292 | 62 | 92 | 4 |
| 2·s1 + s2 | 5/6 | 1/24 / 1/48 | 447 | 248 | 90 | 99 | 10 |

Stuck profiles of the nearly complete runs: 3·s1 + s2, t = 0.84: (0.48,0.2,0.2); 3·s1 + s2, t = 5/6: (0.375,0.375,0.208) (0.458,0.208,0.208) (0.458,0.25,0.25) (0.5,0.208,0.167) (0.5,0.208,0.208); 4·s1 + s2, t = 0.84: (0.38,0.38,0.22) (0.4,0.38,0.24) (0.5,0.18,0.18) (0.5,0.2,0.16) (0.5,0.2,0.18) (0.5,0.2,0.2); 4·s1 + s2, t = 5/6: (0.375,0.375,0.208) (0.5,0.208,0.167) (0.5,0.208,0.208); 5·s1 + s2, t = 5/6: (0.375,0.375,0.208) (0.5,0.208,0.167); 2·s1 + s2, t = 0.84: (0.48,0.2,0.2) (0.48,0.24,0.2) (0.48,0.24,0.24) (0.48,0.28,0.24).

*How the wins look* (c = 3, t = 0.85, 1/20 grid, 77 non-static profiles):
- 40 **contradiction wins**: a request D sealing Y and Z (22 profiles), X and Z (13), Y (4) or
  X (1), and deleting enough of the two edges through a sealed cell, such that *no* response
  satisfies the rules: every response would create a good triple with all cells ≤ 1/2 and
  smaller 3·s1 + s2. `exact_infeasible.py` re-proves all 40 with an exact rational simplex over
  all branch combinations (2504 LPs), using neither the MILP solver nor the pattern tables
  **[E]**. The same exact check passes on the other grids: 244 of 244 (c = 3, t = 0.85, 1/40 grid), 22 of 22 (t = 6/7), 92 of 92 (t = 5/6); for c = 4: 41 of 41 (0.85), 22 of 22 (6/7), 67 of 67 (0.84, 1/25 grid) and 609 of 610 (0.84, 1/50 grid; the exception is a request against which the only escape is a response meeting an old edge in exactly k/2 points, which the exact checker deliberately counts as an escape and the MILP does not). Logs: `out/verify_poth.txt`, `out/verify_p4.txt`.
- 37 **closure wins**: 26 by sealing X, Y, Z and the three static requests Q (these need no
  rule at all, Section 2.4), 11 by sealing two cells, where the rule forces the response to be
  dense and Q (or T_c) closes. These are MILP results **[C]**; `check_wins_lp.py` maximizes
  random linear objectives over the admissible responses and checks every extreme response
  found against the certificate (2220 responses on the 1/20 grid, no failure).

**Lemma A (sparser triple) [P].** Let tau(H) > T and let (E,F,G) be a good triple with pair cells
x ≥ y ≥ z, x ≤ k/2. If x + 2y > 2k − T (+O(1)), then H has a good triple with all pair cells
≤ k/2 and a strictly smaller sum of its two largest pair cells.
*Proof.* If y < k − T then x + 2y < k/2 + 2(k − T) ≤ 2k − T, so y ≥ k − T. Request
D = Y ∪ D_E ∪ D_G with D_E ⊆ E∖Y, D_G ⊆ G∖Y, |D_E| = |D_G| = (T − y)/2. A response K avoids
Y = E∩G, so (E,G,K) is a good triple with pair cells y, |K∩E| ≤ w, |K∩G| ≤ w, where
w = k − y − (T − y)/2 = (2k − y − T)/2 ≤ k/2. Its two largest cells sum to at most
max(y + w, 2w) = max((2k + y − T)/2, 2k − y − T), and both are < x + y: the second because
x + 2y > 2k − T, the first because 2x + y ≥ x + 2y. ∎
So a minimizer of s1 + s2 in the class has x + 2y ≤ 2k − T: at T = 0.85k, x + 2y ≤ 1.15k. This
alone excludes the 6/7 corner (x + 2y = 9k/7) and all 25 "two large cells" profiles of
Section 2.2; the weight 3 on s1 is what handles (0.5,0.2,0.2) and (0.5,0.25,0.25).

*Soundness checks.* A sound rule must leave the requester stuck at the extremal anchor of a
genuine (7,2)-family with tau > t. For K_N, N = 1.68k (which has property (7,2) and
tau = 0.68k + 1) the sparsest anchor in the class is the balanced triple (0.44,0.44,0.44) with
union N; at t = 0.64 the game is indeed stuck there under `poth:-3,-1,0`, `poth:-1,-1,0`,
`poth:-1,-1,-1`, `poth:0,-1,0` and `loose`; similarly `poth:1,-1,0` is stuck at
(0.5,0.4,0.4), t = 0.66 (K_{1.7k}).

*Why it works where looseness does not.* The adversary of Sections 2–3 wins by answering
sparsely. Sparse answers to sealed requests create sparse good triples. Looseness and max-S
bound good triples from the dense side and never see them; a sparsest anchor forbids exactly
them. After sealing a cell and deleting part of the two edges through it, the response has no
room to be dense enough (contradiction) or is forced to be so dense that three static requests
close E,F,G,K. The looseness bound (dense side) and the sparsest anchor (sparse side) pinch the
adversary from both sides; I did not test whether the looseness rows are needed in these wins.

*Grid sensitivity.* At t = 0.84 the 1/25 grid is won completely for c = 4 and c = 5, but the
1/50 grid has six stuck profiles for c = 4: (0.38,0.38,0.22) and (0.40,0.38,0.24), which lie on
the boundary x + 2y = 2 − t of Lemma A, and four profiles (0.5, y, z) with y ≈ 0.2 (the 1/25
grid does not contain x = 1/2). So a coarse grid can miss stuck profiles, and the 0.85 statement
needs the same scrutiny: `boundary_check.py` re-solved, for c = 3 and for c = 4 at t = 0.85, all 461 profiles of the 1/80 grid (requests on the 1/80 grid) with 1.12 ≤ x + 2y ≤ 1.15: 193 static, 268 adaptive, none stuck, both times **[C]** (`out/boundary_log.txt`). The 1/40 grid contains the profiles (0.5, y, z) with y near 0.2, the other place where the 0.84 runs fail, and they are won at 0.85. Finer grids elsewhere were not run.

*What this does not show.* See Section 5, items 2–4 and 9.

---------------------------------------------------------------------------------------------

## 5. Limitations (read before quoting anything)

1. **Scope of the game.** One adaptive response, then *static* requests. The 6/7 manuscript uses
   up to four adaptive responses and pair gaps; this game is strictly weaker on sparse profiles
   (it is stuck at 6/7). "Stuck" is a statement about this game, not about the family.
2. **Grid.** Stuck = no winning request on a grid of step 1/dden (1/40 at t = 0.85, 0.80,
   0.875, 0.9; 1/42 at 6/7; coarser where indicated). Profiles are on a grid of step 1/20 or
   1/21 (1/40 for the corner profile). Features narrower than the grid are invisible: the static
   6/7 corner region at t = 0.85 has diameter about 0.01 and is only represented by (0.425)³.
3. **Exactness.** Requester wins are floating-point MILP results (tolerance 10⁻⁶) plus a sampling
   check. Stuck certificates are verified with integers for `loose` and `maxS` at t = 0.85 (27 and 17 profiles; 3 and 2 of the certificates failed the check because the search had used the sampled sub-tables, were re-solved with complete tables and then passed; `out/exact_repair.txt`), for the corner profile under both rules, and for the integral k = 40 certificate of Section 3. The `none` run at 0.85 and the runs at t = 6/7, 0.80 and x > 1/2 have **not** been exactly re-verified (time; `py repair.py FILE VARIANT T` does it, and as above a few certificates can be expected to need re-solving). All of it rests on the
   completeness of the pattern tables (Section 1.2), which is a short LP-duality argument plus
   an enumeration, cross-checked numerically but not formalized.
4. **Anchors.** Only profiles with x ≤ 1/2 are in the main tables. `maxS` as a global extremal
   rule is optimistic for that reason; the sound `poth` rules are in 4.3–4.4. They presuppose
   that the family has a good triple with all pair cells ≤ k/2. That is not automatic: it
   follows from a pair with intersection in [k − T, k/2], and families without such a pair
   (every two edges meet in fewer than k − T or more than k/2 points) need a separate argument.
5. **Sealing convention.** Looseness and re-anchoring are granted only for sealed cells
   (Section 1.3). This is the correct reading for k → ∞ with an adversary who may spend O(1)
   points, and it is how the existing proofs work, but it is a modelling decision: a robust
   tight-triple lemma for triples with a small core would change the game. I do not see one.
6. **Closures.** Only Q and T_c. In particular no closure that keeps K and one old edge, and no
   closure tailored to pairs meeting in more than k/2.
7. **R3** is inconclusive by construction (Section 3).
8. The two-round analysis of Section 4.2 is a nearest-grid-point heuristic.
9. **Status of the positive result (4.4).** Verified exactly: the contradiction wins (no
   response compatible with minimality), at the grid profiles. Not verified exactly: the closure
   wins (floating-point MILP, tolerance 10⁻⁶, plus an extreme-point check) and the static wins
   (float evaluation of the rational tables). Not covered at all: profiles between grid points
   (the win regions are unions of polytopes, but I did not compute them, and a win need not
   persist under small changes of the profile, in particular near profiles where a cell is
   exactly sealed by a request of size t), the class-non-emptiness of item 4, and the
   O(1) losses of integer rounding. The request-menu version of the game (`value_profile`) was
   unable to find many of these wins; nothing guarantees that the present search is optimal
   either, but that only matters for the stuck side.
10. **Novelty not checked.** I have not compared the sparsest-anchor device with the
   "lexicographically least good profile" of the 11/13 repository (ROADMAP §1.2, [U]); they may
   be related.

---------------------------------------------------------------------------------------------

## 6. Recommended next step

**Turn the sparsest-anchor result into a theorem at t = 0.85, then push t down.** Concretely:

1. *Contradiction lemmas in Lean* (days). Lemma A and its analogues for c·s1 + s2 are statements
   "for this request, every response yields a good triple with all pair cells ≤ k/2 and smaller
   potential": a request, a handful of capacity bounds, and linear arithmetic over the six cell
   counts. They sit directly on top of `Framework.request_cover` / the good-triple vocabulary of
   `TightTriple.lean`. `exact_infeasible.py` already produces, per profile, the request and the
   infeasible branch LPs; Farkas multipliers for those LPs are the Lean proofs.
2. *From grid to continuum* (the real work). The surviving region after the contradiction
   lemmas is {x ≤ 1/2, static value > t, no contradiction}; at t = 0.85 on the 1/40 grid it has
   319 profiles, all won by sealing cells plus Q / T_c with certificates of 3–18 patterns. Each
   certificate is a finite system of linear inequalities in the cell sizes (the pattern weights
   are rationals with denominator dividing 12 or 840), so a win region is a union of polytopes
   in profile space. Needed: a cover of the region by such polytopes with exact LP certificates
   (rational simplex as in `exact_infeasible.py`, or the SAT/LP certificate format of the 11/13
   repository), then an integer audit as in `compute/audit_cases.py`.
3. *The class may be empty.* The argument needs a good triple with all pair cells ≤ k/2. From a
   pair with |E∩F| = x ∈ [k − T, k/2] one gets it by a request containing E∩F and enough of
   E∖F and F∖E (size k − x ≤ T). Families in which every pair meets in fewer than k − T or more
   than k/2 points are the manuscript's small-M regime and must be handled by its Theorem 5.2
   type argument (or a new one); the present experiment says nothing about them, and anchors
   with a pair cell > 1/2 are where the one-round game fails (Section 2.1).
4. *Potential search.* Only about 25 linear potentials were tried, most of them at one value of
   t. At t = 5/6 the potentials 3·s1 + s2 and 4·s1 + s2 leave 5 and 3 of 447 profiles. (2·s1 + s2: 10; 5·s1 + s2: 2.) A systematic search (potentials that are
   piecewise linear in the sorted cells, chosen by a counterexample-guided loop on the stuck
   profiles: the engine evaluates a full grid in 1–3 minutes) should locate the true threshold
   of "sparsest anchor + one response". Nothing in Section 2.3 caps it at 5/6: at its own
   sparsest anchor (the balanced triple with 3a = 2 − t) the complete family's answer to a
   request sealing one cell violates the looseness rows ("not admissible" in the table of 2.3),
   which is the reduction of ROADMAP §4 at work.
5. Only then a second adaptive round. The R3 witnesses (bad tuples made of several responses and
   no anchor) and the corner mixture of Section 2.3 say that the next gain after the one-round
   threshold comes from playing two responses against each other; the exact pattern tables
   extend to five edges with two static requests (4 up-closed families per class) and to
   general four-edge configurations with the same generator.

For the 3/4 conjecture itself the lesson is about *direction*: FKW's M, the manuscript's gaps
and the max-S anchor of the roadmap are "max" extremal choices, which constrain the dense side,
where the tight-triple lemma already does the work. Every obstruction found in this experiment
at t ≥ 0.85 lives on the sparse side and disappears under a "min" choice (the 11/13 repository's
"lexicographically least good profile" may already be of this kind; not checked). The stability
conjecture of ROADMAP §4 should be attacked with a sparsest anchor, not a densest one.

---------------------------------------------------------------------------------------------

## 7. Files (`compute/r1/`)

- `tables.py`: exact pattern tables (rational weights), sampled sub-tables; `check_tables.py`:
  cross-check against an independent MILP.
- `game.py`: regions, closures, rules (variants), adversary MILP, inner constraint generation
  `play`. (`menu`/`value_profile` are the first, menu-based version of the outer loop; they
  declared many profiles stuck that `outer.py` wins. Kept for comparison only.)
- `outer.py`: request grid, shrinking of responses, cuts, `solve_profile`.
- `run_grid.py`: grid driver (multiprocessing); `summarize.py`, `report.py`: tables.
- `exact_check.py`: integer re-verification of stuck certificates; `repair.py`: re-solve failed
  ones with complete tables; `fix_err.py`: re-solve records lost to solver errors;
  `check_wins.py`: sampling check of requester wins.
- `complement.py`, `diag_complement.py`: complete-family response rule against all requests.
- `looseness_slack.py`, `reanchor_stats.py`: diagnostics of Sections 2.1 and 4.2.
- `potential_scan.py`: extremal-anchor scan of Section 4.3; `exact_infeasible.py`: exact rational
  proof of the contradiction wins of Section 4.4; `check_wins_lp.py`: extreme-point check of the
  closure wins.
- `boundary_check.py`: finer-grid probe near the boundary x + 2y = 2 - t (Section 4.4).
- `r3_family.py`: R3 test (build / test / prune).
- `out/`: `grid_VARIANT_T_pden_xmax.jsonl` (one record per profile: win type, winning request and
  pattern pool, or the list of responses of a stuck certificate), logs, R3 outputs, scans.
  `cache/` (pattern tables, 200 MB, rebuilt on demand) is git-ignored.

Reproduce a row of the table: `py run_grid.py loose 0.85` (3 min on 20 cores), then
`py exact_check.py out/grid_loose_0.85_20_0.5.jsonl loose 17/20`.
The sparsest-anchor result: `py run_grid.py poth:-4,-1,0 0.84 --pden 25 --dden 50` (about a
minute), then `py exact_infeasible.py out/grid_poth-4.-1.0_0.84_25_0.5.jsonl -4,-1,0 21/25 --dden 50`.
One profile with a trace: `py outer.py 0.45 0.45 0.1 0.85 loose` (or `poth:-4,-1,0`).
Python: `py` 3.15 with pulp 4 / HiGHS and numpy; nothing outside `compute/r1/` was modified
(`typefam.py` is imported read-only by `r3_family.py`).

