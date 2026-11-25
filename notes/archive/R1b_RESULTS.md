# R1b results: does the sparsest-anchor method get below 5/6 with more adaptive rounds?

Written 2026-11-23. Code `compute/r1b/` (on top of `compute/r1/`), outputs `compute/r1b/out/`,
log of milestones `notes/R1b_PROGRESS.md`. Nothing committed; no Lean file touched.
Tags: **[C]** floating-point MILP evidence, **[P]** hand proof, **[E]** exact arithmetic
(nothing new in this note is [E]: see Section 5).

## 0. Verdict: INCONCLUSIVE (leaning negative for the game as implemented)

- No t < 5/6 was found with 0 stuck anchors, so the outcome is not WORKS.
- It is not a clean FAILS either: what was computed is a restriction of the two-round game
  (re-anchoring only, Section 1), the stuck set shrinks with every round that was added
  (26 → 14 → at most 12 at t = 0.825) and shrinks again when the pair gap is imposed, and the
  deepest runs did not finish. Only t = 0.825 was explored beyond one round, only the potential
  4·s1 + s2, only the 1/20 grid.
- The six anchors that survive three rounds are all *lopsided* (one pair cell ≈ k/2, two small
  ones). For them the natural extra move, the star continuation (no static phase), was
  implemented in an honest form and is **stuck**, already at the ideal two-cluster anchor: the
  obstacle is the trace that every response can keep on the centre (Section 3.4).
- All soundness checks pass (Section 2); one unsound variant was caught by them and discarded.
- Everything here is floating-point evidence on grids.

## 1. What was computed (and what was not)

The full two-round game "exists D1, all K1, exists D2, all K2, close" has a 13-dimensional second
request and a 14-dimensional second response; R1's exhaustive request grid does not extend to
it. I computed a **sound restriction** instead (`game2.py`, `multi.py`):

- Anchor = good triple minimizing Phi = c·s1 + s2 (c = 4 in all runs quoted) over a class:
  `half` = all pair cells ≤ 1/2 (as in R1), or `all` = every good triple. v = Phi(anchor).
- A *position* is a good triple q. One round from q: request D, response K. The requester wins
  the round if (a) K creates, through a sealed cell, a class triple with Phi < v (contradiction
  with global minimality), or (b) 3 static requests close q's edges + K, or 4 static requests
  close a sealed new triple, or (c) **he drops the edge opposite to a sealed cell and plays one
  more round from the new good triple** q' = (|c|, |K∩A1|, |K∩A2|), with the same v.
  Depth d = at most d adaptive responses along a line of play. Edge count: triple + K + 3 ≤ 7.
- So "depth 2" is: two adaptive responses, the second request made after seeing K1, played
  from a good triple that contains K1. **Not included**: closing all five edges E,F,G,K1,K2
  with two static requests; second requests that still use the dropped edge; constraints
  between a response and dropped edges. All omissions bias toward "stuck".
- Second-round positions are looked up on the profile grid (1/20); when a lookup is active the
  first response is restricted to multiples of 1/40, and an off-grid q' counts as won only if
  all neighbouring grid positions are won. The response grid biases toward "win", the corner
  rule and the request grid (1/40) toward "stuck".
- Lemma A (Lean: `SparserTriple.lean`) is applied analytically at the anchor's own level,
  because the request grid misses it by half a step.
- Budgets must satisfy 40·t ∈ ℤ: the ladder is 0.85, 0.825, 0.80, 0.775, 0.75.
- Class `all` is new relative to R1: no "> k/2 escape", no "class may be empty" caveat, but
  anchors with a pair cell > 1/2 (grid 0 < x ≤ 1) must be won as well.

## 2. Soundness checks (all pass)

The parity family cannot be told from K_{7k/4} in the cell-size model (parity is O(1)), and
K_{7k/4} is not a (7,2)-family, so the FKW check was replaced by complete families K_N with
N < 7k/4 (property (7,2), tau = N − k + 1); at t < N/k − 1 the game must be stuck at their
sparsest anchor, the balanced triple with 3a = 3 − N/k.

| family | t | anchor | grids | class, rule | result |
|---|---|---|---|---|---|
| K_{1.65k} | 0.625 | (0.45)³ | 1/20, 1/40 | half and all, c = 4, depth ≤ 3 | stuck |
| K_{1.68k} | 0.64 | (0.44)³ | 1/25, 1/50 | half and all, c = 4, depth ≤ 3 | stuck |
| K_{1.70k} | 0.65 | (13/30)³ | 1/30, 1/60 | half and all, c = 4, depth ≤ 3 | stuck |
| K_{1.74k} | 0.72 | (0.42)³ | 1/50, 1/50 | all, c = 4, depth ≤ 3 | stuck |
| K_{1.65k}, K_{1.68k} | 0.625, 0.64 | as above | as above | all, c = 4, depth ≤ 3, **with Lemma B + pair gap** | stuck |
| H2(1.15k) (two disjoint complete clusters; (7,2), tau = 0.3k+2) | 0.275 | (0.85,0,0) | – | star game, n = 5, 6, 7 | stuck |
| K_{1.65k} | 0.625 | (0.45)³ | – | star game, n = 5 | stuck (n = 6, 7: timeout, undecided) |

Not finished: K_{1.74k} at t = 0.72 with Lemma B + pair gap (the window is empty at a
complete-family anchor, so the gap rows are vacuous there and the earlier check applies; the
Lemma B row is implied by the closure).

**One unsound variant was caught by these checks and discarded**: the potential
1600·s1 + 40·s2 + s3 "won" everything, including the complete-family anchors. Cause: the
big-M constant 8 that switches off the inactive orderings of the potential constraint is too
small for large weights, so the adversary's set became empty. It is valid when
Phi(anchor) ≤ 8, which covers every c ≤ 5 run of R1 and the c = 4 runs here (and R1's
contradiction wins were re-proved without any big-M). Fixed in `game2.py`; tie-breaking
potentials were then dropped anyway (void in the continuum model, NEW_PATHS §1.1).

## 3. Results [C]

### 3.1 Depth 1 (one adaptive round), class `all`, c = 4, grid 1/20 (requests 1/40)
| t | anchors | stuck |
|---|---|---|
| 0.85 | 491 | 1: (0.6,0.05,0.05) |
| 0.825 | 498 | 26 |
| 0.80 | 502 | 61 |
| 0.775 | 504 | 116 |
| 0.75 | 505 | 140 |

So with class `all` one round is as good at 0.85 as R1's restricted class (and no longer needs
a class-non-emptiness lemma), and fails below 5/6, as expected.

### 3.2 More rounds at t = 0.825
Class `all`, c = 4, grid 1/20, requests 1/40, lookups as in Section 1. The run was stopped
after about 80 minutes with 6 anchors unfinished (`out/multi_0.825_4_20_40_all_depth3.jsonl`
plus `memo/`).

| of the 26 anchors stuck at depth 1 | count | which |
|---|---|---|
| won at depth 2 | 12 | (0.45,0.2,0.2), (0.45,0.25,0.2), (0.45,0.3,0.15), (0.5,0.2,0.1–0.2), (0.55,0.1,0.05–0.1), (0.55,0.15,0.05–0.15), (0.6,0.05,0.05) |
| won at depth 3 | 2 | (0.5,0.2,0.05), (0.45,0.3,0.2) |
| stuck at depth 3 | 6 | (0.5,0.1,0.05), (0.5,0.1,0.1), (0.5,0.15,0.05), (0.5,0.15,0.1), (0.5,0.15,0.15), (0.55,0.05,0.05) |
| stuck at depth 2, depth 3 unfinished | 6 | (0.35,0.35,0.1–0.2), (0.4,0.35,0.2–0.25), (0.45,0.25,0.25) |

Class `half` (R1's class), same t and c, depth ≤ 2 (complete run, 281 anchors): 255 won at
depth 1, 8 at depth 2, 18 stuck; 5 of the 18, (0.4,0.4,z), were request-grid artifacts that
Lemma A removes (the lemma needs a half-step request), which is why Lemma A is now applied
analytically. The (0.5, y ≤ 0.2, z) anchors are stuck there too, with the "> k/2 escape".

Reading: each extra round of re-anchoring clears a sizeable part of what the previous one
left, and the survivors separate into two groups: balanced-sparse anchors (x ≈ y ≈ 0.35–0.45,
S ≈ 0.85–0.95, where more depth may still help; not decided) and lopsided ones.

### 3.3 With Lemma B and the pair gap as constraints on every response
Validity was checked first (PROGRESS, Milestone 5). Lemma B is valid for every good triple and
every edge, but relative to the current position it is already one of the patterns of the
"three static requests on E,F,G,K" closure, so the row is redundant in this engine. The pair gap
of NEW_PATHS §1.2 is stated for a lex-min anchor and is **not valid** for the rule 4·s1 + s2; I
used the analogue that is: no two edges meet in m points with m strictly between
2 − t − 2v/(c+1) and (v − (2−t)/2)/(c − 1/2) (for the anchor (0.5,0.15,·): between 0.315 and
0.446), imposed on the three traces of every response.

Rerun of the 12 open anchors at t = 0.825, depth ≤ 3 (stopped unfinished after 45 minutes):

| anchor | without | with Lemma B + gap |
|---|---|---|
| (0.5,0.15,0.1), (0.5,0.15,0.15) | stuck at depth 3 | **won at depth 3** |
| (0.5,0.15,0.05), (0.55,0.05,0.05) | stuck at depth 3 | stuck at depth 3 |
| (0.5,0.1,0.05), (0.5,0.1,0.1) | stuck at depth 3 | stuck at depth 2, depth 3 unfinished |
| six balanced anchors | stuck at depth 2 | stuck at depth 1; deeper unfinished |

Under the gap the adversary's answers at (0.5,0.15,0.05) move out of the window (traces ≤ 0.3
or ≥ 0.45) but keep the same shape: new triples (0.5,0.15,0.025) or (0.525,0.05,0.025), both
with potential exactly 2.15, and 0.4–0.475 new points
(`out/explain_0.825_4_20_40_all_gapB_d2_10_3_1.json`).

### 3.4 Star continuation at lopsided anchors (`star.py`)
Named edges E,F,G and up to four responses, **no static phase**; win = the named edges have no
2-point cover. Roles (centre/petals) need not be fixed: the criterion is symmetric. Honest
model: the adversary can put O(1) points in any Venn cell he is allowed to enter, so a cell is
absent only if it was sealed; a 2-cover exists iff two present cells have union "all edges".
The requester therefore needs a plan of requests (fractions, in eighths, of each cell type per
round; a cell is sealed when the fraction is 1) that kills one cell of every covering pair and
whose request sizes stay ≤ t for every play of the adversary (an LP per round). Search: master
integer program + adversary LPs with cuts. Plans are fixed in advance (bias toward stuck); the
adversary is unrestricted (no gap, looseness or Lemma B rows: also toward stuck).

| anchor | t | n = 5 | n = 6 | n = 7 |
|---|---|---|---|---|
| (0.5875,0,0) (lex-min anchor of the two-cluster witness H2) | 0.825 | stuck | stuck | timeout |
| (0.5,0.15,0.05) | 0.825 | stuck | stopped, undecided | not run |
| (0.5,0.1,0.05) | 0.825 | stuck | not run | not run |
| (0.85,0,0), genuine (7,2) family H2(1.15k) | 0.275 | stuck | stuck | stuck |
| (0.45)³, genuine (7,2) family K_{1.65k} | 0.625 | stuck | timeout | timeout |

The other four lopsided anchors and (0.6,0.05,0.05) at 0.85 were queued and not reached.
Diagnostic (NOT a sound rule): if responses are forbidden to meet G, the star wins at
(0.5875,0,0) with one request (seal E∩F; then E,F,P3 have no common point and G is disjoint from
all of them). So in the honest model the star fails exactly because of the **petal traces on the
centre**: a response keeps a point on G unless all of G is requested (impossible), a point of
G lying in one petal only forces the other petals to have empty common intersection, and
sealing all (s−1)-wise intersections is unaffordable. This confirms by computation the obstacle
stated in NEW_PATHS §5.6. In H2 itself the trace is not small at all: after E∩F is requested the
only edges left are in G's cluster. What a proof needs is a dichotomy for the trace
(tiny ⇒ ... / large ⇒ the response belongs to the centre's cluster and is used as a petal of
the *other* star), i.e. a state that keeps both clusters; the fixed-plan model cannot express
"choose the centre after seeing the response".

## 4. The most informative stuck configuration

Anchor (0.5, 0.15, 0.05) at t = 0.825 (c = 4, class `all`), v = 4·0.5 + 0.15 = 2.15; cells
X,Y,Z = 0.5, 0.15, 0.05, privates 0.35, 0.45, 0.8. Stuck at depth 1, 2 and 3, with and without
Lemma B + pair gap, and in the star game (n = 5). At depth 2 (no extra rows),
43 responses answer all 80 065 grid requests (`out/explain_0.825_4_20_40_all_d2_10_3_1.json`):

- against requests sealing nothing: an **almost new edge**, 0.775–0.8 new points, traces
  ≈ (0.15, 0.175, 0.075) on E,F,G. No rule applies (nothing is sealed), and E,F,G plus an
  almost disjoint edge cannot be closed with three static requests. Lemma B (trace on E∪F∪G at
  least (3t − |W|)/2 = 0.0875) is respected.
- against requests sealing a cell: a response that creates a good triple **with exactly the
  anchor's potential**, e.g. seal X → (0.5, 0.15, 0.025); seal Y or Z → (0.475, 0.25, 0.05–0.15)
  (4·0.475 + 0.25 = 2.15), usually together with a trace just above 1/2 on the third edge
  (0.5–0.575). The new triple is another stuck position on the same level set, so re-anchoring
  goes round in circles: the adversary moves inside the family of minimal triples.
- typical new-point fraction of the sealed answers: 0.05–0.5.

All stuck anchors at depth 3 have this lopsided shape: (0.5, 0.1–0.15, ·), (0.55, 0.05, 0.05):
one pair cell near k/2, the other two small, S ≈ 0.65–0.8.

Realizability: R3 was **not** rerun on this configuration (it needs integral certificates of
the lookup game, which the engine does not record, and the separate realizability study of
NEW_PATHS Path 4 covers it). From R1 the expectation is the same as there: a block-type family
on the Venn cells has response-only bad tuples. The "almost new edge against every unsealing
request" behaviour cannot be sustained by a real family for long (two such answers to different
requests are nearly disjoint from each other and from E,F,G, and Lemma B applied to *their*
triples forbids a third); but exploiting that needs a state with two responses in play, which is
exactly what this restricted game drops.

## 5. Certification status

- Everything in Section 3 is floating-point MILP (HiGHS) on grids: **[C]**. No exact
  certificates were produced for the lookup game: a stuck verdict at depth d depends on stuck
  verdicts of sub-positions at depth d − 1, and I did not build the recursive exact checker.
  Depth-1 verdicts are of the same kind as R1's (whose exact checkers `exact_check.py`,
  `exact_infeasible.py` apply unchanged to class `half`, not yet to class `all`).
- Known biases: toward stuck (no 5-edge closure, request grid 1/40, corner rule for off-grid
  positions, max 1500 requests per position treated as stuck); toward win (first response on
  the 1/40 grid when a lookup is active).
- No finer-grid confirmation was run for any "won at depth ≥ 2" entry. No t below 0.825 was
  run at depth ≥ 2. Only c = 4.
- The pair-gap window used here is my adaptation to the potential 4·s1 + s2 (PROGRESS,
  Milestone 5); the lex-min form of NEW_PATHS §1.2 is not valid for this anchor rule.

## 6. What this says about going below 5/6

1. **No evidence yet that the method passes 5/6, and none that it cannot.** One round fails
   below 5/6 (26, 61, 116, 140 stuck anchors at 0.825, 0.80, 0.775, 0.75). Re-anchoring rounds
   recover a large part at 0.825; I could not afford the depth-3 runs at 0.80 and below.
2. The obstruction that survives three rounds is specific: **lopsided anchors**, i.e. a pair of
   edges meeting in about k/2 plus an edge almost disjoint from both. NEW_PATHS §5.3 identifies
   the family behind it (two disjoint complete clusters; tau > T, not (7,2)) and shows that no
   game keeping at most three named edges per cluster can beat it. My runs agree: the adversary
   answers unsealing requests with almost new edges and sealing requests with triples on the
   level set of the potential, and never has to commit to a cluster.
3. The star continuation in the honest cell model is stuck because of traces on the centre.
   This is the single most informative negative fact of R1b: the next lemma has to be about
   **what a response that touches the centre must look like** (a trace dichotomy using the pair
   gap: a response is far from the centre, hence useless to the adversary as a "trace", or
   close to it, hence a petal of the opposite star), not about another potential or another
   closure.
4. Things I would do next, in order: (a) the star game with adaptive choice of centre and with
   the pair-gap rows (cheap extension of `star.py`: the gap forbids exactly the medium traces);
   (b) depth-3 re-anchoring with the gap at 0.80 on the balanced anchors only; (c) exact
   certificates for the depth-2 wins at 0.825 before anyone builds on them.

## 7. Files (`compute/r1b/`)
- `game2.py`: adversary with re-anchoring lookup, pair gap, Lemma B row, fixed big-M.
- `multi.py`: positions, memo (`memo/`, git-ignored), drivers; `--cls half|all`, `--extra`,
  `--list`. Example: `py multi.py 0.825 4 3 --cls all`.
- `explain.py`: prints the adversary's recorded answers at a stuck anchor.
- `out/`: `multi_*.jsonl` (per anchor: the depth at which it is won, or null), logs,
  `soundness*.txt`, `explain_*.json`. `out/soundness_lex_BUGGY_bigM.txt` is the invalid run.
