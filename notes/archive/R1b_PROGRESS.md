# R1b progress (two/multi-round sparsest-anchor game)

Code: `compute/r1b/` (`game2.py`, `multi.py`), on top of `compute/r1/`. Nothing committed.

## Milestone 1: design fixed, engine written
What is being computed (a *restriction* of the two-round game, chosen because the full
"exists D1, all K1, exists D2, all K2" problem has a 13-dimensional second request and a
14-dimensional second response and cannot be enumerated the way R1 enumerated D):

- Position = a good triple q with all pair cells <= 1/2, plus the standing hypothesis "every good
  triple of the class has c*s1 + s2 >= v", v = potential of the (globally sparsest) anchor.
- Round: request D, response K. The requester wins the round if K contradicts the hypothesis, or
  static closures work (3 requests on the 4 edges, or 4 on a sealed new triple), or — new — he
  **drops the edge opposite to a sealed cell and continues from the new good triple**
  q' = (|c|, |K∩A1|, |K∩A2|) with one round less. Edge count stays <= 7 (triple + K + 3 static).
- So depth 2 = "two adaptive responses, the second played from a triple that contains the first
  response". NOT included: closing all five edges E,F,G,K1,K2 with two static requests, and
  second requests that use the dropped edge. Both omissions bias toward "stuck".
- Second-round positions are looked up on the 1/20 profile grid; when a lookup is active the
  first response is restricted to multiples of 1/40 and q' counts as won only if all neighbouring
  grid positions are won. The grid restriction of the adversary biases toward "win"; flagged.
- Budgets: t*40 must be an integer, so the ladder is 0.825, 0.80, 0.775, 0.75 (instead of
  0.82, 0.80, 0.78, 0.76, 0.75).

## Soundness check: note on FKW
The parity family is indistinguishable from K_{7k/4} in the k -> infinity cell-size model (parity
is an O(1) effect), and K_{7k/4} itself is not a (7,2)-family. So "stuck at the FKW anchor at
t = 0.74" is not something the continuous model can be required to satisfy at exactly N = 7k/4.
The equivalent test with slack is a complete family K_N with N < 7k/4, which is (7,2) with
tau = N - k + 1: at any t < N/k - 1 the game must be stuck at its sparsest anchor, the balanced
triple with 3a = 3 - N/k. Used below: N = 1.65k, anchor (0.45,0.45,0.45), t = 0.625.

## Milestone 2 (first numbers; all floating-point [C])
- Soundness: at t = 0.625 the anchor (0.45,0.45,0.45) of K_{1.65k} is stuck at depth <= 3
  (c = 4), as it must be.
- t = 0.825, c = 4, class "all pair cells <= 1/2", grid 1/20 (requests 1/40):
  depth 1 wins 255 of 281 anchors, depth 2 wins 8 more, 18 stuck. 5 of the 18, (0.4,0.4,z),
  are request-grid artifacts: Lemma A (now in Lean) kills them with a half-grid-step request;
  the engine now applies Lemma A analytically at the anchor level. Real stuck set so far:
  (0.35,0.35,0.1-0.2), (0.4,0.35,0.2-0.25), (0.45,0.25,0.25), (0.45,0.3,0.2) and six profiles
  (0.5, y <= 0.2, z): a pair cell of exactly k/2 next to small cells, where the adversary's
  escape is a response meeting an old edge in more than k/2 points (leaves the class).
- New variant: class = ALL good triples (no <= 1/2 restriction, so no escape and no
  "class may be empty" caveat; anchors with a cell > 1/2 must then be won too).
  t = 0.85, c = 4, depth 1: 490 of 491 anchors won (0 < x <= 1), 1 stuck: (0.6,0.05,0.05).
  This is much better than the restricted class. Ladder 0.825 ... 0.75 running.

## Milestone 3: soundness checks for class = ALL (requested by the coordinator) — PASS
Same settings as the ladder runs (c = 4, depth <= 3, lookup on, class = all), at the sparsest
anchor (balanced triple, 3a = 3 - N/k) of complete families that have property (7,2):
| family | t | anchor | grid (profiles / requests) | result |
|---|---|---|---|---|
| K_{1.65k} (tau = 0.65k+1) | 0.625 | (0.45,0.45,0.45) | 1/20, 1/40 | stuck at depth 1,2,3 |
| K_{1.68k} (tau = 0.68k+1) | 0.64  | (0.44,0.44,0.44) | 1/25, 1/50 | stuck at depth 1,2,3 |
| K_{1.70k} (tau = 0.70k+1) | 0.65  | (13/30,13/30,13/30) | 1/30, 1/60 | stuck at depth 1,2,3 |
(`compute/r1b/out/multi_0.6*_all_depth3.jsonl`). The restricted class was re-checked at 0.625
(stuck); its 0.64 / 0.65 checks are still running. So no unsoundness detected for class = all.
Caveat: these are necessary conditions only, at one profile each.

Depth-1 ladder, class = all, c = 4, grid 1/20 (anchors 0 < x <= 1), all [C]:
t = 0.85: 1 stuck of 491; 0.825: 26 of 498; 0.80: 61 of 502; 0.775: 116 of 504; 0.75: 140 of 505.
One adaptive round does not get below 5/6 with this potential. Depth 2-3 at 0.825 is running:
after 482 of 498 anchors, 9 of the 26 are won at depth 2, none declared stuck yet.

## Milestone 4: the "near-lexicographic" potential (1600,40,1) run was INVALID — cause found
- More soundness checks passed first: class = all, c = 4, depth <= 3 is stuck at the K_{1.70k}
  anchor (t = 0.65, grid 1/30) and at the K_{1.74k} anchor (0.42,0.42,0.42) at t = 0.72 (grid
  1/50), i.e. close to 3/4; the restricted class is stuck at K_{1.68k}, K_{1.70k} as well.
- I then tried the potential 1600*s1 + 40*s2 + s3 (to break the adversary's "stay on the level
  set of the potential" answers, see below). It "won" every anchor at t = 0.85 ... 0.75 in
  seconds AND "won" at the complete-family anchors (K_{1.65k}, K_{1.68k}, K_{1.74k}). That is
  impossible, so the variant was unsound as implemented. **All (1600,40,1) results are void.**
- Cause: not ties. The MILP encodes "one of the 6 orderings of the new cells, and for that
  ordering a*v1 + b*v2 + c*v3 <= Phi(anchor)" with a big-M constant of 8 on the inactive
  orderings (inherited from r1/game.py). With weights of size 1600 the inactive rows are not
  switched off (they would need M ~ 2000), so every response was required to satisfy the
  potential bound for all six orderings at once; the adversary's set became empty and every
  request looked like a contradiction win.
- Does it affect earlier runs? The constant is valid whenever |a|+|b|+|c|+|Phi(anchor)| <= 8.
  For c*s1+s2 with c <= 5 and x <= 1/2 (all of R1) the left side is at most 6 + 3 = 9 in the
  crudest bound but the actual requirement, max(lhs) - Phi(anchor) = Phi(anchor) <= 8 (lhs <= 0),
  holds: Phi <= 5*0.5 + 0.5 = 3. For class = all with c = 4: Phi <= 4*1 + 0 ... at most 4.5 <= 8.
  So c <= 5 runs (R1 and the c = 4 runs here) are not affected; the c = 4 runs also pass the
  complete-family checks, and R1's contradiction wins were re-proved by an exact rational
  simplex that has no big-M at all. A c = 8 run that was in progress (Phi can exceed 8 for
  x > 0.9) was stopped and discarded.
- Fix (compute/r1b/game2.py only; r1 is untouched and keeps the limitation, now documented in
  the code): M = |a|+|b|+|c|+|Phi(anchor)|+1. The (1600,40,1) soundness checks are being rerun
  with the fix before that potential is used again.

What the adversary does at a depth-2 stuck anchor (c = 4, class all, t = 0.825, anchor
(0.5,0.15,0.05)): against requests that seal nothing it answers with an almost new edge (80% new
points); against sealing requests it creates a triple with exactly the anchor's potential
(e.g. (0.475,0.25,0.05) or (0.5,0.15,0.025), both 4*s1+s2 = 2.15), i.e. it moves along the level
set of the potential to another stuck position.

## Milestone 5: tie-breakers dropped; Lemma B and pair gap added (validity notes)
- The (100,10,1) / (1600,40,1) line is dropped (NEW_PATHS.md §1.1: void in the continuum model).
  For the record, with the fixed big-M the (100,10,1) rule passed the complete-family checks
  (stuck at K_{1.65k}, K_{1.68k}, K_{1.74k}) and at t = 0.825 had 14 depth-1-stuck anchors
  instead of 26; its depth-2 run was stopped unfinished. Nothing from it is used.
- Validity of the two new constraints in THIS engine (anchor = minimizer of 4*s1 + s2 over ALL
  good triples; positions = good triples; k -> infinity, O(1) dropped):
  * Lemma B: I re-derived the proof; it holds for any good triple and any edge, no extremality
    needed. BUT with respect to the current position's triple it is already inside the engine:
    the lemma's three requests (K∩W ∪ P_i) are one pattern of the closure "E,F,G,K + 3 static
    requests", so every response violating it was already beaten. It can only add information
    relative to triples whose third edge has been dropped, and the engine does not track a
    response's trace on a dropped edge. Added anyway as a row (current triple); expect no effect.
  * Pair gap: the form in NEW_PATHS §1.2 ("no pair intersection in [2k−2u−T, u)") needs a
    lex-min anchor (every good triple has a cell >= u). That is FALSE for the rule used here:
    with 4*s1+s2 the triple (0.475,0.25,·) is allowed next to the anchor (0.5,0.15,·). The
    correct analogue for a linear potential c*s1+s2 (class = all): if two edges meet in m
    points, the request (A∩B) + (t−m)/2 points of each side returns a good triple with cells
    m, <= w, <= w, w = (2−t−m)/2, whose potential is at most g(m) = c*m + w (if m >= w) or
    (c+1)*w (if m < w). So no pair intersection has g(m) < v, i.e. none lies strictly between
    m_lo = 2 − t − 2v/(c+1) and m_hi = (v − (2−t)/2)/(c − 1/2); the window is non-empty iff
    v > (c+1)(2−t)/3, and it is empty at the balanced anchor of every K_N with N > (1+t)k, as
    it must be. Example: anchor (0.5,0.15,0.05), t = 0.825, c = 4: no two edges meet in
    (0.315, 0.446). Implemented for the traces of the response on the three edges of the
    current position (at every depth). Doubt: only the even split of the request is used
    (an uneven split could give a wider window); this errs on the safe side.
  * Not implementable in this engine: gap/Lemma B constraints between a response and edges
    that were dropped, or between two responses; that needs the 5-edge state.

## Milestone 6: 0.825 with more rounds; Lemma B + gap; star continuation (all [C])
- Soundness with Lemma B + pair gap on (class all, c = 4, depth <= 3): stuck at the K_{1.65k}
  anchor (t = 0.625) and at the K_{1.68k} anchor (t = 0.64); the K_{1.74k} check (t = 0.72) was
  still running when this was written.
- t = 0.825, class all, c = 4, no extra constraints, depth <= 3 (run stopped at 492 of 498
  anchors after about 80 minutes): of the 26 anchors stuck at depth 1, 12 are won at depth 2,
  2 at depth 3, 6 are stuck at depth 3 — (0.5,0.1,0.05), (0.5,0.1,0.1), (0.5,0.15,0.05),
  (0.5,0.15,0.1), (0.5,0.15,0.15), (0.55,0.05,0.05), all lopsided — and 6 balanced ones
  ((0.35,0.35,0.1-0.2), (0.4,0.35,0.2-0.25), (0.45,0.25,0.25)) are stuck at depth 2 with depth 3
  unfinished.
- Same anchors with Lemma B + pair gap: (0.5,0.15,0.1) and (0.5,0.15,0.15) are now WON at
  depth 3; (0.5,0.15,0.05) is still stuck at depth 3; the other nine were unfinished (all nine
  are stuck at depth 1, the lopsided ones also at depth 2). So the gap helps, slowly.
- Star continuation (compute/r1b/star.py): named edges E,F,G plus up to 4 responses, no static
  phase, win = no 2-cover. Because the adversary may put O(1) points wherever he is allowed,
  a Venn cell is absent only if sealed, so the requester needs a seal plan; requests may also
  take fractions (multiples of 1/8) of cells; plans are fixed in advance (bias toward stuck).
  Result so far: STUCK for n = 5, 6, 7 at (0.5,0.15,0.05), t = 0.825 and already at the pure
  two-cluster anchor (0.5875,0,0). Diagnostic: if responses are forbidden to meet the centre G
  (not a sound rule), the star wins at once (seal E∩F). So in the honest model the obstacle is
  exactly the petal traces on the centre flagged in NEW_PATHS §5.6: every response can keep a
  point on G unless all of G is requested, and then all (s−1)-wise petal intersections would
  have to be sealed, which is unaffordable.

## Milestone 7 (final): runs stopped, write-up in notes/R1b_RESULTS.md
- Verdict: INCONCLUSIVE. No t < 5/6 with 0 stuck anchors; at t = 0.825 (class all, 4*s1+s2)
  26 anchors stuck after one round, 14 after two, at most 12 after three (6 stuck, 6 unfinished);
  with Lemma B + pair gap two more are won at depth 3, (0.5,0.15,0.05) and (0.55,0.05,0.05)
  stay stuck at depth 3, the rest unfinished.
- Star game, honest model, fixed plans with fractional requests: stuck at (0.5875,0,0)
  (n = 5, 6; n = 7 timed out) and at (0.5,0.15,0.05) (n = 5; n = 6 timed out); stuck, as it
  must be, at the genuine (7,2) anchors (0.85,0,0) at t = 0.275 (n = 5, 6, 7) and (0.45)^3 at
  t = 0.625 (n = 5). The remaining lopsided anchors and (0.6,0.05,0.05) at 0.85 were not
  reached. Obstacle = petal traces on the centre (wins immediately if traces are forbidden,
  which is not a sound rule).
- Not done: K_{1.74k} check with the extra rows (unfinished), any t < 0.825 beyond one round,
  finer grids for the depth >= 2 wins, exact certificates for anything in R1b, R3 on a stuck
  R1b configuration.
- All R1b computations were stopped; nothing is running.
