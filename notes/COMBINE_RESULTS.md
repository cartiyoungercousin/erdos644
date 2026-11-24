# COMBINE: min-S anchor game below the stability threshold sigma0(t) = (17 - 11t)/7

Written 2026-11-24. Code: `compute/combine/run.py` (driver; calls `compute/r1b/multi.py` with
potential s1+s2+s3, class = all), `why.py`; outputs `compute/combine/*.txt` and
`compute/r1b/out/multi_0.84_p1_1_1_25_50_all_depth{1,2}_list.jsonl`. No commits, no Lean edits.
Everything here is floating-point MILP evidence **[C]**, not a proof.

## Verdict
**t = 0.84 is NOT clean.** With the min-S anchor (contradiction = a response creating a good
triple of strictly smaller S; plus static, adaptive Q/T_c closures; fixed big-M), 296 of the 743
grid anchors with S <= sigma0(0.84) = 1.1086 are stuck after one adaptive round (311 of 783 when
the grid layer S = 1.12 is included). Depth 2 rescues some but not all. Lower budgets (0.83,
0.82) were not run, since they can only be worse. No new record from this route.

## Setup
k = 1. Anchor = good triple of minimum S = x+y+z over all good triples; profiles on the grid 1/25
(requests 1/50), x >= y >= z, x + y <= 1, S <= 27/25 (plus the layer 28/25). Anchors with
S >= sigma0 are closed by Theorem 11.1 (Lean644/Stability.lean) and not tested. No analogue of
Lemma A was used (the Lean lemma controls the two largest cells, not the sum). The pair-gap
construction gives min S <= 2 - t, which is above sigma0 for t > 3/4, so it adds nothing here.

## Soundness (passed)
Sum potential, class all, depth <= 2, at the balanced anchors of complete families (all inside the
tested region S <= sigma0(t)): K_1.65k (t = 0.625, anchor 0.45^3), K_1.68k (t = 0.64, 0.44^3),
K_1.74k (t = 0.72, 0.42^3): all stuck, as they must be (`compute/combine/soundness.txt`).

## Depth 1 at t = 0.84 (`out_0.84_d1.txt`)
783 anchors: 472 won, 311 stuck. Stuck / total by S*25:
<= 14: 0/146; 15: 1/27; 16: 3/30; 17: 7/33; 18: 10/37; 19: 14/40; 20: 19/44; 21: 26/48;
22: 37/52; 23: 43/56; 24: 43/61; 25: 41/65; 26: 30/56; 27: 22/48; (28: 15/40, above sigma0).

The 296 stuck anchors with S <= 27/25, by region:
- **Lopsided, x > 1/2 (x >= 0.52): 260** (of the 330 anchors with x >= 0.52). y from 0 to 0.40,
  y + z <= 0.56. Includes the degenerate end (0.56..1.0, 0, 0), i.e. two nearly equal edges and a
  third edge almost disjoint from both. Smallest stuck S: (0.56, 0.04, 0) with S = 0.60.
- **Two large cells, x in [0.40, 0.48], y in [0.40, 0.48], small z (<= 0.16): 24.**
  (0.40,0.40,0.04..0.08), (0.44,0.40,0..0.16), (0.44,0.44,0..0.16), (0.48,0.40,0..0.12),
  (0.48,0.44,0..0.12), (0.48,0.48,0..0.12).
- **The rest: 12**: (0.40,0.36,0.04), (0.44,0.36,0.04), (0.44,0.36,0.16), (0.48,0.20,0.20),
  (0.48,0.24,0.20), (0.48,0.24,0.24), (0.48,0.28,0.24), (0.48,0.32,0.08), (0.48,0.32,0.12),
  (0.48,0.36,0.04), (0.48,0.36,0.08), (0.48,0.36,0.12).
- Nothing with x <= 0.36 is stuck, and nothing with S <= 0.56.

## Depth 2 samples (stopped on the coordinator's instruction after three finished)
| anchor | result |
|---|---|
| (0.72, 0, 0) | stuck at depth 2 |
| (0.80, 0.08, 0.08) | stuck at depth 2 |
| (0.56, 0.04, 0) | wins at depth 2 |
(0.52,0.08,0.08), (0.48,0.24,0.24), (0.64,0.16,0.16), (0.40,0.40,0.08) were started, not finished.

## Why lopsided min-S anchors resist
At (0.72, 0, 0) (E and F share 0.72, G is disjoint from both) the adversary answers every
request with one of two kinds of edge: a near-copy of G (about 0.5 to 0.7 of G's private part
plus points outside E, F, G), or an edge inside E u F (about half of E n F plus equal shares,
about 0.22 each, of the two private parts). So the shown family stays a two-cluster family:
every new good triple again consists of two heavily overlapping edges and a far one, its S is not
below 0.72, and no template or tight-triple closure appears. Minimum S does not penalise one
large pair cell, which is exactly what the potential 4*s1 + s2 of R1/R1b was designed to do; the
sum potential gives up that leverage, and Theorem 11.1 does not constrain the profile of the
sparsest anchor (only the value of min S), so the two tools do not combine directly.


# §2. Near-lex anchor below the Theorem 6.4 threshold (run of 2026-11-24)

Code: `compute/combine/run_lex.py` (calls `compute/r1b/multi.py`); outputs
`compute/combine/out_lex_*.txt`, `soundness_lex.txt`, `lex_0.84_g50_d2_part1.jsonl`,
`compute/r1b/out/multi_0.8{3,4}_p2000_40_1_*`. Floating MILP on grids: evidence **[C]**, no proof.

## Verdict
**t = 0.84: clean on the 1/25 grid** (all 609 anchors with largest cell <= 0.56 win within two
adaptive rounds). On the 1/50 grid 4022 of 4087 win at depth 1; of the 65 others, 34 have
finished depth 2 and all of them win; 31 were still unfinished when I stopped (none found
stuck). **t = 0.83:** 590 of 609 win at depth 1; depth 2 on the 19 others: 5 finished, all
win, 14 unfinished. So 0.84 is a candidate, not yet a clean statement.

## Setup, and what exactly is sound
- Anchor = minimiser of Phi = 2000*s1 + 40*s2 + s3 over all good triples (class all), cells
  sorted. Contradiction = a response that creates a good triple of strictly smaller Phi; this is
  sound for the Phi-minimiser (fixed big-M of `game2.py`). It is NOT the true lexicographic
  order. Fresh weights were used because the memo of the old (1600,40,1) runs predates the
  big-M fix.
- Link to Theorem 6.4: if the lex-min largest cell is u, the Phi-minimiser has
  s1 <= u * (1 + 41/2000). So a family not closed by 6.4 at t = 0.84 (u < 0.5627) has a
  Phi-anchor with s1 < 0.5743 (0.5715 with the LP constant 26). **Gap:** the grids stop at
  s1 = 0.56; the strip 0.56 < s1 < 0.574 is not tested (the layer s1 = 0.58 of the 1/50 grid
  would cover it; not run). At t = 0.83 the 6.4 threshold is u >= 0.5687, Phi-anchor s1 < 0.580;
  tested up to 0.56 only.
- Closures used by the engine: static, adaptive Q / T_c, Phi-contradiction, re-anchoring at
  depth 2 (a response whose new triple, rounded to the grid in every admissible way, is a
  depth-1 win at the same Phi level). Lemma A is not applied (it is coded for two-weight
  potentials only); Lemma B / pair gap not switched on.
- Depth 1 on the 1/50 grid uses requests on the same 1/50 grid (coarse).

## Soundness (passed)
Phi = (2000,40,1), class all, depth <= 2: the balanced anchors of K_1.65k (t = 0.625),
K_1.68k (t = 0.64), K_1.74k (t = 0.72) are all stuck (`soundness_lex.txt`).

## t = 0.84
Grid 1/25 (requests 1/50), 609 anchors with s1 <= 0.56: 597 win at depth 1. The 12 stuck at
depth 1, all won at depth 2:
(0.40,0.36,0.08), (0.40,0.40,0.24), (0.44,0.40,0.28), (0.44,0.44,0.28), (0.44,0.44,0.32),
(0.48,0.40,0.28), (0.52,0.16,0), (0.52,0.16,0.12), (0.52,0.28,0.12), (0.52,0.32,0.28),
(0.52,0.36,0.32), (0.56,0.04,0.04).

Grid 1/50 (requests 1/50), 4087 anchors: 4022 win at depth 1, 65 stuck at depth 1
(`out_lex_0.84_d1_g50.txt` has the list). Regions: 29 with s1 = 0.54 or 0.56 and small y, z
(y <= 0.14 or z = 0); 2 with (0.50, 0.40 / 0.46, 0); the other 34 have s1 in [0.38, 0.54] with
two or three large cells. Depth 2 status: 34 of the 65 finished, all win at depth 2. Unfinished (31, stopped for time, none found stuck): (0.38,0.38,0.22), (0.40,0.34,0.20), (0.40,0.38,0.24), (0.40,0.40,0.24), (0.42,0.34,0.10), (0.42,0.34,0.14), (0.42,0.42,0.26), (0.52,0.16,0), (0.54,0.04,0.02..0.04), (0.54,0.06,0.02..0.06), (0.54,0.08,0..0.08), (0.54,0.10,0.02), (0.54,0.10,0.04), (0.54,0.10,0.06), (0.54,0.10,0.10), (0.54,0.14,0), (0.56,0.02,0.02), (0.56,0.04,0.02), (0.56,0.04,0.04), (0.56,0.06,0..0.06), (0.56,0.08,0.02). Finished results: `compute/combine/lex_0.84_g50_d2_part1.jsonl` and `compute/r1b/out/multi_0.84_p2000_40_1_50_50_all_depth2_list.jsonl`.

## t = 0.83
Grid 1/25 (requests 1/100), 609 anchors: 590 win at depth 1. Stuck at depth 1 (19):
(0.36,0.36,0.20), (0.40,0.36,0.04), (0.40,0.36,0.24), (0.40,0.40,0.36), (0.44,0.36,0.28),
(0.44,0.40,0.28), (0.48,0.36,0.32), (0.52,0.04,0.04), (0.52,0.08,0.04), (0.52,0.08,0.08),
(0.52,0.12,0.04), (0.52,0.12,0.08), (0.52,0.12,0.12), (0.52,0.16,0.04), (0.52,0.24,0),
(0.52,0.32,0), (0.52,0.36,0), (0.56,0.04,0.04), (0.56,0.08,0).
Depth 2 status: 5 of the 19 finished, all win at depth 2: (0.52,0.36,0), (0.52,0.32,0), (0.52,0.24,0), (0.48,0.36,0.32), (0.56,0.08,0). The other 14 are unfinished (stopped for time).

## What a Lean proof would need
The depth-1 region is the bulk and uses static / Q / T_c / Phi-contradiction; the depth-2 wins
need the re-anchoring step per profile (use `compute/r1b/explain.py` on a profile to list the
closures per response). I did not extract the per-region closure lists.


# §3. Completion at t = 0.84 and proof blueprint (2026-11-24)

Code: `compute/combine/d2.py`, `blueprint.py`; data `blueprint_0.84.jsonl`,
`lex_0.84_g50_d2_part{1,2}.jsonl`, `lex_0.84_strip_d2.jsonl`, `out_lex_0.84_strip_d1.txt`,
`out_lex_0.84_d1_g50_r100.txt`. All **[C]** (floating MILP on grids). No exact certificates were
produced in this round (see 3.4).


## 3.0 Verdict of this round
**t = 0.84: no stuck profile found, two profiles undecided.** On the 1/50 grid every anchor with
s1 <= 0.58 (4087 + 244 anchors) wins within two adaptive rounds, except (0.38,0.38,0.22) and
(0.40,0.38,0.24), whose depth-2 runs did not finish (not shown stuck, not shown won). The 1/25
grid is completely clean. So: clean up to two undecided grid points; still grid evidence only.

## 3.1 The 31 unfinished 1/50 profiles
- With requests on the 1/100 grid, 16 of the 31 win already at depth 1 (so their depth-1
  failure was a request-grid effect).
- The other 15: (0.38,0.38,0.22), (0.40,0.38,0.24), (0.40,0.40,0.24), (0.54,0.04,0.02),
  (0.54,0.04,0.04), (0.54,0.06,0.02..0.06), (0.54,0.08,0.02..0.08), (0.56,0.02,0.02),
  (0.56,0.04,0.02), (0.56,0.04,0.04). Depth 2 (requests 1/50): 13 finished: 12 win at depth 2; (0.56, 0.02, 0.02) is stuck at depth 2 with 1/50 requests but **wins at depth 2 with 1/100 requests** (`lex_0.84_g50_d2_r100.jsonl`), so that was a request-grid effect. Two did not finish in about an hour each: **(0.38,0.38,0.22) and (0.40,0.38,0.24)** (both were also among the six stuck profiles of R1 at 0.84; their neighbour (0.40,0.40,0.24) wins at depth 2).
- Note: `compute/r1b/out/multi_0.84_p2000_40_1_50_50_all_depth1_list.jsonl` was overwritten by
  the strip run (same file name); the full 4087-anchor result survives in
  `out_lex_0.84_d1_g50.txt` (summary line with the complete stuck list).

## 3.2 The strip s1 = 0.58 (1/50 grid, 244 anchors)
238 win at depth 1. The 6 others, (0.58,0.02,0), (0.58,0.02,0.02), (0.58,0.06,0),
(0.58,0.22,0.08), (0.58,0.32,0), (0.58,0.38,0), all win at depth 2. **The strip is clean**, so
the difference between the Phi-minimiser and the true lex-min anchor does not matter on the grid.

## 3.3 Blueprint (from the 1/25 grid, 609 anchors with s1 <= 0.56, depth 1 re-solved with the
winning line recorded)

Cells: X >= Y >= Z pair cells of the anchor (E n F, E n G, F n G), PE, PF, PG private parts.
"Seal" = request the whole cell. Five line types cover 598 anchors; 11 need a second round.

| # | line | anchors | region on the grid |
|---|---|---|---|
| A | static: the 4-request closure of the anchor itself (phi_static <= t) | 299 | all anchors with x <= 0.32; for x >= 0.36 a subset that is not an interval in S (it interleaves with B to D) |
| B | one request sealing Y and Z (plus arbitrary filling), no closure needed: EVERY admissible response creates a good triple of smaller Phi | 125 | x in [0.40, 0.56], y in [0.08, 0.48], z >= 0.04, S in [0.68, 1.28] |
| B' | same with other seals: X and Z (38), Y only (18, z = 0 mostly), X only (7), Z only (5) | 68 | X,Z: x in [0.44,0.56], y in [0.40,0.48]; Y only: x >= 0.44, z small |
| C | seal X, Y, Z, then a Q-closure (quadruple E,F,G,K) per response case; up to 12 patterns | 67 | x in [0.36, 0.52], y <= 0.36, z <= 0.20, S in [0.48, 0.84] |
| D | seal two cells (or fewer), response cases closed by Q, in 8 anchors also by T_X / T_Y | 39 | x in [0.36, 0.56], S in [0.56, 1.00]; up to 15 patterns |
| E | second adaptive round (re-anchoring) | 11 | the depth-1 stuck list of §2 (one anchor of that list won on this re-run: the request search is randomised) |

Reading of the table:
- Type A is a single LP statement in (x,y,z): one 4-request pattern per sub-region; the exact
  pattern tables of `compute/r1/tables.py` give the piecewise-linear phi_static exactly, so this
  region can be certified exactly with the existing `exact_check.py` machinery.
- Types B, B' are the cleanest new statements: "if the lex-min anchor has profile in the region,
  the request (Y u Z u filler) has no admissible answer". The recorded filler is not canonical
  (the search takes the first winning request), so the request as a function of the profile is
  still to be chosen; natural candidate: the Lemma-A request (seal Y, Z, split the rest evenly
  between PE-side and PF-side). This is a Lemma A / pair-gap type argument and should be
  provable by hand per case of which anchor edges the response replaces.
- Types C, D are R1-style adaptive wins: finite case split over response regions with one
  closure pattern (a row of the quad or triple table) per case; 3 to 15 cases per anchor.
- Type E needs a two-round statement; this is the part furthest from a hand proof.

## 3.4 What is NOT done (honest list)
- **No polytope partition with exact rational certificates.** The table above is a
  classification of grid points by line type, with coordinate ranges, not a partition into
  polytopes; the regions of types B to E interleave on the grid, partly because the search
  returns the first winning request, not a canonical one. Every region other than A therefore
  **depends on the grid** at present.
- The first request as an explicit function of the profile is not fixed for B to E.
- Depth-2 wins use the re-anchoring lookup with grid rounding (every admissible rounding of
  the new triple must be a depth-1 win): grid dependent by construction.
- The potential is 2000 s1 + 40 s2 + s3, not true lex; contradictions found by the engine are
  Phi-decreases. For a Lean proof either the potential itself is used as the minimality
  principle (sound as it is), or each contradiction case must be re-checked to be a lex decrease.
- Not rerun: t = 0.83 beyond §2.


# §4. Towards a certified statement at t = 0.84 (2026-11-24, at most 3 worker processes)

Code: `compute/combine/static_cert.py`, `canon.py`, `d2.py`; data `static_cert_50.json`,
`canon_out.txt`, `lex_0.84_undecided_r100.jsonl`.

## 4.1 The two undecided profiles
(0.38,0.38,0.22) and (0.40,0.38,0.24), depth 2, requests 1/100, 2 processes: **still undecided**: neither finished within about 65 minutes (stopped; sub-results stay in `compute/r1b/memo/`, so a rerun of `py d2.py lex_0.84_undecided_r100.jsonl 2 100 "19,19,11;20,19,12"` continues from there).
The 1/100-profile neighbourhoods were not run (each such anchor needs a fresh depth-2 memo on
the 1/100 profile grid; out of reach with 2 processes in this session).

## 4.2 Line type A, exact **[E]**
Region R = {x >= y >= z > 0, x <= 0.56, x + y + z <= 1.32}, t = 21/25. Lattice boxes of side 1/50
(those meeting x + y + z > 1.32 are left out of numerator and denominator). A box is certified
when ONE pattern of the 4-request triple table has all its request loads <= t at all 8 corners,
with the exact rational weights (`tables.exact_weights`, denominators dividing 840). The loads
are affine in (x,y,z), so the closure holds on the whole box.

**Result: 33.8 % of the volume of R is exactly certified** (certified weight 3520/3 of 10406/3
box units), using 71 patterns; the six most used cover 900 of the boxes. Pattern ids, their label
patterns and the list of uncertified boxes are in `static_cert_50.json`.
- This is a certificate per box (a finite union of boxes, each with one closure), not the exact
  polytope of each pattern: the exact region of pattern p is the polytope
  {W_p(lambda) . mass(x,y,z) <= t for all lambda}, and the certified set is an inner
  approximation of the union of these polytopes by 1/50-boxes. Boxes straddling the boundary
  of the static region are counted as uncertified, so the true static volume is larger.
- What it rests on: completeness is not needed here (a pattern that closes is a proof by
  itself); what is needed is that each table pattern is a valid closure, i.e. the correctness of
  `tables.py` weights (blocker / compatibility construction), which is a hand argument of
  R1_RESULTS and is not formalised.
- The faces z = 0 (a missing pair cell) are not covered by this run (the engine uses a different
  table there).

## 4.3 Line types B to E: canonical request, **not achieved**
- Test of three canonical first requests on the 193 type B / B' anchors of the 1/25 grid
  (floating MILP, `canon_out.txt`): seal Y and Z and put the rest of the budget
  (c1) into X, overflow to PE, PF, PG: wins 88; (c2) half into PE, half into PF: wins 53;
  (c3) one third each into PE, PF, PG: wins 67; at least one of the three wins at 118 of 193.
  So no single affine request serves the region; the winning request depends on the profile in
  a way I have not parametrised (and 38 + 7 + 5 of these anchors were won with other seals).
- No exact rational certificate was produced for B to E. For B a certificate is the
  infeasibility of the adversary system, which contains the disjunctive "no smaller-Phi triple"
  constraints (binaries): an exact certificate needs a case split over those disjunctions
  with one Farkas vector per case; not built.
- Hence: **exactly certified fraction of the region = 33.8 % (type A only)**; the remaining
  66 % rests on floating-point MILP at grid points (1/25 complete, 1/50 complete up to the two
  profiles of 4.1), with first requests found by search.

## 4.4 What a certified statement still needs
1. Decide the two profiles of 4.1.
2. Type A: finer boxes near the boundary (or the exact polytopes) to push 33.8 % up to the full
   static region; the faces z = 0.
3. Types B, B': choose the request per sub-region (c1 on its 88-anchor region first), then a case
   split with exact Farkas certificates; this is the natural next lemma (one request, no closure).
4. Types C, D: exact versions of the per-response closure cases (the R1 `exact_check.py`
   machinery checks stuck profiles, not wins; a win checker has to be written).
5. Type E (11 anchors at 1/25, more at 1/50): a two-round statement; furthest from a proof.
