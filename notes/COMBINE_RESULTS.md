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
