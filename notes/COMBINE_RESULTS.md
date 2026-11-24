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
