# Programme 5: the critical bridge configuration — joint 3-request MILP and the seed families (PARTIAL; research phase concluded)

Tags: [proved by hand] / [computed exact] / [computed, grid] / [heuristic] / [open]. Units k/14 in Part 1 (members 14,
t = 12 − δ). Code and logs: `compute/programme5/bridge/` (`logs/`), `py -3.14`. Committed as a partial snapshot at wind-down (Part 1 runs were still going; their logs are a
snapshot). LEDGER, Lean644/, notes/sources/ untouched. Nothing here is independently verified.

## 0. Headlines
- Part 1: [open] — joint MILP not concluded (§1).
- Part 2: **no RECORD** [computed exact on the families built]. Best seven-free spectrum-respecting seed family at
  k = 14 has τ = 4 (record 11). The seed is killed by the "2×2 grid six" (§2).

## 1. Part 1 [open]
Joint MILP over the three adaptive requests after Theorem P's K (`part1_joint.py`, units k/14, α = 6.75). The
first h = 0 run printed "CONVERGED: tau* = 0" with an all-zero first request (`logs/part1_joint_a6.75_h0.log`), an
output not interpreted here (likely a model artefact); the rerun at budget 11.98 had not converged at snapshot time
(`logs/part1_run_a6.75.out`). No verdict below 6/7.

## 2. Part 2: realising the seed (k = 14; kill checked at k = 14, 28, 42)
- Spectrum [computed exact]: allowed |B∩B'| avoid (.268k, 5k/14) and (.435k, 10k/21): k = 14 forbids {4};
  k = 28 forbids {8, 9, 13}; k = 42 forbids {12, 13, 14, 19}.
- **The 2×2 grid six** [computed exact, brute force, k = 14, 28, 42; spectrum checked on every pair]: F, G disjoint,
  F = A ⊔ A′, G ⊇ C ⊔ C′ (halves), four K-bridges A∪C, A∪C′, A′∪C, A′∪C′. F's co-edge covers pairs in R1 ∪ P, G's
  covers R2 ∪ P, the four rectangles (F∖K)×(G∖K) tile F×G. All intersections 0 or k/2 (k = 42: 0, 1, 20, 21, 22),
  so the spectrum allows it; adding E gives a good seven. No three of the four K's suffice.
- Seven-free CEGAR from E, F, G (k = 14, n = 31): best τ = 4 (42 members), spectrum on or off [computed exact τ;
  search heuristic]. Shape alone allows τ up to 13–20; seven-freeness, not shape, caps τ.
