# RECORD — exact certification of the R1 route (ML-R1 of FRONTIER §5)

Code `compute/record/` (search: `model.py`, `search.py`, `exact_lp.py`, `certify.py`, `cover.py`,
`certify_grid.py`, `grid_scan.py`; **independent checker `check.py`**, which imports nothing from
the search or from compute/r1, r1b). Nothing committed.

Tags: **[E]** exact rational certificate re-verified by `check.py` (no LP solved there, only
multiplication of stored rationals); **[C]** floating-point (HiGHS) evidence; **[P]** hand proof
written here, not machine-checked; **[F]** fact used, not re-derived (listed in §5).

## 0. Verdict

1. **17/20 is NOT reachable by the depth-1 game, with any potential tried.** [C] The profiles
   x ≈ 0.5625–0.5875, y, z ≤ 0.04 (the lopsided corner, centre (23,1,1)/40 = (0.575, 0.025, 0.025))
   are stuck at t = 0.85 for C = 3, 4, 5, 6, 8, 12, 20, request grids 1/40, 1/80, 1/120, profile
   grids 1/40 and 1/80. (FRONTIER's "0.85 is won" was a 1/20-grid statement; on the 1/20 grid only
   (0.6, 0.05, 0.05) shows it.) The same profile is stuck for t = 0.851 … 0.856 and **at t = 6/7**
   (requests 1/40 with remainder), and won at t = 0.86, 0.87. So the uniform-margin cover at 17/20
   needs depth 2 there (R1b's re-anchoring); that is the open item for 17/20 (§3).
2. **Task (i) at 17/20 is done [E]:** every won profile of the 1/20 grid (class all, C = 4, the
   FRONTIER run) has an exact certificate: 490 of 490 (195 static, 59 Lemma-A, 236 one-request
   wins; the stuck (0.6, 0.05, 0.05) excluded). `py check.py compute/record/grid_scan_0.85_4_20_40/*.json.gz`.
3. **Task (ii) at t = 43/50 = 0.86, C = 8: about 99.9% done, NOT complete.** 9102 octree boxes
   carry exact certificates, and `check.py` accepts all of them: 3338 outside R, 542 static, 5222
   one-request plans. A part of R of volume ≈ 2·10⁻⁴ of the root box (about 0.13% of R) is
   uncovered, in three pockets: (a) the lopsided corner x ∈ [0.54, 0.62], y ≤ 0.12, z ≤ 0.05;
   (b) x ∈ [0.5, 0.56], y ∈ [0.1, 0.27], z ≤ 0.2 (R1's (0.5, 0.2, 0.2) family); (c) a strip along
   the Lemma-A boundary x + 2y = 2 − t near (0.4, 0.37, 0.07). The float game wins at every 1/100
   grid point tested there [C]. What fails is extending one affine request across a box, and the
   boxes reach side 1/512 without succeeding. My reading [H]: the winning plans switch along
   oblique planes with zero margin, so axis-parallel boxes cannot resolve them. The fix is to cut
   pieces along those planes, e.g. x + 2y = 2 − t; not done.
4. **Task (iii):** no extra margin is needed: the cover is closed and exact at t itself, and the
   finite-k loss is read off the certificates' multipliers (§4): f(k,7) ≤ tk + O(1).

## 1. The game that is certified (continuum, k = 1)

Family H, k-uniform, property (7,2), τ(H) > T = tk.
- A good triple exists (Frankl: a 3-wise intersecting family has τ ≤ (k−1)/2 + 1 < T) [F].
- **Anchor**: a good triple E, F, G minimising Φ = C·s1 + s2 (s1 ≥ s2 the two largest pair cells)
  over *all* good triples of H. Sorted cells x ≥ y ≥ z; profile region
  R = {x ≥ y ≥ z ≥ 0, x + y ≤ 1, x + y + z ≤ 3 − 2t} (looseness: Lean `goodTriple_S_le`).
- On a profile polytope P ⊆ R a **plan** is a set SIG of sealed pair cells (requested completely)
  and an affine request d_c(p) on the other cells, checked exactly: 0 ≤ d_c ≤ |c|, Σ d_c ≤ t on P.
- A response K (an edge missing the request; exists since τ > T) has 0 ≤ k_c ≤ |c| − d_c, k_N ≥ 0,
  Σ = 1. For each sealed c the triple (A1, A2, K) through c is good, so
  looseness |c| + |K∩A1| + |K∩A2| ≤ 3 − 2t and minimality max_{i≠j} C·w_i + w_j ≥ C·x + y
  (w = (|c|, |K∩A1|, |K∩A2|), C ≥ 1). The max is split into 6 branches per sealed cell; each
  branch is a root of the certificate. (A degenerate K equal to A1 or A2, possible only when
  |c| = 0, satisfies both rows anyway, so the rows never exclude a real response [P].)
- **Closures** (all loads ≤ t): Q = E, F, G, K + 3 static requests; T_c (c sealed) = A1, A2, K + 4
  static requests; static = E, F, G + 4 requests. Every region is treated as present on P (also
  where its mass is 0), except c ∩ K for sealed c: conservative. On a degenerate box {p} with a
  pair cell identically 0 the checker allows that cell's classes to be absent (needed for the
  z = 0 grid profiles: with z treated as present their static value is 0.8625–1.0 > 0.85).
- Joint variables u = (x, y, z, K) ∈ Q^10: every constraint and every closure load is affine in u,
  so "plan wins on P" is a statement about a union of polytopes in u-space.

**Certificate (per box, per branch root) = a tree.** Node = polytope (named rows, plus strict rows
from the path). EMPTY leaf: Farkas (y.b < 0) or Motzkin (y.b ≤ 0 with positive weight on a strict
row) multipliers. PATTERN node: a closure pattern (one label family per class); the checker
verifies cross-intersection on all candidate pairs (membership union = all kept edges), rebuilds
the load rows Σ_c m_c(u)·min_{L∈F_c} λ(L) for every λ of the arrangement vertex set Λ_r (recomputed
independently: |Λ_3| = 10, |Λ_4| = 101), and for **every** load row requires either a dual
certificate (row ≤ t on the closure of the node) or a child node = node ∩ {row > t}. Hence
node ⊆ {pattern closes} ∪ children. The cover: octree leaves of [0,1]×[0,1/2]×[0,1/2] ⊇ R; the
checker verifies that the leaves tile the root box, that each certificate's box is its leaf, and
each leaf is `outside` (box ∩ R = ∅, Farkas), `static`, or `plan`.

## 2. Results

| item | t | C | what | status |
|---|---|---|---|---|
| grid wins, 1/20 grid, class all | 17/20 | 4 | 490/490 won profiles | **[E]** |
| depth-1 stuck set | 17/20 | 3–20 | lopsided corner x ≈ 1 − t/2, y, z small | stuck **[C]** |
| depth-1 stuck at (0.575, 0.025, 0.025) | 0.851–0.856, 6/7 | 8 | | stuck **[C]** |
| float grid scans, class all, depth 1 | 0.86 (1/50 grid), 6/7 (1/42) | 8 | all won | **[C]** |
| continuum cover | 43/50 | 8 | 9102 boxes certified, ≈0.13% of R open (3 pockets) | **[E]** on covered part |

Run log: first pass `--start 4 --maxlevel 3 --lden 50` (15162 s, 22 cores), then a retry of the
failed boxes with local solves on the 1/100 grid (cells kept > 0), stopped part-way. Raw failure
logs are in `certs_43_50_C8/index.json["failed"]`; `py check_leaves.py certs_43_50_C8` checks
every leaf and measures what is uncovered. `py check.py certs_43_50_C8` (full tiling check) fails
until the pockets are closed.

## 3. What remains

- **17/20 (and anything ≤ 6/7):** the lopsided corner needs a second adaptive round. R1b's depth-2
  game is a lookup on grid positions; a continuum version needs covers of the (q', v) position
  space (4 parameters) with the same tree certificates, the "q' is won" condition being affine in
  (p, K). Not built. Without it the R1 route gives nothing below the threshold t1 with
  6/7 < t1 ≤ 0.86 (float).
- Facts [F] of §5 to be written up / formalised (none is computational).
- An independent second implementation of the checker (it is ~350 lines; reviewing it is the
  audit).

## 4. Finite k (task iii) [P]

At finite k everything is the continuum system with right-hand sides moved by ≤ 1/k: unsealed
request amounts are rounded down (capacity rows +1/k each, budget still ≤ T), both looseness rows
read S ≤ 3 − 2t + 1/k; the minimality rows, sums and box rows are exact in integers. Walk the tree
with threshold t + ε at PATTERN nodes (go to the child of a row exceeding t + ε). At a dual leaf
the row is ≤ t + Y/k where Y = sum of the multipliers on the moved rows; at a Motzkin leaf the path
rows hold with margin ε, contradiction once ε > Y_mot/k; a Farkas leaf (y.b < 0) stays infeasible
for k > Y/|y.b|. Finally the fractional label split of each closure is rounded, costing ≤ 13·7 = 91
points per request. So with Ycov, Ymot, k0 printed by `check.py`:
  **τ(H) ≤ tk + max(Ycov, Ymot) + 92 for k > k0**, i.e. f(k,7) ≤ tk + O(1), with explicit constants
(on the certified part at 43/50: Ycov = 21.83, Ymot = 0, k0 = 2.76·10⁶, so the additive constant is ≤ 114 for k > k0; the large k0 comes from Farkas leaves with a tiny gap |y.b|.)

## 5. Facts used, not machine-checked

- [F1] cost of a fixed label pattern = max over the simplex of Σ_c m_c min_{L∈F_c} λ(L) (LP
  duality), attained at a vertex of the arrangement {λ(A) = λ(B)} (concave piecewise linear).
  Only the *validity* of the patterns used matters (no completeness of the tables is needed for
  wins).
- [F2] a pattern with all loads ≤ T yields 3 (resp. 4) requests whose responses, together with the
  kept edges, have no 2-cover (every 2-cover consists of two old points covering the kept edges;
  both lie in a common request).
- [F3] Frankl's bound for good-triple existence; Lean `goodTriple_S_le` (looseness).
- The game model of R1 §1 (sealing convention), unchanged.

## 6. Reproduce

    py -3.14 grid_scan.py 0.85 4 --pden 20 --dden 40           # float scan with requests
    py -3.14 certify_grid.py out/scan_0.85_4_20_40.jsonl 17/20 4 20
    py -3.14 check.py grid_scan_0.85_4_20_40/*.json.gz
    py -3.14 grid_scan.py 0.86 8 --pden 50 --dden 50
    py -3.14 cover.py 43/50 8 out/scan_0.86_8_50_50.jsonl 50 --start 4 --maxlevel 3 --lden 50
    py -3.14 check.py certs_43_50_C8
