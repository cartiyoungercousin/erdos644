# Programme 5: the grid six as a closure move — drop-one frames after the critical bridge triple

Tags: [proved by hand] / [computed exact] / [computed, grid] / [heuristic] / [open]. Units k/14 (members 14,
t = 12 − δ, δ = .002 unless stated, i.e. t = .85700). Code and logs: `compute/programme5/gridsix/` (`logs/`),
`py -3.14`, OR-Tools SCIP for every infeasibility claim (HiGHS is never used for one). Nothing committed. Nothing
here is independently verified.

## 0. Headline (pre-registered form)
**STILL 6/7: the adversary avoids grid sixes by moving K's spare mass onto E′ and keeping a 0⁺ "hub" of K∩E′ in
his answers.** The certificate behind this is only partial: §4–§5 say how far it goes.
- **The old adversary line is broken** [computed exact, §3]. The joint MILP's K = A₇ ∪ B₇ loses as follows:
  - R1 = Y₄.₉₉₈ ∪ B (and Y₅ ∪ B₆.₉₉₈) closes against every legal M1 by a static drop-one finish;
  - so does every K = A_a ∪ B₇ ∪ (spare on outside points), a ∈ {6, 6.083, 20/3, 6.7, …, 7}, via
    R1 = X_{t−a} ∪ A;
  - this holds for t from 11.97 to 11.998 (the whole range where S* is known).
  - The closure needs both the grid frame (drop E) and the drop-G frame. With either one alone, an M1 escapes.
- **Repaired line** [computed exact on the breaking requests; whole grid open]:
  - K_e = A(20/3) ∪ B(7) ∪ (E′∩K)(1/3).
  - The same works with spare 7 − a on E′ at a = 6.7 and 6.75, and partly at 6.8 and 6.9 (§4).
  - Answer to R1 = Y₄.₉₉₈ ∪ B: M1 = X₆ ∪ A₃.₇₅ ∪ Gd₂.₃₃₁ ∪ Ep₁.₆₉₃ ∪ (E′∩K)₀₊ ∪ Y_ε ∪ out.₂₂₃.
  - Answer to R1 = X₅.₃₃₁ ∪ A: M1 = X.₆₆₉ ∪ Y₅ ∪ B₅.₄₄₁ ∪ Fd.₅₈₃ ∪ Gd.₁₁₆ ∪ Ep₂.₁₉₂ ∪ (E′∩K)₀₊.
  - Answer to R1 = A ∪ X₃ ∪ B₁ ∪ Y₁.₃₃₁: M1 = X₂.₄₄₂ ∪ Y₂.₈₉₁ ∪ B₄.₆₆₇ ∪ Fd₁ ∪ (E′∩K)₁/₃ ∪ Ep₂.₆₆₇.
  - Each is S*-legal, every static drop-one finish needs ≥ 11.999–12.03 > t, and each is ADV in the E-frame game
    (jm.stage2, SCIP; sound model, `recheck_e.py`).
- **Why it works** [heuristic reading of the certificates]:
  - A point h ∈ E ∩ K ∩ M1 is a hub. In the drop-G frame (E, F, K, M1) every pair (h, f) with f ∈ F∖M1 is alive;
    in the drop-F frame every pair (h, g) with g ∈ G∖M1 is alive.
  - So 0⁺ of K∩E′ inside M1 forces the drop frames that broke the old line to cover all of F∖M1 (or G∖M1) again.
    Their values return to 12.0 = 3t + O(δ), the same knife edge as everywhere else.
  - K's spare on outside points gives a weaker hub: an outside point of K pairs only with X or with Z.
- Not "NOT EXPRESSIBLE": the grid-six lemma is a cell-level alive-pair condition (§1), first order with 0⁺ cells.

## 1. The lemma in the game's language [proved by hand]
- **Lemma G (frame criterion).** A set Q of members is a good seven iff no atom pair (α, β) of Q's Venn diagram
  (α = β allowed, atoms of mass 0⁺ count) is *alive*, i.e. has every member of Q containing α or β.
  - For Q = {F, G, M₁, …, M_r}, F ∩ G = Z: the alive pairs are the (f, g) ∈ (F∖G) × (G∖F) outside every rectangle
    (F∖M_i) × (G∖M_i), plus Z × ⋂_{i : z ∉ M_i} M_i.
  - The grid six is r = 4 with four rectangles tiling F × G.
  - Equivalently, the co-types σ(p) = {i : p ∉ M_i} on F and on G are cross-intersecting.
- **Lemma G2 (forced avoidance).** |F∖M| + |G∖M| ≥ k − |F∩G| for every member M. So in an F,G-frame every answer
  kills a rectangle of semi-perimeter ≥ (1 − z)k, of which her request fixes only ≤ t.
  - This is the first-order content of the grid six. Frames that keep E cannot see it. It punishes answers that
    put mass outside F ∪ G.
- **Frames.**
  - E-frame: E, F, G, K, M₁, M₂, M₃ (the joint MILP).
  - Drop-one frames after M₁: three of E, F, G, K + M₁ + three static requests, or E, F, G, K, M₁ + two.
  - The drop-E frame {F, G, K, M₁, …} is the grid frame.
  - Fresh outside points are in no alive pair of these frames (E∩F∩G = E∩F∩K = E∩G∩K = F∩G∩K = ∅). K's own
    outside points pair only with X or Z, and K∩E′ points pair with F or G (the hub).
- **The grid six alone cannot be forced** [proved by hand + computed exact]:
  - from F, G alone, four static requests leave uncovered area ≥ 1 − 4(t/2)² > 0 for t < 1;
  - after Theorem P's K, the static four-cover of the grid L-shape needs t ≥ 12.6 (`t_static.py`).
  - Every forced grid six therefore uses the adversary's own avoidance (Lemma G2).

## 2. Theorem P's passive adversary loses once E may be dropped [computed exact; brute force on sets]
- Passive answers M = (X∪Y∪A∪B) ∖ R ∪ outside avoid Fd, Gd and everything outside the live cells.
  - In the grid frame F, G, K + four answers, four static requests of size 11.6 close (`cover.py`):
    A ∪ X₄.₆, B ∪ Y₄.₆, A ∪ B₂.₈ ∪ X₁.₄ ∪ Y.₄, A ∪ B₄.₂ ∪ Y.₄, plus Z.
- Brute force (`bf_passive.py`, k = 70, T = 59, t = .843 < 6/7): {F, G, K, M₁..M₄} has no 2-transversal, while
  {E, F, G, K, M₁, M₂, M₃} has one.
- These passive answers are not S*-legal. Theorem P stays true as stated (sevens ⊇ E, F, G, K), but "no depth
  closes" does **not** extend to closures that discard E.

## 3. Drop-one frames against the joint-MILP certificates and the old K [computed exact]
- `run_states.py`: exact static values of the four drop-one frames for all 5 139 certified E-frame ADV states.
  - 4 286 survive every frame.
  - Grid coverage drops to 11 356 / 11 616 first requests on the k/14 grid and 110 756 / 113 111 on the k/28 grid
    (`cover_check.py`).
  - The 260 / 2 355 losers are the Lemma-Φ family and its mirrors: R1 ⊇ almost all of Y ∪ B, or of X ∪ A + dead.
  - The certified escapes X(6−d) ∪ A ∪ Y_ε ∪ out have drop-G static value 10.5–10.7.
- **Exact stage-1 CEGAR** (`stage1.py`, `stage1g.py`).
  - His M1 is continuous and S*-legal against E, F, G, K.
  - Her moves are relative full-support static plans of every drop-one frame. Their request sizes are linear in
    M1, and partial-support plans carry "atom must be empty" switches.
  - INFEASIBLE (SCIP) = every M1 is closed.
  - Checker `verify_stage1(g).py` (independent code): plan coverage, plus a 0.25/0.5 grid and 2–4 M random M1.

  | K | R1 | result | check (worst plan − t) |
  |---|---|---|---|
  | A₇ ∪ B₇ | Y₄.₉₉₈ ∪ B₇ | INFEASIBLE (43 / 39 plans) | OK, ≤ −.03 |
  | A₇ ∪ B₇, t = 11.97 | Y₄.₉₇ ∪ B₇ | INFEASIBLE (55) | OK, ≤ −.058 |
  | A₇ ∪ B₇ | Y₅ ∪ B₆.₉₉₈ | INFEASIBLE (37) | OK, ≤ −.069 |
  | A₆.₈₃₃ ∪ B₇ ∪ out.₁₆₇ | Y₄.₉₉₈ ∪ B₇ | INFEASIBLE (67) | OK, ≤ −.007 |
  | A_{20/3} ∪ B₇ ∪ out_{1/3} | X₅.₃₃₁ ∪ A;  A ∪ X₃ ∪ Y₁.₃₃ ∪ B₁ | INFEASIBLE | OK, ≤ −.035 / −.005 |
  | A_a ∪ B₇ ∪ out, a ∈ {6, 6.083, 6.7, 6.75, 6.8, 6.9, 7} | X_{t−a} ∪ A | INFEASIBLE | not re-verified |
  | A₇ ∪ B₇ | X₃.₉₉₈ ∪ A ∪ Gd₁;  X₁ ∪ Y₃.₉₉₈ ∪ B;  X₃.₉₉₈ ∪ Y₅ ∪ B₃ | M1 escapes (static > t, ADV) | — |

  - Frame ablation, K = A₇ ∪ B₇, R1 = Y ∪ B (`FRAMES_OFF`). Without the grid frame, or with only drop-G, or with
    only the grid frame + E-static, an M1 escapes. The plans used are mostly grid-frame (18) and drop-G (15).
- **Which K can he use?** [proved by hand]
  - Her class-A first request can put its whole extra 1 − δ on F′, which forces |K∩F′| ≤ 7 + δ.
  - The E-frame forces |K∩F′| > 7 − δ: otherwise R1 = Y ∪ B, then X₃ ∪ A, X₃′ ∪ A close, spectrum-free. It also
    forces |K∩G′| > 6 − δ, and S* then gives |K∩G′| ∈ (6 − δ, 6.083] ∪ [20/3, 7 + δ].
  - So K = A_a ∪ B₇ ∪ spare (7 − a), with the spare on E′ and/or outside points.
  - The middle band a ≤ 6.083 was missed in a first draft of this note.

## 4. Spare on E′ (the repaired family) [computed exact per point]
`ascan.py` covers R1 ∈ {Y ∪ B, X ∪ A, A ∪ X₃ ∪ B₁ ∪ Y}, spare on E′; `recheck_e.py` redoes the E-frame check soundly:
jm gets only E′∖K, and the K∩E′ points are left out of his answers.
- a ∈ {20/3, 6.7, 6.75}: all three requests are refuted (statically invulnerable M1 + E-frame ADV).
- a ∈ {6.8, 6.9}: X ∪ A and A ∪ X₃ ∪ B₁ ∪ Y are refuted. The Y ∪ B runs did not finish.
- The Y ∪ B runs for a ∈ {6, 6.083} also did not finish (all runs were stopped at wind-down).
- a ∈ {6, 6.083} (middle band):
  - A ∪ X₃ ∪ B₁ ∪ Y is refuted.
  - X_{t−a} ∪ A is statically invulnerable, but jm returns REQ. That REQ is in the restricted model (he may not
    use K∩E′ points), so it is not a certified closure [open].
- Whole-grid certification of K_e (every first request, then continuous) is not done [open].

## 5. Whole-grid status of the intermediate repair K* = A_{20/3} ∪ B₇ ∪ out_{1/3} [computed exact per state]
- `kstar_map.py` maps the 5 139 old states to K*: 3 985 survive (static > t and stage2 ADV). They refute
  10 799 / 11 747 k/14 first requests and 107 255 / 113 434 k/28 first requests.
- `kstar_resid.py` (exact per request) on the k/14 rest: 48 refuted (invulnerable + ADV), 1 invulnerable with an
  E-frame REQ.
- 7 requests *close* (all contain A; `logs/kstar_close_*.json`, two re-verified):
  - X₅.₃₃ ∪ A;
  - A ∪ X₃ ∪ Y₁.₃₃ ∪ B₁; A ∪ X₃ ∪ Y₂ ∪ B.₃₃; A ∪ X₃ ∪ Y₁.₃₃ ∪ Ep₁;
  - A ∪ Y₁.₃₃ ∪ B₁ ∪ Ep₃; A ∪ Y₃.₃₃ ∪ B₁ ∪ Ep₁;
  - A ∪ X₃.₃₃ ∪ Ep₁ ∪ Fd₁.
- So K* is broken, which is why the line moved its spare onto E′ (§4). The run was stopped with 552 requests left.

## 6. Depth 2 and other sevens
- Depth-2 drop frames (`depth2.py`, `run_depth2.py`) [heuristic for her; his refutations exact]. After M1 she
  requests R2 → M2, then closes by |U| ≤ t in the E-frame or by a five-member drop-one frame with two static
  requests.
  - On 81 sampled α = 7 states × 42 her-R2: 80 states refute every R2.
  - State [6, 0, 7, 1, 0, 0, 0, 0] leaves one R2 unrefuted by his candidates [open].
- Other sevens in the failed seeds (BRIDGE Part 2 CEGAR logs).
  - "C1 C2 E E E E + K" is F, G + five bridges, i.e. an F,G-frame (Lemma G), the drop-E frame at depth ≥ 5.
  - "E E E K K K + E" has no anchor: seven answers, outside every frame of the game [open].

## 7. What is left
1. Certify K_e on the whole first-request grid (k/14, k/28, then continuous) with drop-one statics + E-frame. The
   jm pipeline must be generalised to the cells E′∩K and K-outside (here they are folded out conservatively).
2. A K-level CEGAR: the plans are linear in (a, spare split, |K∩F′|) as well, so one adversary MILP can cover a
   whole interval of K. If every K closes, the critical limit triple closes at t = 12 − δ.
   - Then the critical window (q, y) must be handled and the S-game rerun. The move is monotone in S, so it stays
     valid as S* shrinks.
3. Her other class-A first requests (extra split between F′ and E′, which shrinks the room for the E′ hub).
   Depth-2 drop frames exactly.

## 8. Files (`compute/programme5/gridsix/`)
- `cover.py` (cell-level static cover MILP), `frames.py`, `t_static.py`, `bf_passive.py`.
- `run_states.py`, `cover_check.py` (§3); `advsearch.py`, `run_adv.py`, `greedy.py` (heuristic M1 search,
  superseded by stage1).
- `stage1.py`, `stage1g.py` (exact CEGAR; `ALPHA`, `FRAMES_OFF` env), `verify_stage1.py`, `verify_stage1g.py`.
- `t_jm_check.py`, `t_jm_a6667o.py`, `recheck_e.py` (E-frame checks).
- `kstar_map.py`, `kstar_cover.py`, `kstar_resid.py`, `ascan.py`, `depth2.py`, `run_depth2.py`.
- Main logs: `states_static.jsonl`, `stage1*_*.json` (plans), `kstar_states.jsonl`, `kstar_resid*.jsonl`,
  `ascan*.jsonl`, `recheck_e*.jsonl`.
