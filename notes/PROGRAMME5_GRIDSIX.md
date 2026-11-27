# Programme 5: the grid six as a closure move — drop-one frames after the critical bridge triple

Tags: [proved by hand] / [computed exact] / [computed, grid] / [heuristic] / [open]. Units k/14 (members 14,
t = 12 − δ, δ = .002 unless stated, i.e. t = .85700). Code and logs: `compute/programme5/gridsix/` (`logs/`),
`py -3.14`, OR-Tools SCIP for every infeasibility claim (HiGHS is never used for one). Nothing committed. Nothing
here is independently verified.

## 0. Headline (pre-registered form)
> **Superseded by §9 (round 2, partial).** K_e below is broken by requests that contain the hub; see §9.5 for the
> current status.

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

## 9. Round 2 (bottleneck attack on K_e) — PARTIAL, wound down mid-run

### 9.1 K_e = A(20/3) ∪ B(7) ∪ (E′∩K)(1/3) is broken [computed exact; independently re-checked]
- `screen_ke.py` ran 70 first requests against K_e: exact stage-1, then a sound jm check.
- Two requests that contain the hub E′∩K in full close statically against every legal M1:
  - R1 = X₄.₉₉₈ ∪ A ∪ (E′∩K): 28 plans; `verify_stage1g`: 0 coverage violations, worst plan ≤ t − .026;
  - R1 = Y₅ ∪ B₆.₆₆₅ ∪ (E′∩K): 46 plans; worst plan ≤ t − .018.
  - Certificates: `logs/kec_*.json`.
- The other 68 requests are refuted, or statically invulnerable with an uncertified jm REQ
  (`logs/screen_ke1.jsonl`). So requesting the hub removes it from M1, and the line of §0 does not survive.

### 9.2 K-level CEGAR over every forced K (`kstage.py`) [computed exact per finished box; NOT re-verified]
- Range: a ∈ (6 − δ, 6.083] ∪ [20/3, 7 + δ], kb ∈ (7 − δ, 7 + δ], spare split freely between E′ and outside.
- Families of her second request: X∪A∪hub∪K-outside, Y∪B∪hub∪K-outside, X∪A, Y∪B.
- Finished boxes:

  | box (a, e = |K∩E′|) | result |
  |---|---|
  | a ∈ [5.998, 6.0835], e ∈ [0, .35] | INFEASIBLE: every K closes |
  | a ∈ [5.998, 6.0835], e ∈ [.35, .70] | INFEASIBLE: every K closes |
  | three high boxes (bH9, bH11, bH12) | empty (infeasible at iteration 0) |

- Unfinished at wind-down:
  - middle band, e ∈ [.70, 1.01]: margin μ = .004 at it 15;
  - high band, a ∈ [6.667, 7.002] × e ∈ {[0, .12], [.12, .24], [.24, .34]}: 9 boxes;
  - μ was falling everywhere, to .004 in bH7, bH8, bH10;
  - no box returned "K SURVIVES"; logs `logs/kstage_b*.out`.
- Not re-verified: a K-level verifier (grid over K × M1) still has to be written.

### 9.3 Partial ascan outcomes (round 1, recorded at wind-down)
Spare on E′ means the line K = A_a ∪ B₇ ∪ (E′∩K); all values are [computed exact] per run.
- a = 6.0:
  - spare outside: X∪A and A∪X₃∪B₁∪Y close;
  - spare on E′: A∪X₃∪B₁∪Y is refuted (ADV);
  - spare on E′: X∪A and Y∪B are statically invulnerable, but the jm verdict is REQ in the restricted model, so
    not certified.
- a = 6.083: spare outside, X∪A and A∪X₃∪B₁∪Y close; spare on E′, A∪X₃∪B₁∪Y is ADV and X∪A is
  REQ (uncertified); Y∪B did not finish.
- a = 6.75 / 6.9 / 7.0: as in §3–§4. At 6.9 the spare-E′ Y∪B run did not finish.
- These spare-on-E′ escapes do not use the hub-containing requests of §9.1. §9.2 is the test that does.

### 9.4 Conditional S-game (`sgame_cond.py`): no output before the stop.

### 9.5 Status and how to resume
- Headline unchanged in form: **STILL 6/7 is no longer supported by an adversary line.**
  - The last explicit line (K_e) is broken.
  - Every K in the middle band with |K∩E′| ≤ .7 closes.
  - The rest of the K range is open, with margins falling.
  - No certified new cap yet.
- Resume, step 1: rerun the unfinished boxes, e.g.
  `py -3.14 kstage.py bH1 XAH,YBH,XA,YB 0.002 6.6666,6.75,0,0.12`. The boxes are listed at the top of each
  `logs/kstage_b*.out`; drop more boxes if needed.
- Step 2: write `verify_kstage.py` (grid over K × M1 against the saved plans `logs/kstage_*.json`; INFEASIBLE runs
  dump them).
- Step 3: if every box is INFEASIBLE, handle the critical window (make X, Y variables in `kstage.py`). Then run
  `py -3.14 sgame_cond.py 168 3 0.0 0.855 0.8572 5` (conditional S-game: critical triples marked closed) and
  replace the condition by the proved move.
- Step 4: if some box SURVIVES, read its K and M1 from the log. That is the adversary's line; state the lemma
  needed to beat it.
- `stage2g.py` (depth-2 drop-frame test for a fixed M1, R2) is written and has not been run.
- Nothing committed.

## 10. Round 3: K-level boxes finished, checker, conditional S-game — STILL 6/7

### 10.0 Headline (pre-registered form)
**STILL 6/7: the adversary avoids grid sixes by answering the critical DUMP away from the limit triple.**
- Every K closes at the limit critical triple [computed exact, independently re-checked]; see §10.1.
- But the S-game fixed point does not move even when the whole limit window is declared closed [computed, grid;
  §10.3]. Its surviving DUMP answers fill a two-dimensional region, most of which is out of reach of class-A
  first requests.
- So no certified t* < 6/7.

### 10.1 K-level CEGAR: no K survives at the limit triple [computed exact; re-checked]
- Setup:
  - triple cells X = 6, Y = 5, Z = 0⁺ (units k/14), t = 11.998;
  - her class-A first request has its extra all on F′;
  - K ranges over a ∈ (6 − δ, 6.083] ∪ [20/3, 7 + δ], kb ∈ (7 − δ, 7 + δ], with any split of the spare between E′
    and outside points;
  - second requests come from 4 relative families;
  - finishes are static drop-one frames after M1.
- Every box returned INFEASIBLE (SCIP):

  | box (a; e = \|K∩E′\|) | plans | `verify_kstage.py` |
  |---|---|---|
  | [5.998, 6.0835]; [0, .35] (bM1) | 71 | OK: indep. SCIP INFEASIBLE, 90 K × 20 000 M1, worst ≤ t − .061 |
  | [5.998, 6.0835]; [.35, .70] (bM2) | 87 | OK, worst ≤ t − .015 |
  | [5.998, 6.0835]; [.70, 1.01] (bM3) | 159 | OK, worst ≤ t − .085 |
  | [6.6666, 6.75]; [0, .34] (hA1) | 212 | OK, worst ≤ t − .088 |
  | [6.75, 6.85]; [0, .34] (hA2) | 214 | OK, worst ≤ t − .049 |
  | [6.85, 6.95]; [0, .34] (hA3) | 199 | OK, worst ≤ t − .035 |
  | [6.95, 7.002]; [0, .34] (hA4) | 167 | OK, worst ≤ t − .066 |

- What `verify_kstage.py` checks (code independent of `kstage.py`, `stage1g.py` and `cover.py`):
  - plan coverage: 0 violations in every box;
  - a fresh SCIP model with escape margin 0, stricter than the CEGAR's 10⁻⁵: INFEASIBLE in every box;
  - a sampled grid of K × M1.
- Hand-proved inputs:
  - the forced ranges kb > t − y and a > t − q (E-frame, spectrum-free closures);
  - kb ≤ 7 + δ (from her first request).
- **So at the limit triple (q, y, z) = (3/7, 5/14, 0⁺), t = .85700, the class-A line closes for every K.**
- Off the limit point (`kstage_w.py`: X, Y, Z as real cells, forced ranges in terms of q, y), triple (6, 5, 0.5):
  all four K boxes are INFEASIBLE [computed exact, SCIP; not yet re-checked by `verify_kstage.py`, which assumes
  the limit cells].
  - Triples with q + y + z > t admit no class-A first request at all (the K range is empty there).

### 10.2 Why that does not move the cap [computed, grid; `crit_answers.py`, `sgame_cond.py`]
- At t = .855 and G = 168, take the critical pairs q = 69..73 /168.
- For the DUMP split whose survivors have the least z, about 800 answers survive at each q:
  y ∈ [60, 96]/168 and z ∈ [0, 25]/168, e.g. at q = 72 with (h1, h2) = (96, 25).
- They include y > 1/2, and they include y + z > t − q, where X ∪ Y ∪ Z exceeds t.
- Every split leaves survivors with y + z up to h1 + h2 ≥ 2 − t − q = .717 > t − q.
- `sgame_cond.py 168 3 0.0`: the old S-game, with every critical-window triple at z = 0 marked closed. Result:
  - ADVERSARY at t = .85500, .85555, .85610, .85665, with S* unchanged = [0-45, 60-73, 80-167]/168;
  - requester at .85720, as before.

### 10.3 The adversary's line, and the lemma a proof would need
- **Line:** at a critical pair q (q ≈ 3/7, i.e. 69–73/168), answer the balanced DUMP with a medium/heavy
  E∩G-trace y and a small F∩G-trace z.
  - This works either with y + z > t − q, so that no request contains X ∪ Y ∪ Z (and our class-A closures do not
    apply), or with z ≥ 0.5k/14 in the parts not yet certified.
  - Everything else follows the old S-game: S* = [0, .268] ∪ [5/14, .435] ∪ [10/21, 1).
- **Needed lemma (first order):** for every triple (q, y, z) with q in the critical window and (y, z) in the old
  survivor set, so y ∈ [5/14, 4/7], z ∈ [0, .15], y + z ≤ 2 − t − q, a closure valid under spectrum S*.
  - When q + y + z ≤ t: the K-level class-A closure of §10.1, extended over (y, z). It is numerically promising;
    at z = 0.5k/14 all four boxes close.
  - When q + y + z > t: a new first request that does not contain X ∪ Y ∪ Z (e.g. X ∪ Z + most of Y, or the
    drop-one frames applied to a non-class-A first answer). Nothing here covers it.

### 10.4 Files and resume
- New code: `verify_kstage.py`, `kstage_w.py` (env `QYZ=q,y,z`), `crit_answers.py`, `sgame_cond.py`.
- Logs: `logs/kstage_{bM1,bM2,bM3,hA1..hA4}.*`, `logs/verify_kstage_*.out`, `logs/kstagew_z*.out`,
  `logs/crit_answers_t855.out`, `logs/sgame_cond_z0.out`.
- Resume:
  1. Extend `kstage_w.py` to treat (q, y, z) as box variables, as K already is: cover the survivor set with
     q + y + z ≤ t.
  2. Design non-class-A first requests for q + y + z > t and add them as families.
  3. Replace the condition in `sgame_cond.py` by the certified closure set and rescan t.
- Nothing committed.

## 11. Round 4: what the S-game actually needs, and the general CEGAR — PARTIAL (runs in progress at write-up)

### 11.0 Headline (pre-registered form)
**STILL 6/7 (no certified t*).** The adversary's surviving line at t = .855 is the old S* = [0-45, 60-73, 80-167]/168
together with the critical pair q = 73/168.
- A closure of all its surviving answers would give t* ≤ .855 [computed, grid; conditional].
- It is not yet certified: §11.3 lists what is closed and what is open.

### 11.1 Exactly which closures move the S-game [computed, grid; `sgame_cond.py`, env YMAX / QHI]
Each row adds one conditional move to the unchanged S-game (G = 168, ν = 3): every triple with q in the stated set
(any y, z) is declared closing.

| q declared closing | t = .855 | .856 | .857 |
|---|---|---|---|
| (t/2, min(3−3t, 9/7−t)] (= {72}) | ADV, S* = [0-45,60-71,73,80-167] | ADV (same) | ADV (same) |
| (t/2, 3−3t] (= {72, 73} at .855) | **requester**, S* = [144-167] | ADV (only 72 is in the window) | — |
| (t/2, .47] or (t/2, 1/2] | **requester** | — | — |

- So the cascade starts iff pair q = 73/168 = .4345, the top of S*'s middle band, also leaves S*. That happens
  only for t ≤ (3 − 73/168)/3 = .8552.
- Hence the best this programme can give within the range where S* is known (t ≥ .855) is **t* ≤ .855**,
  *conditional* on closing every surviving answer at q = 72 and q = 73.

### 11.2 The answers to close [computed, grid; `crit_answers2.py`, `logs/crit_survivors_t0.855.json`]
- Best DUMP split, minimising the survivors not reachable by a class-A first request:
  - q = 72: split (60, 61), 115 survivors;
  - q = 73: split (60, 60), 78 survivors.
- Up to the E↔F symmetry (y ↔ z), every survivor is (q, y, z) with y ∈ {60, 61}/168 (y = 61 only at q = 72) and
  z ∈ [0, 38]/168.
- In k/14 units: q ∈ {6, 6.083}, y ∈ {5, 5.083}, z ∈ [0, 3.17], t = 11.97.
- Class-A covers z ≤ t − q − y (≤ .97); the rest (z up to 3.17) needs a first request without all of Z.

### 11.3 `kgen.py`: general exact CEGAR
- Features:
  - variable triple box (q, y, z);
  - a chosen first-request type R0 (classes A / A_G / noZ / partY / partYnoZ / partX);
  - every K (amounts on every cell R0 leaves) and 8 R1 families;
  - K-level static frames ({E,F,G,K}+3 and drop-one +4), which replace the hand-proved forced ranges;
  - M1-level drop-one frames;
  - the "dead atom" rule (an atom in every member of a frame pairs with a fresh common point of the later answers,
    so it must be empty).
- Status when stopped (δ = .03, t = 11.97; SCIP; no box finished, no SURVIVES found):

  | run | box / point | R0 | stopped at |
  |---|---|---|---|
  | a1 | q = 6, y ∈ [5, 5.083], z ∈ [0, .45] | A | it 30, μ .23 |
  | a2 | q = 6, y ∈ [5, 5.083], z ∈ [.45, .97] | A | it 25, μ .76 |
  | a3 | q = 6.083, y = 5, z ∈ [0, .45] | A | it 35, μ .06 |
  | a4 | q = 6.083, y = 5, z ∈ [.45, .887] | A | it 45, μ .06 |
  | b1 | (6, 5, 2.0) | noZ, 8 families | it 15; XAH/XAZ/YBZ escape at some K, others close |
  | b2 | (6, 5, 3.17) | noZ, 8 families | it 15; XAZ/YBZ escape at some K |
  | sanity | (6, 5, 0⁺), δ = .002 | A (no hand ranges) | it 65, μ .004 |

  - kgen is much slower than kstage (2–3 min per iteration): with no hand-proved K ranges, the K-level plans have
    to carve out the whole K space.
  - The plans found are lost (they are dumped only on exit). Resuming means rerunning from scratch. Add the hand
    ranges as an option to speed it up.
  - Resume commands:

    `py -3.14 kgen.py a1 A XAH,YBH,XA,YB 6,6,5,5.0834,0,0.45 0.03` (likewise a2–a4, the boxes in the table), and

    `py -3.14 kgen.py b1 noZ XAH,YBH,XA,YB,XAY,YBX,XAZ,YBZ 6,6,5,5,2,2 0.03`.
- Caveat: kgen INFEASIBLE certifies only box ∩ {R0 valid}; the class-A boxes say nothing about z > t − q − y.
- **Earlier exact results still stand**:
  - §10.1: every K closes at the limit triple;
  - `verify_kstage.py`, generalised (env QYZ), certifies the four kstage_w boxes at (6, 5, 0.5): independent SCIP
    INFEASIBLE, 0 coverage violations, sampled worst ≤ t − .048 (`logs/verify_kstagew_*.out`).

### 11.4 Resume
1. Rerun the kgen boxes to completion (logs `logs/kgen_*.out`; certificates are dumped as `logs/kgen_*.json` on exit).
   A kgen-specific independent checker is still to write: adapt `verify_kstage.py` to the 13-cell model and the
   K-level plans.
2. Cover z ∈ [0, 38]/168 completely:
   - class-A boxes for z ≤ t − q − y;
   - noZ / partY boxes beyond, adding R0 types if b1/b2 report SURVIVES (then read its K and M1 lines: they are
     the adversary's line).
3. Once every survivor at q = 72, 73 is certified closed, replace the YMAX/QHI condition in `sgame_cond.py` by
   the certified set. Rerun at t = .855 and report t* ≤ .855.
- Nothing committed.

## 12. Round 5: certified closures at q = 72, 73 — PARTIAL (runs continuing in the background)

### 12.0 Headline (pre-registered form)
**STILL 6/7 (no certified t* yet).** No surviving answer has been shown to escape, but the closures of the
q = 72, 73 survivors are not finished. §12.3 says what is certified, what is running, and how to finish.

### 12.1 kgen upgrades
- **K-range option** (env `KRANGE`):
  - `hand` imposes the E-frame-forced ranges |K∩F′| > t − y and |K∩G′| > t − q;
  - `comp` restricts K to the complement and uses K-level plans only.
  - A `comp` certificate makes the `hand` runs rigorous without the hand lemma.
- **Incremental plans**: every plan is appended to `logs/kgen_<tag>.plans.jsonl` and reloaded on restart (same
  tag), so a resume does not start from scratch.
- **Checker `verify_kgen.py`** (independent code). It checks:
  - coverage of every plan on its support, and the dead-atom rule;
  - a fresh SCIP model of the joint adversary (triple box, K, krange, one M1 per family with the applicability
    and cap switches).
- **Tie tolerance.** The checker counts a plan as closing when its largest request is ≤ t + 10⁻⁶ (in k/14):
  - kgen's CEGAR uses 10⁻⁵; at margin 10⁻⁷ the checker finds only numerical ties.
  - Example: at (6, 5.0077, 0.9623) with |K∩F′| = t − y exactly, the EFGK plan's value is t + 10⁻⁷, while a
    fresh EGK+4 plan closes at 11.81.
  - So certificates are at t + 10⁻⁶·k/14.

### 12.2 Certified so far [computed exact; re-checked]
- **hc**: K-level plans only (80 plans), box q ∈ [6, 6.0834], y ∈ [5, 5.0834], z ∈ [0, .97] ∩ class-A, t = 11.97.
  Every K outside the hand ranges closes; `verify_kgen`: 0 violations, independent SCIP INFEASIBLE.
  - So the hand ranges are no longer an assumption on the class-A part of the survivor set.
- Earlier: §10.1 (limit triple, δ = .002), §11 / `verify_kstagew` (triple (6, 5, 0.5), δ = .002).
  - These are at δ = .002, not at the S-game's t = .855; they show the mechanism but do not enter §12.4.

### 12.3 Running at write-up (δ = .03, t = 11.97; 7 processes, plans saved incrementally)

| tag | R0 | box (q; y; z) | families | progress |
|---|---|---|---|---|
| h1 | A, hand | 6; [5, 5.0834]; [0, .5] | 4 | it 15, μ 1.31, 214 plans |
| h2 | A, hand | 6; [5, 5.0834]; [.5, .97] | 4 | it 20, μ .95, 246 plans |
| h3 | A, hand | 6.0833; 5; [0, .5] | 4 | it 15, μ 1.14, 209 plans |
| h4 | A, hand | 6.0833; 5; [.5, .887] | 4 | it 15, μ 2.17, 202 plans |
| z1 | noZ | 6; [5, 5.0834]; [.8, 2] | 8 | it 35, μ .29, 212 plans |
| z2 | noZ | 6; [5, 5.0834]; [2, 3.1667] | 8 | it 15, μ 1.16, 271 plans |
| z3 | noZ | 6.0833; 5; [.8, 3.1667] | 8 | it 15, μ 1.55, 178 plans |

- These boxes cover every q = 72, 73 survivor of §11.2 up to E↔F symmetry:
  - q = 72: y ∈ {60, 61}, z ≤ 38;
  - q = 73: y = 60, z ≤ 38.
- Each box certifies only its part where its first request is valid: class A needs q + y + z ≤ t, noZ needs
  q + y ≤ t.
- In the noZ boxes some families escape at some K (XAH, XAY), but no K has escaped all eight so far.
- Iterations take 1–3 min (seven SCIP jobs alongside other runs), and μ is still far from 0. Expect hours.

### 12.4 Finishing
1. Let the seven runs finish. If a run is stopped, restart it with the same command and tag: it reloads its plans.
   The commands are in the first line of each `logs/kgen_<tag>.out`; KRANGE=hand for h1–h4.
2. `py -3.14 verify_kgen.py <tag>` for each INFEASIBLE run.
3. Write `logs/certs_t855.json` as a list of {tag, R0, box, t: 11.97} for the verified runs. Then
   `py -3.14 sgame_cert.py 168 3 0.855 logs/certs_t855.json`. This marks exactly the certified grid triples and
   all their permutations.
   - Requester ⇒ **NEW CAP t* ≤ .855** (up to the 10⁻⁶ tie tolerance).
   - Adversary ⇒ the S* it prints names the pair that still escapes.
4. If a run reports SURVIVES, the K and M1 it prints are the adversary's answer at that triple. Add first-request
   types (A_G, partY, partX exist in kgen) and rerun that box.
- Nothing committed.
- PIDs at write-up: h1 42892, h2 36472, h3 44196, h4 10136, z1 24300, z2 10376, z3 18472.
- To stop them: `Stop-Process -Id <pid>`. The plans are already on disk.

### 12.5 Restart after the timeouts (still PARTIAL)
- Five boxes (h2, h3, z1, z2, z3), then h1 and h4, had ended with "adversary TIMEOUT": the old code exited when
  SCIP found neither a point nor a proof within 170 s.
- New behaviour (`kgen.py`): a timeout never ends the run.
  - First attempt: env `KGEN_TL0` (now 600 s), with the margin objective.
  - Then retries as a pure feasibility problem, doubling the time limit up to `KGEN_TLMAX` = 2720 s.
  - Then continues with the next iteration.
- All seven were restarted with the same tags, so their saved plans were reloaded (427–487 each, z3 216). They run
  under KGEN_TL0 = 600, KRANGE = hand for h1–h4. At most 7 kgen processes, plus a status waiter.
- `kstatus.py tags…` prints the last segment of each run.
- Progress at write-up:
  - plans h1 491, h2 447, h3 451, h4 509, z1 509, z2 463, z3 243;
  - margins μ between 0 and 0.3 and falling;
  - no RESULT yet, no SURVIVES.
  - Each iteration now takes about 5–10 minutes, so expect several hours.
- The finishing recipe is unchanged (§12.4): verify_kgen on each, then `logs/certs_t855.json`, then sgame_cert.

## 13. Wind-down (2026-11-27)

The #644 work was stopped at the owner's request. All seven kgen boxes (h1–h4, z1–z3) were stopped mid-run. They had
not converged, no K had escaped, and none had been verified. Their plans are saved in `logs/kgen_<tag>.plans.jsonl`,
and a restart with the §12.5 commands resumes them.

**Final state:**
- **No certified bound below 6/7.**
- **Certified [computed exact, re-checked with independent SCIP]:**
  - every K closes at the limit triple (§10);
  - the four boxes at triple (6, 5, 0.5) close (§11);
  - the class-A complement mode at t = 0.855 closes (§12).
- **Conditional [computed, grid]:** t* ≤ .855 follows once every surviving answer at q = 72/168 and q = 73/168 is
  closed (§11). That closure was in progress when the work was stopped.
- Update: the seven processes and the status waiter were found terminated, with no RESULT and not by this session's
  commands (external stop).
- Plans saved by then: h1 502, h2 462, h3 466, h4 526, z1 537, z2 487, z3 258.
- All seven were restarted from those plans with the same commands. New PIDs: h1 21816, h2 38496, h3 14568,
  h4 35664, z1 8508, z2 36448, z3 36520.
