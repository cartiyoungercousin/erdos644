# Programme 5: joint 3-request game after the critical bridge triple, with spectrum forcing

Tags: [proved by hand] / [computed exact] / [computed, grid] / [heuristic] / [open]. Units k/14 (members 14,
t = 12 − δ). Code and logs: `compute/programme5/jointmilp/` (`logs/`), `py -3.14`, OR-Tools SCIP and CP-SAT, scipy-HiGHS
only as a proposer, ≤ 16 cores. Nothing committed. Nothing here is independently verified.

## 0. Headline (pre-registered form)
**CAPPED AT 6/7 INCL. 3-REQUEST FORCING** for the closure class of §1.
- Grids: every first request on the k/14 grid (11 616) and the k/28 grid (113 111) is refuted [computed exact per
  branch; first requests on the grid, second requests continuous, third exact].
- Continuous first requests [open]: 127 escape rounds, ≥ 790 escaping requests, every one refuted, but the loop did
  not converge (§3).
- No closure was found, so sgame.py is not rerun and **t\* stays 6/7**.
- Lemma Φ [proved by hand, §4]: Theorem P's *passive* adversary is not S*-sound. The S*-adversary survives only by
  *voluntary* drops in M1. A search steered at that weakness found no request that makes every voluntary drop cost
  more than it saves (§4–5).
- **Correction to the first version of this note.** scipy's bundled HiGHS declared a feasible master MILP infeasible
  (`dbg_master.py`: the R2-fixed copy is feasible and SCIP finds the point). Every earlier "ADV" was therefore
  re-proved with SCIP (`reverify.py`). All 1 850 were confirmed; the threat state of §4 was re-decided.

## 1. Model and the exact closure class
- State after Theorem P's K (BELOW67 §2), α = |A| = 7, β = |B| = 7:
  - live cells X = 6 (E,F), Y = 5 (E,G), A = 7 (G,K), B = 7 (F,K); alive pairs X×A ∪ Y×B;
  - dead cells E′ = 3, F_d = 1, G_d = 2; Z = 0⁺ ignored; outside points unlimited (ν = ∞).
- α = 7 answers every class-A request [proved by hand]: f ≤ 1 − δ < α − 6, g ≤ 1; traces E 0, F 7, G 7.
- S* = [0, 45/12] ∪ [5, 73/12] ∪ [80/12, 14] (S-game, G = 168, valid for t ∈ [.855, .857]).
- Budget: δ = .002, i.e. t = .85700. A cap there caps every smaller t, by monotonicity. X = 6, Y = 5 are legal there.
- **Game.** Adaptive R1 → M1, R2 → M2, R3 → M3; answers avoid their request, have mass 14, and meet E, F, G, K and
  earlier answers in S*. The seven are E, F, G, K, M1, M2, M3.
- **Exact finish** [proved by hand]. M3 needs only 0⁺ of a type, so she closes iff after M2 the endpoint set U of
  alive pairs has |U| ≤ t; then R3 = U.
- Calibration [computed exact]. Without the spectrum the rigid line returns REQ at t = 12 and ADV at 11.998.

## 2. Method (`jm.py`, `run_cover2.py`)
- **Stage 2**, for a fixed (R1, M1): CEGAR.
  - Her master: R2 continuous, against his *patterns*. A pattern keeps min(P_c, |c| − R2_c) per refined cell and
    fills with fresh outside points.
    - Each pattern must be inapplicable (mass > 14), illegal (gaps closed by 1e-6 in her favour) or leave |U| ≤ t.
      HiGHS proposes R2; **every infeasibility (ADV) is proved by SCIP.**
  - His oracle: the exact max-|U| M2, recomputed from the answer; a REQ needs the SCIP oracle to agree. Robust
    answers maximise the trace distance to the gap ends at |U| ≥ t + {.001, .5, 3}.
    - *Saturated* variants turn a cell he takes completely into "all of it that R2 leaves". These make patterns
      adapt along families of R2, which is what made the threat state (§4) converge: 19–66 iterations, versus
      none in 400 before.
- **Stage 1.** An M1 refutes every R1 it avoids (m1 + r1 ≤ |c|), so states cover sets of requests.
  - Candidates: min-drop answers (5 weightings); answers to *enlarged* requests R1 + η, η ∈ {.03 … 2}, which
    refute a whole box; and voluntary-drop variants (d ∈ {.25, .5, 1} of one live cell → outside).
  - Greedy set cover over the candidates.
- **Continuous first requests** (`cont` mode). States are down-boxes. A request escaping all of them is found, or
  shown not to exist, by an exact 0/1 CP-SAT model (levels = thresholds + 1e-5, costs rounded down in her favour;
  a returned request is re-checked directly).
- Checks (no MILP, `verify_cert.py`, `verify_threat.py`) [computed exact]:
  - 48 000 random (state, R2) pairs on 800 states: 0 failures;
  - 20 000 Lemma-Φ-shaped R2 against each threat certificate: 0 failures.
  - Earlier, the same check on the old HiGHS certificate found 5 491/20 000 failures, which exposed the bug.

## 3. Results (α = 7, t = 11.998; certificates `logs/cover_v3_a7_d0.002.jsonl`)
| run | first requests | result |
|---|---|---|
| k/14 grid | 11 616 maximal | all refuted by SCIP-verified states |
| k/28 grid | 113 111 maximal | all refuted |
| Lemma-Φ family (§4), steps .05–.25 near Y ∪ B′ and its mirror X ∪ A′ | 13 317 | all refuted |
| continuous (CP-SAT escape loop) | all with \|R1\| ≤ t | 127 rounds; ≥ 790 escaping requests, all refuted; not converged |
- Decided states: 9 323. Of these, 5 139 are ADV (median 4 CEGAR iterations, max 66; median 18 patterns, max 504),
  4 159 are REQ (a single M1 that loses while another M1 refutes the same requests), and 25 are undecided.
- Uniform Monte Carlo over maximal requests: 0 of 50 000 escape every ADV state.
- **Why the continuous loop does not converge** [heuristic]. The escapes creep in steps of 1e-5 along families where
  his refuting answer must keep *all* of a cell that R1 leaves (r_Y = r_B = 0, X ≈ all of X). Such an answer
  refutes only a zero-width box, so no finite list of fixed M1 states can cover the family.
  - One family was closed by hand-picked states: R1 = Y ∪ B′ plus at most 1/2 of X and of A. Two ADV states cover it:
    M1 = X(5.5) ∪ A(6.5) ∪ B_.001 ∪ out and X(5.5) ∪ A(6.5) ∪ Y_.001 ∪ out. Either r_B ≤ 6.999, or r_Y ≤ 4.999.
  - Closing the rest needs R1-adaptive M1 patterns, i.e. the joint (R1, R2) CEGAR.

## 4. Lemma Φ, the threat line, and the escape
**Lemma Φ (passive play loses)** [proved by hand]. Assumptions:
- α = β = 7, t = 12 − δ, 0 < δ < 1/12;
- R1 = Y ∪ B′ with |B′| = 7 − δ, and B_ε := B ∖ B′;
- passive M1 = X ∪ A ∪ B_ε ∪ O1, |O1| = 1 − δ. It is legal: traces E 6, F 6 + δ, G 7, K 7 + δ.

Then R2 = X ∪ A_a ∪ Y_y ∪ B_ε, with a ∈ (3 − δ, 3.25 − 4δ] and y = 6 − 2δ − a, closes.

*Proof.*
- M2 ∩ M1 ⊆ (A ∖ A_a) ∪ O1, which has mass 8 − δ − a < 5. So legality forces |M2 ∩ A| ≤ 3.75.
- Alive pairs need q ∈ A ∩ M2 (X×A), or q ∈ B_ε and p ∈ Y ∖ Y_y (Y×B).
- So |U| ≤ 6 + 3.75 + (5 − y) + δ ≤ 12 − δ. ∎

The exact oracle gives |U| = 11.756 at δ = .002, a = 3.
- **Escape** [computed exact]. Voluntary-drop answers to R1 = Y ∪ B′ that are refuting, SCIP-proved ADV:
  - X(6 − d) ∪ A ∪ B_ε ∪ outside, for d = .25 and .5 (19 iterations each);
  - X ∪ A(7 − d) ∪ B_ε ∪ outside, for d = .25, .5 and 1 (66, 25 and 29 iterations);
  - X(5.75) ∪ A(6.75) ∪ B_ε ∪ outside (29 iterations).
- **Why the X-drop works** [proved by hand, only for R2 of Lemma-Φ shape, i.e. R2 ⊇ X ∪ B_ε]:
  - With d of X replaced by outside points, M2 ∩ M1 can be lifted to 5 unless a + r_O > 3 − δ + d (r_O: her request
    on M1's outside points), while closure needs a + r_O ≤ 3.25 − 4δ. The window is empty once d ≥ .25 − 3δ.
  - Dropped X points kill nothing in round 1 (A ⊆ M1) and stay in U.
  - General R2 is covered by the certificate only.
- **Steering** (the coordinator's request). The requester's ways to make voluntary drops cost something:
  - R1 also takes s of X, so that dropped A meets requested X;
  - R1 takes u less of Y, or adds dead cells;
  - the mirror line X ∪ A′.
  - All 13 317 such requests are refuted (§3). The cost a drop imposes on him is always paid back by the extra
    Y×B_ε or X×A_s mass she must then cover. The margin is 3δ in the Lemma-Φ shape [heuristic for general R2].

## 5. What is ruled out, precisely
- Ruled out [computed exact per branch]:
  - critical triple at t = .85700 (and below); class-A request answered by Theorem P's K with α = 7;
  - then any first request on the k/14 or k/28 grid (dead cells 0/half/full), or in the Lemma-Φ family, followed by
    any continuous R2 and the exact R3;
  - answers S*-legal against E, F, G, K and earlier answers;
  - seven = E, F, G, K + three answers.
- Certificate per refuted request: an avoiding M1 state of the jsonl, its pattern list, and SCIP's infeasibility proof.
- Not ruled out [open]: off-grid first requests in general (§3), discards (route B), class-B first requests,
  depth > 3, and families beyond the spectrum.
- Lemma Φ: any hand proof of the cap must use non-passive (voluntary-drop) answers.

## 6. Files (`compute/programme5/jointmilp/`)
- `jm.py` (model, oracles, master, CEGAR), `run_cover2.py alpha delta nproc grid h | list file | cont rounds`.
- `reverify.py` (SCIP re-proof), `save_cert.py`, `verify_cert.py`, `verify_threat.py`, `escape_frac.py`,
  `dbg_master.py` (HiGHS false-infeasibility repro).
- Superseded: `run_cover.py`, `cover_cont.py`, `logs/cover_a7_d0.002.jsonl` (HiGHS-era file).
