# Programme 5: joint 3-request game after the critical bridge triple, with spectrum forcing

Tags: [proved by hand] / [computed exact] / [computed, grid] / [heuristic] / [open]. Units k/14 (members 14,
t = 12 − δ). Code and logs: `compute/programme5/jointmilp/` (`logs/`), `py -3.14`, scipy-HiGHS with an OR-Tools SCIP
fallback, ≤ 12 cores, about 2.5 h wall. Nothing committed. Nothing here is independently verified.

## 0. Headline (pre-registered form)
**CAPPED AT 6/7 INCL. 3-REQUEST FORCING** for the closure class of §1 with first requests on the grid k/14
(11 616 requests). Every request is refuted by an explicit S*-legal answer M1 plus a list of M2-patterns; the
certificate is the MILP's infeasibility proof [computed exact per branch, grid of first requests]. Status §3.
- No closure exists in this class, so sgame.py is not rerun and **t\* stays 6/7**.
- **New and negative for the old argument** [proved by hand, Lemma Φ, §4]. Theorem P's passive adversary is NOT
  S*-sound. For every δ ∈ (0, 1/12) (spectrum S*) there is a first request R1 = Y ∪ B′ after which forcing beats waste:
  a forced drop of 1/4 against a deficit of 3δ. The adversary survives only by a *voluntary* drop in M1.
- Not covered [open]: the k/28 grid of first requests, fully continuous first requests (§3), the α ≠ 7 branches
  (not needed, §1), discards, and other first requests (class B).

## 1. Model and the exact closure class
- State after Theorem P's K (BELOW67 §2), with α = |A| = 7 and β = |B| = 7:
  - live cells X = 6 (E,F), Y = 5 (E,G), A = 7 (G,K), B = 7 (F,K); alive pairs X×A ∪ Y×B;
  - dead cells E′ = 3 (E), F_d = α − 6 = 1 (F), G_d = 9 − α = 2 (G); Z = 0⁺ (ignored); outside points unlimited (ν = ∞).
- **Why α = 7 is enough** [proved by hand]. α = 7 is legal for every class-A request (f ≤ 1 − δ < α − 6, g ≤ 1)
  and S*-legal: its traces are E 0, F 7, G 7, and x + α > t, y + β > t. So one α answers every class-A request.
- Spectrum: S* = [0, 45/12] ∪ [5, 73/12] ∪ [80/12, 14], from the S-game at G = 168, valid for t ∈ [.855, .857].
- Budget t = 12 − δ, δ = .002 (t = .85700, the largest t with S* valid; a cap there caps every smaller t, since
  smaller requests leave him more answers). X = 6, Y = 5 are legal critical cells: q = 72/168 ∈ (t/2, 3 − 3t].
- **Game.** She requests R1 → M1, R2 → M2, R3 → M3, each request depending on the earlier answers.
  - Each answer avoids its request, has mass 14, and meets E, F, G, K and every earlier answer in S*.
  - The kept seven are E, F, G, K, M1, M2, M3 (no discards).
- **Exact finish** [proved by hand]. M3 needs only one point (0⁺) of a type, and adding it keeps traces in S*. So
  she closes iff, after M2, the set U of endpoints of still-alive pairs has |U| ≤ t; then R3 = U.
- Calibration [computed exact]. Without the spectrum the rigid line R1 = X∪Y + 1 of A returns REQ at t = 12 and ADV
  at t = 11.998 (`t_nospec.py`), reproducing Theorem P's 6/7.

## 2. Method (`jm.py`)
- **Stage 2** [computed exact], for a fixed (R1, M1). CEGAR between two parts:
  - her master: R2 continuous (stronger for her than any grid) against a list of his *patterns*. A pattern P
    answers any R2 by keeping min(P_c, |c| − R2_c) on every refined cell (cell × in M1), then fills with fresh
    outside points.
    - In the master she must make every pattern answer inapplicable (mass > 14), illegal (some trace in a gap),
      or leave |U| ≤ t.
  - his oracle: the exact best response M2, an MILP maximising |U| with trace-interval binaries, plus two
    "robust" answers that maximise the trace distance to the gap ends subject to |U| ≥ t + .5 or t + 3.
  - Master infeasible ⇒ ADV: each pattern is a genuine strategy of his, so the pattern list together with the
    infeasibility proof is a certificate.
  - Oracle |U| ≤ t ⇒ REQ for this M1.
  - Relaxations all favour her: gaps closed by 1e-6, nonempty means mass > 0 for her and ≥ 1e-3 for him.
- **Stage 1** (`run_cover.py`). Any legal M1 refutes every R1 it avoids (m1_c + r1_c ≤ |c|), since its traces do not
  depend on R1.
  - Candidates: his min-drop answer to each grid R1 (5 drop weightings, pads from outside preferred), and in
    phase 2 voluntary-drop variants (d ∈ {.25, .5, 1} of one live cell replaced by outside points).
  - A greedy set cover selects which M1 to decide.
  - Grid: live cells on k/14 with the remainder of t in one live cell; dead cells 0, half or full. That gives
    11 616 maximal first requests.
- **Independent check** (`verify_cert.py`, no MILP). On 14 refuted states, 4 200 random second requests (cells
  taken fully, partly or not at all) were each defeated by some certificate pattern: 0 failures [computed exact].

## 3. Results (α = 7, t = 11.998)
| run | first requests | refuted (ADV) | status |
|---|---|---|---|
| k/14 grid, phase 1 (`logs/run_a7_h1.out`) | 11 616 | 11 589 by 612 M1 states | 27 left: 1 REQ state, 7 solver errors, 19 timeouts |
| k/14 grid, phase 2 (`logs/run_a7_h1_phase2.out`) | the 27 | 26 on retry; the last (R1 = Y ∪ B′, §4) by M1′ of §4 | all 11 616 refuted; M1′'s patterns not yet in the jsonl (run cut at wind-down) |
| continuous R1 (`cover_cont.py`, stopped) | escaping R1 by MILP | 17 rounds, 577 new states, all ADV | not converged [open] |
| k/28 grid | 79 357 | not run | [open] |
- Stage-2 CEGAR: median 4–7 iterations, up to 150. Phase-1 time was about 3 min on 12 cores.
- The only REQ state in phase 1 is the passive answer to the threat line of §4.

## 4. The strongest forcing found: Lemma Φ and the adversary's escape
**Lemma Φ (passive play loses)** [proved by hand]. Assumptions:
- the state of §1 with α = β = 7 and t = 12 − δ, 0 < δ < 1/12;
- R1 = Y ∪ B′ with B′ ⊆ B, |B′| = 7 − δ, and B_ε := B ∖ B′, so |B_ε| = δ;
- his passive answer M1 = X ∪ A ∪ B_ε ∪ O1, with O1 outside and |O1| = 1 − δ. It is legal: traces E 6, F 6 + δ,
  G 7, K 7 + δ.

Then R2 = X ∪ A_a ∪ Y_y ∪ B_ε closes, for any a ∈ (3 − δ, 3.25 − 4δ] and y = 6 − 2δ − a, with A_a ⊆ A and
Y_y ⊆ Y. Here |R2| = t.

*Proof.* M2 avoids X and B_ε, so M2 ∩ M1 ⊆ (A ∖ A_a) ∪ O1, of mass 8 − δ − a < 5 (a > 3 − δ). The S* values
below 5 lie in [0, 3.75], so legality forces |M2 ∩ A| ≤ |M2 ∩ M1| ≤ 3.75 (a drop, as 7 − a > 3.75).
- Alive pairs after M2:
  - X×A: (p,q) with q ∈ A∩M2 (X ⊆ R2, and every p ∈ X lies in M1). A ∖ M2 has no alive partner.
  - Y×B: (p,q) with q ∈ B_ε (the only part of B in M1) and p ∈ Y∩M2 ⊆ Y ∖ Y_y. Pairs with B′ died in round 1,
    because Y ∪ B′ ⊆ R1.
- So |U| ≤ 6 + 3.75 + (5 − y) + δ = 14.75 − y + δ ≤ 12 − δ, using y ≥ 2.75 + 2δ. Take R3 = U. ∎

The exact oracle confirms it at δ = .002, a = 3: his best M2 leaves |U| = 11.756 (`logs/threat_line.log`).
- **Meaning.** The forced drop is 7 − a − 3.75 ≈ 1/4 of live mass, at zero waste. The gap (3.75, 5) of the
  answer–answer spectrum catches M2 ∩ M1. This is exactly the "forcing beats waste" event that SPECTRUM §3 left open.
  It happens against Theorem P's passive play, so Theorem P does not extend to the S*-game as it stands.
- **Escape** [computed exact, `t_threat.py`]. M1′ = X ∪ (6.75 of A) ∪ B_ε ∪ (1.248 outside) is legal and wins
  stage 2: the master is infeasible after 106 iterations.
  - The dropped quarter of A kills nothing in round 1, since X ⊆ M1.
  - Dropping X instead (M1 = 5.8 of X + A + B_ε) was undecided after 150 iterations. Dropping B_ε loses
    (|U| = 8.002).
- Hand reason for the escape [heuristic]. The extra outside mass lets him lift M2 ∩ M1 to 5. R2 can block that
  only by taking A ∖ M1 or the outside points, which costs exactly the budget the gap saved her.

## 5. What is ruled out, precisely
- Ruled out [computed exact per branch; grid of first requests; R2 continuous]:
  - critical triple at t = .85700 (and below, by monotonicity); class-A request answered by Theorem P's K, α = 7;
  - then any first request on the k/14 grid (dead cells 0/half/full), any continuous second request, and the
    exact finishing third request;
  - his answers S*-legal against E, F, G, K and all earlier answers;
  - seven = E, F, G, K + three answers.
- Certificate: `logs/cover_a7_d0.002.jsonl`, one line per decided M1 (M1, the pattern list, CEGAR iterations).
- **Not** ruled out [open]:
  - off-grid first requests. The continuous outer loop kept finding escaping R1 near cell boundaries and was
    stopped. All 577 states it decided were ADV;
  - the k/28 grid;
  - discards (route B beyond SPECTRUM §4);
  - class-B first requests with the spectrum;
  - depth > 3.
- Lemma Φ shows that any future proof of the cap must use non-passive (voluntary-drop) adversary answers.

## 6. Files (`compute/programme5/jointmilp/`)
- `jm.py`: model, oracles, master, CEGAR. `run_cover.py alpha h delta nproc`: grid cover, checkpointed.
- `cover_cont.py`: continuous first requests. `adv1_search.py`: adversary search over M1 for one R1.
- `verify_cert.py`, `summarize.py`, `t_threat.py` (Lemma Φ line), `t_nospec.py` (calibration), `count_states.py`.
- Logs: `cover_a7_d0.002.jsonl` (certificates), `run_a7_h1*.out`, `cont_a7.out`, `threat_line.log`,
  `adv1_threat.out`.
