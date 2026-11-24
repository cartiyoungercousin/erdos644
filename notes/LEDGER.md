# LEDGER: status of every claim on the route to Erdős #644

Status levels:
- **LEAN**: machine-checked in Lean.
- **VERIFIED**: hand proof that passed an independent verifier (report in notes/verify/).
- **HAND**: hand proof, not yet verified.
- **EXACT**: computed exactly (rational or brute force).
- **FLOAT**: computed in floating point.
- **HEUR**: heuristic.
- **DEAD**: refuted or abandoned.

A claim moves to VERIFIED only through the gate: a PASS report from a fresh-context verifier.

## Reductions and tools
| Claim | Where | Status |
|---|---|---|
| Lemma 4.1–4.8 (6/7 manuscript), tight triple, Theorem A, stability 11.1, lopsided top 6.4, sparse triple, trace lemma, pair gap, three centres, Fano criterion, flat 7-tuple, Fano blocks, waste adversary, anchor/petal reductions | Lean644/*.lean | LEAN |
| Anchored reduction (TWIN §13), padding transfer | TWIN §13 | HAND |
| Theorems J, K, L (petal spread case) | PETAL §3, §7, §8 | HAND |
| Concentrated case N <= 3T - k/2 | TWIN 16.A | HAND |
| Theorems T, Q, pool theorem P, slack count | CORE §2–§5 | HAND (computed exact on instances) |

## Core window (Barrier D+E): classification of structured families
| Claim | Where | Status |
|---|---|---|
| Theorem S (finite-partition profile families lose) | CORE §36 | VERIFIED (V1; non-vacuous for N >= 1 + t) |
| Density form of S | CORE 39.2 | VERIFIED (V3; the sharpness remark needs some cell at π_j = v_j/3) |
| Theorem S+ (finite k, <= 4εk - 12 cells) | CORE 39.4, §45 | VERIFIED (V1; needs T <= n - k; the optimality-for-pencils remark is not verified) |
| Q' (set form of Theorem Q) and the pool-family miss of base/2 | CORE §37 | VERIFIED (V3) |
| Reduction CP <= (Σ) | CORE §38 | VERIFIED (V3) with corrected (b): "union is V and triple intersection >= N - 2t" (not kernel in [N-2t, N-3/2]); "balanced matchings" means Q'’s three per-matching conditions |
| Ordered frozen anti-plan has a good seven | CORE §46 | VERIFIED (V2; finite-k H-branch needs o <= 4ω - 3) |
| Theorem W (window-selected greedy rules lose) | CORE §47 | VERIFIED (V2; finite k needs 4 \| k; selectors reading \|S\| are outside W; threshold corollary holds for upward thresholds only) |
| Window lower end: 3t - 1/2 < N <= 5t - 2 closed by a fixed class-(T) plan when omega <= 4·eps | CORE 21.2 | GAP (V4): it assumes zero base waste for every adversary, with no steering lemma; static Theorem T tolerates only about 2ε of deficit. So the open window starts at 3t - 1/2, not 5t - 2. |
| Literal SPOIL false | CORE §40 | EXACT |
| SPOIL at all depths is not a disproof | CORE §43 | HAND |
| One-bit rule has a good seven | CORE §44 | EXACT (89 instances) |
| Kernel lemma; regularity reduction; c(N)·k cell bound; bounded-request game | CORE §34–35, §39, §45, Parts V–VII | DEAD |

## Petal side (Barrier F)
| Claim | Where | Status |
|---|---|---|
| Theorem J′ (6μ), Theorem J″ (4μ) | PETAL 14.1, 18.1 | VERIFIED (V4; Step 1 needs t >= 2/3; the third-class branch and integer rounding are not written) |
| Theorem DS, DS-b | PETAL 20.2, §21 | HAND + EXACT replay, verification pending (V5) |
| Lemma FF, Theorem AP | PETAL 23.1, 23.2 | HAND + EXACT replay, verification pending (V5) |
| Theorem N adversary beats 2+2 | PETAL §12 | HAND |
| 𝒜(t,δ), 𝒦₂ (c >= 0.5217) as obstructions | PETAL §20, §22 | DEAD |

## Open
- The core window is 3t - 1/2 < N < 3 - t (21.2 does not close (3t - 1/2, 5t - 2]).
- (Σ) for hash-like, non-greedy and self-cut families (core window).
- Fixed two-class families not of arena-with-pool form (petal).
- Strategy-form SPOIL; the five-reply candidate break (CORE §41).

## Consistency items (from paper/TODO.md)
- CORE §1 states the window as 5t - 2 < N; §7 and §33 use 3t - 1/2 < N. The gap interval rests on 21.2 (above).
- TWIN 16.A vs Lean `TheoremA` (one-anchor Fano template): they are different statements. 16.A stays HAND.
- The 6/7 main theorem (`SixSeventhsStatement`) is not proved in Lean; only its lemmas 4.1–4.8 are.
- Not yet scheduled for verification: Theorems J, K, L, T, Q, P, N; TWIN §13; 16.A.
- Covering numbers C(v,k,2) behind f(6,7) >= 5 and f(7,7) >= 6: our own ILP only; La Jolla tables unchecked.
