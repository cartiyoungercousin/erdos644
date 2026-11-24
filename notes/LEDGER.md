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
| Theorem S (finite-partition profile families lose) | CORE §36 | HAND, verification pending (V1) |
| Density form of S | CORE 39.2 | HAND, verification pending (V3) |
| Theorem S+ (finite k, <= 4εk - 12 cells) | CORE 39.4, §45 | HAND, verification pending (V1) |
| Q' (set form of Theorem Q); reduction CP <= (Σ) | CORE §37, §38 | HAND, verification pending (V3) |
| Ordered frozen anti-plan has a good seven | CORE §46 | HAND + EXACT (12 instances), verification pending (V2) |
| Theorem W (window-selected greedy rules lose) | CORE §47 | HAND + EXACT (1200 random), verification pending (V2) |
| Literal SPOIL false | CORE §40 | EXACT |
| SPOIL at all depths is not a disproof | CORE §43 | HAND |
| One-bit rule has a good seven | CORE §44 | EXACT (89 instances) |
| Kernel lemma; regularity reduction; c(N)·k cell bound; bounded-request game | CORE §34–35, §39, §45, Parts V–VII | DEAD |

## Petal side (Barrier F)
| Claim | Where | Status |
|---|---|---|
| Theorem J′ (6μ), Theorem J″ (4μ) | PETAL 14.1, 18.1 | HAND, verification pending (V4) |
| Theorem DS, DS-b | PETAL 20.2, §21 | HAND + EXACT replay, verification pending (V5) |
| Lemma FF, Theorem AP | PETAL 23.1, 23.2 | HAND + EXACT replay, verification pending (V5) |
| Theorem N adversary beats 2+2 | PETAL §12 | HAND |
| 𝒜(t,δ), 𝒦₂ (c >= 0.5217) as obstructions | PETAL §20, §22 | DEAD |

## Open
- (Σ) for hash-like, non-greedy and self-cut families (core window).
- Fixed two-class families not of arena-with-pool form (petal).
- Strategy-form SPOIL; the five-reply candidate break (CORE §41).
