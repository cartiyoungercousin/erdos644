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
| Anchored reduction (TWIN §13), anchor lemma, Theorem A, padding transfer | TWIN §13 | VERIFIED (W1) |
| Theorems J, K, L (petal spread case) | PETAL §3, §7, §8 | VERIFIED (W3; L's statement should repeat p <= t; J's band disjunct untested in simulation) |
| Concentrated case N <= 3T - k/2 - O(1) | TWIN 16.A | VERIFIED at first order (W1); finite-k proof has a GAP at line 904 (Theorem C's half-split isn't integral), and O(1) can't be 0 (K(9,5): τ = 5 > 4, N = 9 <= 9.5) |
| Slack count, Theorem T, Theorem Q (= Q′) | CORE §2–§4 | VERIFIED (W2; Q's 'iff' holds only for the fixed quadrangle scheme) |
| Pool theorem P | CORE §5 | VERIFIED at first order; FAILS at finite k when εk = 1/4: counterexample (k,T,N,|Z|) = (5,4,9,0), since C(9,4,2) = 8. Needs εk >= 1/2 plus a rounding lemma (W2) |

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
| Bottom strip 3t - 1/2 < N <= 5t - 2 closed for ε <= ε_0 (ineffective): a pair with overlap in [N - 2t, 3t - 2] gives a good seven; Frankl–Rödl forces such a pair because T-covering families are dense (e^{-O(ε ln 1/ε) n}) | CORE §90–§94 | VERIFIED (bottom-strip verifier; Frankl–Rödl checked against arXiv 1402.6294, α = 3/7, η = 1/14, δ absolute) |
| Theorem R (uniformly random / 6-wise independent selectors over heads of size ω lose unless R >= e^{(1.19-o(1))k} classes; Chebyshev) | CORE §55–§59 | VERIFIED (R/H verifier; the exponent is 1.183 at t -> 3/4, 1.1925 at t = 0.76, 1.259 at 5/6) |
| Theorem H (> 2/3 of the lines over one kernel present gives a good seven; W is a special case) | CORE §55–§59 | VERIFIED (R/H verifier; 2/3 is sharp: the Kleitman set; §58.1 wording fix: 'J has ω points outside the window W') |
| Hash-like selectors: 805/805 trials have a good seven (the 7 earlier misses were search failures) | CORE §56 | EXACT |
| (8,6,15) family: τ = 7; good-seven question UNDECIDED; at ε = 0, irrelevant to CP | CORE §55 | EXACT (τ) |
| Literal SPOIL false | CORE §40 | EXACT |
| SPOIL at all depths is not a disproof | CORE §43 | HAND |
| One-bit rule has a good seven | CORE §44 | EXACT (89 instances) |
| Junta approximation in measure (Dinur–Friedgut, Keller–Lifshitz); spread lemmas (ALWZ, FKNP) | CORE §50–§53 | DEAD (proved: the families are at most n/c < 2.28-spread; junta theorems need k < n/C) |
| Kupavskii–Zakharov decomposition into head classes + remainder (H_τ) | CORE §54 | HAND; restates the hash-selector problem, not a reduction |
| Fractional relaxation + rounding (τ* <= (35k)^{1/3} for (7,2)-families; rounding in the window is CP itself; Alon–Kleitman ε-net route can't give 3/4) | CORE §80–§84 | DEAD (proved) |
| Hypergraph containers + supersaturation (codegree condition fails above a thin strip; the supersaturation step needed already implies CP) | CORE §85–§89 | DEAD (proved) |
| Flag algebras / SDP on the limit object (Cauchy–Schwarz constraints automatic; CP is not a density statement; 'no good seven' doesn't pass to the limit, corrects §39.3) | CORE §75–§79 | DEAD (proved) |
| Transfer lemma (finite-depth first-order win at t' < t gives CP at t for large k) | CORE §75 | HAND |
| Density / forbidden-pattern arguments above the bottom strip (Theorem 96.1: the c-sets avoiding a point and containing a fixed Y have no static certificate yet density rate <= 0.17γ; no pattern rate can beat γ) | CORE §95–§99 | DEAD (HAND, not yet verified) |
| Frankl–Wilson makes the bottom strip effective (ε_0 ≈ 0.0088), except a vanishing top sliver | CORE §97 | FLOAT/HEUR |
| Adaptive density / dependent random choice via links, traces, exclusions (links move (N,t) away from every closed region; Theorem 102.1: the static-certificate budget S_q = (q-3)δ + (7-q)ε depends only on (N,t,q)) | CORE §100–§104 | DEAD (HAND) |
| Entropy method (Gilmer size form; iid copies AHS/Chase–Lovett; correlated laws / pencil supersaturation; witness-pair union bound); obstruction: certificates need cyclic dump constraints, entropy handles only acyclic ones | CORE §70–§74 | DEAD (HAND) |
| core9 two-class reversed-order family at (8,6,15): 0 pencils (vs 128,301 random-predicted) and no (Σ)-shape at ε = 0 | CORE §72 | EXACT |
| Covering-design stability / anti-Pasch analogy / code constructions (size is the wrong measure: pool families are minimal yet far above the Schönheim bound; random designs are supercritical; code redundancy needed > covering budget) | CORE §105–§109 | DEAD (HAND/FLOAT) |
| Kernel lemma; regularity reduction; c(N)·k cell bound; bounded-request game | CORE §34–35, §39, §45, Parts V–VII | DEAD |

## Petal side (Barrier F)
| Claim | Where | Status |
|---|---|---|
| Theorem J′ (6μ), Theorem J″ (4μ) | PETAL 14.1, 18.1 | VERIFIED (V4; Step 1 needs t >= 2/3; the third-class branch and integer rounding are not written) |
| Theorem DS, DS-b | PETAL 20.2, §21 | VERIFIED only when the ground set is the two arenas. DS FAILS if 𝒜 leaks outside them (51–100 of 400 games end in a 2-cover with a 40-point outside pool). AP covers the pool but needs c > θ(t). |
| Lemma FF, Theorem AP | PETAL 23.1, 23.2 | VERIFIED (V5; 112/151 is sharp; asymmetric arenas replayed; AP's τ_c comes from a direct count, not 'FF with equality') |
| Theorem PS (pooled 𝒜 loses for δ < 3t/16, no condition on c) | PETAL §26 | VERIFIED (PS verifier; 3t/16 is sharp) |
| Small-k search for non-arena two-class families (k = 12, at most 4 atoms; k = 16, at most 4 atoms, n <= 44) | PETAL §25 | INVALID as a certificate: it used least-hitting-set cost, but AP needs absorption (found in §40). Redone with Theorem CR in §40: no hits (blow-up model, k = 12 at most 4 atoms plus 5–6 atoms n <= 34; k = 16 at most 4 atoms) |
| Theorem PS2 (pooled 𝒜 loses for δ < t/4) | PETAL §27 | VERIFIED (PS2 verifier: independent vertex enumeration confirms all 93; 17k games; at δ = t/4 with T even, X must be the class with the smaller hit number) |
| Theorem PS3 (pooled 𝒜 loses for δ < t/2 - 1/6; closes all t >= 7/9) | PETAL §28 | VERIFIED (PS3 verifier: independent LP, 31k games). The limit δ* = t/2 - 1/6 holds within the window-and-seal model only; it says nothing about two-class petals, re-selection or adaptive trace release. |
| Petal strip, forced-centre model: an adaptive request 7 saves only about δ/2; the adversary wins for δ in (3t/10, 1 - t) at t = 0.75, 0.76 | PETAL §31 | EXACT (zero-gap MIP; requester relaxed in her favour); with unforced centres still open |
| Lemma PC (cross overlap <= 2 - 2c - t), Lemma YC, Theorem CR (absorbing-set play without disjoint regions); fixed two-class gap reduced to θ(t) < c < 1 - 5t/9 and to the one-class statement SL1 | PETAL §40 | HAND, verification pending |
| Theorem N adversary beats 2+2 | PETAL §12 | VERIFIED (W3) |
| 12.3 (𝒜 loses to 4+3 when she knows the arenas) | PETAL 12.3 | GAP (W3): assumes the ground set is the two arenas; a leak outside them breaks it. Check whether DS / the 𝒜 kill inherits this, or whether AP's pool covers it |
| 𝒜(t,δ), 𝒦₂ (c >= 0.5217) as obstructions | PETAL §20, §22 | DEAD |

## Open
- Petal: pooled 𝒜 for t/2 - 1/6 <= δ < 1 - t with 3/4 < t < 7/9 ([0.2083, 0.25) at t = 3/4). The window-and-seal method is maxed out at δ* = t/2 - 1/6 (exact LP), so a new certificate is needed here. The earlier note claiming §19.1 closes this was wrong: §19.1 only marks where AP's hypothesis fails (verifier, notes/verify/PS.md).
- Core window: 5t - 2 < N < 3 - t (for small ε; the bottom strip is VERIFIED closed).
- (Σ) for hash-like, non-greedy and self-cut families (core window).
- Petal: fixed two-class families with θ(t) < c < 1 - 5t/9 (empty for t >= 63/79); reduced to the one-class stability statement SL1 (PETAL §40).
- Strategy-form SPOIL; the five-reply candidate break (CORE §41).

## Consistency items (from paper/TODO.md)
- CORE §1 states the window as 5t - 2 < N; §7 and §33 use 3t - 1/2 < N. The gap interval rests on 21.2 (above).
- TWIN 16.A vs Lean `TheoremA` (one-anchor Fano template): they are different statements. 16.A stays HAND.
- The 6/7 main theorem (`SixSeventhsStatement`) is not proved in Lean; only its lemmas 4.1–4.8 are.
- Not yet scheduled for verification: Theorems J, K, L, T, Q, P, N; TWIN §13; 16.A.
- Covering numbers C(v,k,2) behind f(6,7) >= 5 and f(7,7) >= 6: our own ILP only; La Jolla tables unchecked.
