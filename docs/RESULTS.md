# Results index

Every established result, with its statement in brief, where the proof lives, and how it was checked. Abbreviations: **CORE**, **PETAL** and **TWIN** refer to `notes/CORE.md`, `notes/PETAL.md` and `notes/TWIN.md`. Verification reports are in `notes/verify/`. Terminology is explained in [GLOSSARY.md](GLOSSARY.md).

Levels: **LEAN** = machine-checked. **VERIFIED** = hand proof that passed an independent adversarial check. **EXACT** = exact computation.

## 1. Framework and reductions

| Result | Statement (brief) | Proof | Check |
|---|---|---|---|
| Request principle, game equivalence | the problem is a covering game; requester wins ⇔ $f(k,7)\le T$ | CORE Part VII; [brief](../reports/EXTERNAL_BRIEF.md) §2 | LEAN (`exists_response`) + VERIFIED |
| Confinement | three answers with empty triple intersection confine play to $\le 3k$ points | TWIN §13 | VERIFIED (`TWIN13_16A.md`); LEAN (`Anchor.lean`, `GapAnchor.lean`) |
| Petal reduction | 2–6 petals with empty common intersection | PETAL §1 | LEAN (`PetalReduction.lean`) |
| Flat 7-tuple lemma | $\tau>T\ge 3k/4$ ⇒ seven edges with all degrees $\le 4$ | PROOFS / FRESH_C §1 | LEAN (`FlatTuple.lean`) |
| Fano criterion, Fano blocks | Fano-labelled sevens with empty pencil intersections have no 2-cover | NEW_PATHS (archived) | LEAN (`Fano.lean`, `FanoBlocks.lean`) |
| Waste adversary | the seven-request endgame is refuted below $4k/5$ | FRESH_C | LEAN (`Waste.lean`) |
| Reduction CP ⇐ $(\Sigma)$ | the core window follows from one of three configurations | CORE §38 | VERIFIED (`Qprime_Sigma_density.md`) |

## 2. Finishing tools (core window)

| Result | Statement (brief) | Proof | Check |
|---|---|---|---|
| Slack count | $\sum_x(\lvert I_x\rvert-3)=4\delta$ for any seven co-edges | CORE §2 | VERIFIED (`T_Q_P_slack.md`) |
| Theorem T | a triangle in the stated window is finished by four requests | CORE §3 | VERIFIED |
| Theorem Q = Q′ | a quadrangle finish, exact condition | CORE §4, §37 | VERIFIED |
| Pool theorem P | dumps in a known pool $Z$ ⇒ requester wins | CORE §5 | VERIFIED at first order; a finite-$k$ repair is needed |

## 3. Closed regions

| Region | Result | Proof | Check |
|---|---|---|---|
| Crowded, $N\le 3t-\tfrac12$ | requester wins | TWIN 16.A | VERIFIED at first order |
| Bottom strip, $3t-\tfrac12<N\le 5t-2$ | pair criterion plus Frankl–Rödl density | CORE §90–94 | VERIFIED (`bottom_strip.md`) |
| Petal side, $N\ge 3-t$ | closed except two residues | PETAL Theorems J, K, L, AP, PS–PS3 | VERIFIED (`J_K_L_N.md`, `DS_FF_AP.md`, `PS*.md`) |

## 4. No structured counterexamples in the core window

| Result | Excludes | Proof | Check |
|---|---|---|---|
| Theorem S | families that depend only on profiles of a bounded partition | CORE §36 | VERIFIED (`S_Splus.md`) |
| Theorem S⁺ | the same at finite $k$, up to $4\varepsilon k-12$ cells | CORE §39.4, §45 | VERIFIED |
| Frozen orders | fixed in-cell order rules | CORE §46 | VERIFIED (`46_W.md`) |
| Theorem W | greedy order rules selected by a window of $\le T-k/2$ points | CORE §47 | VERIFIED |
| Theorem H | kernel density above $2/3$; the constant is sharp | CORE §58 | VERIFIED (`R_H.md`) |
| Theorem R | random or 6-wise independent selectors with fewer than about $e^{1.19k}$ classes | CORE §57 | VERIFIED |
| Density form of S | dense profile classes force a good seven | CORE 39.2 | VERIFIED |

## 5. Petal side, in detail

| Result | Proof | Check |
|---|---|---|
| Theorems J, J′, J″ | PETAL §3, 14.1, 18.1 | VERIFIED |
| Theorems K, L, N | PETAL §7, §8, §12 | VERIFIED |
| Lemma FF, Theorem AP | PETAL §23 | VERIFIED |
| Theorem DS-b | PETAL §21 | VERIFIED |
| Theorems PS, PS2, PS3 (pooled arena adversary loses for $\delta<t/2-\tfrac16$) | PETAL §26–28 | VERIFIED |
| Lemma PC, Theorem CR (reduction to the one-class statement SL1) | PETAL §40 | under verification |

## 6. Exact small values

| Result | Check |
|---|---|
| $f(6,7)=5$, $f(7,7)=6$ | upper bounds by exact certificate (FRESH_C §14); lower bounds from covering numbers computed by ILP (`small_values.md`); published-table cross-check pending |

## 7. Approaches shown not to work in the core window

21 approaches, each with its obstruction: [`reports/FAILED_ROUTES.pdf`](../reports/FAILED_ROUTES.pdf).
