# Lean verification plan — six-sevenths bound

Target: `Erdos644.SixSeventhsStatement` (frozen, `Lean644/Statements.lean`).
Source: cubres/erdos-644-research `six_sevenths_v3.tex` @ e8e5f93.

## Design
Every construction in the manuscript = (a) split cells into pieces of prescribed sizes,
(b) integer inequalities. We formalize with
* `Finset.exists_subset_card_eq` (pieces of given size) instead of max-flow/Hall;
* `omega` / `linarith` for the inequalities;
* `request_cover` to turn "every candidate pair lies in a request" into `False`.
Requests may depend on earlier responses: this is just nested `obtain`s.

## Lemma map (manuscript → Lean) and status

| # | Manuscript | Lean | Status |
|---|---|---|---|
| 1 | Lemma 2.1 request-cover principle | `Framework.request_cover` | DONE |
| 2 | responses exist when τ > T | `Framework.exists_response` | DONE |
| 3 | candidate pairs of a good triple (eq. 2.1) | `Triple.triple_candidate`, `closes_of_four_requests` | DONE |
| 4 | Lemma 2.4 four edges (candidate pairs of E,F,G,K) | `Triple.four_candidates` | todo |
| 5 | Lemma 2.2 integral allocation | replaced by explicit splits | n/a |
| 6 | Lemma 2.5 balanced request; 2.6 capped request | `Seeds.*` | todo |
| 7 | Lemma 3.1 Hall allocation; Cor 3.2 | `Static.triangle_split`, `Static.hall_sizes` (integer core DONE); set-level `hall_closes`, `hall_cor` todo | partial |
| 8 | Lemma 3.3 boxed triangle (pure integers) | `Static.boxed_triangle` | todo |
| 9 | Lemma 3.4 symmetric allocation | `Static.symmetric` | todo |
| 10 | Lemmas 4.1–4.3 one core / split A / split B (adaptive, App. A) | `Adaptive.*` | todo |
| 11 | Lemmas 4.4–4.6 gap traces / gap core / two cores (App. A) | `Adaptive.*` | todo |
| 12 | Lemmas 4.7–4.8 near core / two large (App. A) | `Adaptive.*` | todo |
| 13 | Prop 5.1 local finisher | `Finish.local_finish` | todo |
| 14 | Thm 5.2 finishing theorem | `Finish.finish` | todo |
| 15 | Prop 5.3 rank seven | `RankSeven.*` | todo |
| 16 | Lemma 6.1 endpoints (integers) | `Gaps.endpoints` | todo |
| 17 | Props 6.2–6.4 three gaps | `Gaps.*` | todo |
| 18 | §7 main proof (k ≥ 7 only; padding step not needed) | `Main.six_sevenths` | todo |

Official wording: `SixSeventhsErdosWording` (frozen, "exactly 7") follows from the
manuscript statement by `Bridge.six_sevenths_erdos_wording_of` — DONE.

Audit at the end: `Lean644/Audit.lean` with `#print axioms`, blind back-translation, non-vacuity.

## Findings log (fidelity / errors found in the manuscript)
- Lemma 3.1: inequalities `2k+2a+b <= 4T` and `2k+2a+c <= 4T` are redundant (implied by
  `3k+a <= 4T` and `a+b, a+c <= k`); confirmed by the Lean proof of `hall_sizes`, which does not
  use them. Harmless. Also: the remaining hypotheses are exactly feasibility (brute force, k <= 8).
