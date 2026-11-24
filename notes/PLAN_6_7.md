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
| 4 | Lemma 2.4 four edges (candidate pairs of E,F,G,K) | `FourEdges.four_candidate_core`, `closes_of_three_requests` | DONE |
| 5 | Lemma 2.2 integral allocation | replaced by explicit splits | n/a |
| 6 | Lemma 2.5 balanced request; 2.6 capped request | `Seeds.*` | todo |
| 7 | Lemma 3.1 Hall allocation; Cor 3.2 | `Static.hall_sizes`, `HallClose.hall_closes`, `HallClose.hall_cor` | DONE |
| 8 | Lemma 3.3 boxed triangle (pure integers) | replaced by explicit witness `Symmetric.symmetric_sizes` | DONE |
| 9 | Lemma 3.4 symmetric allocation | `Symmetric.symmetric_closes` | DONE |
| 10 | Lemmas 4.1–4.3 one core / split A / split B (adaptive, App. A) | `OneCoreLemma.onecore_closes` (4.1) DONE, `SplitA.splitA_closes` (4.2) DONE, `SplitB.splitB_closes` (4.3) DONE; shared: `Adaptive.no_core_candidate`, `SplitA.no_core_closes` | DONE |
| 11 | Lemmas 4.4–4.6 gap traces / gap core / two cores (App. A) | `GapTraces.gapTraces_closes` (4.4), `GapCore.gapCore_closes` (4.5), `TwoCores.twoCores_closes` (4.6); def `IntersectionGap` | DONE |
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

## Computational audit of the case logic
`compute/audit_cases.py`: for every k in 7..400 with T = ceil(6k/7), enumerates all cell sizes
allowed in Prop 5.1 (local finisher), Lemma 6.1 (endpoints) and Props 6.2–6.4 (three gaps), and
checks that the lemma invoked in each case has all its integer hypotheses. Result: 0 failures
(~2M lemma invocations for k <= 120). Mutation test (tightening one inequality of Lemma 3.4 by 1)
produces 17 failures, so the audit is sensitive. NOT yet audited: Thm 5.2 (finishing), Prop 5.3
(rank seven), and the internal arithmetic of the adaptive lemmas (Appendix A) — Lean will cover these.

## Findings log (fidelity / errors found in the manuscript)
- Lemma 3.1: inequalities `2k+2a+b <= 4T` and `2k+2a+c <= 4T` are redundant (implied by
  `3k+a <= 4T` and `a+b, a+c <= k`); confirmed by the Lean proof of `hall_sizes`, which does not
  use them. Harmless. Also: the remaining hypotheses are exactly feasibility (brute force, k <= 8).
