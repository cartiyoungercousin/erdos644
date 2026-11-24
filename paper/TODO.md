# TODO: unverified items in paper/draft.md

## [cite?] (references not checked against sources)
- Problem page erdosproblems.com/644: exact wording and the table of known values (taken from notes/NOTES.md, second-hand).
- EFKT92 (Erdos, Fon-Der-Flaass, Kostochka, Tuza, Siberian Adv. Math. 2 (1992) 82-88): values for r=3..6 are second-hand; paper not accessible. Novelty of the Lean tight-triple lemma and Theorem A relative to it is unconfirmed.
- Erdos-Hajnal-Tuza 1991 and Kostochka 2002: abstract-level only.
- 2026 claims: cubres/erdos-644-research (six_sevenths_v3, 6/7), skyvegetable666/erdos-644-11-over-13, arXiv:2610.02945 (Ansatz): authors, titles, dates taken from notes/LITERATURE.md; not re-checked.
- Mills (Ars Combin. 8 (1979)) covering-number thresholds; "exact C(v,k,2) known for v/k <= 13/4" (from a web-search snippet, unchecked).

## [to check]
- La Jolla Covering Repository (site unreachable from this environment, search returned no table values): C(9,4,2)>=8, C(10,5,2)<=7, C(10,4,2)>=8, C(11,5,2)<=7, C(12,5,2)>=8, C(13,6,2)<=7 (the facts behind the lower bounds f(5,7)=5.., f(6,7)>=5, f(7,7)>=6). Our own source is a single ILP (complete_int.py), not independently re-run.

## Items used but NOT in LEDGER.md (status as stated in the notes)
- f(6,7)=5, f(7,7)=6 (FRESH_C 14.1-14.3): EXACT certificates, conditional on the anchored reduction (HAND).
- Seven-request thresholds 5/6, 11/13, 7/8 (FRESH_C section 10, PROOFS section 6): FLOAT MILP only; 4/5 for class W is hand-proved (Theorem 8, Lean waste_core/waste_adversary).
- Lemma 3 corollaries 3a/3b, FRESH_B 1.3 (complete families <-> covering numbers), Theorems C and D (TWIN 13.4, 13.5), Theorem B (13.3), Prop. 16.A text: only "TWIN section 13" / "16.A" appear in the ledger.
- CORE section 48 (hash-like selectors, Kleitman remark, sunflower-Ramsey SAT): interim, not in ledger, not claimed.
- PETAL 23.3 plan-game formula s(x): fitted to LP values, not proved.

## Unverified dependencies / inconsistencies to resolve
- All HAND items: no verifier report exists (notes/verify/ empty when drafted). Pending: V1 (S, S+), V2 (anti-plan, W), V3 (density S, Q', CP<=(Sigma)), V4 (J', J''), V5 (DS, DS-b, FF, AP). Not scheduled in ledger: Theorems J, K, L, T, Q, P, N, TWIN 13, 16.A.
- CORE 1.2 says TWIN 16.A "= Lean TheoremA"; Lean TheoremA.lean is the one-anchor Fano template (tau <= ceil((n-k)/3)+2ceil(k/4)). Ledger lists 16.A as HAND. Resolve.
- Ledger lists Lemmas 4.1-4.8 of the 6/7 manuscript as LEAN, STATUS_AND_PLAN.md (2026-11-23) says 4.1 WIP; the main 6/7 theorem (SixSeventhsStatement) has no proof in Lean644/ (only Bridge.lean). Confirm via lake build and #print axioms (not re-run for this draft).
- PETAL.md says petal reduction "not Lean-formalised" but PetalReduction.lean exists (ledger: LEAN). P3(ii) strategy transfer is prose only.
- Replays (J'', DS, AP, anti-plan) test one scripted adversary each; claim for all adversaries is by hand proof only.
- CORE window statement inconsistency: CORE 1 uses 5t-2 < N, CORE 7/33 use 3t-1/2 < N; draft uses 3t-1/2 (the proved range). Interval (3t-1/2, 5t-2] has only float evidence at t=0.76.
- Statements are first-order (k -> infinity, masses); finite-k rounding not done for profile selectors (47.4) or S++.
