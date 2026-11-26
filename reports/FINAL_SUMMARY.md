# Erdős Problem #644: final summary of the research phase

*26 November 2026. This is the authoritative entry point. Where any other document disagrees with it on the status
of a claim, [`notes/LEDGER.md`](../notes/LEDGER.md) decides, and this file should be corrected.*

**Notation.** H is a family of sets, τ(H) its transversal number. H is **(7,2)** if every subfamily of at most seven
members has a transversal of at most two points; f(k,7) is the largest τ of a k-uniform (7,2)-family. A **good seven**
is seven members with no 2-point transversal. For a k-uniform family on n points write s = n − 7k/4, e = τ − 3k/4,
T = τ − 1 and r = n − k − T (the covering excess: every (k+r)-set contains a member). A **pencil** is three members with
empty common intersection; its weight is |x₁ △ x₂ △ x₃|.

**Status tags** (as in the ledger). **LEAN**: machine-checked in Lean 4/Mathlib, standard axioms, no `sorry`.
**VERIFIED**: hand proof that passed an independent, fresh-context adversarial check (report in `notes/verify/`).
**EXACT**: exact or exhaustive computation, with certificates re-checked by separate code where stated.
**HAND**: hand proof by the project, not independently checked.

## 1. Status

**Erdős #644 is not solved.** We do not decide whether f(k,7) = (3/4 + o(1))k, and we give no bound on f(k,7) better
than the published ⌈7k/8⌉ of Fon-Der-Flaass, Kostochka and Woodall (FKW 1999). What we did achieve: verified upper
bounds on τ as a function of the ground-set size n. Every k-uniform (7,2)-family on n ≤ 2k points has
τ − 3k/4 ≤ (3/11)(n − 7k/4) + 21/11 (slope 3/11, previously 1/3), and near n = 7k/4 the slope is 1/5 + o(1) (Frankl–Wilson).
These bounds do not bound f(k,7) by themselves, because padding with private points makes n arbitrarily large. Around
them sit an exact classification of good sevens below 11k/6 (all are of Fano type), theorems ruling out several
structured classes of counterexamples (rich families, near-complete blocks, coset families with few classes), the
exact values f(6,7) = 5 and f(7,7) = 6, and about 20 Lean-checked lemmas. We also identified the barrier: arguments
that use seven-freeness only through pencils cannot get below slope ≈ 0.18, and the remaining problem is a 7-term
supersaturation question for exponentially sparse covering families.

## 2. Certain results (LEAN / VERIFIED / EXACT only)

Each item gives the statement, where the proof is, and the check. "PAPER" is [`reports/PAPER.tex`](PAPER.tex) (PDF alongside).

1. **Main bound, slope 3/11** [VERIFIED]. Every k-uniform (7,2)-family on n ≤ 2k points has
   τ ≤ (3n + 3k + 21)/11, i.e. e ≤ (3/11)s + 21/11, for every k ≥ 1. The Fano classification is not used.
   *Proof:* PAPER Thm 9.5 (`thm:main`); `notes/PROGRAMME3_LT.md`. *Check:* `notes/verify/PEN_P1.md` (C), own code in
   `compute/verify_pen/` (computed to n ≤ 11k/5; the constant was lowered from 24 to 21 by the referee).
2. **Pencil bound, PEN(1/2)** [VERIFIED with fixes]. If H is k-uniform and (k+r)-covering on n points, T = n − k − r,
   4T ≥ 2k + 5r + 3 and 3r ≤ 2k − 2, then H has a pencil of weight ≤ ⌊3r/2⌋ + 1. The size conditions are needed:
   SAT witness at (n,k,r) = (12,6,3), re-checked by brute force [EXACT]. *Proof:* PAPER Thm 9.4 (`thm:pen`), with the
   pair bound and centred dump (Lemmas 9.2, 9.3). *Check:* `notes/verify/PEN_P1.md` (A).
3. **Lemma P1, every n** [VERIFIED]. If H has members of size ≤ k, T < τ(H), and some pencil has weight ≤ 4T − 3k − 6,
   then H has a Fano-type good seven. So in a (7,2)-family every pencil has weight ≥ 4T − 3k − 5. No condition on n.
   *Proof:* PAPER Lemma 9.1 (`lem:P1`); `notes/PROGRAMME2_C.md` §4. *Check:* `notes/verify/PEN_P1.md` (B).
4. **Frankl–Wilson pencils, slope 1/5 near 7k/4** [VERIFIED with fixes]. With ν = n/k, p the least prime ≥ (k+r+1)/2
   and g the largest prime gap up to k: if r ≤ (c₀(ν) − o(1))k, a covering family has a pencil of weight ≤ r + 2g
   (c₀ = 0.02976, 0.04009, 0.05979 at ν = 7/4, 11/6, 2). Hence e ≤ max((s + 2g + 10)/5, s + 1 − (c₀ − o(1))k),
   so e ≤ s/5 + o(k) for n ≤ 1.79406k, and a counterexample with e = εk, ε ≤ 0.00881, has n ≥ (7/4 + 5ε − o(1))k.
   *Proof:* PAPER Thm 9.6 (`thm:FW`); `notes/PROGRAMME4_PEN.md`. *Check:* `notes/verify/PEN_FW.md`, own code in
   `compute/verify_fw/` (c₀ and thresholds are numerical roots, recomputed independently).
5. **Fano classification below 11k/6** [VERIFIED, EXACT; computer-assisted]. If seven sets each of size ≥ k have union
   of size < 11k/6 and no transversal of size ≤ 2, they form a Fano-type seven. Method: all 1 422 564 maximal intersecting
   families on [7] (716 classes; matches OEIS A001206), one LP per class with rational primal and dual certificates
   checked exactly; the Fano class has value 7/4 and every other feasible class ≥ 11/6. 11/6 is sharp for this LP
   relaxation (nothing more is claimed). *Proof:* PAPER Thm 3.1 (`thm:class`). *Check:* `notes/verify/programme2_task0.md`
   (two independent methods), code `compute/programme2/verify/maxint7_*`.
6. **Pencil-sum identity** [VERIFIED]. For a Fano-type seven B_ℓ ⊆ R_ℓ with pencil sums s_p = Σ_{ℓ∋p} B_ℓ and
   j_x = #{ℓ : x ∈ B_ℓ}: Σ_p wt(s_p) = Σ_x j_x(4 − j_x) ≤ 3(4|⋃B_ℓ| − Σ|B_ℓ|); if the right side is 0, then
   {∅} ∪ {B_ℓ} is a 3-dimensional subspace. Consequences [VERIFIED]: the coset obstruction (a k-uniform coset family
   with 7ρ_par > 3(4n − 7k) has no Fano-type seven) and a three-line proof that the FKW parity family is (7,2) with
   τ = 3m + 1. *Proof:* PAPER Lemma 4.1, Cor 4.2 (`notes/PROGRAMME_2.md`, Lemma 5). *Check:* `notes/verify/programme2_task0.md`.
7. **Theorem RA (rich families)** [VERIFIED]. If H consists of nonempty sets of size ≤ k, τ*_b(H) ≤ 7/3 − η and
   τ(H) > (k+1)/2 + 49/(3η), then H is not (7,2). (τ*_b is the least total weight of a point weighting giving every
   transversal weight ≥ 1.) It uses Lemma A0 [VERIFIED, LEAN]: if every three members share a point, τ ≤ (k+1)/2.
   *Proof:* PAPER Thm 5.2; `notes/PROGRAMME2_A.md`. *Check:* `notes/verify/theorem_RA.md` (end-to-end tests k = 40–140).
8. **Theorem NC (near-complete blocks)** [VERIFIED]. If H (sets of size ≤ k) is (W,d)-complete (every (k+d)-subset of W
   contains a member), |W| = w ≥ k + d + 2, and τ(H) > (k+1)/2 + max(0, 2k + 2d + 3 − w), then H is not (7,2)
   (under the "at most seven" definition). Corollary: with T = ⌈(3/4+ε)k⌉ and τ ≥ T + 1 (the "+1" closes a rounding
   gap for odd k), every block with w ≥ (7/4 − ε)k + 2d + 3 is fatal. With W = V it gives τ ≤ (2n + k + 11)/6 for every
   n (DERIVED in PAPER eq. (1); not separately re-checked). *Proof:* PAPER §6; `notes/PROGRAMME2_NC.md`.
   *Check:* `notes/verify/theorem_NC.md`.
9. **Theorem D (c* = 1)** [VERIFIED]. For a covering coset family H = (a + C) ∩ (V choose k), covering at level
   w = k + r, T = n − w, e = dim span{hᵢ + hⱼ}: if n ≥ 2e + 1 and e ≤ min(w, T), then ρ ≤ r + 1 (ρ ≤ r for even w),
   also for ρ_par; the hypotheses hold when dim C ≥ k + r > T. With the counting bound, dim C ≥ k + r for all N < 11/6
   at t = 3/4 [VERIFIED]. *Proof:* PAPER Thm 7.1, Cor 7.2. *Check:* `notes/verify/theorems_9prime_D.md`.
10. **Theorem 9′** [VERIFIED]. A coset family with three pairwise disjoint Ω₁, Ω₂, Ω₃ ∈ a + C satisfying (H0) Σ|Ωᵢ| ≤ 4n − 7k,
    (H1) |Ωᵢ| ≡ k (mod 2), and the few-classes hypotheses (H2)–(H4′) contains seven distinct members forming a Fano-type
    seven. *Limit [GAP, recorded]:* (H2)–(H4′) need codimension O(log k); D + 9′ do **not** close general coset families.
    *Proof:* PAPER Thm 7.4; `notes/PROGRAMME2_TASK3.md`. *Check:* `notes/verify/theorems_9prime_D.md`.
11. **Small values f(6,7) = 5 and f(7,7) = 6** [EXACT, resting on VERIFIED confinement]. Lower bounds by hand
    (Schönheim covering bound: K₁₀⁽⁶⁾ and K₁₂⁽⁷⁾ are (7,2)). Upper bounds: exhaustive eight-request strategy trees
    (88 and 207 requester nodes) that keep their three anchors, replayed by an independent checker; the transfer from
    the confined game uses TWIN §13 [VERIFIED]. The checker's use of interchangeable equal-type points is a hand step.
    *Proof:* PAPER Thm 8.1 (`thm:small`); `notes/FRESH_C.md` §14. *Check:* `notes/verify/small_values.md`, `notes/verify/TWIN13_16A.md`.
12. **Two-cell profile table, k = 8..20** [EXACT for the upper bound]. For each k = 8..20 and T = ⌊(3k+5)/4⌋, no
    one- or two-cell profile family (membership depends only on the trace sizes on a fixed 2-partition of V) on
    n ∈ [k+T, ⌊2.4k⌋] points is (7,2) with τ > T: 1904 UNSAT instances, every certificate re-checked by `check_cert.py`
    (imports nothing from the search; final step is a plain-Python exhaustive hitting-set search). The matching lower
    bounds (τ = ⌊(3k+5)/4⌋ attained for 9 ≤ k ≤ 20 by complete or parity families; 6 at k = 8) are **solver-only**
    (CP-SAT, and HiGHS for complete families). Scope: profile families only; nothing here bounds f(k,7).
    *Source:* `notes/PROGRAMME4_CELLS.md` §3, certificates in `compute/programme4/cells/certs/`. Not yet in the ledger.
13. **Lean-checked lemmas** [LEAN]. About 20 lemmas in `Lean644/*.lean`, including: the request principle
    (`exists_response`); padding (`padding_iff`) and the minimal-frame lemmas (`private_set`, `saturation`, `antichain`);
    the one-anchor bound τ ≤ ⌈(n−k)/3⌉ + 2⌈k/4⌉ (`TheoremA.lean`); the Fano criterion and Fano blocks; the flat
    7-tuple lemma; the colouring criterion and Lemma A0 (`RichFamilies.lean`); anchor and petal reductions; the waste
    adversary; tight/sparse triple, trace, pair-gap, three-centres, stability 11.1, lopsided-top 6.4; and Lemmas
    4.1–4.8 of the external 6/7 manuscript. The 6/7 theorem itself (`SixSeventhsStatement`) is **not** proved in Lean.
    *Check:* `lake build` and `scripts/check_trust.sh` (frozen `Statements.lean`, no `sorry`/`admit`/axioms).
14. **Confined-game results** [VERIFIED, but conditional]. For families confined to the union V of three anchors
    (|V| ≤ 3k): the crowded region N ≤ 3t − 1/2, the bottom strip 3t − 1/2 < N ≤ 5t − 2 (Frankl–Rödl, ineffective ε₀),
    the petal side up to two residues, and Theorems S, S⁺, W, H, R excluding structured counterexamples in the core
    window. These do **not** bound f(k,7): the lift G2 ("far replies") is open. *Source:* `docs/RESULTS.md` §1–5,
    `notes/CORE.md`, `notes/PETAL.md`, `notes/TWIN.md`; reports in `notes/verify/`.

**Scoreboard** (proven bounds on e for k-uniform (7,2)-families): e ≤ s/5 + o(k) for n ≤ 1.794k [VERIFIED];
e ≤ 3s/11 + 21/11 for n ≤ 2k [VERIFIED]; e ≤ s/3 + 13/6 for all n [LEAN]; e ≤ k/8 + 1 for all n (FKW, published).
So a counterexample with e ≥ εk needs n ≥ (7/4 + 11ε/3)k − O(1) (ε ≤ 3/44), and the Fano range n < 11k/6 matters only
for ε < 1/44 + O(1/k).

## 3. Supported but not independently verified (HAND)

Everything in this section is a project hand proof, often with exact per-instance checks, but **no fresh-context
verifier has passed it**. Nothing in Section 2 depends on it.

- **3/11 extended to n ≤ (8k+11)/3** [HAND]. A two-stage dump weakens the pencil-bound size condition to
  4T ≥ 2k + 3r + 3. `notes/PROGRAMME5_BULK.md` §2.
- **NC-P, relative pencil lemma** [HAND, from VERIFIED PEN + P1]. If τ(H) ≥ T + 1 and a block (W,d) has
  4(w − k − d) ≥ 2k + 5d + 3, 3d ≤ 2k − 2 and d ≤ (8e − 22)/3, then H has a Fano-type seven (works down to
  w ≈ 3k/2 + 9d/4). `notes/PROGRAMME5_COMPRESS.md` §2.
- **HUB lemma** [HAND; 1403 brute-force checks]. A non-Fano (type 195, "Fano minus a line") analogue of P1 for pencils
  with small or balanced pairwise parts, independent of n. `notes/PROGRAMME5_BULK.md` §3.2.
- **P1′** [HAND]. Every pencil of a (7,2)-family has weight ≥ 4T − 3k − 2 (P1: −5); would improve the 3/11 constant.
  `notes/PROGRAMME4_P1.md`.
- **Theorem QK** [HAND]. For deg q ≤ 2 and 4n − 7k ≥ 128, the full level set {B : |B| = k, q(B) = a} has a Fano seven
  or τ ≤ 26; quadratic level sets are dead as counterexamples. `notes/PROGRAMME5_QUAD.md` §2.
- **Theorem O** [HAND + exact certificate]. For t < 8/9 and ν > 2 + t a two-cluster adversary defeats every bounded
  combination of the project's static covering lemmas, so they cannot give ε < 1/8 for ν ≥ 23/8. `notes/PROGRAMME5_BEAT78.md`.
- **Theorem P** [HAND]. In the critical bridge configuration at t = 6/7 − δ, any first request containing X ∪ Y ∪ Z
  leaves two disjoint complete bipartite pair sets whose continuation needs request mass 2x + 2y + 1 > 3t: no depth
  closes. `notes/PROGRAMME5_BELOW67.md` §2.
- **Depth-3 spectrum game capped at exactly 6/7** [HAND + computed grid, G = 168]. With all project lemmas plus the
  manuscript's moves, the game value is ε* = 3/28 for every ν ≥ 3 (adversary spectrum S* = [0, .268] ∪ [5/14, .435] ∪
  [10/21, 1)). `notes/PROGRAMME5_ADAPT.md` §2.
- **Matroid dictionary** [HAND]. τ(H) = critical number of U_H = {y : supp y contains a member}; H has a Fano-type seven
  iff U_H contains a PG(2,2), for every n. PAPER §10; `notes/PROGRAMME4_TOPO.md`.
- **(LT) = yes** [the identity is VERIFIED; the yes-answer is DERIVED]. For fixed ε > 0 and large k, every family with
  n < 11k/6 and τ ≥ (3/4+ε)k + 1 has a pencil of weight ≤ (12n − 21k)/7; so Lemma Q never certifies a counterexample.
  The identity is `notes/verify/PEN_P1.md` (D); the combination is PAPER Remark 9.7, not separately re-checked.
- **Hand check of the external 6/7 manuscript** [HAND; **not our result**]. The manuscript (credited to its authors;
  unrefereed; kept locally in `notes/sources/`, not distributed) claims f(k,7) ≤ ⌈6k/7⌉ for k ≥ 7. Its Lemmas
  4.1–4.8 are in Lean; we checked its remaining parts (Lemmas 2.5, 2.6, Prop 5.1, Thm 5.2, Prop 5.3, §7 assembly) by
  hand and found no gap. An independent referee is pending. `notes/PROGRAMME5_ADAPT.md` §3.
- **f(8,7) = 7** [EXACT computation, not yet independently re-checked; not in the ledger]. An explicit 8-uniform family
  on 15 points (2352 members) with τ = 7, checked (7,2) against all 68 classes of pair-coverings of K₁₅ by seven
  7-sets (two enumerators; exhaustive embedding, plus CP-SAT). With FKW's ⌈7k/8⌉ = 7 this gives f(8,7) = 7.
  `notes/PROGRAMME4_LADDER.md` §1.
- **Other HAND results**: Theorems B1, S0, S1 (coset families with many classes), C1/C2, Lemma Q, Theorem 2P,
  CR/SL1 reductions. PAPER §10; ledger.

## 4. The open frontier

- **Q1, the core below 11k/6.** For fixed ε > 0 and large k: must a k-uniform (k+r)-covering family on n < 11k/6
  points with τ ≥ (3/4+ε)k + 1 contain a Fano-type seven (equivalently a Fano plane in its pencil 3-graph, or a
  PG(2,2) in U_H)? One may assume it is thin, has no near-complete block, every pencil has weight ≥ 4T − 3k − 5, and
  e ≤ 3s/11 + O(1). `reports/OPEN_QUESTION.md` §5.
- **Q2, n ≥ 2k.** The same where good sevens need not be of Fano type ("Fano minus a line" types appear; HUB is the
  P1 analogue). Large n is equivalent to the whole problem (private-point padding), and no compression to n ≤ 2k is known.
- **The pencils-versus-sevens barrier** [heuristic: exact binomial estimates]. Random unions of about n³ cosets of a
  random linear code are covering, thin, block-free and far from cosets, with every pencil of weight ≥ λr for
  λ < λ* ≈ 0.83–0.90, yet they have many good sevens. So arguments that use seven-freeness only through pencil
  weights cannot beat τ ≤ 3k/4 + ≈0.18s. Pencils reach PEN* (sharp, slope ≈ 0.18) at best; PEN(η) for η < 1/2 is
  open beyond r ≤ c₀k ("Target D"). Slope 0 needs a 7-term supersaturation argument for exponentially sparse
  families. PAPER §11 (b)–(c); `notes/PROGRAMME4_INVP.md`.
- **The bridge configuration below 6/7.** Two near-disjoint members F, G joined by a bridge E with feet ≈ 3k/7 and
  5k/14 is the configuration on which every closure we know stops at 6/7 (Theorem P, the depth-3 game). Live leads:
  forcing answer traces into the gaps of S* away from the rigid cover shape (`notes/PROGRAMME5_SPECTRUM.md`; the joint
  three-request MILP of `notes/PROGRAMME5_BRIDGE.md` Part 1 did not finish), and closures that drop E, F or G. On the
  counterexample side, seven-free spectrum-respecting seed families reach only τ = 4 at k = 14 (record 11): the seed
  is killed by the "2×2 grid six" (Part 2).
- **Lifting (G2).** Transfer of the confined-game results to general families (anchor-keeping certificates, or a
  far-replies lemma). `notes/FRONTIER.md` §1.
- **Record below 7/8.** The depth-1 sparsest-anchor game cannot reach 17/20; at t = 43/50 the exact cover leaves three
  small pockets, so **no bound below 7/8 is certified**. `notes/RECORD.md`.

## 5. Dead routes (one line each; mostly HAND obstructions)

- Junta approximation and spread lemmas: families are < 2.28-spread; juntas need k < n/C. CORE §50–53.
- Fractional relaxation + rounding: rounding in the window is the problem itself. CORE §80–84.
- Hypergraph containers + supersaturation: codegree condition fails; supersaturation already implies CP. CORE §85–89.
- Flag algebras / SDP: "no good seven" does not pass to the limit object. CORE §75–79.
- Entropy methods: certificates need cyclic dump constraints. CORE §70–74.
- Adaptive density via links, traces, exclusions: links leave every closed region. CORE §100–104; `notes/verify/dead_routes.md`.
- Covering-design stability / code constructions: size is the wrong measure. CORE §105–109.
- Fractional pair-cover LP: ρ* small does not give ρ ≤ 7. CORE §115–119.
- Multi-pool designs + isoperimetry: needs β ≈ 10⁻⁵. `notes/FABLE_A.md`.
- Size-2 co-type static certificates for N > 2: not forced, not steerable. `notes/FABLE_C.md` §3.
- Kernel lemma, regularity reduction, c(N)·k cell bound, bounded-request game. CORE §34–35, §39, §45.
- BLR / linear Fourier gluing from the seven-condition. `notes/PROGRAMME2_C.md`.
- Counting with density increment: works only for dense families (γ ≲ 4ε). `notes/PROGRAMME3_GAMMA.md`.
- Lemma Q / the BAND shape as a counterexample route: (LT) holds. Ledger, PEN(1/2) entry.
- INV-P as the crux: vacuous as stated, false for λ < λ*. `notes/PROGRAMME4_INVP.md`.
- Topological rainbow criterion: needed connectivity unprovable by standard tools. `notes/PROGRAMME4_TOPO.md`.
- Slice rank, Chevalley–Warning, MacWilliams: blind to the k-uniform covering structure. `notes/PROGRAMME5_ALG.md`.
- Random Fano colourings (slope 3/7) and the coarse-threshold dichotomy CTS (false). `notes/PROGRAMME5_SEVEN.md`.
- 7INV in coset form: the Fano system has true complexity 2. `notes/PROGRAMME5_7INV.md`.
- Quadratic level sets as counterexamples (Theorem QK). `notes/PROGRAMME5_QUAD.md`.
- One-configuration lemmas beating 7/8 at n ≥ 2k: capped at 1/8 (Theorem O). `notes/PROGRAMME5_BEAT78.md`.
- Compression via τ-critical subfamilies, pencil padding, merging, random restriction. `notes/PROGRAMME5_COMPRESS.md`.
- Depth-1 record game at 17/20. `notes/RECORD.md`.
- Bridge seed families: killed by the 2×2 grid six. `notes/PROGRAMME5_BRIDGE.md` §2.
- Full catalogue with obstructions: `reports/FAILED_ROUTES.pdf`.

## 6. How to verify

- **Lean:** `lake exe cache get && lake build && scripts/check_trust.sh` (checks that `Lean644/Statements.lean` is
  unchanged and that no `sorry`, `admit`, extra axiom or `native_decide` appears).
- **VERIFIED proofs:** each report in `notes/verify/` names the target section, gives a step-by-step check, and the
  independent test code (in `compute/verify*/`, `compute/programme2/verify/`). Run with `py -3` (Python 3 with
  `pulp`, `highspy`, `python-sat`).
- **EXACT computations:** certificates and their separate checkers sit next to the searches in `compute/`
  (`compute/README.md`). An UNSAT result counts as exact only when its certificate was re-checked by separate code;
  otherwise it is "solver-only", as marked above.
- **Statuses:** `notes/LEDGER.md` is authoritative; `docs/RESULTS.md` indexes results with proof locations.
- **Problems:** counterexamples to any VERIFIED claim are especially welcome via issues.
