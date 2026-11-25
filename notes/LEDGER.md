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
| Anchored reduction (TWIN §13), anchor lemma, Theorem A, padding transfer | TWIN §13 | VERIFIED (W1), for anchor-keeping strategies only. Confined results (16.A, bottom strip, CP) do not keep the anchors; transferring them needs the far-replies lift G2 (TWIN §17), which is OPEN (notes/FRONTIER.md §1) |
| Theorems J, K, L (petal spread case) | PETAL §3, §7, §8 | VERIFIED (W3; L's statement should repeat p <= t; J's band disjunct untested in simulation) |
| Concentrated case N <= 3T - k/2 - O(1) | TWIN 16.A | VERIFIED at first order (W1); finite-k proof has a GAP at line 904 (Theorem C's half-split isn't integral), and O(1) can't be 0 (K(9,5): τ = 5 > 4, N = 9 <= 9.5). Repaired (FINITE_K.md): N <= 3T - k/2 - 1 holds; 142,350 end-to-end plays |
| Slack count, Theorem T, Theorem Q (= Q′) | CORE §2–§4 | VERIFIED (W2; Q's 'iff' holds only for the fixed quadrangle scheme) |
| Pool theorem P | CORE §5 | VERIFIED at first order; FAILS at finite k when εk = 1/4: counterexample (k,T,N,|Z|) = (5,4,9,0), since C(9,4,2) = 8. Finite-k repair (notes/FINITE_K.md): P holds for 4T >= 3k with 4T != 3k+1; rounding lemma proved, all 48,864 instances k <= 30 pass |

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
| Reduction sanity check: the FKW parity family (m = 3, k = 12, ε = 0) has no good seven and no (Σ)-shape; pencils are excluded by parity | CORE §110–§114 | HAND + EXACT |
| Window exact searches: (10,8,21) is the smallest genuine instance ((13,10,·) is degenerate: the complete family already has τ = 11); 231 symmetric (cell-invariant) searches are all UNSAT with checked certificates; the reversed-order template dies at (10,8,21) | CORE §110–§114 | EXACT (certificates) / solver-only (template) |
| Literal SPOIL false | CORE §40 | EXACT |
| SPOIL at all depths is not a disproof | CORE §43 | HAND |
| One-bit rule has a good seven | CORE §44 | EXACT (89 instances) |
| Junta approximation in measure (Dinur–Friedgut, Keller–Lifshitz); spread lemmas (ALWZ, FKNP) | CORE §50–§53 | DEAD (proved: the families are at most n/c < 2.28-spread; junta theorems need k < n/C) |
| Kupavskii–Zakharov decomposition into head classes + remainder (H_τ) | CORE §54 | HAND; restates the hash-selector problem, not a reduction |
| Fractional relaxation + rounding (τ* <= (35k)^{1/3} for (7,2)-families; rounding in the window is CP itself; Alon–Kleitman ε-net route can't give 3/4) | CORE §80–§84 | DEAD (proved) |
| Hypergraph containers + supersaturation (codegree condition fails above a thin strip; the supersaturation step needed already implies CP) | CORE §85–§89 | DEAD (proved) |
| Flag algebras / SDP on the limit object (Cauchy–Schwarz constraints automatic; CP is not a density statement; 'no good seven' doesn't pass to the limit, corrects §39.3) | CORE §75–§79 | DEAD (proved) |
| Transfer lemma (finite-depth first-order win at t' < t gives CP at t for large k) | CORE §75 | VERIFIED (backlog.md; strategy may depend on the family; 'win' = zero bad mass) |
| Density / forbidden-pattern arguments above the bottom strip (Theorem 96.1: the c-sets avoiding a point and containing a fixed Y have no static certificate yet density rate <= 0.17γ; no pattern rate can beat γ) | CORE §95–§99 | Theorem 96.1 VERIFIED (notes/verify/thm96_1.md); 'no rate beats γ' holds only for density-only hypotheses and static certificates (float comparison) |
| Frankl–Wilson makes the bottom strip effective (ε_0 ≈ 0.0088), except a vanishing top sliver | CORE §97 | FLOAT/HEUR |
| Adaptive density / dependent random choice via links, traces, exclusions (links move (N,t) away from every closed region; Theorem 102.1: the static-certificate budget S_q = (q-3)δ + (7-q)ε depends only on (N,t,q)) | CORE §100–§104 | DEAD (HAND) |
| Links audit (§100–§104) | notes/verify/dead_routes.md | VERIFIED dead; 100.1(c) reworded (|S∖Y| > ε); GAP: Theorem 102.1's corollary fails for N > 2, q >= 4. The correct budget is S_q + m_2 (size-2 co-type mass), so static certificates with size-2 co-types are NOT excluded in the upper window |
| Entropy method (Gilmer size form; iid copies AHS/Chase–Lovett; correlated laws / pencil supersaturation; witness-pair union bound); obstruction: certificates need cyclic dump constraints, entropy handles only acyclic ones | CORE §70–§74 | DEAD (HAND) |
| core9 two-class reversed-order family at (8,6,15): 0 pencils (vs 128,301 random-predicted) and no (Σ)-shape at ε = 0 | CORE §72 | EXACT |
| Covering-design stability / anti-Pasch analogy / code constructions (size is the wrong measure: pool families are minimal yet far above the Schönheim bound; random designs are supercritical; code redundancy needed > covering budget) | CORE §105–§109 | DEAD (HAND/FLOAT) |
| Fractional pair-cover (edge-clique-cover) LP: (N/c)^2 <= ρ* <= (N/t)^2; a fixed request rule can't beat the random T-set; no 'ρ* small implies ρ <= 7' can hold (pools with ρ* ≈ 5.44 but ρ >= 8) | CORE §115–§119 | DEAD as a route (HAND + EXACT) |
| Multi-pool designs + isoperimetry (FABLE_A): dead as a route to CP (it needs β < s²/(32t), about 10^-5); survivor Theorem 2P (two-class reversed-order rule loses for 5t-2 < N < 17/8), which rests on a float LP | notes/FABLE_A.md | DEAD route; 2P HAND |
| Size-2 co-type static certificates for N > 2 (FABLE_C §3): not forced (pool + 3 confining members has m_2 = 0; 124 exact witnesses at (10,8,21)) and not steerable (double-counts the dump) | notes/FABLE_C.md | DEAD (HAND + EXACT) |
| Σ_6 (six members whose uncovered-pair endpoints fit in a T-set) | notes/FABLE_C.md §2 | proved to imply CP, but it is CP with one inessential dump; dropped |
| (Σ) on data: 0 of 2896 window families shape-free; 949 of 3083 forced sevens shape-free, 57 with no static certificate | notes/FABLE_C.md | EXACT / solver-certified |
| Collinear-repair adaptive certificate: the pool finish survives misses <= 4ε/7 of Y per reply | notes/FABLE_C.md §5 | VERIFIED (backlog.md; exhaustive adaptive games) |
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
| Lemma PC (cross overlap <= 2 - 2c - t), Lemma YC, Theorem CR (absorbing-set play without disjoint regions); fixed two-class gap reduced to θ(t) < c < 1 - 5t/9 and to the one-class statement SL1 | PETAL §40 | VERIFIED (backlog.md; CR for fixed families; YC needs m_P(A) > 0) |
| Pooled strip family test: the full and natural τ > T subfamilies all fail (7,2) at 5 instances; centres-first play beats the §31 adversary A_T (even inside its 'loss region'), but a leak-on-triple-centre variant beats that plan | PETAL §45 | EXACT + HAND; strip still open |
| SL1 (petal item 3): exact arena form false (three-arena triangle); 'cost <= τ + (8/3)d' false; K-stability criterion: SL1 holds for t > (112+42K)/(151+51K); no family beats SL1's margin in searches of up to 5 arena classes; missing: an explicit K for general classes | PETAL §41 | HAND + FLOAT; open |
| Theorem N adversary beats 2+2 | PETAL §12 | VERIFIED (W3) |
| 12.3 (𝒜 loses to 4+3 when she knows the arenas) | PETAL 12.3 | GAP (W3): assumes the ground set is the two arenas; a leak outside them breaks it. Check whether DS / the 𝒜 kill inherits this, or whether AP's pool covers it |
| 𝒜(t,δ), 𝒦₂ (c >= 0.5217) as obstructions | PETAL §20, §22 | DEAD |

## Minimal-counterexample frame (notes/MINIMAL_FRAME.md)
| Claim | Where | Status |
|---|---|---|
| Lemma 1 (padding: f with sets of size at most k = f), Lemma 3 (private sets), Lemma 4 (saturation), Corollary 5 (co-edge form), (G) equivalent to the 3/4 bound | MINIMAL_FRAME.md | VERIFIED + LEAN (Lean644/MinimalFrame.lean: private_set, saturation, antichain, padding_iff; standard axioms only) |

## Task 1 (saturation), notes/SATURATION.md
- FKW m=3: one loose incidence class (edges with 11 X-points, z their Y-point). Shrinking gives H1 (323,236 members, τ = 10, antichain, all classes saturated, (7,2) by hand + MILP). H1 contains the literal pencil shape yet has no good seven, so (Σ)(b) is invalid for non-uniform families. H1 is not yet minimal (only 12 members have private sets). [EXACT + HAND]
- Near-pool at (10,8,21): Corollary 5's U_z sets exist in 31/32 incidence classes. Saturation's consequences do NOT contradict near-pool structure; the open class does not shrink. [EXACT]

## Task 2 (proof side in the minimal frame), notes/TASK2.md — NEGATIVE
- Lemma 4U (ii) is implied by (i), so the uniform variant equals Lemma 4 restricted to points of degree >= 2. Near-pool test at (10,8,21) with (ii): 31/32 classes still have U_z. [HAND + EXACT]
- Questions (a)–(c) give only restatements or identities. The summed slack is the identity ‖H‖(4δ+1); no waste lower bound follows.
- Complete families on ⌈7k/4⌉ points (k = 5, 9, 13) are saturated in every incidence and satisfy all the frame's lemmas (O(1) rounding effects). The minimal frame alone gives no leverage on the window.

## Programme 2 (notes/PROGRAMME_2.md)
- Task 1 (notes/PROGRAMME2_TASK1.md): every stored family is thin at its small k, because the max-atom term 7·max y (≈ 7/τ) dominates. tau*_b values: FKW and H1 2.2, near-pool 1.75–2, k=8 2–2.29, U1 533/220 ≈ 2.42, k=10 window families exactly 7/3. Asymptotically Theorem 3 needs tau*_b < 7/3 as atoms tend to 0 (coordinator's reading, not proved). [EXACT/float LP]

- Task 0 (notes/verify/programme2_task0.md):
  - Lemma 2, Theorem 3, Lemma 5, Corollary 7, Lemma 8: VERIFIED.
  - Heavy-atom case FAILS as stated: K_10^(6) is (7,2) with τ = 5 > 3k/4 and tau*_b = 2. So 'rich implies not (7,2)' is false at finite k, and asymptotically it is a GAP. Refined Theorem 3H covers heavy atoms by placement LPs.
  - Every good seven is Fano-type for N < 11/6: VERIFIED EXACT (all 1,422,564 maximal intersecting families on 7 points, rational LP certificates; 11/6 is sharp).
  - (Σ)(a) in F₂ form: four-term relation, PASS. (Σ)(c): not a four-term relation (the pair sums and the triple sum all have weight >= n − T).
- Verification of 9′ and D (notes/verify/theorems_9prime_D.md):
  - Theorem 9′: VERIFIED. Theorem D: VERIFIED. Counting threshold: N < 1.938 (VERIFIED). Three disjoint parity Ω's: proved for N < 1.852.
  - GAP: the chain to a good seven needs 9′'s hypotheses H2–H4′, which assume codimension O(log k) (c <= 2^r). Theorem D only bounds codimension by T, so B is NOT closed for general coset families.
  - Between 11/6 and 1.938: only ρ_par <= r + 1 for a single Ω. Above 1.938: only Lemma 8.
- Piece A for large k (notes/PROGRAMME2_A.md; called 'Theorem A' there, renamed **Theorem RA** here to avoid clashing with the Lean TheoremA): if H has nonempty sets of size <= k, tau*_b <= 7/3 − η and τ > (k+1)/2 + 49/(3η), then H is not (7,2). Proof: put the heavy points (weight >= η/7, fewer than 49/(3η) of them) on one Fano point; Lemma A0 (if every three members share a point then τ <= (k+1)/2) gives three members missing them with empty triple intersection; plus Theorem 3H. VERIFIED (notes/verify/theorem_RA.md: every step passes; the A2 branch tested end to end on about 408 real families, k = 40–140).
- Lean (Lean644/RichFamilies.lean): Lemma A0, the colouring criterion (Lemma 2) and the A1 step of RA (weights as real hypotheses) are formalised; build + check_trust pass, standard axioms only [LEAN]. The full RA (heavy-point placement, Theorem 3H) is not yet in Lean. Literature (notes/LIT_A0.md): A0 is folklore-level (Nagy–Patkós Prop. 2.2 at r=3; Bishnoi–Das–Morris–Szabó Thm 1.7 for r-partite), tight on K_n^(k).
- Task 4 (notes/PROGRAMME2_TASK4.md, D2 measurement): every stored family with no Fano-type seven found is a ρ = 2 coset family up to at most 12 members (FKW exact; H1-type after deleting 12 sets; one k=8 family up to 1 member). The (8,6,15) pencil-free selector is exactly a parity function. Data support 'seven-free implies most members in one coset with ρ > 4T − 3k', but only in the weak regime 4T − 3k = 0, and seven-freeness is certified only for FKW. [EXACT/sampled]
- Task 2 (notes/PROGRAMME2_TASK2.md, D1): NO counterexample.
  - Theorem D [HAND + EXACT tests]: if dim C >= k + r, every covering coset family has ρ_par <= r + 1 (parity-correct), so c* = 1.
  - Counting gives dim C >= k + r for ω < 0.188 (t = 3/4), which contains all of N < 11/6. So D1 lands in 'B within reach' there.
  - For ω >= 0.188 (N >= 1.94) only ρ <= 2r + 1 is known.
  - Exact tables: ρ >= r + 2 only when τ <= 2. (7,14) is excluded for k >= 36; residue-class targets were corrected.
- Task 3 (notes/PROGRAMME2_TASK3.md): Proposition 9 as literally stated is FALSE (size parity; counterexample by hand + SAT). Theorem 9′, with correct parity |Ω_i| ≡ k (mod 2) and size hypotheses, is proved by hand: the 7×7 F₂ class system is always solvable, and size residues are repaired by same-class pairs. Proof construction exact on 10,300 instances; with parity-correct Ω's, a good seven existed in 284/284 ground-truth instances (conjecture: parity alone suffices). [HAND + EXACT], not independently verified.

- Piece B, many classes (notes/PROGRAMME2_B.md, compute/programme2/B/):
  - Coset families have NO perfect pencil (the three membership conditions sum to 0 = α), so Theorem R never applies to them, at any dual distance [HAND]. S⁺ applies with m = c; its trigger is the primal class count, not the dual distance.
  - **Theorem B1** [HAND, not independently verified]: for N < 1.852 every covering coset family has a Fano-type good seven once codim(C_ev) − 1 ≤ min((k − 5r − 41)/15, (r + 4εk − 11)/5), for every column structure. It replaces 9′'s c ≤ 2^r. 496/496 constructions verified exactly, including 82 covering families outside 9′'s H2 [EXACT per instance].
  - OPEN: codimension between B1's bound and about 0.43k. B1m covers random columns up to e ≈ 2.8m, conditional on (SPAN) [EXACT per instance]. Counting via MacWilliams is exact, but the error is governed by the dual's low-weight structure (coloops, series pairs), not by c. Two rigorous pieces are missing (B §5.5).
  - Counting update: Lemma F1 (rigorous fixed-count bound), Theorems F/F2/F‴ [HAND]: F‴ gives a good seven up to codimension ≈ 0.09k whenever the light-word factor G(7^{-1/2}) ≈ 1 (random-like codes). Decomposition step (§5.7) OPEN: slack is not the binding constraint (dual words off the Ω's cost 0 slack; coloops cost 12/point). Codes with linearly many disjoint short dual words defeat every absolute-value counting criterion (no-go P3); they need multiplicative/polymer handling with a canonical decomposition.
  - Task 3's conjecture ((H0)+(H1)+V=∪H suffice) is FALSE: two τ = 2 instances [EXACT, SAT]. No counterexample to B.

- Bridge C stability data (notes/STABILITY_DATA.md, stopped early): complete K_13^(8) is (7,2) with τ = 6 = 3k/4, yet at most 61.5% of its members lie in any ρ ≥ 1 coset [EXACT]. So 'thin ⇒ near-coset' FAILS at γ = 0 (for every k by the same construction); C can only hold strictly above 3k/4. No certified (7,2) family with τ > 3k/4 at n ≥ 15 was produced; exact (7,2) certification is the bottleneck.

- Near-complete lemma (notes/PROGRAMME2_NC.md) [VERIFIED 2026-11-25, notes/verify/theorem_NC.md: NC1, Theorem NC, NC0 and E_k PASS (Theorem NC under the repo definition "every subfamily of at most 7 members"); Corollary NC has a half-point rounding GAP for odd k — fixed by requiring τ ≥ ⌈(3/4+ε)k⌉ + 1 or w ≥ (7/4−ε)k + 2d + 7/2; no-gap with RA at δ ≈ 7ε/3 only for d < (5ε/3 − η′/2)k − 3/2; NC never fires when n < 7k/4 + d + 3/2; shift-0 layers covered only when their block excess d is small (d = O(r) unproved); 1,800 adversarial instances k ≤ 8 (≤ 16 symmetric), 0 failures; NC1 EXACT-checked on 2,992 instances at k = 4..9 only — the asymptotic regime (linear d, small ε) rests on the hand proof]: Theorem NC: if some W with |W| = w has every (k+d)-subset containing a member, and τ(H) > (k+1)/2 + max(0, 2k+2d+3−w), then H is not (7,2). For τ > (3/4+ε)k this covers every w ≥ (7/4−ε)k + 2d + 3, with arbitrary members outside W. Exact form: τ > (k+1)/2 + max(0, 2k+2d+3−w), i.e. τ > 3k/4 + 2d − (w − 7k/4) + 7/2 when the max is positive. So the near-complete branch (covering form, w ≥ (7/4−ε)k + 2d + 3) of the two-structure C is EMPTY for every ε > 0; NOT covered and left inside C: the fraction-density form for w < (7k+18)/4, and defect d ≥ (w − (7/4−ε)k − 3)/2, and C reduces to its near-coset half (with no such block present). Seam example E_k (k-subsets of W, |W| = 7k/4, odd on a part) is (7,2) with τ = 3k/4 and is both ρ=1-coset and complete: the structures overlap only at ε = 0.

- C near-coset half (notes/PROGRAMME2_C.md) [HAND, not independently verified]: BLR/linear-Fourier gluing from the seven-condition alone is DEAD ({q=1} with deg q ≤ 2 has no Fano plane yet looks random). Pencil lemma P1 + Lemma 8′ give Theorem C1: every k-uniform (7,2) family has τ ≤ (2n+k)/6 + 2 (so δ ≥ 3ε); independent of NC. Theorem C2: two-block families (|B∩X| ∈ J) with τ ≥ 3k/4+3, 3k/2 ≤ n < 9k/4 have a good seven (600/600 EXACT-checked, k = 8..40). At small k (4T−3k ≤ 0) seven-free families are only 77–86% in one coset [EXACT], so C needs εk → ∞. Remaining gap INV-P: thin, covering, 3ε ≤ δ < 1/12, every empty-intersection triple sum of weight ≥ 4εk − O(1) ⇒ near one coset [open; reduction conditional on NC]. Candidate obstruction: a non-linear sum-free set of density ≤ 5/16 with all triple-sum classes heavy (none known).

- CORRECTION (reviewer, 2026-11-25): the "B gap 1.852 ≤ N < 11/6" quoted in reports/RESPONSE_TO_DIRECTION_2 is EMPTY (11/6 ≈ 1.833 < 1.852): B1's three Ω's cover the whole Fano range N < 11/6. The genuine open range for B is N ≥ 11/6 (non-Fano good sevens; Theorem D to 1.938; core window to ≈ 2.25). Slack units: per-point slack (3−j)(4−j) in units of 3(4n−7k); a dumped point costs 12 there = 4 in units of 4n−7k (total 4δk). Short dual words: members meet supp(h) evenly (⟨h,B⟩ = 0); wt(h) may be odd.

- γ precheck for the counting route (notes/PROGRAMME3_GAMMA.md) [computed; cost model heuristic]: covering families have density p = e^{−γk} with γ ≤ γ_a = (1+ω)h(ω/(1+ω)) ≈ 0.10–0.29 in the Fano window. The brief's light-character cutoff w* ≈ 1.03γk leaves e^{0.39k}–e^{0.70k} light characters (rigorous Parseval cutoff: essentially all 2^n). Density increment: < 1 deficiency unit of slack per step. VERDICT: Tasks C/D (counting + increment for arbitrary families) work only for dense families (γ ≲ 4ε); for sparse seven-free covering families the wall is the whole regime. Stored CORE §56 greedy families are dense (γ ≈ 0.8ω). Also: with C1 (δ ≥ 3ε) and N < 11/6, the Fano window is nonempty only for ε < 1/36; for larger ε every counterexample has N ≥ 11/6 (non-Fano sevens), outside Programme 2's B/C framework.

- Brief 3 Task A (notes/PROGRAMME2_B.md §8–§9) [HAND; constructions EXACT-checked by a fresh verifier]: B for EVERY linear layer. Shift 0 reduces to the coset machinery with Ω = ∅ (9′, B1, F, F2, F‴, S⁺ hold verbatim). Theorem S0 (Schur triangle + NC1): B holds for every shift-0 layer with 4 | k, τ > 3k/4, N < 11/6 (k ≡ 2 mod 4: N < 1.7985); 319/319 sevens verified. Theorem S1 (untested): B at every shift when r ≤ 4εk − 7, any codimension up to ~k/2 — so B's remaining gap is r ≥ 4εk with codimension above B1's bound. Contraction: Ω's first then contract (Lemma P) removes lost-parity/Ω-block issues; F1w, F1⁺ (rigorous 1/7 damping), F‴w (needs a mixed-constant hypothesis, open). Giant blocks of weight-≥3 words and check (ii) (codim > 0.09k, no short dual words: needs a bound on medium-weight dual words) OPEN. N ≥ 11/6: Ω's reach 1.909 (empty common intersection), S1 reaches 1.9385; nothing above.
- N ≥ 11/6 scoping (notes/PROGRAMME3_BULK.md): no exclusion bound reaches into N ≥ 11/6 at small ε — LPs over all 716 seven types with ≤ 2 anchors give exactly C1 (Fano type is always best); the obstacle is forcing a pencil, not finishing. No family with N ≥ 11/6 and τ > 3k/4 + 1 avoiding good sevens is known (stored tgw families, 231 symmetric UNSAT searches, two-block exhaustive). Hand remark (unverified): sizes ≤ k with smallest member b give τ < (2n+b)/6 + 23/6.

- Brief 3 Task B / D3 (notes/PROGRAMME3_TASKB.md) [computed, Monte Carlo counts; small k only]: verdict (iii) at reachable sizes — seven-count minimisers stay unstructured; normalised count (vs random subfamily at same size) stays 1.00 ± 0.02; random starts never drift toward linear layers; planted FKW-type layers break up and converge to the random-start state. Planted layers have ~11–16% fewer normalised sevens, but the advantage does not grow from k = 8 to 12 at fixed 4T−3k = 4. Minimisers end near the covering minimum (γ/γ_a ≈ 0.72–0.80). CAVEATS: no Fano-range instance is reachable (first is (17,13,31), ~10^7 members); e^{−4εk} is only e^{−2}–e^{−4}; one seed at k = 10, 12. Read as a weak hint that thin families near ε > 0 are counting-type, not structure-type; not a decision.

- Counterexample hunt (notes/PROGRAMME3_CX.md) [computed; 45-min cap]: deep cosets of BCH [31,16,7], RM(2,5), and non-linear unions of deep cosets of shortened RM(2,5) all have τ well below 3k/4 (covering forces |H| ≥ C(n,k)/C(k+r,r); high codimension cannot cover at small r). Design families and many-cell sum-free sets not tried. Lemma Q (HAND, unverified): a (7,2) certificate for N < 11/6 via a linear map with member classes in T, when every vector with class in T+T+T has weight > (12n−21k)/7 (Corollary 7 is the single-coset case). Remaining Lemma-Q-type shape BAND: covering + no pair of members with intersection in a band of width (5δ/14 + ε/2)k from (k−r)/2; random families fail it by e^{0.68k}. Proving every covering family has such a pair would kill this route.

- **PEN(1/2) and slope 3/11 (notes/PROGRAMME3_LT.md)** [HAND, verification pending]: every k-uniform family in which every (k+r)-set contains a member has a pencil of weight <= floor(3r/2)+1 (mild size conditions, about T >= k/2 + 5r/4): the two-sided version of the brief-4 Lemma 5 gives a pair with |x1 Δ x2| in [k+r/2, k+3r/2]. With Lemma P1 (HAND): every (7,2) family on n <= 2k points has τ <= (3n+3k+24)/11, i.e. excess e <= (3/11)s + O(1) (was 1/3; the 1/3 bound itself is VERIFIED via NC with W = V: e <= s/3 + 11/6). Consequences: (LT) holds (a light triple, even a pencil, always exists), so Lemma Q never certifies a counterexample and BAND is dead as a counterexample route. Lemma Q with σ = id re-checked: it uses only the verified pencil-sum identity and the Fano classification. Obstruction to η < 1/2: single dumps are dodged (heuristic); η -> 0 would give slope 1/5.

- **Lead 1, topological rainbow criterion (notes/PROGRAMME4_TOPO.md)** [criterion HAND + Volovikov 2000; NO-GO as a route]: if the complex N(H) of compatible Fano-coloured members is F_7-homologically 5-connected, H has a Fano-type good seven (the reviewer's map needed an affine fix). The toy (triples, Z_3, S^1) fires on all 20 tested families with τ >= k/2+2, k <= 4 [computed], but the needed connectivity is not provable by the standard tools: for intersecting H two monochromatic vertices totally dominate the incompatibility graph, so domination bounds give only connectivity 0. The method moves the difficulty into a new connectivity theorem. Matroid dictionary [HAND]: τ(H) = critical number of U = {supersets of members}; Fano-type seven exists iff U contains PG(2,2) (every n); good triple iff U not sum-free.

## Open
- LIFT (G2 / far replies): transfer confined results to general families (anchor-keeping certificates, or show far replies with large outside overlap lose). Needed for the full solve.
- Record path: exact certification of R1's sparsest-anchor argument at t = 17/20 (anchor-keeping, transfers) would give f(k,7) <= (17/20 + o(1))k (FRONTIER §4–5).
  - **Update (RECORD.md):** 17/20 is NOT reachable by the depth-1 game [C]: the lopsided corner near (0.575, 0.025, 0.025) is stuck at t = 0.85–0.856 and at 6/7 for C = 3..20 and grids down to 1/120 (FRONTIER's 'won at 0.85' was a 1/20-grid artefact); 17/20 needs the depth-2 re-anchoring game. At t = 43/50 = 0.86, C = 8: 9102 exact certificates accepted by the independent checker, about 0.13% of the region still uncovered in three pockets where box subdivision to side 1/512 fails (float game wins at the grid points; plan switching along slanted planes suspected). No bound below 7/8 is certified yet.
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
- Covering numbers behind f(6,7) >= 5 and f(7,7) >= 6: certified by hand (Schönheim bound; notes/verify/small_values.md). The upper bounds come from exact certificates (FRESH_C §14) plus the VERIFIED TWIN §13, so f(6,7) = 5 and f(7,7) = 6 are certified.

## Finite-k hypotheses (notes/FINITE_K.md)
- DS-b: n - k + 7δ + 1 <= T. W: any k with 4T != 3k+1 (false at k ≡ 1 mod 4, T = (3k+1)/4). J′: T >= 2⌈k/3⌉. §46: L-branch ω <= T - ⌈k/2⌉, H-branch o <= 4ω - 3.
