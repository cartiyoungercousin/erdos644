# Programme 3: the bulk N ≥ 11/6 (scoping map and first attack)

Tags: VERIFIED / HAND / EXACT (exact computation) / LP (float LP, HiGHS) / DEAD / OPEN.
Code: `compute/programme3/bulk/` (`anchor_lp.py`, `find7.py`, `logs/`). Nothing committed.
Setting: Statement (G). By Lemma 1 we may take H k-uniform, n = |∪H|, N = n/k, T = ⌈(3/4+ε)k⌉, τ > T. Padding
changes n, so (G) needs every N. ε is small and fixed throughout.

## 0. Verdict
- **Nothing general covers N ≥ 11/6 at small ε.** The only unconditional bounds there (C1, 16.A, Theorem 3) bite
  only when ε > (N − 7/4)/3.
- **New, negative:** no static finish with at most two anchors, over all 716 seven-types, beats C1 anywhere in
  [11/6, 9/4] [LP, §2.3]. So **C1 is the one-anchor Fano template**, equal to 16.A / Lean `TheoremA`. Non-Fano
  types add nothing until five or six anchors are placed exactly (CORE 17.2).
- **Small remark [HAND]:** the one-anchor form needs no uniformity: τ < (2n + b)/6 + 23/6, where b is the smallest
  member size (§2.4).
- **Supersaturation test (§3):** no known family with N ≥ 11/6 and τ > 3k/4 + 1 avoids good sevens. All stored ones
  have a verified Fano-type seven; 231 symmetric searches are DRUP-UNSAT; the exhaustive two-block search tops out at
  3k/4 + 1. Every seven-free (or undecided) example sits at τ ≤ 3k/4 + 1.

## 1. Inventory: what bears on N ≥ 11/6 without confinement
Key reading [HAND, mine; please check]. In (G), V = ∪H, so every member lies in V automatically. A CORE result
stated in **family form** (CORE 1.2: "every T-covering family of k-subsets of an n-set …") is a statement about
k-uniform H at N = n/k, and it transfers. The G2 lift is needed only by the old anchored route, where V was a union of
anchors and H had members outside V. Results tied to anchors, arenas or petal unions do not transfer as region
closures: their "N" is not n/k.

| result | applies at N ≥ 11/6? | transfers to (G)? | what it gives there |
|---|---|---|---|
| 16.A crowded (N ≤ 3T − k/2 − 1), VERIFIED + FINITE_K | no: it is N < 7/4 + 3ε | yes (family form; Lean `TheoremA`, one-anchor Fano) | nothing at small ε |
| C1 τ ≤ (2n+k)/6 + 2, HAND | yes | yes (k-uniform, any n) | excludes ε > (N − 7/4)/3: 1/36 at 11/6, 1/12 at 2, 1/6 at 9/4 |
| Theorem 3 (uniform y: τ ≤ 3n/7 + 3), VERIFIED | yes | yes | ε > 3N/7 − 3/4: 1/28, 3/28, 3/14. Weaker than C1 for N > 7/4 |
| RA (rich, tau*_b ≤ 7/3 − η), VERIFIED | yes, any N | yes (sizes ≤ k) | rich families only. Uniform y gives tau*_b ≤ N/t, which is ≥ 7/3 once N ≥ 7/4 + 7ε/3, and no stored family is rich (TASK1) |
| Lemma A0 (3-wise intersecting ⇒ τ ≤ (k+1)/2), LEAN | yes | yes | a pencil triple exists; no weight bound |
| P1 (pencil of weight ≤ 4T − 3k − 6 ⇒ Fano seven), HAND | yes, any N | yes | needs a pencil of weight ≈ 4εk. Lemma 8′ gives only 2r + 1 ≈ 2(N − 7/4)k |
| Theorem NC (near-complete W), HAND | yes, any N; members outside W allowed | yes | only families with a (k+d)-covered W, w ≥ (7/4−ε)k + 2d + 3. W = V reproduces C1 |
| Bottom strip (7/4+3ε, 7/4+5ε], VERIFIED, ε ≤ ε₀ | no | yes (family form: pair criterion + Frankl–Rödl) | nothing |
| S (profile families, 3/2 ≤ N ≤ 9/4, first order), VERIFIED | yes, up to 9/4 | yes | structured class only |
| S⁺ (finite k, ≤ 4(T−3k/4)/3 − 4 cells, n/3 + m ≤ T), VERIFIED | up to N ≈ 9/4 + 3ε | yes | structured class only; vacuous unless εk ≳ 12 |
| C2 (two-block, 3k/2 ≤ n < 9k/4, τ ≥ 3k/4 + 3), HAND + EXACT | yes, to 9/4 | yes | structured class only |
| H (kernel density > 2/3), W, R (selector families), VERIFIED | yes (window) | yes, as family statements | structured classes only |
| D (dim C ≥ k + r ⇒ ρ_par ≤ r + 1), HAND; B1 (N < 1.852), HAND | D: up to N < 1.938 (counting); B1: no | yes | coset families only; above 1.938 only Lemma 8 |
| Petal side: J, J′, J″, K, L, N, DS, AP, FF, PS–PS3, CR, SL1 | – | **no** as region closures | they concern petal/arena configurations and restricted adversaries (arena, pooled 𝒜, two-class); J is a dichotomy. They may survive as lemmas, but they close no N-range of (G) |
| CP / core-window strategy trees, Theorem T/Q/P finishes | – | the tools transfer (static finishes); CP itself is OPEN | – |

## 2. Seven types for 11/6 ≤ N < 9/4
### 2.1 The spectrum [EXACT]
Source: the 716 S₇-classes of maximal intersecting families on [7] (1,422,564 labelled), with exact LP values
LP(M) from `programme2/verify/out/maxint7_classes_lp.json`. LP(M)·k is the least union of seven k-sets whose
co-types lie in M. So at a given N, the available types are exactly those with LP(M) ≤ N.

| LP value | 7/4 | 11/6 | 15/8 | 17/9 | 19/10 | 21/11 | 23/12 | 25/13 | 27/14 | 29/15 | 31/16 | 33/17 | 35/18 | **2** |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| classes | 1 (Fano) | 4 | 45 | 20 | 47 | 27 | 26 | 12 | 10 | 4 | 2 | 2 | 1 | **380** |

Above 2 the values come back down from 35/17 to 9/4. They are 35/17 (1 class), 33/16 (3), 31/15 (2), 29/14 (6),
27/13 (9), 25/12 (14), 23/11 (11), 21/10 (17), 19/9 (14), 17/8 (14), 15/7 (12), 13/6 (10), 11/5 (8) and 9/4 (6).
Beyond those: 7/3 (4), 5/2 (2), 3 (1). One class (a dictator) is infeasible.
- **Cumulative.** 1 type below 11/6; 5 below 15/8; 201 below 2; 581 at N = 2; 708 of 715 at N = 9/4.
- **Shape of the spectrum.** It accumulates at 2 from both sides: (2j+1)/(j+1) from below and (2j+1)/j from above.
  At N = 2 six members can already cover all pairs (K4: members are the 6 pairs of 4 blocks of k/2; also 2-(6,3,2)).
- **Fano-supported up to 15/8.** The 11/6 optimum is still Fano-supported (CORE 16). Lineless supports exist just
  above 11/6 with small extra mass. Minimal non-Fano patterns start at 15/8.

### 2.2 Static finishes (the generalised C1/Theorem 3) [LP, `anchor_lp.py`]
**Model.** A finish of type M uses some anchor members of H in a forced position. Every other member i is found by
covering: if its region R_i = {x : i ∉ I_x} has ≥ n − T points, it contains a member. Lemma 2 (or pairwise
intersection of M) finishes.
- **Zero anchors.** The best case is N(1 − 1/LP(M)) ≤ t, minimised by Fano, giving t ≥ 3N/7 (Theorem 3).
- **One anchor.** Any member, exact size.
- **Two anchors.** B₂ lies in a request S of n − T points with |S ∩ B₁| = s chosen by us. The adversary picks
  d = |B₁ ∩ B₂| in [max(0, s − ω), s], where ω = N − t − 1. By convexity both ends of that window suffice.
Least t over all types and anchor labellings:

| N | 0 anchors (3N/7) | 1 anchor | 2 anchors | C1 (2N+1)/6 | best type |
|---|---|---|---|---|---|
| 11/6 | .786 | .7778 | .7778 | .7778 | Fano |
| 15/8 | .804 | .7917 | .7917 | .7917 | Fano |
| 19/10 | .814 | .8000 | .8000 | .8000 | Fano |
| 2 | .857 | .8333 | .8333 | .8333 | Fano |
| 21/10 | .900 | .8667 | .8667 | .8667 | Fano |
| 9/4 | .964 | .9167 | .9167 | .9167 | Fano |

**Reading.**
- (a) The one-anchor Fano finish already attains C1, and a second anchor buys nothing.
- (b) **No non-Fano type does better** with at most two anchors.
- (c) With ideally placed anchors, CORE 17.2 finds Fano best for q ≤ 4 throughout [11/6, 9/4]. Non-Fano types win
  only at q = 5 (from N ≈ 2.2) or q = 6 (from N = 2).
- (d) With three ideal anchors (a pencil of weight 0), P1 works at every N once T ≥ 3k/4 + 3/2. So the barrier is
  **forcing**, not finishing. A C1-type exclusion at small ε needs a pencil of weight ≤ 4εk − 6 at N ≥ 11/6. Lemma 8′
  gives 2r + 1, and even Pencil-D (r + O(1)) would give only ε > (N − 7/4)/5, which excludes nothing above 11/6 for
  ε < 1/60.
- **Answer to the brief's question:** there is no pencil-lemma analogue from static finishes that excludes any part
  of N ≥ 11/6 at small ε. C1, NC (W = V) and Theorem 3 bite exactly at ε > (N − 7/4)/3, (N − 7/4)/3 and
  3N/7 − 3/4 respectively.

### 2.3 Hand check of (a) [HAND]
Fix a line ℓ*.
- Colour a member B₁ (|B₁| = b) evenly with the 4 points off ℓ*, and V∖B₁ evenly with the 3 points of ℓ*.
- Every other line ℓ meets ℓ* in one point. So R_ℓ = χ⁻¹(points off ℓ) consists of two ℓ*-classes plus two of the
  B₁-classes, and |R_ℓ| ≥ 2⌊(n−b)/3⌋ + 2⌊b/4⌋ ≥ 2n/3 − b/6 − 17/6.
- If this is ≥ n − T, each R_ℓ contains a member (its complement has ≤ T points). Lemma 2 then gives a good seven.

### 2.4 Corollary (non-uniform one-anchor bound) [HAND]
**Claim.** If H has members of size ≤ k, smallest size b, n = |∪H|, and (7,2), then τ < (2n + b)/6 + 23/6.
- The proof is §2.3 with T = τ − 1. Uniformity is not used.
- For a minimal (non-uniform) counterexample this gives n > (9/4 + 3ε)k − b/2 − O(1). **Small members push N up**:
  b ≤ k/2 forces N > 2 + 3ε.
- The bound is not new for uniform H (C1 has +2), but it avoids padding.

## 3. Supersaturation test [EXACT unless tagged]
Target: a family with N ≥ 11/6 and τ > 3k/4 + 1 and no good seven.

| family | (k, n, N) | τ vs 3k/4+1 | result |
|---|---|---|---|
| `tgw_fam_10_8_21` + rand2s1/s2, rand3s1/s2 (core12) | (10, 21, 2.1) | 9 > 8.5 | Fano-type seven found in try 0 for all 5; each verified by brute force over all ≤2-sets (`find7.py`, `logs/find7.log`) |
| `tgw_fam_8_6_16` | (8, 16, 2) | 7 = 7 (boundary) | Fano seven, verified |
| `tgw_fam_13_10_25` | (13, 25, 1.92) | 11 > 10.75 | Fano-type seven found in try 0, verified by brute force (`logs/find7_k13.log`) |
| profile families, ≤ 2 cells (all partitions), some 3-cell (CORE §113) | (10,8,21), (13,10,25–28), (14,11,28–30), (15,12,31–32), (16,13,34): N = 1.92–2.15 | all T + 1 > 3k/4 + 1 | 231 runs UNSAT, DRUP-certified: no such family is a counterexample |
| near-pool (10,8,21), 8 profiles; (8,7,16) SAT family; FKW controls at n = 7m+2 (TASK4) | N = 2–2.1 | 9–12, 8, 8 / 11 | sevens found (TASK4) |
| two-block H_J, every J and split (`search2.py`) | k=8: n = 15, 16, 17, 18 | max Fano-free τ = 7, 6, 7, 7 (≤ 3k/4+1 = 7) | none. Fano-free ⊇ seven-free, so this is a valid upper bound |
| two-block, k = 10 | n = 19 | max Fano-free τ = 7 (< 3k/4 = 7.5) | none. n = 20–22 and k = 12 (n = 22–26) not finished in the timebox (stopped; partial log `logs/twoblock_bulk.log`) |

- **Undecided example.** The only one is (8,6,15) (CORE 55.5) at N = 1.875 with τ = 7 = 3k/4 + 1, the boundary and
  not strict.
- **Seven-free examples at N ≥ 11/6.** All of them, two-block or complete, have τ ≤ 3k/4 + 1.
- **Caveat.** All tests have 4T − 3k ≤ 8. At these k the asymptotic regime (εk → ∞) is not reached, and C2 shows
  finite-k junk layers exist only at 4T − 3k ≤ 0.

### 3.1 What a softer supersaturation argument would need [heuristic]
- **Dead inputs.**
  - Containers (CORE §85–89: the codegree condition fails above a thin strip).
  - Plain density counting for sparse families (GAMMA: it works only for γ ≲ 4ε; covering allows γ up to 0.29 near
    11/6).
- **The natural averaged template is §2.3.** Take a random member B₁ and a random balanced Fano colouring. Each line
  region R_ℓ has 2n/3 − b/6 points, which is n − T − Δ with **Δ = ((N − 7/4)/3 − ε)k = Θ(k)** below the covering
  threshold.
  - A good seven exists if Pr[all six R_ℓ contain a member] > 0.
  - Sufficient: the hole density h(w) at w = n − T − Δ is < 1/6, by a union bound (the R_ℓ are uniform sets of
    their size once B₁ is fixed).
  - Necessary input: **a hole-density bound just below the covering threshold**. That is a Kruskal–Katona-type
    growth statement: h(n − T) = 0 must force h(n − T − Δ) < 1/6 unless the family is structured.
- **Why this fails as stated.**
  - Random covering designs have h(n − T − Δ) → 1 once Δ ≫ log k. They have plenty of good sevens of other types,
    but not via this template.
  - So the argument must be a dichotomy. Either (i) holes are sparse at deficit Δ (the averaged one-anchor template
    wins), or (ii) the family is sparse and random-like, and sevens come from correlations among ≥ 3 forced members.
- **(ii) is the real content.** It is a forcing statement: every sparse T-covering family on n ≥ 11k/6 points has
  either a pencil of weight ≤ 4εk − 6 (then P1) or an exactly placed 5–6-member configuration (then CORE 17.2's
  non-Fano endings).
- **No extremal target is known.** In contrast to the Fano range (FKW, cosets, INV-P), no seven-free family with
  N ≥ 11/6 and τ > 3k/4 + 1 is known. Either the bulk is "easier" (every covering family is supersaturated there),
  or its extremal structure is still undiscovered.
- **Cheapest next exact test.** An unsymmetrised CEGAR SAT search at (10,8,19) or (10,8,20), in the style of CORE
  55.5. The profile searches only cover cell-invariant families.

## 4. Region map (small fixed ε; N = n/k, H k-uniform after Lemma 1)

| N-range | covered by | status |
|---|---|---|
| N < 7/4 + 3ε − O(1/k) | 16.A = C1 = one-anchor Fano (§2.3) | VERIFIED (16.A + FINITE_K); C1 HAND |
| 7/4 + 3ε ≤ N ≤ 7/4 + 5ε | bottom strip (family form) | VERIFIED, ε ≤ ε₀ ineffective (transfer reading HAND) |
| 7/4 + 5ε < N < 11/6 | Programme 2: RA (rich), B1 (cosets), C1/NC/INV-P | OPEN (A VERIFIED for rich; B1, NC HAND; INV-P open) |
| 11/6 ≤ N < 15/8 | minimal patterns still Fano-supported (5 types); C1 only for ε > (N−7/4)/3 | OPEN |
| 15/8 ≤ N < 2 | 201 types; D for cosets up to 1.938 (HAND); S, S⁺, C2, H, W, R, NC for structured classes | OPEN |
| N = 2 to 9/4 | 581–708 types; 6-member endings available; S, C2 to 9/4 | OPEN |
| N ≥ 9/4 (old petal side) | petal theorems do not map to n/k (§1); C1′ only | OPEN; old closures DEAD as coverage |
| any N, ε > (N − 7/4)/3 | C1 / C1′ | HAND |
| any N, rich families / near-complete blocks / profile, two-block, coset (to 1.938) families | RA / NC / S, S⁺, C2 / D | VERIFIED / HAND |

The 60-minute timebox covered §2.1–2.3 and the tests in §3. Not done: CEGAR SAT at N ≥ 11/6, three-anchor
(pencil-forced) LPs with an adversarial pencil, and exact (rational) re-certification of the §2.2 LPs. The Fano
column matches the hand formula to 4 decimals.
