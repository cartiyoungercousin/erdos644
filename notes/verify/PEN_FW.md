# Referee report: PEN(η) for small r via Frankl–Wilson (`notes/PROGRAMME4_PEN.md`)

This is an independent adversarial check of PROGRAMME4_PEN §§0–2. I wrote my own code in `compute/verify_fw/`
(`fw_core.py`, `fw_frontier.py`) and did not use `compute/programme4/pen/` code. I read only its two logs, to find out
what its finite-k numbers mean.

Conventions:
- T = τ − 1 and r = n − k − T = n − k − τ + 1.
- s = n − 7k/4 and e = τ − 3k/4 = s − r + 1.
- P1 (verified in PEN_P1.md): every pencil of a (7,2) family has weight w ≥ 4T − 3k − 5.
- Weight means the number of points lying in exactly one of the three members, given an empty triple intersection.
- g(k) is the largest gap between consecutive primes ≤ k.

| Item | Verdict |
|---|---|
| (A) Lemma FW (forbidden intersection k − p) | **VERIFIED** (self-contained proof correct; the published theorem gives the sharper C(n, p−1)) |
| (B) Covering count \|H\| ≥ C(n,k)/C(k+r,r) | **VERIFIED** |
| (C) c0(ν) values and finite-k claims | **VERIFIED WITH FIXES** (the entropy values are right; the "finite k is better" sentence needs its weight slack stated) |
| (D) Dump: pencil of weight ≤ r + 2g + 1, empty intersection | **VERIFIED** (in fact ≤ r + 2g; no room outside x1 ∪ x2 is ever needed) |
| (E) Corollary, the 1.784 / 1.7994 thresholds, δ ≥ 5ε | **VERIFIED** (all constants correct, slightly conservative; sharpenings below) |

## (A) Lemma FW [VERIFIED]

**Statement.** p is prime with (k+1)/2 ≤ p ≤ k, and F ⊆ C([n],k) has no two members meeting in exactly k − p points.
Then |F| ≤ Σ_{i<p} C(n,i).

**Published source.** This is the uniform modular Ray-Chaudhuri–Wilson theorem of **Frankl–Wilson** (Combinatorica 1
(1981) 357–368). It states: let p be prime, F k-uniform, L a set of s residues mod p with k mod p ∉ L, and |F∩G| mod p ∈ L
for all distinct F, G. Then |F| ≤ C(n, s). Here L = F_p ∖ {k mod p}, so s = p − 1 and the bound is **C(n, p−1)**.

Equivalently it is the Frankl–Wilson "one forbidden intersection" corollary with ℓ = k − p and q = k − ℓ = p prime,
under the condition k ≤ 2q − 1, i.e. p ≥ (k+1)/2.

The note proves the weaker bound **Σ_{i<p} C(n,i)**. That is the Deza–Frankl–Singhi non-uniform modular bound, and its
proof (multilinear polynomials, no inclusion-matrix rank) is fully self-contained. Either bound works, and the note
uses only the weaker one.

**Hypotheses, checked one by one.**
- **Residue step.** Distinct k-sets have |F∩G| ∈ [0, k−1]. Suppose i ≡ k (mod p) and i < k. Then i = k − tp with t ≥ 1,
  and k − 2p ≤ −1, so only t = 1 is possible and i = k − p.
  - Computed: every k ≤ 400, every prime p ∈ [(k+1)/2, k], every i, giving 1 909 366 cases and 0 exceptions
    (`logs/residue_400.log`).
  - The hypothesis p ≥ (k+1)/2 is needed. With p = k/2 the intersection 0 = k − 2p is also ≡ k.
- **Condition "k mod p ∉ L".** This holds by construction.
- **P_F(1_F) = Π_{μ≠k}(k−μ) = (p−1)! ≡ −1 ≢ 0 (Wilson's theorem).** Checked numerically (`logs/rank.log`).
- **Multilinearisation.** It keeps the values on {0,1}^n and gives degree ≤ p − 1, so the space has dimension
  Σ_{i≤p−1} C(n,i). Independence follows because the evaluation matrix on the family is diagonal and nonzero.
  - Computed: the rank of {P_F} over all k-sets on {0,1}^n is ≤ Σ_{i<p} C(n,i) in 6 tiny cases (`logs/rank.log`).
- **Uniformity.** It is used only so that the "self" residue is k mod p for every F.
- **No condition on n is needed.** If p > n − k, the hypothesis is vacuous, and the bound still holds since
  Σ_{i≤n−k} C(n,i) ≥ C(n,k).
- **Conditions in published versions.** Some statements of the C(n,s) version add s ≤ k or n ≥ k + s. Both hold here
  (p − 1 < k, and p ≤ 0.6k < n − k in the window).

**Brute force** (CP-SAT, 2 workers, exact optimum, one member fixed by symmetry; `logs/brute.log`).
- All 20 cases with n ≤ 9, C(n,k) ≤ 130 and the lemma's hypotheses were solved exactly.
- In every case the maximum is ≤ C(n, p−1) ≤ Σ_{i<p} C(n,i).
- Equality with C(n, p−1) occurs at (8,3,2) (max 8) and at (n,2,2).
- These agree with the note's 5, 8, 17, 21, 21 for the shared cases.

## (B) Covering count [VERIFIED]

- Double count the pairs (B, S) with B ∈ H, S a (k+r)-set and B ⊆ S. Every S contains at least one member, and every
  B lies in C(n−k, r) sets S. So |H| ≥ C(n, k+r)/C(n−k, r).
- The identity C(n,k+r)/C(n−k,r) = C(n,k)/C(k+r,r) = n!·r!/((k+r)!(n−k)!) holds by hand.
  - Computed: exact rationals for all 39 710 triples with n ≤ 60, 0 mismatches (`logs/cover_60.log`).
- The count needs exact k-uniformity, which the corollary assumes.

## (C) c0(ν) [VERIFIED WITH FIXES]

### Entropy limit
The condition is f(ρ) = νH(1/ν) − (1+ρ)H(ρ/(1+ρ)) − νH((1+ρ)/(2ν)) > 0. I re-derived it from
C(n,k) > C(k+r,r)·Σ_{i<p} C(n,i) with p/n → (1+ρ)/(2ν) < 1/2. Since p/n < 1/2 the sum is Θ(C(n,p−1)), so the
choice of bound does not matter in the limit. Prime gaps shift p by g = o(k), so they do not matter either.

Bisection results (`logs/entropy.log`):

| ν | 1.70 | 7/4 | 1.784 | 1.8 | 11/6 | 1.9 | 2 |
|---|---|---|---|---|---|---|---|
| c0(ν) | 0.02347 | **0.02976** | 0.03400 | **0.03599** | **0.04009** | 0.04814 | **0.05979** |

- All four of the note's values match.
- f is strictly decreasing on [0, c0], so the root is unique.
- c0 is strictly increasing in ν on [1.70, 2.03] (grid step 0.001).

### Exact finite k
I used exact big-integer binomials. p is the least prime ≥ (k+r+1)/2, the note's §2 choice, which gives weight 2p − k.
Result (`logs/exact_frontier.log`): the condition holds for every r ≤ R and fails at R + 1, with no recoveries in the
next 40 values of r.

| k | ν = 7/4 | 1.8 | 11/6 | 2 |
|---|---|---|---|---|
| 500 | 0.0280 | 0.0340 | 0.0380 | 0.0580 |
| 1000 | 0.0290 | 0.0360 | 0.0400 | 0.0570 |
| 2000 | 0.0300 | 0.0360 | 0.0390 | 0.0600 |
| 4000 | 0.0297 | 0.0355 | 0.0403 | 0.0592 |
| 8000 | 0.0296 | 0.0357 | 0.0396 | 0.0599 |

- Using C(n, p−1) instead of Σ changes R only once (k = 500, ν = 11/6: 19 → 20).
- The values converge to the entropy limit, oscillating by ±0.001 because of prime gaps.

**Fix 1.** §0 says "Exact finite k is better: k = 2000 gives r ≤ 0.0325k (ν = 7/4) and r ≤ 0.045k (ν = 11/6)". With the
note's own §2 choice of p, k = 2000 gives only **0.0300 and 0.0390**.
- The note's figures come from `fw_frontier.log`'s definition: any prime p, either pair-bound branch, and weight
  ≤ r + 2√k (about r + 89).
- I reproduce them independently: R = 65 (0.0325) and R = 90 (0.045) (`logs/slack_2000.log`).
- With slack 2g + 1 = 69 instead, I get 0.0325 and 0.0445.
- At k = 2000 this slack is larger than r itself, so "better" means a pencil of weight about 2r, not about r. The
  sentence must state the slack and the use of the first branch (2p < k + r, with room p ≥ 2k + r − n). The asymptotic
  c0 is unaffected.
- The corollary uses only weight ≤ r + 2g + 1, so the finite-k numbers are legitimate for the corollary at k = 2000. They
  are not "PEN with weight r + o(k)" at that k.

**Fix 2 (cosmetic).** §0 writes p ∈ [(k+r)/2, (k+r)/2 + g]. For r = 0 with k even and k/2 prime, this allows p = k/2,
which violates p ≥ (k+1)/2 (see (A)). Use (k+r+1)/2 as in §2.

## (D) The dump [VERIFIED]

- **Choice of p.** p is the least prime ≥ (k+r+1)/2, so 2p ≥ k+r+1 > k+r. **This is always the branch
  |x1Δx2| > k + r.** A strict (k+r)-subset A of x1Δx2 exists, and no point outside x1 ∪ x2 is needed.
- **Covering step.** Covering gives a member x3 ⊆ A with |A| = k + r ≤ n. Then:
  - x3 ∩ x1 ∩ x2 ⊆ A ∩ x1 ∩ x2 = ∅;
  - points of x3 lie in exactly two members, points of x1∩x2 lie in exactly two, and the rest of x1Δx2 lies in exactly
    one;
  - so the weight is |(x1Δx2) ∖ x3| = 2p − k.
- **Repeated member.** x3 = x1 is possible only if p = k (x1, x2 disjoint). P1 tolerates repeated members.
- **Gap bound.** Let q be the prime before p. Then q < x := (k+r+1)/2 and q, p ≤ k, so p − x < p − q ≤ g. Hence
  2p − k − r − 1 < 2g and, by integrality, **2p − k ≤ r + 2g**. The note's r + 2g + 1 is true but loses 1.
- **Random test.** 20 000 random pencils (k ≤ 40) built exactly this way all have triple intersection ∅, all points
  covered at most twice, weight 2p − k, and weight ≤ r + 2g (`logs/dump_4000_1.log`).
- **First branch.** Used only in `fw_pen`'s table and finite frontier: 2p < k + r, |O| = k + r − 2p outside x1 ∪ x2,
  room iff p ≥ 2k + r − n, weight ≤ k + 2r − 2p. This is the PROGRAMME3 pair bound already verified in PEN_P1 (A).

## (E) Corollary and thresholds [VERIFIED]

**Algebra (exact).**
- P1 gives 4T − 3k − 5 ≤ w, and FW gives w ≤ r + 2g + 1 = n − k − T + 2g + 1. So 5T ≤ n + 2k + 2g + 6.
- With e = T + 1 − 3k/4: 5e ≤ n − 7k/4 + 2g + 11. So **e ≤ (s + 2g + 11)/5** ✓.
- Using (D)'s r + 2g, this sharpens to **e ≤ (s + 2g + 10)/5**.
- Also e = s − r + 1 ✓. The exception r > (c0 − o(1))k gives e < s + 1 − (c0 − o(1))k ✓.

**"Exception impossible for ν ≤ 1.784 − θ".**
- The note's step r ≤ s + 1 needs e ≥ 0, which is unstated. If e < 0 and s ≥ 0, the bound holds trivially. If s < 0,
  then either r ≤ c0k (FW applies) or e < s + 1 − c0k ≤ (s + 11)/5. So the claim holds for all n ≤ (1.784 − θ)k.
- The root of c0(ν) = ν − 7/4 is **ν = 1.78400** ✓.

**Remark (improvement, not an error).** e ≤ max((s+2g+11)/5, s + 1 − c0k + o(k)) is ≤ s/5 + o(k) whenever
s ≤ (5/4)c0(ν)k. So **e ≤ s/5 + o(k) holds up to ν = 1.79406** (root of 5c0/4 = ν − 7/4), not only up to 1.784.

**Crossover with 3/11.** max(s/5, s − c0k) < 3s/11 iff s < 11c0(ν)k/8. The root of 11c0(ν)/8 = ν − 7/4 is
**ν = 1.79937** ✓ (the note says 1.7994).

**δ ≥ 5ε.** Take a counterexample with e = εk at s = δk.
- Either δ ≥ 5ε − o(1), or δ > ε + c0(7/4 + δ) − o(1).
- Since c0 is increasing (checked), δ ≥ 0 gives c0(7/4 + δ) ≥ c0(7/4) = 0.02976. So δ > 5ε whenever 4ε ≤ c0(7/4), i.e.
  **ε ≤ 0.00744** ✓ (the note says 0.0074).
- For δ < 0 the second alternative is self-contradictory.
- Sharper: δ − c0(7/4 + δ) is increasing (c0′ ≈ 0.12 < 1), so the exact condition is 4ε ≤ c0(7/4 + 5ε). That gives
  **ε ≤ 0.00881**.

**Exact table at k = 2000.**
- `fw_frontier.py slopefull` uses any prime and both branches, as in the note. It reproduces the note's e_max exactly:
  6, 10, 14, 18, 26 at s = 20, 40, 60, 80, 100, and = 3/11 for s ≥ 110 (`logs/slopefull_2000.log`). It also matches
  "e_max = s/5 + 2 up to s ≈ 0.045k".
- With only the least prime ≥ (k+r+1)/2 (branch 2), e_max is slightly larger: 11, 17, 28 at s = 40, 60, 100
  (`logs/slope_2000.log`). The note's table therefore depends on branch 1 and on choosing the prime freely. Both are
  valid.
- Cosmetic: at s = 0 the note lists e_max = 2, but τ ≤ n − k + 1 forces e ≤ s + 1 = 1.

## Reproduction (`compute/verify_fw/`, `py -3.14`, ≤ 2 cores)
- `fw_core.py residue 400`, `fw_core.py cover 60`, `fw_core.py dump 4000 1`, `fw_core.py rank`, `fw_core.py brute`
- `fw_frontier.py entropy`, `fw_frontier.py exact 500,1000,2000,4000,8000`, `fw_frontier.py slack 2000`
- `fw_frontier.py slope 2000 ...`, `fw_frontier.py slopefull 2000 ...`
- Logs are in `compute/verify_fw/logs/`.

Nothing is committed. `notes/LEDGER.md` and `Lean644/` were not touched.
