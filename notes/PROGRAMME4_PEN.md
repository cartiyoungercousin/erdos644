# Programme 4, PEN(η) below 1/2: a counting proof for small r, and where it stops

Tags: [proved by hand], [computed exact], [heuristic], [open], [cited]. Nothing here is independently verified.
Code: `compute/programme4/pen/` (`fw_pen.py`, `lemma_brute.py`, `exact_sat.py`), logs in `pen/logs/`. Nothing committed.
Notation as in PROGRAMME3_LT: H k-uniform on n points, (k+r)-covering, T = n−k−r, ν = n/k, s = n − 7k/4,
e = τ − 3k/4 = s − r + 1. Pencil = three members with empty common intersection; weight wt(x1+x2+x3).
H(x) = −x ln x − (1−x) ln(1−x). g(k) = largest gap between consecutive primes below k (g = O(k^0.525), so o(k)).

## 0. Verdict
- **PEN(η) for every η > 0 when r ≤ c0(ν)k** [proved by hand, with Lemma FW proved in full below]. Precisely: for
  k ≥ k0(ν), every (k+r)-covering k-uniform H on n = νk points with r ≤ (c0(ν) − o(1))k has two members with
  |x1 Δ x2| = 2p for a prime p ∈ [(k+r)/2, (k+r)/2 + g], hence a **pencil of weight ≤ r + 2g(k) = r + o(k)**.
  - c0(7/4) = 0.0298, c0(1.8) = 0.0360, c0(11/6) = 0.0401, c0(2) = 0.0598 (entropy limit) [computed exact].
  - Exact finite k is better: k = 2000 gives r ≤ 0.0325k (ν = 7/4) and r ≤ 0.045k (ν = 11/6) [computed exact].
  - Pair form, so it is optimal for pairs: INV-P says the pair-band form cannot go below weight r.
- **Corollary (slope 1/5 near N = 7/4)** [proved by hand; uses Lemma P1 (HAND)]. Every k-uniform (7,2) family has
  e ≤ (s + 2g(k) + 11)/5 unless r > (c0(ν) − o(1))k.
  - For ν ≤ 1.7840 − θ (any θ > 0, k ≥ k0(θ)) the exception cannot occur, since r ≤ s + 1 < c0(ν)k.
    So **e ≤ s/5 + o(k) for n ≤ (1.784 − θ)k**.
  - Old slope: 3/11. The new bound beats 3/11 for ν < 1.7994.
  - So a counterexample with e = εk, ε ≤ 0.0074, needs **δ ≥ 5ε − o(1)** (was 11ε/3).
- **Not reached:**
  - Uniform PEN(η < 1/2) for 0.03k < r ≤ k/12 [open].
  - The INV-P target "pencil weight ≤ λ_lin r", λ_lin ≈ 0.85 [open].
  - A sharpness construction for η = 1/2 is not needed: INV-P's random coset unions bound the pencil form from
    below at ≈ 0.85r, and the theorem above shows pairs reach r + o(k) for small r.
- Of the coordinator's (a)/(b)/(c): **(a) reached in the regime r ≤ c0(ν)k** (η → 0, weight r + o(k)). (b) not
  reached. (c) not needed: no gap construction was attempted.

## 1. Lemma FW (forbidding one intersection; Frankl–Wilson modular method) [proved by hand]
**Lemma FW.** Let p be prime with (k+1)/2 ≤ p ≤ k. Let F be a family of k-subsets of [n] in which no two members
meet in exactly k − p points. Then |F| ≤ Σ_{i<p} C(n,i).

*Proof.*
- **Residue step.** If i ∈ [0, k−1] and i ≡ k (mod p), then i = k − tp with t ≥ 1. Since k − 2p ≤ −1, only t = 1
  is possible, so i = k − p. Hence distinct F, G ∈ F have |F∩G| ≢ k (mod p). (`fw_pen.py check 400`: 0 exceptions.)
- **Polynomials.** Over F_p, put L = F_p ∖ {k mod p} (p − 1 residues) and P_F(x) = Π_{μ∈L} (Σ_{i∈F} x_i − μ).
  - For G ≠ F, P_F(1_G) = Π(|F∩G| − μ) = 0, because |F∩G| mod p ∈ L.
  - P_F(1_F) = Π_{μ≠k}(k − μ) = (p−1)! ≢ 0.
- **Independence.** Replace each x_i^a by x_i. This keeps the values on {0,1}^n and gives degree ≤ p − 1.
  If Σ c_F P_F = 0, evaluating at 1_G gives c_G (p−1)! = 0. So the P_F are independent in a space of dimension
  Σ_{i<p} C(n,i). ∎
- This is the classical Frankl–Wilson argument. The sharper bound C(n, p−1) [cited] is not needed.
- Brute check, 7 tiny cases (n ≤ 10): exact maxima 5, 8, 17, 21, 21, 27, 28 against bounds 8, 9, 37, 46, 46, 56,
  56 [computed exact, `lemma_brute.py`].

## 2. Theorem FW (PEN by counting) [proved by hand]
**Covering count.** Every (k+r)-set contains a member, and each member lies in C(n−k, r) such sets. So
|H| ≥ C(n, k+r)/C(n−k, r) = C(n,k)/C(k+r, r).

**Theorem FW.** Let H be k-uniform and (k+r)-covering on n points. Let p be prime with max((k+1)/2, (k+r)/2) ≤ p ≤ k
and C(n,k) > C(k+r, r) · Σ_{i<p} C(n,i). Then H has a pencil of weight 2p − k ≤ r + (2p − k − r).

*Proof.* By the count and Lemma FW, some x1, x2 ∈ H have |x1∩x2| = k − p, so |x1Δx2| = 2p ≥ k + r.
- Let A ⊆ x1Δx2 with |A| = k + r. Covering gives x3 ⊆ A.
- Then x1∩x2∩x3 = ∅ and wt(x1+x2+x3) = |(x1Δx2) ∖ x3| = 2p − k.
- This is the second branch of the PROGRAMME3 pair bound. No outside points are needed. ∎
- `fw_pen.py` also allows 2p < k + r, using the first branch (weight k + 2r − 2p). This needs p ≥ 2k + r − n.

**Asymptotics.** Take p the least prime ≥ (k+r+1)/2. Then 2p − k − r ≤ 2g + 1. With ρ = r/k, the condition holds for
k ≥ k0 whenever
  (1+ρ) H(ρ/(1+ρ)) + ν H((1+ρ)/(2ν)) < ν H(1/ν) − o(1).
The largest such ρ is c0(ν) (`fw_pen.py frontier`, `limits`). Everything here is explicit, with no ineffective
constant.
- Uniform in ν: Theorem FW needs no hypothesis on n. A first version used Frankl–Rödl [cited: Keevash–Long 2014,
  Thm 1] after deleting points down to n′ = ⌈7k/4⌉. Deleting points preserves (k+r)-covering. That version gives
  only an ineffective c0, so FW replaces it.

**Corollary (slope 1/5 near 7/4).** Let H be k-uniform and (7,2) with τ = T + 1.
- Lemma P1: every pencil has weight ≥ 4T − 3k − 5.
- If r ≤ (c0(ν) − o(1))k, Theorem FW gives weight ≤ r + 2g + 1 = n − k − T + 2g + 1.
- So 5T ≤ n + 2k + 6 + 2g, that is, e ≤ (s + 2g + 11)/5.
- In the other case r > c0 k, and then e = s − r + 1 < s + 1 − c0 k.
- Hence e ≤ max(s/5, s − c0(ν)k) + o(k), and ≤ 3s/11 + O(1) always.
- For ν ≤ 1.7840 we have s + 1 < c0(ν)k, so the first case always holds. The new bound is the better one for
  s < 11c0(ν)k/8, that is ν < 1.7994 [computed exact].
- Exact combination, k = 2000 (`fw_pen.py slope 1000 2000`):

  | s | 20 | 40 | 60 | 80 | 100 | ≥ 110 |
  |---|---|---|---|---|---|---|
  | e_max | 6 | 10 | 14 | 18 | 26 | = 3/11 |
  | 3/11 bound | 7 | 13 | 18 | 24 | 29 | |

  Up to s ≈ 0.045k this is e_max = s/5 + 2 [computed exact; rests on P1 and Theorem FW].

## 3. Why it stops at r ≈ 0.03k, and what would extend it [proved by hand / heuristic / open]
- **Offset identity** [proved by hand]. Write j_ab = (k−r)/2 + α_ab. A pencil has weight 3r − 2(α12 + α13 + α23).
  The pair bound gives r + 2|α|.
  - So weight < r needs Σα > r/2, which is a genuinely three-member event.
  - Pair forms floor at r (INV-P). Theorem FW achieves that floor.
- **Bands do not help FW** [proved by hand].
  - Forbid all intersections in [k−p, k−p+w] with k−p+w < p. The same proof, with L missing w+1 residues, gives
    |F| ≤ Σ_{i<p−w} C(n,i).
  - In distance terms the degree is d_lo/2, where d_lo is the bottom of the forbidden distance band. So η only
    shifts p down to (k+(1−η)r)/2.
  - c0 at η = 1/2: 0.0315 (ν = 7/4) and 0.0428 (ν = 11/6). The hard ceiling (d_lo → k) is 0.0336 and 0.0461
    [computed exact].
- **Density-only arguments cannot pass ρ ≈ 0.108 (ν = 7/4) / 0.120 (ν = 11/6)** [proved by hand].
  - The star {B ⊇ S}, |S| = ⌈k/2⌉, has all distances < k. Its density is exp(−k[νH(1/ν) − (ν−½)H(1/(2ν−1))]).
  - That density exceeds the covering lower bound 1/C(k+r,r) beyond those ρ.
  - The Fano window needs r ≤ s + 1 ≤ (ν − 7/4)k + 1 ≤ 0.084k. That is below 0.108, so a sharper
    forbidden-intersection bound could still cover the whole window.
  - **Target D** [open]: k-uniform families on νk points (7/4 ≤ ν ≤ 11/6) with no intersection in a band of width
    ηr around (k−r)/2 have density < 1/C(k+r, r) for all r ≤ (ν − 7/4)k + 1. This would give PEN(η), hence slope
    (1+η)/(5+η), throughout the window. FW proves it for r ≤ c0(ν)k.
- **Local (dump) methods** [heuristic, open].
  - PROGRAMME3 §6: one two-member dump cannot beat η = 1/2. In offsets the adversary's escape is clean: either
    both new offsets fall ≤ −ηr/2 (cost ηr per side), or a mixed pattern.
  - In the escapes I checked, the pencil (x1, x2, y) itself is heavy: e.g. at α12 = −ηr/2 with all r drops in A,
    its weight is ≥ (2+η)r.
  - I did not complete the multi-round analysis. Covering is used only through global density in Theorem FW;
    combining local covering with FW (e.g. counting in links or traces) is the natural next step.
- **Small SAT probes** (covering + no pair at the exact centre l = ⌊(k−r)/2⌋, `exact_sat.py`) [computed exact]:
  - UNSAT: (13,7,1), (14,8,1), (15,8,1).
  - SAT: (13,7,2) and (14,8,2), but only through K^{(k)}_{n−r}, whose intersections are ≥ 2k−n+r > l. This is a
    boundary artefact: Theorem FW needs l ≈ k/2 ≫ 2k − n + r.
  - These sizes are far from the window and say nothing about c0.

## 4. Status and checks
- Lemma FW: classical argument, rewritten in full. Theorem FW: three lines on top of it. The corollary rests also on
  P1 (HAND). Nothing has had independent review. The integer arithmetic is checked by `fw_pen.py` for k ≤ 2000.
- What a checker should re-verify:
  - (i) the residue step;
  - (ii) the multilinear independence;
  - (iii) |H| ≥ C(n,k)/C(k+r,r);
  - (iv) the e-arithmetic of the corollary, (s + 2g + 11)/5;
  - (v) the entropy limits, `fw_pen.py limits`.
- Upstream (not applied; LEDGER untouched): the scoreboard could add "e ≤ (s + 2g(k) + 11)/5 for n < 1.784k, and
  e ≤ max(s/5, s − c0(ν)k) + o(k) beyond" [HAND, via P1]. The four-region lower end becomes (7/4 + 5ε)k for
  ε ≤ 0.0074.

## 5. Reproduction (`compute/programme4/pen/`, `py -3.14`, single core)
- `fw_pen.py check 400` (seconds). `fw_pen.py frontier` (~10 min). `fw_pen.py limits` (seconds).
- `fw_pen.py slope 1000 2000` (~3 min).
- `lemma_brute.py` (MaxSAT; the last case, (11,5,3), was stopped unfinished). `exact_sat.py n k r [l=L] [t=S]`.
- Logs: `logs/fw_frontier.log`, `fw_limits.log`, `fw_slope.log`, `lemma_brute.log`, `exact_sat_small.log`.
