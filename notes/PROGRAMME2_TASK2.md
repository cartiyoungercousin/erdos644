# PROGRAMME 2, Task 2: the constant c* (decision point D1)

Code: `compute/programme2/task2/`. Logs: `compute/programme2/task2/logs/`. Nothing is committed and nothing is in Lean.
Tags: [proved by hand], [computed exact] (explicit objects, re-checked by independent code), [literature, checked]
(I read the statement myself, source named), [heuristic].

## Verdict and D1 outcome

**D1 outcome: the "B within reach" branch, wherever Corollary 7 is the operative mechanism (N < 11/6).** The kill
criterion is NOT triggered.

- **Theorem D [proved by hand].** Every covering coset family with dim C ≥ k + r (plus two mild conditions, which hold
  automatically in our regime) has **ρ_par ≤ r + 1**. Here ρ_par is the least weight ≡ k (mod 2) on a + C.
- The hypothesis dim C ≥ k + r follows from counting alone (|C| ≥ |H| ≥ C(n,k+r)/C(n−k,r)) once ω = r/k < 0.188 at
  t = T/k = 3/4. The bound rises to 0.237 at t = 7/8.
- This range contains the whole region N < 11/6, where Corollary 7 plus "all good sevens are Fano-type" would give a
  counterexample. So **c* = 1 there**: ρ_par/r ≤ 1 + 1/r. That is far below both thresholds:
  - the kill threshold (12/7)(1 + ε/ω);
  - the "B within reach" threshold (4/3)(1 + ε/ω).
- Theorem D also gives Proposition 9 its input: three pairwise disjoint Ω_i ⊆ a + C of the right parity, each of
  weight ≤ r + 1. The adjustment step remains Task 3's.
- **Not settled:** the range ω ≥ 0.188 (N ≥ 1.94), and small k (below). There the counting does not give
  dim C ≥ k + r. Corollary 7 alone does not decide (7,2) there in any case.

**Parity (Task 3's point).** It costs nothing.
- Replace C by its even subcode C_ev: we have H ⊆ a + C_ev because members have weight k.
- Every weight in a + C_ev is ≡ k (mod 2), so ρ(a + C_ev) = ρ_par.
- The two inputs of Theorem D are unchanged:
  - the new columns are (h_i, 1), whose pairwise differences are those of h, so dim E is unchanged;
  - |C_ev| ≥ |H| still holds.
- So every bound below is stated for ρ_par ≥ ρ. Corollary 7 is also valid with ρ_par, because the pencil sums are odd
  sums of members.

## 1. Set-up

- Columns h_1..h_n ∈ F₂^M, s ≠ 0.
- D = a + C = {x : Σ_{i∈x} h_i = s}, C = ker, H = D ∩ (V choose k).
- r is least such that every (k+r)-set contains a member. T = n − k − r, so τ(H) = T + 1. Put w = k + r.
- E = span{h_i + h_j}, e = dim E ≤ M = n − dim C.

**Lemma A [proved by hand].** For every nonzero c ∈ C (or c ∈ C_ev, for ρ_par):
  ρ ≤ r + |wt(c) − w|.
- *Case wt c ≥ w.* Take S ⊆ c with |S| = w, and a member x ⊆ S. Then x + c ∈ D and has weight wt c − k.
- *Case wt c ≤ w.* Take S ⊇ c with |S| = w, and a member x ⊆ S. Then |x ∩ c| ≥ k + wt c − w, so
  wt(x + c) ≤ 2w − k − wt c.

So ρ ≤ r + 1 as soon as C has a word of weight w − 1, w or w + 1. This generalises the second half of Lemma 8.

**Lemma B (rainbow matching) [proved by hand].** If n ≥ 2e + 1, there are e pairwise disjoint pairs {i_t, j_t} whose
differences h_{i_t} + h_{j_t} form a basis of E.

*Proof.*
- Take a maximal family of t < e such pairs, with independent labels spanning F.
- If two unmatched positions lie in different cosets of F, add that pair.
- Otherwise all n − 2t ≥ 3 unmatched positions lie in one coset c + F. Some matched pair (i, j) has h_i, h_j ∉ c + F;
  otherwise E ⊆ F.
- Write F = span(others) ⊕ ⟨h_i + h_j⟩. Let ε(u, u') be the ⟨h_i + h_j⟩-coefficient of h_u + h_{u'}. ε is additive,
  so among three unmatched positions some pair has ε = 0.
- Replace (i, j) by (i, u) and (j, u'). The t + 1 labels are independent:
  - h_i + h_u ∉ F;
  - h_j + h_{u'} = (h_i + h_u) + (h_i + h_j) + f with f ∈ span(others), and h_i + h_j ∉ span(others, h_i + h_u). ∎

**Lemma C (fixed-size subset sums fill the coset) [proved by hand].** If n ≥ 2e + 1 and e ≤ w ≤ n − e, then
  {ΣQ : |Q| = w} = w·h_1 + E.
*Proof.* Put one endpoint of each Lemma-B pair in Q, plus w − e unmatched positions; this needs n − 2e ≥ w − e.
Swapping any subset of the pairs adds any element of E. ∎

**Theorem D [proved by hand].** If n ≥ 2e + 1 and e ≤ min(w, T), then ρ ≤ r + 1, and ρ ≤ r when w is even. Applied
to a + C_ev, the same holds for ρ_par.
- *w even.* 0 ∈ E, so some w-set is a codeword. Lemma A gives ρ ≤ r.
- *w odd.* Some w-set Q has ΣQ = h_1. Then Q ∖ {1} or Q ∪ {1} is a codeword of weight w ∓ 1, and Lemma A gives
  ρ ≤ r + 1. ∎

**Corollary (counting) [proved by hand].** e ≤ n − dim C ≤ n − log₂|H|, and |H| ≥ C(n,w)/C(n−k,r) by double counting
pairs (member ⊆ w-set). So Theorem D applies whenever
  ⌈log₂ C(n,k+r) − log₂ C(n−k,r)⌉ ≥ max(k + r, T, ⌈(n+1)/2⌉).

**Byproduct for linear codes [proved by hand].** Let C be a binary linear code of codimension M with 2M + 1 ≤ n and
M ≤ min(w, n − w). Then C has a word of weight w if w is even, and of weight w ± 1 if w is odd.
- This is consistent with Enomoto–Frankl–Ito–Nomura (EFIN): at n = 4t, w = 2t our hypothesis needs dimension ≥ 2t + 1.
  For even codes it needs only 2t, since then e = M − 1.
- EFIN's sharp examples (doubly-even codes of dimension 2t − 1) avoid weight 2t, so the corollary is sharp up to one
  dimension.

**Tests [computed exact].** `test_theorem_d.js` over 4,000 random configurations (M ≤ 7, n ≤ 16), brute force
(`logs/test_theorem_d.log`):
- Lemma C: 26,075 checks, 0 failures.
- Theorem D: 3,237 instances inside its hypotheses, 0 failures.
- All 112 instances with ρ ≥ r + 2 lay outside the hypotheses (e > T; τ ≤ 2).

## 2. Asymptotics (part c) [proved by hand; closed formula evaluated numerically, `asymptotic.py`]

Normalise by k. Theorem D applies when
  g(ω,t) = N·h((1+ω)/N) − (t+ω)·h(ω/(t+ω)) − (1+ω) ≥ 0,  with N = 1 + ω + t.

| t = T/k | Theorem D holds for | i.e. N < |
|---|---|---|
| 0.75 | ω < 0.1881 | 1.938 |
| 0.80 | ω < 0.2078 | 2.008 |
| 0.875 | ω < 0.2366 | 2.112 |

- **Region N < 11/6** (ω + ε < 1/12): min g = 0.316 > 0. So ρ_par ≤ r + 1 for all large k [proved by hand].
- **Three disjoint Ω's.** Shrinking the ground set by 2(r + 1) keeps the family covering with the same k and r. Theorem
  D still applies there (min g = 0.113 over N < 11/6), giving pairwise disjoint parity-correct Ω₁, Ω₂, Ω₃. Their total
  is ≤ 3r + 3 ≤ 4n − 7k = 4r + 4εk once r ≥ 3 or εk ≥ 1. I have not checked the "mild size hypotheses" of
  Theorem 9′ against these Ω's.
- **Finite k, Corollary-7 targets** (`counting_cover.py`, `logs/counting_cover.log`):
  - Targets are 7ρ > 3(4n − 7k), ρ ≡ k (mod 2), r + 2 ≤ ρ ≤ min(2r + 1, k), with T one above the benchmark.
  - For every k ≤ 400 (both T = ⌊3k/4⌋ + 1 and ⌈3k/4⌉), every target that the counting does NOT exclude has
    N ≥ 1.94. None has N < 11/6 [computed exact; integer arithmetic plus floating log₂ with a ceiling; margins are
    large except at the boundary].
- **Frankl–Rödl** (statement as quoted in Keevash–Long) would give ρ ≤ r + 1 only for ω below an ineffective
  constant. Theorem D supersedes it.
- **Uncovered.** For ω ≥ 0.188 nothing better than Lemma 8 (ρ ≤ 2r + 1) is proved. The Delsarte LP does not help at
  small n (`lp_exclusion.py`): at k = 16, 20 its bound is about 2^25–2^32, against |H| ≥ 2^15–2^20. The script then
  crashed on an LP failure; the bug is fixed but the script was not re-run.
- [heuristic] Random codes have ρ < r in this range. I know of no structured family with ρ ≥ r + 2 and τ ≥ 3.

## 3. Small exact tables (part b) [computed exact]

`tables.js` enumerates column-type multisets with s = e₁ (WLOG), every k, and computes τ, r, ρ by brute force over
position subsets (`engine_b.js`).
- M = 2, n ≤ 12: 1,819 multisets.
- M = 3, n ≤ 11: 75,581 multisets.
- M = 4, n ≤ 11, ρ ≥ 3 supports only: 1,640,639 multisets.

Independent cross-check: `ilp_crosscheck.py` (Python, HiGHS ILP on the explicit member list; ρ by subset
enumeration) matches on 5 sample configurations, including both violators below.

Pairs with ρ ≥ r + 2 found (everything else found has ρ ≤ r + 1):

| (r, ρ) | rows | max τ | example (columns as integers, k) |
|---|---|---|---|
| (0,2), (0,3), (0,4) | 2, 3, 4 | 1 | n = k (H = {V}) |
| (1,3) | 3 | 2 | [0,0,2,2,2,4,4,4,7,7,7], k = 9 |
| (1,4) | 4 | 1 | [0×7, 2,4,8,15], k = 10 |
| (2,4) | 4 | 2 | [2,2,2,4,4,4,8,8,8,15,15], k = 8 |

**Answers.**
- **(2,4):** achievable, but only degenerately (τ = 2, T = 1). It is impossible whenever e ≤ min(k+2, T) and
  n ≥ 2e + 1, by Theorem D. None of these violators lies in the Lemma-8 regime n ≥ 3k/2 + r + 1, or has T ≥ 3k/4
  with τ ≥ 2.
- **(3,6):** needs M ≥ 6, which was not enumerated. By Theorem D it is confined to e > T, e > k + 3 or n ≤ 2e,
  i.e. τ ≤ e ≤ M or tiny k or tiny n.
- **(7,14) at k = 4m, T = 3m + 1:** excluded for k ≥ 36 by Theorem D [proved by hand + exact integer check]. Not
  decided for k = 16, ..., 32 (counting is too weak there and the LP is weaker still).
- **Correction to the brief.** (7,14) is the smallest target only for k ≡ 0 (mod 4), because the parity of ρ is that
  of k. The smallest targets for the other residues, all with T one above ⌊3k/4⌋:

  | k | smallest target | status |
  |---|---|---|
  | 4m + 1 (T = 3m + 1) | (1,3) | excluded for all m (counting covers every m) |
  | 4m + 2 | (4,8) | open for m = 2, 3, 4 |
  | 4m + 3 | (2,5) | open for m = 1 |

- **Few rows in general [proved by hand].** ρ ≥ r + 2 needs T < e ≤ M, or k + r < e, or n ≤ 2e. So violators have
  τ ≤ M, n ≤ 2M, or k + r < M. A weaker pigeonhole version: T ≥ 2^M − 1 already gives ρ ≤ r + 1 through pairs of
  equal columns.

## 4. Literature (part a)

- **Enomoto, Frankl, Ito, Nomura**, "Codes with given distances", Graphs Combin. 3 (1987) 25–38,
  DOI 10.1007/BF01788526 [literature, checked secondhand].
  - I could not open the original.
  - Read via Boyadzhiyska–Das–Lesgourgues–Petrova, arXiv:2410.05887, Thm 3.3(c): the maximum dimension of a binary
    linear code of length 4t with no word of weight 2t or 4t is 2t − 1 (EFIN Thm 1.1).
  - The same Thm 3.3 records more results on codes avoiding a few weights, from Mazorow's thesis and from
    Bassalygo–Cohen–Zémor 2000. Example: (d) for even t, t − 1 ≤ κ(n,{t,n−t,n}) ≤ n − t − 2, where κ is that maximum
    dimension.
  - Relevance: these avoid single weights. Our Lemma C is the matching "fixed-size subset sum" statement, sharp up
    to 1 against EFIN.
- **Bassalygo, Cohen, Zémor**, "Codes with forbidden distances", Discrete Math. 213 (2000) 3–11. Read only via the
  same Thm 3.3(e): excluding weight 2d costs about d·log n of dimension. Not directly needed.
- **Frankl–Rödl**, forbidden intersections: Theorem 1 as stated in Keevash–Long, arXiv:1402.6294 [checked there].
  Its δ is not explicit.
- **Ward, divisible codes**: Theorem 3.2 of Kurz's survey "Divisible codes", arXiv:2112.11763 [checked]. A Δ-divisible
  code with gcd(Δ, q) = 1 is a Δ-fold replication of a code plus zero coordinates.
  - I did not locate Ward's dimension bound for 2^e-divisible codes.
  - Relevance: divisibility is the classical way to avoid a weight window, but our C has rate ≥ (k+r)/n > 1/2,
    beyond what doubly-even codes allow. Theorem D makes this precise.
- **Covering radius against redundancy**: R ≤ n − dim C [standard; not re-read]. Here this gives ρ ≤ M. Theorem D
  replaces it by ρ ≤ r + 1 once M ≤ T.
- **Asymmetric CSS bounds**: Sarvepalli–Klappenecker–Rötteler, Proc. R. Soc. A (2009) [checked, MSR PDF]:
  - Lemma 3.3: every F_q-linear CSS-type [[n,k,d_x/d_z]] code satisfies k ≤ n − d_x − d_z + 2;
  - Theorem 3.4 gives LP bounds.
  - With one logical qubit, d_x = ρ, d_z ≥ T + 1, this gives ρ ≤ k + r, which is trivial here.
  - The CSS view loses the covering property, which is what Theorem D uses.

## 5. Kill criterion

No coset family with ρ > (12/7)δk was found or is possible in the proved range. No τ / uniformity / all-sevens check
was triggered.

Side remark [heuristic, not checked]: Corollary 7 with ρ = 1 says K_{7m+2}^{(4m+1)} (τ = 3m + 2) has no Fano-type good
seven. Whether it is (7,2) is the pair-covering question C(7m+2, 3m+1, 2) > 7, already handled by FRESH_B 1.3 and the
small-values tables. It is a complete family, not a coset construction.
