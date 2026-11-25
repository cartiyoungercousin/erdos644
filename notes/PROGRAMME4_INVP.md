# Programme 4: INV-P, go/no-go

Tags: [proved by hand], [computed], [heuristic], [open]. Not independently verified; nothing committed. Code: §6.
Notation as in PROGRAMME2_C / PROGRAMME3_LT: n = (7/4+δ)k, T = (3/4+ε)k, H is k-uniform and T-covering (every
(k+r)-set contains a member, r = n−k−T = (δ−ε)k). P(H) = least wt(x1+x2+x3) over pencils (x1∩x2∩x3 = ∅).
Key ratio: **λ := (4T−3k−5)/r ≈ 4ε/(δ−ε)**. Seven-free forces P(H) ≥ λr (Lemma P1). With e = T−3k/4 and s = n−7k/4,
e = λs/(4+λ). λ = 1 is ε = δ/5; λ = 3/2 is ε = 3δ/11.

## 0. Verdict: NO-GO for INV-P as a route, except possibly a thin band
- **Literal INV-P is vacuous** [proved by hand, §1]: every family lies in the parity coset.
- **Meaningful INV-P is false for λ < λ\*(δ) ≈ 0.83–0.90, i.e. ε < (0.172–0.183)δ** [heuristic, exact-binomial
  margins, §3]. The witness is a random union of poly(n) heavy cosets of a random linear code: covering, thin,
  block-free, *every* triple sum of weight ≥ λr, no heavy coset holding a constant fraction of H, and no covering
  coset layer of *any* code inside H.
- **These witnesses are not counterexamples**: good sevens are expected to abound (2^{+9000} expected good Fano
  colourings at k = 2000) [heuristic]. Pencil (3-term) information is insufficient; seven-freeness must enter as 7-term.
- **λ > 1 (ε > δ/5): INV-P is not needed**: (S<) follows from PEN(λ−1) in pencil form, and INV-P is equivalent to it
  (§1.4); λ ≥ 3/2 is closed by PEN(1/2). **Unclear: λ\* < λ ≤ 1** (about 0.18δ < ε ≤ 0.2δ), exactly the coset
  constant c\* ∈ (λ_lin, 1] of Programme 2 (largest ρ/r over covering coset families).
- **Barrier** [heuristic]: using seven-freeness only via "all pencils heavy" plus covering gives at best
  τ ≤ 3k/4 + (λ\*/(4+λ\*))s ≈ 3k/4 + 0.18s, never the conjectured slope 0 below 11k/6.

## 1. INV-P made precise, and the reduction
**1.1 Definitions** (PAPER.tex, PROGRAMME_2). *Thin*: τ\*_b(H) > 7/3 − η (η from Theorem RA). *Block*: a
(W,d)-complete W with |W| ≥ (7/4−ε)k + 2d + 3; Corollary NC (VERIFIED) kills blocks, so this hypothesis is free and no
longer conditional on NC. *Coset*: a + C, C ≤ F₂^V linear; ρ_par(a+C) = least weight ≡ k (mod 2) in a+C.
*Layer*: L(a+C) = (a+C) ∩ (V choose k).

**1.2 The literal statement is vacuous** [proved by hand]. PROGRAMME2_C §6 asks for "all but o(|H|) members in one coset
a + C with every pencil sum in a + C". Take C = even-weight code and a any k-set: a + C = {weight ≡ k} contains every
member and every pencil sum (weight ≡ 3k ≡ k). Two meaningful forms:
- **INV-P_θ**: some coset with ρ_par(a+C) ≥ θ·λr contains all but γ|H| members (θ > 0 fixed, γ → 0).
- **INV-P^L**: H contains a full T-covering layer L(a+C). This is what Piece B consumes, because B builds sevens out
  of arbitrary members of a full layer.

**1.3 Reduction check** [proved by hand, by composition]:
- **(S<) ⇐ P1 + INV-P^L + (B on the layers that INV-P^L can produce).** (S) ⇔ (G) is DERIVED (RA, Corollary NC,
  padding). A seven-free (S<) family has P(H) ≥ λr by P1 [HAND]; INV-P^L gives L ⊆ H; B gives a seven in L ⊆ H.
- **INV-P_θ does not suffice.** It needs **B_sub**: "a T-covering H with (1−γ)|H| members in a heavy coset has a good
  seven", where the members in the coset are only a *subfamily* of the layer, possibly sparse and not covering alone.
  None of D, 9′, B1, S0, S1 covers subfamilies; B_sub is [open] and new (PROGRAMME2_C's "o(|H|) robustness" is a case).

**1.4 Regime split** [proved by hand; uses P1 HAND, PEN(1/2) HAND, Theorem D VERIFIED, S1's sum-filling HAND untested]:
- **λ ≥ 3/2 + O(1/r)**: PEN(1/2) gives a pencil of weight ≤ ⌊3r/2⌋+1 < λr, so no seven-free family exists.
- **1 + 2/r < λ < 3/2**: (S<) ⇐ PEN(η) in pencil form with 1+η < λ − O(1/r); INV-P plays no role. A covering layer L
  has a pencil of weight ρ_par(L) ≤ r+1 < λr (Theorem D plus S1's x1+x2+x3 = Ω), so under INV-P^L the hypothesis
  class is empty: **INV-P^L ⇔ "no family with P(H) ≥ λr"**.
- **λ ≤ 1 + 2/r** (r ≥ 4εk − 6): this is the only regime where structure (INV-P + B) could matter.

**1.5 Piece B cases still needed** (only for λ ≤ 1, and only for layers L ⊆ H):
- L inherits P(L) ≥ 4εk − 5, so ρ_par(L) ≥ 4εk − 5 wherever S1's pencil exists (codim ≲ k/2). Shift-0 layers with
  4 | k or N < 1.7985 contain a Schur-triangle pencil of weight 0 (S0), so they are excluded automatically.
- **Needed**: covering coset layers with N < 11/6, r ≥ 4εk − 6, ρ_par ≥ 4εk − 5, and
  codim(C_ev) − 1 > min((k−5r−41)/15, (r+4εk−11)/5) (above B1). This is B's open item: check (ii), giant blocks of
  dual words of weight ≥ 3, and the F‴w mixed-constant condition; plus shift 0 with k ≡ 2 (mod 4), N ≥ 1.7985.
- By §3 the route is dead for λ < λ\*. So B is needed only for codes with **ρ_par/r > λ\* ≈ 0.85**, i.e. near-extremal
  for Theorem D (c\* > λ_lin). Random codes do not reach this [heuristic]; whether any code does is [open].

## 2. Structured candidates: none violates INV-P
- **≤ 4 cosets, of any codes** [proved by hand; `algebra.py` (a), exhaustive in F₂^m for m ≤ 5].
  - Put C′ = ΣC_i and let Γ be the classes in F₂^V/C′. For |Γ| ≤ 4, Γ+Γ+Γ = aff(Γ). So if the classes of all
    realised triple sums are heavy, H lies in the single heavy coset aff(Γ) + C′.
  - Two cosets of different codes are the special case (mixed sums live in a_i + C1 + C2). Caveat [heuristic]:
    "realised" assumes sum-filling of mixed triples, as in Theorem D (C).
  - A non-linear obstruction needs ≥ 5 classes and a light odd sum of ≥ 5 of them (`algebra.py` (b): 2688/4368
    five-sets in F₂^4 have 3Γ ≠ aff Γ).
- **Davydov–Tombak / 5-cap lifts** [proved by hand, modulo realisability].
  - For Γ the 5-cap in F₂^4 (density 5/16), 3Γ = F₂^4∖{0}. So any two cells with distinct columns c ≠ c′ give a
    weight-2 vector of class c + c′ ∈ 3Γ, and P(H) ≤ 2.
  - In general, sum-free (0 ∉ 3Γ) controls only weight 0. Heaviness at level λr needs 3Γ to avoid the image Λ of the
    whole Hamming ball B_{<λr}, which contains all column differences. So dense sum-free sets are irrelevant.
- **Block-ball families** (q blocks, A = {β : wt β ≥ q−ρ}) [proved by hand; `algebra.py` (c)]. 3-sums have weight
  ≥ q − 3ρ. But a (k+r)-set can avoid the ρ+1 smallest blocks unless (ρ+1)n/q > T, which forces q − 3ρ ≤ 2 on the
  whole window. Covering kills heaviness via holes.
- **Algebraic non-linear codes** (Nordstrom–Robinson, Kerdock, Preparata, Z₄-linear) [proved by hand, envelope remark].
  Each lies in a linear envelope (RM(2,m), extended Hamming), and all odd sums lie in that envelope coset, so as Γ they
  *satisfy* INV-P's conclusion. As families they are far too small to cover (weight-36 Kerdock words of length 64,
  k = 36, N = 1.78: 2016 of them, against C(64,36) ≈ 10^{18}). Thickened by a code G they are §3 with an envelope.

## 3. The random coset-union family: INV-P is false for λ < λ\*
**Construction.** G ≤ F₂^V is a random linear code of codimension m, R = F₂^V/G, σ the syndrome map. N_b = C(k+r, r)
counts the k-subsets of a (k+r)-set. Λ = {classes containing a vector of weight < λr and parity k}, so
|Λ| ≤ V(n, λr). Take 2^m ≈ 4(n²+n+1)N_b. Let Γ ⊆ R be random with density p = 2 ln C(n,k+r)/N_b (|Γ| = O(n³)), and
delete every class in a triple (repeats allowed) with γ1+γ2+γ3 ∈ Λ. Put **H = ∪_{γ∈Γ} L(γ+G)**.

**Properties:**
- (i) **All triple sums are heavy**, deterministically: every x1+x2+x3 has class in 3Γ, which avoids Λ, so wt ≥ λr.
  This is stronger than the pencil hypothesis.
- (ii) **Covering** [heuristic]. Each (k+r)-set S has ≈ N_b distinct classes of k-subsets (collisions ≈ N_b²/2^m), so
  P(S uncovered) ≤ e^{−2 ln C(n,k+r)}. A union bound covers all S. Alteration removes an e^{−Ω(k)} fraction of Γ.
- (iii) **Heaviness survives the alteration** iff 3p²·2^m·|Λ| ≤ 0.1. Asymptotically this reads
  N·h(λω/N) < (1+ω)·h(ω/(1+ω)) with ω = δ−ε, i.e. V(n, λr) ≪ C(k+r, r). This is the same threshold as for a single
  random heavy covering coset (λ_lin), so λ\* = λ_lin + o(1).
- (iv) **No covering layer of any code inside H** [proved by hand, given (ii) and near-equal layer sizes]. A covering
  L′ has |L′| ≥ C(n,k)/N_b, so it meets ≥ 2^m/N_b ≥ 4(n²+n+1) classes, all of which must lie in Γ: probability
  ≤ p^{4(n²+n+1)}. There are ≤ 2^{n²+n} pairs (C′, a′), so INV-P^L fails.
- (v) **Far from every heavy coset** [heuristic]. If a+C′ holds (1−γ)|H|, it holds dense parts of most layers, whose
  differences span G, so C′ ⊇ G. Then a + C′ ⊇ aff(Γ′) + G = (parity class), since |Γ′| ≫ m and Γ′ is random. So
  ρ_par ≤ 2, and INV-P_θ fails for every θ > 0.
- (vi) **Thin and no block** [heuristic]. H is random-like, so τ\*_b ≈ n/τ ≈ N/t, and N/t > 7/3 ⇔ 3δ > 7ε. W = V is
  not a block, since n ≥ (7/4−ε)k + 2r + 3 ⇔ δ ≤ 3ε. A block with d ≤ r − Ω(k) needs local d-covering, and Γ is too
  sparse for that.

**Thresholds** (`rates.py`, exact log-binomials with the polynomial factors above; `logs/rates_*.log`) [computed]:

| δ | k = 2000: ε\*/δ, λ\* | k = 10⁴ | k = 10⁵ | asymptotic | linear coset, k = 10⁵ |
|---|---|---|---|---|---|
| 0.01 | 0.150, 0.41 | 0.170, 0.76 | 0.182, 0.884 | 0.183, 0.897 | 0.183, 0.890 |
| 0.04 | 0.163, 0.70 | 0.173, 0.82 | 0.177, 0.859 | 0.177, 0.863 | 0.177, 0.862 |
| 0.08 | 0.163, 0.74 | 0.170, 0.81 | 0.172, 0.833 | 0.173, 0.836 | 0.173, 0.835 |

**Sevens** [heuristic]. Lemma 5 gives no obstruction (7λr ≤ 12(r+εk) ⇔ λ ≤ 3). A balanced colouring has
|R_u| = 4n/7 = k + r′ with r′ = 4(r+εk)/7, and log₂ E[# colourings with every R_u containing a member] =
log₂ multinomial + 7 log₂(p·C(k+r′, r′)). This is +9053…+9635 at k = 2000 and +4.5·10⁵ at k = 10⁵ (`rates.py`,
column 7exp). The seven classes γ_u are unconstrained, so these families are expected to have good sevens: no
counterexample. No exact seven-freeness test was run; none is possible at these sizes.

**Not shown:** a rigorous alteration (Janson/BK) for (ii)/(iii); a worst-case collision bound for random linear
codes; (v), (vi). No finite in-window instance can be checked (at n = 100 the in-window r is ≤ 3; this needs k ≳ 10³).

## 4. Proof side: where density enters, and why covering cannot replace it
- **Natural quotient.** Let R = F₂^V/C, m = codim C, Γ the classes met by H. Covering and counting give
  |H| ≥ C(n,k)/N_b, hence |Γ| ≥ (1−o(1))2^m/N_b; that is all the density covering supplies. Heaviness needs
  3Γ ∩ Λ = ∅ with Λ ⊇ the image of B_{<λr}, which is non-trivial only if 2^m ≳ V(n, λr) = 2^{Θ(εk log(1/ε))}.
- **Dense regime.** Γ dense in R (DT needs > 5/16; Green/Sanders-type results need density 2^{−o(m)}) forces
  2^m ≤ O(|Γ|). For one coset that means 2^m ≤ O(1). Even for poly(n) classes the quotient is too small for Λ ≠ R,
  i.e. heaviness is invisible there. The random union lives at |Γ| = poly(n) in |R| = 2^{Θ(k)}: density
  2^{−m}·poly(n), below every structure theorem.
- **Covering in the quotient is a hitting condition.** Γ must meet every "drop ball" img(S) = σ(S) + σ(r-subsets of S),
  each of size ≈ N_b. A random Γ of size ≈ ln C(n,k+r)·2^m/N_b does this, and random sets have no additive structure.
  So covering cannot substitute for density in a Freiman/DT/arithmetic-regularity argument [heuristic, rates exact].
  The remaining lever is the 7-term condition (C0), whose inverse theory is quadratic (U³; PROGRAMME2_C §3) at the
  same exponentially small density.

## 5. Best partial results and the exact obstruction
- [proved by hand] INV-P (any form) holds for families supported on ≤ 4 cosets of codes, given sum-filling.
- [proved by hand] For λ > 1 + 2/r, INV-P^L ⇔ PEN-type non-existence. So (S<) in 1/5 < ε/δ < 3/11 is exactly
  PEN(η < 1/2) in pencil form, with no structure needed.
- [heuristic] For ε/δ < 0.172–0.183, INV-P is false and pencils cannot prove (S<). The obstruction is concrete: a random
  set Γ of poly(n) classes in R = F₂^V/G (|R| ≈ n²C(k+r,r)) with 3Γ ∩ σ(B_{<λr}) = ∅ and aff(Γ) = R. This is the
  "non-linear sum-free S of density ≤ 5/16 in a quotient" recorded in PROGRAMME2_C §6, now realised (density ~ n/N_b).
- [open] The band λ\* < λ ≤ 1. Two clean targets:
  **PEN\***: every covering family has a pencil of weight ≤ (λ_lin(δ)+o(1))r (sharp by §3; gives (S<) for
  ε > ε\*(δ) ≈ 0.18δ, i.e. slope 0.18 instead of 3/11); and **c\* ≤ λ_lin** (no covering coset family beats random
  codes in ρ_par/r), the coding half of the band.
- [open] For ε < 0.18δ, (S<) needs a 7-term argument; the random-union family (heavy-pencil, coset-free, expected
  not seven-free) is the test case any such argument must pass.

## 6. Reproduction (`compute/programme4/invp/`, `py -3.14`)
`rates.py 2000 10000` (1 s), `rates.py 100000` (27 s) → `logs/rates_*.log`; `algebra.py` (3 s) → `logs/algebra.log`.
