# Programme 3, counterexample side (CX): structured candidates for τ > (3/4+ε)k with (7,2)

Tags: [proved by hand], [computed exact], [heuristic], [dead], [open]. Not independently verified.
Code: `compute/programme3/cx/` (`tools.py`, `coset_fams.py`, `deep_union.py`), logs in `cx/logs/`. Nothing committed.
Budget: ~45 min, ≤ 3 processes. Notation as in PROGRAMME2_C.md: n = (7/4+δ)k, T = τ−1 = (3/4+ε)k, r = n−T−k.

## 0. Verdict
- **No counterexample found; nothing promising.** Every structured family tried either has excess τ − 3k/4 = O(1)
  (no better than FKW at the same (n,k)) or contains a good seven. Section 3 has the table.
- **One useful reduction (Lemma Q, §1)**: a cheap (7,2) certificate for N < 11/6 that needs no SAT. It turns the hunt
  into a concrete extremal question, the band-avoidance problem (BAND, §2). BAND is open, but random and
  coset families fail it for structural reasons, so a counterexample needs a new kind of structure.

## 1. Lemma Q: the quotient certificate [proved by hand]
Let σ: F₂^V → Q be linear, T ⊆ Q, and H k-uniform with σ(B) ∈ T for every member. Put
W_σ = min{ wt(y) : σ(y) ∈ T+T+T } (repeats allowed).
**If 7·W_σ > 3(4n − 7k), H has no Fano-type good seven.** So for n < 11k/6 (every good seven is Fano-type,
Task 0) H is (7,2).
*Proof.* In a Fano seven, B_u ⊆ R_u = φ(u) with φ linear (C0). So R_u + R_v + R_{u+v} = 0, and
B_u + B_v + B_{u+v} = E_u + E_v + E_{u+v}, where E_u = R_u ∖ B_u and e_u = |E_u|. The left side has class in T+T+T,
so e_u + e_v + e_{u+v} ≥ W_σ on each of the 7 lines. Summing gives 3Σe_u ≥ 7W_σ, while
Σe_u = Σ|R_u| − 7k ≤ 4n − 7k. ∎
- σ = id (T = H): the condition is "every triple of members has |x1 Δ x2 Δ x3| > 12δk/7".
- σ = quotient by a code C with T = {a}: this is Corollary 7 (ρ > 12δk/7).
- **Cosets cannot use it** [proved, from Theorem D]: for N < 1.938 covering coset families have ρ ≤ r + 1 =
  (δ−ε)k + 1 < 12δk/7. Lemma Q is too weak for cosets; their seven-freeness needs B1-type arguments.

## 2. What Lemma Q demands: band avoidance [proved by hand + heuristic]
**Pair bound.** If members x1, x2 have s = |x1 Δ x2| ≤ k + r, then W_id ≤ k + 2r − s.
*Proof.* Extend x1 Δ x2 to a (k+r)-set A. By covering A contains a member x3, with |x3 ∩ (x1Δx2)| ≥ s − r. ∎
So Lemma Q at T = (3/4+ε)k needs every pairwise intersection to avoid the band
I = [(k−r)/2, (k−r)/2 + (5δ/14 + ε/2)k]. I is non-empty for every δ, and C1 already forces δ ≥ 3ε.
- **(BAND) [open]**: is there a T-covering k-uniform family on (7/4+δ)k points with no pairwise intersection in I
  and no light triple sum? Covering forces pairs with intersection in every window [ℓ−r, ℓ] for ℓ ∈ [k/4−εk, k].
  Since |I| < r once δ > 7ε/3, covering alone does not force a pair inside I.
  Frankl–Rödl-type bounds give density (1−c)^n, which does not beat the covering density e^{−Θ(k)}. No
  contradiction is known.
- **Random families die** [heuristic count]. At density p = covering threshold e^{−(k+r)h(r/(k+r))}, the expected
  number of triples with |x1∩x2| ≈ k/2 and x3 within 12δk/7 of x1 Δ x2 is ≫ |H|. At δ = 0.08 the exponent is
  ≥ +0.68k. Random linear cosets fail too: at the covering codimension, GV gives ρ ≪ 12δk/7. Their good-seven count
  is ≈ e^{(4.5−1.4)k} ≫ 1 (consistent with F‴).
- So a Lemma-Q counterexample must be a covering family whose intersection spectrum has a gap of width Θ(k) just
  below k/2. Parity/coset families have no such gap (all intersections occur). This is the cleanest form of
  "non-linear structure needed" I can give.

## 3. Constructions tried
Columns: k, N = n/k, M = number of members, τ [computed exact, HiGHS MIP], excess τ − 3k/4, W/P = minimum triple /
pencil sum (exact, or sampled pairs with the third member exhaustive = [heuristic upper bound]), Q-thr = (12n−21k)/7,
seven = general good-seven SAT result (any type, CaDiCaL; SEVEN found sevens are brute-force verified).

| # | construction | n | k | N | M | τ | τ − 3k/4 | W / P | Q-thr | seven | tag |
|---|---|---|---|---|---|---|---|---|---|---|---|
| E1a | deepest coset found (ρ = 5) of BCH [31,16,7] | 31 | 16 | 1.94 | 9152 | 5 (ILP opt.) | −7 | 8 / 8 (sampled) | 5.14 | UNKNOWN (400k conflicts) | [computed exact] τ; [dead] |
| E1b | deepest coset found (ρ = 6) of RM(2,5) [32,16,8], weight 18 | 32 | 18 | 1.78 | 14400 | ≤ 9 (greedy), τ* = 1.78 | ≤ −4.5 | — | 0.86 | not run | [computed exact] bound; [dead] |
| E2a | NON-LINEAR union: k-sets whose coset of shortened RM(2,5) [22,7] has weight ≥ 6 | 22 | 12 | 11/6 | 412096 | ≤ 8 (greedy) | ≤ −1 | — | 1.71 | not run | [computed exact] bound; [dead] |
| E2b | same, coset weight ≥ 8 | 22 | 12 | 11/6 | 9984 | ≤ 6 (greedy) | ≤ −3 | — | 1.71 | not run | [computed exact] bound; [dead] |
- RM(2,5) is an even code, so only even k occur in the ρ = 6 coset; only k = 18 lies in the window 1.72 ≤ N ≤ 1.95.
- E1a: Lemma Q holds (W = 8 > 5.14 on the sampled pairs), so there is probably no Fano seven. But N > 11/6, and
  τ = 5 makes it irrelevant.
- Not run in budget: (c) design families (AG(d,3), PG(d,2), Steiner systems) and the sum-free S of (a) on many cells.
  Reason: §4's codimension budget already rules out every high-codimension algebraic layer at these sizes. Lines of
  projective planes are not (7,2) for q ≥ 5, since 7 lines with no 3 concurrent need 4 points [hand].
- Trend in k: not measured. Every instance is already far below 3k/4 at the only k available, so no family reached
  the stage where growth matters.

## 4. Which poster condition kills what
- **Codimension budget (the killer for (a), (b) and the E2 unions)**.
  - [proved, double counting] τ ≥ T + 1 means every (k+r)-set contains a member. Counting the pairs (A, B ⊆ A)
    gives |H| ≥ C(n,k)/C(k+r, r).
  - [heuristic] A coset family has |H| ≈ C(n,k)/2^codim (exact on average over cosets), so 2^codim ≲ C(k+r, r).
  - At finite k, r = n − T − k is tiny (r ≤ 3 for τ ≥ 3k/4 + 1 in every row above). Structured codes of
    codimension 15–16 are hopeless there, which is why τ collapses to 5–9.
  - Asymptotically the budget is codim ≲ (k+r)h(r/(k+r)), so Θ(k) codimension needs r = Θ(k).
  - P1/C1 then wants 4εk ≤ 2r + 1, which is compatible. But Lemma Q needs W > 12δk/7, and by §2 random-like codes
    at the budget have W ≈ GV radius ≪ 12δk/7 (killed by **P1 / Corollary 7**, the heavy-triple condition).
- Deep-class unions (non-linear T) inherit the budget: T is a union of classes, so per A at most C(k+r,r)
  syndromes still have to hit T. This helps only by the factor |T|/|Q|, and taking T = {cw ≥ w0} keeps |T|/|Q| a
  constant while deleting the light classes. E2a keeps 63% of the slice and still loses 3 below K_22^(12)'s τ = 11.
- Coset families with few classes / small codimension: excluded by the poster (9′, D, B1). Large-codimension cosets:
  killed by the budget plus Theorem D (ρ ≤ r+1 < 12δk/7, so not even Lemma Q helps).
- Complete / near-complete blocks (K_n^(k), designs blown up to near-complete): **Theorem NC**.
- Profile families on few cells (two-block J-families, parity layers): **Theorem S⁺** and C2.
- What survives the poster and this note: covering families whose pairwise-intersection spectrum has a Θ(k) gap
  just below (k−r)/2 (BAND, §2), at N ∈ [7/4 + 3ε, 11/6). Or anything at N ≥ 11/6, where Lemma Q is not a
  certificate. No algebraic family with such a gap and covering density is known to me.
- Recommendation: do NOT invest further compute in algebraic layers. The one question worth hand time is BAND:
  prove that a T-covering family has a pair with |x1 ∩ x2| ∈ [(k−r)/2, (k−r)/2 + ck] for small c. That is a
  Frankl–Rödl-with-covering statement and would kill every Lemma-Q-type counterexample.
- Kaggle compute (offered mid-task) not used: no candidate was worth a large-k check.

## 5. Reproduction
From `compute/programme3/cx/` with `py -3.14`: `coset_fams.py rm25|bch31` (E1), `deep_union.py srm22 W0` (E2), `quick_tau.py rm25` / `quick_tau.py srm22 6|8` (LP + greedy τ brackets).
Logs: `cx/logs/e1_*.log`, `cx/logs/e2_*.log`, `cx/logs/qt_*.log`. The E1/E2 full runs (ILP + SAT) hit the 600 s cap
after one row; τ ILP at M ≈ 10^4 is the bottleneck (≈ 7 min).
