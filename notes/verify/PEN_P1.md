# Referee report: PEN(1/2), Lemma P1, slope 3/11, (LT) identity

Independent adversarial check of `notes/PROGRAMME3_LT.md` §§1–4 and Lemma P1 (`notes/PROGRAMME2_C.md` §4).
Own code only: `compute/verify_pen/` (none of `compute/programme3/` was used). Logs in `compute/verify_pen/logs/`.
Conventions used below: H is k-uniform on n points, (k+r)-covering (every (k+r)-set contains a member),
T = n − k − r (so τ ≥ T+1), j = |x1 ∩ x2|, s = n − 7k/4. **e_T := T − 3k/4** (the note's e) and
**e_τ := τ − 3k/4** (the brief's e). With T = τ − 1, e_τ = e_T + 1.

| Item | Verdict |
|---|---|
| (A) pencil bound / PEN(1/2) | **VERIFIED WITH FIXES** (one missing size condition; the conditions are necessary) |
| (B) Lemma P1 | **VERIFIED** (no restriction on n; constant depends on which ε) |
| (C) slope 3/11 corollary | **VERIFIED** for every k ≥ 1 and n ≤ 2k; the constant 24 can be lowered to 21 |
| (D) (LT) identity | **VERIFIED WITH FIXES** (off by 3/2 in the brief's convention e = τ − 3k/4) |

## (A) Pencil bound [VERIFIED WITH FIXES]

Checked line by line.
- **Pair bound.** If s = |x1Δx2| ≤ k+r: A = (x1Δx2) ∪ O with |O| = k+r−s. O fits outside x1 ∪ x2 iff
  n − (2k−j) ≥ k + r − (2k−2j), i.e. iff j ≤ T ✓. A member x3 ⊆ A has |x3 ∩ (x1Δx2)| = a ≥ s − r, and its weight is
  s + k − 2a ≤ k + 2r − s ✓. If s ≥ k+r: x3 ⊆ A ⊆ x1Δx2 has weight s − k ✓. In both branches A ∩ x1 ∩ x2 = ∅, so the
  common intersection is really empty ✓.
- **Lemma 5c.** A ∩ xi = Ai, because A2 ⊆ x2∖x1 and O lies outside. A k-set y ⊆ A misses exactly r points of A. If
  |y ∩ Ai| < lo for both i, then y misses ≥ 2(w+1) > r points ✓. The lemma uses k-uniformity (|y| = k).
- **Starting pair.** Take |A ∩ x1| = ℓ = k − hi. A member x2 ⊆ A has j ∈ [max(0, ℓ−r), ℓ]. This needs
  k + r − ℓ ≤ n − k ⇔ hi ≤ T ✓. Room for O is needed for the realised j, so the worst case j = max(0, ℓ−r) is the
  binding one. The note's "k − hi − r ≥ max(0, 3k+r−2hi−n)" is a correct sufficient form (exact form:
  max(0, k−hi−r) ≥ 3k+r−2hi−n).
- **Theorem PEN.** w = ⌈(r−1)/2⌉ gives 2w+2 ≥ r+1 > r ✓. The values 2j − (k−r) over I form a step-2 progression of
  w+1 terms, all ≡ k+r (mod 2), so D = w if w ≡ k+r and D = w+1 otherwise ✓. Then r + D ≤ r + w + 1 = ⌊3r/2⌋ + 1:
  check r = 2m gives 3m+1, and r = 2m+1 gives 3m+2 ✓. The pair bound on (xi, y) needs T ≥ j′, which follows from
  j′ ≤ hi ≤ T ✓. Also y ≠ xi, since j′ ≤ hi < k. Parity is consistent: every pencil weight is ≡ k (mod 2), and so is r + D.

**Fixes.**
1. **Missing condition |O| = k + r − 2hi ≥ 0.** §1 lists only the upper bound on |O|. For r ≥ 1 the D-minimising I
   satisfies it automatically (2hi ≤ k − r/2 + 1 ≤ k + r). For **r = 0 with k odd**, the two D-minimising intervals
   are {(k−1)/2} and {(k+1)/2}. The upper one gives |O| = −1, so the tie must be broken downward. "Choose I minimising
   D" should say "the lower one on a tie" (or state |O| ≥ 0).
2. **Clean sufficient form** (replaces "T ≥ k/2 + 5r/4 + O(1)"):
   r ≥ 1, 4T ≥ 2k + 5r + 3 and 3r ≤ 2k − 2 imply every exact condition.
   - Hand: the D-minimising I has 2hi ∈ [k − r/2 − 3/2, k − r/2 + 1].
   - Computed: 789 560 cases, k ≤ 120, 0 failures (`suff_check.py`, `logs/suff_check_120.log`).
3. **The size conditions are not removable** (a caveat, not an error).
   - SAT witness at (n,k,r) = (12,6,3), T = 3: a 20-member 6-uniform family on 12 points in which every 9-set contains
     a member, and every pencil has weight exactly 6 > ⌊3r/2⌋ + 1 = 5 (`logs/pen_sat_12_6_3_5.log`). It was
     re-verified by a plain brute-force script (`verify_witness.py`).
   - Families with no pencil at all also occur when T is small (`[N]` lines in `logs/pen_sat_sweep.log`).
   - So (A) is true only with the conditions. Anything quoting "PEN(1/2)" must carry them.

**SAT check of (A)** (`pen_sat.py`; CaDiCaL; one member fixed by symmetry; distinct members; claim tested at the
sharp value P = r + D ≤ ⌊3r/2⌋ + 1). Results are in `logs/pen_sat_sweep.log`:
- **[C] lines**: every (n,k,r) with n ≤ 13, r ≥ 1, P < k and C(n,k) ≤ 1716 where the exact conditions hold. That is
  24 instances, **all UNSAT**, so the bound holds there. They include (12,5,2), (12,6,1), (13,5,2), (13,6,1), (13,6,2)
  (64.7M pencil clauses) and (13,7,1). The n = 13, k ∈ {6,7} instances used Glucose4; the rest used CaDiCaL.
- **[Csharp] lines** (P = r + D − 2):
  - SAT at (8,4,1), (11,6,1), (12,6,1), so r + D is attained at some sizes;
  - UNSAT at (9..13,4,1);
  - (12,5,2,P=1) timed out at 240 s;
  - (13,5,2,P=1) was stopped unfinished (the CaDiCaL interrupt did not fire).
  These runs test beyond the theorem and do not bear on the verdict.

## (B) Lemma P1 [VERIFIED]

**Statement.** Let H have members of size ≤ k and be T-covering (every (n−T)-set contains a member ⇔ τ > T). If a
pencil (three members, x1∩x2∩x3 = ∅) has w = wt(x1+x2+x3) ≤ 4T − 3k − 6, then H has a Fano-type good seven.

**Proof check.**
- Colouring. Z → p0, D_ij → Q_k (k the third index), E_i → Q_{i+1}. Then:
  - x1 = E1 ∪ D12 ∪ D13 → Q2, Q3, Q2;
  - x2 = E2 ∪ D12 ∪ D23 → Q3, Q3, Q1;
  - x3 = E3 ∪ D13 ∪ D23 → Q1, Q2, Q1.
  None of these hits ℓ_i = {p0} ∪ Q_i, so x_i ⊆ R_{ℓ_i} ✓. Here R_ℓ = {x : colour ∉ ℓ}.
- Each of the other 4 lines misses p0 and meets each ℓ_i in one point of Q_i ✓. So
  |R_ℓ| ≥ |Z| + Σ⌊|C_i|/2⌋ ≥ n − |∪x_i|/2 − 3/2 ✓.
- |∪x_i| = (Σ|x_i| + w)/2 ≤ (3k + w)/2, using the empty triple intersection ✓. So |R_ℓ| ≥ n − T ⇔ w ≤ 4T − 3k − 6 ✓.
- Any two Fano points lie on a common line, so B_ℓ ⊆ R_ℓ for all 7 lines leaves no 2-point transversal ✓.
- Repeated members give a set of < 7 members, which is still a violation under the "at most seven" convention ✓.

**Hypotheses.** No condition on n is needed: neither n < 11k/6 nor the Fano classification. Uniformity is not needed
(sizes ≤ k suffice), and T is arbitrary.

**Contrapositive.** A seven-free family has w* ≥ 4T − 3k − 5 for every T < τ. The best choice is T = τ − 1, which
gives w* ≥ 4τ − 3k − 9. **The constant depends on the definition of ε:**
- With ε := T/k − 3/4 (T the covering/request size, as in the GLOSSARY's t), w* ≥ 4εk − 5. So "w* ≥ 4εk − 6" is true
  (1 weaker than proved).
- With ε := (τ − 3k/4)/k (the brief's excess), only **w* ≥ 4εk − 9** follows. "4εk − 6" is not proved in that
  convention.

**Explicit test.** `p1_check.py 3000 1`: 3000 random pencils (k ≤ 14), 1978 of them with the threshold reachable.
For each, the colouring was built, x_i ⊆ R_{ℓ_i} and the |R_ℓ| bounds were checked, and random B_ℓ ⊆ R_ℓ were
brute-force checked to have no 2-point transversal. 0 failures (`logs/p1_check_3000_1.log`).

## (C) Corollary τ ≤ (3n+3k+24)/11 [VERIFIED; the range is the full n ≤ 2k]

**Arithmetic (exact).** (7,2) and P1 give: every pencil has weight ≥ 4T − 3k − 5, with T = τ − 1. PEN gives a pencil
of weight ≤ ⌊3r/2⌋ + 1. Hence ⌊3r/2⌋ ≥ 4T − 3k − 6, so 3r ≥ 8T − 6k − 12. With r = n − k − T this is
**11T ≤ 3n + 3k + 12, i.e. τ ≤ (3n+3k+23)/11**. The note's chain ("8T−6k−12 < 3r+2 ⇒ 11T < 3n+3k+14") is valid but
loses 1. Better still:

**Sharper constant: τ ≤ (3n+3k+21)/11** [hand + computed].
- Suppose 11T ≥ 3n+3k+11.
- If 3r ≤ 8T − 6k − 13, then ⌊3r/2⌋ + 1 ≤ 4T − 3k − 6 directly.
- The two boundary cases have D = w forced by parity:
  - 3r = 8T−6k−12: r = 2m and 3(k+m) = 4T−6, so k+m is even, so w = m ≡ k+r.
  - 3r = 8T−6k−11: r = 2m+1 and 3(k+m) = 4T−7, so k+m is odd, so w ≡ k+r.
  - In both, r + D = ⌊3r/2⌋ ≤ 4T−3k−6.
- So P1 fires; hence 11T ≤ 3n+3k+10.
- Computed: `cor_check21.py 300`, 204 509 cases, 0 failures. C = 20 fails for this argument (r = 0 cases,
  e.g. k=5, n=10, T=5).

In excess form: **e_τ = τ − 3k/4 ≤ (3/11)s + 24/11** (note's constant), or **≤ (3/11)s + 21/11** (sharpened). In the
note's convention, e_T ≤ 3s/11 + 10/11. "δ ≥ 11ε/3" is correct up to O(1/k).

**Range.** (B) holds for all n, so the range is limited only by PEN's size conditions in the regime T + 1 > bound.
- Hand: 11T ≥ 3n+3k+14 gives:
  - 11r ≤ 8n − 14k − 14 ≤ 2k − 14, hence 3r ≤ 2k − 2;
  - the room condition n ≥ 2k + 2r − hi reduces to 9T ≥ 5n − 3k + 3, which holds for n ≤ (60k+93)/28 = 15k/7 + 93/28;
  - hi ≤ (k+1)/2 ≤ T.
  So every condition holds for **all k ≥ 1 and all n ≤ 2k**. For n ≤ (14k+13)/8 the bound is trivial
  (τ ≤ n − k + 1).
- Computed, all T above the bound:
  - `cor_check.py 300` (C = 24): 201 475 cases, 0 failures;
  - `cor_check23.py 300`: 0 failures;
  - `cor_check21.py 300`: 0 failures;
  - beyond 2k (k ≤ 80): 0 failures up to n ≤ 11k/5; first failures at n ≤ 9k/4 (k = 56, n = 126, room for O).
- The Fano classification (n < 11k/6) is not used anywhere, so no shrinking of the range is needed.

**Known families** (all checked against the sharper (3n+3k+21)/11):
- **K_n^(k).** Write n = 7m+q. A balanced Fano colouring has max line sum 3m + c(q), with c = (0,1,2,2,2,3,3). So
  (7,2) forces k ≥ 4m + q − c(q) + 1. The bound then needs 14c(q) ≤ 6q + 24, which holds for every q ✓.
  - K_13^(8): τ = 6 ≤ 7.6.
  - K_16^(9): τ = 8 ≤ 8.7.
  - K_23^(13): τ = 11 ≤ 11.7.
- **FKW** (n = 7m+1, k = 4m, τ = 3m+1): τ ≤ 3m + 24/11 ✓ for every m.
- **Seven-free two-block extremals** (PROGRAMME2_C §5 table): τ = 6, 8, 9, 10 ≤ 7.9, 9.5, 10.9, 11.2 ✓.
- **Exhaustive two-block falsification** (`twoblock_check.py`, own exact τ and own CP-SAT Fano model): every
  H_J with k ≤ 13 and n ≤ 2k (151 761 families) was tested. The 4033 families above (3n+3k+21)/11 all have an
  explicit Fano-type good seven (`logs/twoblock_k13_C21.log`); the same holds even at constant 20 (`logs/twoblock_k13_C20.log`).

## (D) (LT) identity [VERIFIED WITH FIXES]

- **Note's convention.** With r = n − k − T and e = e_T = T − 3k/4,
  (12n−21k)/7 − 3r/2 = (3n − 21k + 21T)/14 = (3s + 21e_T)/14 ✓ (exact).
- **Brief's convention.** With e = τ − 3k/4 and r = n − k − τ + 1 (so T = τ − 1), the identity as written is
  **false by 3/2**. The correct form is
  **(12n−21k)/7 − 3r/2 = (3s + 21e_τ)/14 − 3/2**.
- **Positivity.** The left side is > 0 iff e_T > −s/7 (⇔ e_τ > 1 − s/7).
- **Lightness.** "Light" means weight ≤ (12n−21k)/7 (PAPER (LT)), and PEN gives weight ≤ ⌊3r/2⌋ + 1. The note's
  sufficient condition e_T ≥ −s/7 + 2 leaves margin ≥ 2 ✓.
- **Exact scan** (`lt_check.py 200`): k ≤ 200, n < 11k/6, every T > 3k/4, including PEN's size conditions. 9809 cases:
  - Route B gives a light pencil in all cases but 49.
  - **The 49 exceptions** all have r = 0 and 4T = 3k+1, so k ≡ 1 (mod 4) and H = K_n^(k) with n = (7k+1)/4. There
    the threshold is 3/7 < 1 ≤ every (odd) pencil weight. So (LT) genuinely fails at these finite instances, with
    ε = 1/(4k).
  - This does not contradict (LT) as posed (fixed ε > 0, k large). But the note's "fails only at ε = 0 with r ∈ {1,2}"
    misdescribes the finite exceptions: its scan used only ε ∈ {0.005, 0.01, 0.02}.

## Reproduction (`compute/verify_pen/`, `py -3.14`, single core each)
- `cor_check.py 300`, `cor_check23.py 300`, `cor_check21.py 300`, `cor_check.py 80 11 5`
- `suff_check.py 120`, `lt_check.py 200`, `p1_check.py 3000 1`, `twoblock_check.py 13 21`
- `pen_sat.py n k r P [timeout]` (env `PEN_SOLVER=g4` for Glucose), `verify_witness.py logs/pen_sat_12_6_3_5.log 12 6 3`
- `run_jobs.sh` / `run_rest.sh` produce `logs/pen_sat_sweep.log` (job list `jobs.txt`)

Nothing here is committed. `notes/LEDGER.md` and `Lean644/` were not touched.
