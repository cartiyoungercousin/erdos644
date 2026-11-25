# Programme 3, (LT), (PEN) and Lemma 5: light triples and pencils in covering families

Tags: [proved by hand], [computed exact], [heuristic], [open]. Nothing here is independently verified.
Code: `compute/programme3/lt/` (`lt_exact.py`, `pen_check.py`, `gap_sat.py`), logs in `lt/logs/`. Nothing committed.
Notation: H k-uniform on n points, (k+r)-**covering** (every (k+r)-set contains a member), T = n − k − r, so
τ ≥ T+1 gives covering. s = n − 7k/4, e = T − 3k/4 (excess), ε = e/k, δ = s/k. j = |x ∩ y|. A **pencil** is three
members with x1∩x2∩x3 = ∅; its weight is wt(x1+x2+x3).

> **Implications box (three separate questions).**
> - **(LT)** (all triples, threshold (12n−21k)/7, n < 11k/6). A NO would be a counterexample via Lemma Q (σ = id) plus
>   the Fano classification. **Lemma Q with σ = id rests on VERIFIED results only**: it is the pencil-sum identity
>   (PROGRESS Lemma `lem:pencil`, VERIFIED) applied as in Corollary 7 (§4; this confirms PAPER.tex Prop. `prop:LT`).
>   General σ adds only "σ(s_p) ∈ 𝒯+𝒯+𝒯" (one line). **Answer: YES** for every ε > 0 and k large (§3). In fact the
>   light triple can be taken to be a **pencil**. This kills every Lemma-Q counterexample, for every σ.
> - **(PEN(η))** (a pair with |x1Δx2| − (k+r) ∈ [−ηr, ηr], so a pencil of weight ≤ (1+η)r). **PEN(1/2) holds**, with
>   ηr = ⌈(r−1)/2⌉ + 1 (§2). With Lemma P1 this gives a **new unconditional bound** τ ≤ (3n+3k+24)/11 for every
>   k-uniform (7,2) family with n ≤ 2k, i.e. **slope 3/11** (old: 1/3, Lemma 8′ and Theorem A). Corollary: δ ≥ 11ε/3.
>   PEN(η) for η < 1/2 is [open]. A gap family (a NO) would only be a construction target, not a counterexample.
> - **Where they meet**: the pair bound W ≤ r + |s − (k+r)| (both sides, s = |x1Δx2|, §1). The YES for (LT) and the
>   slope gain both come from the same centred dump.

## 0. Verdict
- **(LT): YES** [proved by hand]. Precisely: every (k+r)-covering family satisfying the size conditions of §1 has a
  pencil of weight ≤ ⌊3r/2⌋ + 1. And (12n−21k)/7 − 3r/2 = (3s+21e)/14, so whenever e ≥ −s/7 + 2 this pencil is light.
  Lemma Q never certifies anything with τ ≥ 3k/4 − s/7 + O(1) (σ arbitrary, since W_σ ≤ W_id).
  Exact scan, Erdős range, k = 8..160, ε ∈ {0.005, 0.01, 0.02}: the argument wins in every case. It fails only at
  ε = 0 with r ∈ {1,2} (O(1) boundary) [computed exact].
- **PEN(1/2): YES** [proved by hand], hence **τ ≤ (3n+3k+24)/11** for (7,2) families, n ≤ 2k. The arithmetic and size
  conditions are checked for all k ≤ 300, n ≤ 2k [computed exact]. This rests on Lemma P1 (HAND, re-checked in §4).
- The brief's Lemma 5 is correct as stated, but its interval is one-sided. **Centring the interval** at (k−r)/2 is
  the whole gain (§5).
- Below η = 1/2: [open]. Two-member dumps provably cannot go lower (§6). Small gap searches find no gap families.

## 1. The centred dump (Lemma 5c) and the two-sided pair bound [proved by hand]
**Pair bound.** For members x1, x2 with s = |x1Δx2| there is x3 with x3 ∩ x1 ∩ x2 = ∅ and
wt(x1+x2+x3) ≤ r + |s − (k+r)|.
- If s ≤ k+r, let A = (x1Δx2) ∪ (k+r−s points outside x1∪x2). This needs T ≥ j. Then x3 ⊆ A has weight
  ≤ k + 2r − s.
- If s ≥ k+r, let A ⊆ x1Δx2. Then x3 ⊆ A has weight s − k.
- (Lemma 8′ / CX §2 used only the first branch. The second is also in Lemma 8′'s proof.)

**Lemma 5c.** Let I = [lo, hi] be an interval of w+1 integers with 2w+2 > r. Suppose members x1, x2 have
j = |x1∩x2| ≤ k − hi and k + r − 2hi ≤ n − 2k + j. Then some member y has |y∩x1| ∈ I or |y∩x2| ∈ I.
*Proof.* Take A = A1 ∪ A2 ∪ O with Ai ⊆ xi∖x_{3−i}, |Ai| = hi, O outside x1∪x2, |O| = k+r−2hi. A member y ⊆ A
omits exactly r points of A, and |y∩xi| = |y∩Ai| ≤ hi. If both are < lo, y omits ≥ w+1 points of each Ai, so
2w+2 ≤ r, a contradiction. ∎
- **Existence of x1, x2.** Covering gives, for each member x1 and each ℓ with k+r−ℓ ≤ n−k, a member x2 with
  j ∈ [ℓ−r, ℓ] (take |A ∩ x1| = ℓ). Take ℓ = k − hi. This works if k − hi − r ≥ max(0, 3k+r−2hi−n) and hi ≤ T.
- Brute force on explicit sets: 52 random instances, every y ⊆ A enumerated, all pass [computed exact].

## 2. PEN(1/2) and the slope 3/11 [proved by hand]
**Theorem PEN.** Let w = ⌈(r−1)/2⌉. Choose I of w+1 integers minimising D = max_{j∈I} |2j − (k−r)|. Then D = w if
w ≡ k+r (mod 2), and D = w+1 otherwise.
Under the size conditions of §1 for this I and for x1, x2, H has a pencil of weight ≤ r + D ≤ ⌊3r/2⌋ + 1.
- Asymptotically the conditions are hi ≈ k/2 − r/4 ≤ T and T ≥ k/2 + 5r/4 + O(1).
*Proof.* By Lemma 5c, some y has |y∩xi| = j′ ∈ I. Then s′ = 2k − 2j′ has |s′ − (k+r)| = |2j′ − (k−r)| ≤ D.
Apply the pair bound to (xi, y). ∎ So PEN(η) holds with ηr = D ≤ r/2 + 1.

**Corollary (slope 3/11).** Let H be k-uniform and (7,2) on n ≤ 2k points. Then τ(H) ≤ (3n + 3k + 24)/11, i.e.
τ ≤ 3k/4 + (3/11)(n − 7k/4) + O(1).
*Proof.* Put T = τ − 1, so H is (k+r)-covering with r = n − k − T ≥ 0.
- By Lemma P1, every pencil has weight ≥ 4T − 3k − 5.
- By Theorem PEN, some pencil has weight ≤ ⌊3r/2⌋ + 1.
- So 8T − 6k − 12 < 3r + 2. This gives 11T < 3n + 3k + 14.
- Size conditions: if T+1 > (3n+3k+24)/11, then r < (8n−14k)/11 and T ≥ k/2 + 5r/4 + O(1) for n ≤ 15k/7 − O(1). ∎

Checks:
- `pen_check.py corollary 300`: for every k ≤ 300, n ≤ 2k and every T above the bound, the conditions hold and P1 is
  triggered. 0 exceptions [computed exact].
- Comparison: (2n+k)/6 + 2 = 3k/4 + s/3 + 2 (C1 / Theorem A). New: 3k/4 + 3s/11. Coordinator formula
  ((1+η)/(5+η))s at η = 1/2 gives 3/11 ✓.
- Sanity: K_n^(k) with n = ⌈7k/4⌉ − 1 has τ = n−k+1 ≤ (3n+3k+24)/11 ⇔ 8n ≤ 14k + 13 ✓ (nearly tight). So no known
  (7,2) family violates it.
- SAT, independent of the proof: "a covering family with no pencil of weight ≤ P" is UNSAT at
  (n,k,r,P) = (11,5,1,1), (12,5,2,3), (10,4,2,4), and even (10,4,2,2). Lemma 8′ would give only 3, 5, 5.
  (12,5,2,1) timed out [computed exact, `logs/pen_sat_small.log`]. Small sizes only.

## 3. (LT): YES, two independent routes [proved by hand; exact scans]
- **Route B (pencil).** Theorem PEN gives a pencil of weight ≤ ⌊3r/2⌋ + 1. With r = n−k−T,
  (12n−21k)/7 − 3r/2 = (3s+21e)/14 > 0 once e > −s/7. With ε > 0 the margin is ≈ (δ/7 + 5ε)·(3/2)k → ∞.
- **Route A (two steps, all triples; found first).** Lemma-Q band: B = {j : k − w0 ≤ 2j ≤ k − 2r + w0}, with
  w0 = ⌊(12n−21k)/7⌋. A pair in B gives a light triple (pair bound). B is two-sided, width w0 − r = (5δ/7+ε)k.
  The note's band was the upper half only.
  - Step 2: let j = μ + t, just above B (μ = max B). Take A2 = (x1Δx2) ∪ (a points of x1∩x2) ∪ outside, with
    |A2 ∩ x1| = b ∈ [λ + r, μ + (r−t)/2] (λ = min B).
  - Every x3 ⊆ A2 then has |x3∩xi| ∈ B for some i, or a light (x1,x2,x3).
    - "Below B" needs > r drops.
    - "Both above B" leaves the drops in x1Δx2 below r − t, so wt(x1+x2+x3) ≤ w0.
  - This works for t ≤ 2w0 − 3r, so B ∪ step-2 is an interval of length 3w0 − 4r. It contains a covering window
    (length r) iff 3w0 ≥ 5r, i.e. δ/7 + 5ε ≥ 0.
  - `lt_exact.py` enumerates every adversary drop vector (no closed form). k = 20..220, all n ∈ [7k/4, 11k/6),
    1 ≤ r ≤ w0: the argument wins in every case with 3w0 ≥ 5r (20 113 cases) [computed exact].
- (LT) YES does not give a slope by itself. Route B does, because its triples are pencils.

## 4. Re-checks [proved by hand]
- **C0** (PROGRAMME2_C §1). Index lines by u ∈ F₂³∖0, with q ∈ ℓ_u iff u·q = 0. Colour a_x = χ(x). Then
  R_{ℓ_u} = {x : u·a_x = 1}. Its indicator is x ↦ u·a_x, which is linear in u. So R_u + R_v + R_{u+v} = 0 ✓.
  B_u ⊆ R_u is the definition of Fano type (PROGRESS, lemma col) ✓.
- **Lemma Q, line by line.**
  - E_u = R_u∖B_u. Then B_u+B_v+B_{u+v} = E_u+E_v+E_{u+v}, of weight ≤ e_u+e_v+e_{u+v} ✓.
  - The left side is a sum of three members, so its weight is ≥ W ✓ (σ = id; for general σ its class lies in
    𝒯+𝒯+𝒯 ✓).
  - Each u lies on 3 of the 7 lines {u,v,u+v}, so 3Σe ≥ 7W ✓.
  - Σ|R_u| = Σ_x 4·[a_x ≠ 0] ≤ 4n and Σ|B_u| = 7k, so Σe ≤ 4n − 7k ✓. **Correct.**
- **Confirmed (coordinator's question):** for σ = id this is exactly the pencil-sum identity (VERIFIED). There
  Σ_p wt(s_p) ≤ 3(4|∪B| − Σ|B|) ≤ 3(4n−7k), and each s_p is a sum of three members. Repeats have weight k > threshold.
  Then Theorem `thm:class` (EXACT) for n < 11k/6. So "covering family with no light triple ⇒ (7,2)" rests on
  VERIFIED results only, not on hand-only Lemma Q. (Moot now: such families do not exist for ε > 0, k large.)
- **Lemma P1** (needed for §2), re-derived:
  - Colour Z → p0, D_ij → Q_k, E_i → Q_{i+1}. Then x_i ⊆ R_{ℓ_i} ✓.
  - Each of the other 4 lines meets each Q_i once, and each point of Q_i lies on two of them ✓.
  - With even splits, |L_ℓ| ≤ (|∪x_i| + 3)/2 ≤ ((3k+w)/2 + 3)/2 ≤ T iff w ≤ 4T − 3k − 6 ✓. Then R_ℓ contains a
    member by covering ✓.
  - P1 is correct as stated. It is HAND, not LEAN, so the Corollary of §2 is [HAND].

## 5. The brief's Lemma 5 [proved by hand]
- As stated (I = [⌈(k−r)/2⌉, ⌈(k−r)/2⌉ + w]), the proof is right. The exact hypotheses are those of §1 (pair
  existence: k − hi − r ≥ max(0, 3k+r−2hi−n), hi ≤ T). In the Fano window these hold, since T ≈ 3k/4 ≫ k/2 + 5r/4.
- With w = 5r/14 + 6εk/7 (the note's one-sided Q-band), 2w+2 > r ⇔ r < 6εk + 7 ⇔ δ < 7ε + 7/k ✓, as the brief says.
- **Why it gives only η = 1 for PEN**: I starts at the centre (k−r)/2, so |2j − (k−r)| ranges up to 2w ≈ r. Put I
  around the centre instead: the pair bound is two-sided, so the deviation is ≤ w+1 ≈ r/2. That gives η = 1/2.
- For (LT), the two-sided Q-band has width w0 − r. Lemma 5c then needs 2(w0−r) + 2 > r ⇔ 3δ/7 + 3ε > 0: always.

## 6. Below η = 1/2: obstruction [proved by hand for two-member dumps; rest heuristic / open]
- **Two-member dumps cannot beat 1/2.**
  - Take A ⊆ V∖(x1∩x2) with parts of sizes h1, h2 in x_i∖x_{3−i}. With h_i ≤ hi, the adversary drops just over ηr
    from each part.
  - Then both |y∩xi| fall below I, at total cost 2ηr + 2 ≤ r when η < 1/2.
  - That y is far from x1Δx2: wt(x1+x2+y) ≥ k − 2j + 2(1+η)r. This is > (1+η)r at every admissible j ≤ k − hi.
  - Points of x1∩x2 in A only help the adversary (shared drops), and kill the pencil.
  - The two-step game (Route A) also fails for pencils: the adversary escapes by keeping one point of x1∩x2.
- **General one-shot dumps** (m known members):
  - The adversary needs an r-set D ⊆ A with every |D ∩ x_i| outside a window of w+1 values. This asks to cover the
    polytope P_A = {(|D∩x_i|)_i} by m coordinate slabs of width w.
  - Disjoint parts would give w ≈ r/m. But |A∩x_i| ≥ hi ≈ k/2 and |A| = k+r allow only 2 disjoint parts, and
    overlaps couple the coordinates. The 3- and 4-part patterns I tried do worse than Lemma 5c.
  - Proportional drops show that no dump beats η* ≈ (1 − r/k)/(2 + r/k) by more than O(r/k) [heuristic].
  - So PEN(η < 1/2) needs a new idea (multi-step with pencil threats, or counting). [open]
- **Gap families, small sizes** (`gap_sat.py`; covering + no pair with j ∈ J, solution re-verified if SAT)
  [computed exact]:
  - (14,5,3), J = {1,2} (Lemma 5c interval): UNSAT ✓.
  - (14,5,3), J = {2} (single centred value, η < 1/2): UNSAT. So no gap family exists here.
  - (15,6,3), J = {1,2}: UNSAT ✓. The single-value runs (15,6,3), J = {1} / {2}: see `logs/gap_sat_small.log`.
  - These sizes are far from the Fano window (r ~ k/2). They are evidence about the small-r combinatorics only.

## 7. What changes upstream
- Kills BAND and (LT) as counterexample routes: no Lemma-Q-certified counterexample exists for ε > 0, k ≥ k0.
  A counterexample in the Fano window must be seven-free for a reason other than all triple sums being heavy.
- New bound: (7,2) ⇒ τ ≤ (3n+3k+24)/11 for n ≤ 2k, so δ ≥ 11ε/3 (was 3ε). The four-region map's lower end n ≥ (7/4+3ε)k
  improves to (7/4 + 11ε/3)k − O(1) [HAND, via P1].
- Next target: PEN(η) for η < 1/2. η → 0 (Pencil-D) would give slope 1/5, i.e. δ ≥ 5ε.

## 8. Reproduction (from `compute/programme3/lt/`, `py -3.14`, all single-core, each < 6 min)
- `lt_exact.py scan 20 140` and `scan 141 220`: two-step argument, exhaustive over drops.
- `lt_exact.py routes 8 160`: Erdős-range scan, both routes.
- `pen_check.py table | lemma5 300 | corollary 300 | sat n k r P`.
- `gap_sat.py n k r j...`.
- Logs: `logs/lt_*.log`, `logs/pen_*.log`, `logs/gap_sat_small.log`.
