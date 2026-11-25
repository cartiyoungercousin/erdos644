# FRONTIER — does the verified machinery give f(k,7) <= (t* + o(1))k with t* < 7/8?

Brief: use only LEDGER items marked VERIFIED/LEAN (plus steps proved here) to find the smallest t* with
f(k,7) <= (t* + o(1))k; exploit that the core window 5t − 2 < N < 3 − t is empty for t >= 5/6.
Code: `compute/frontier/stretch_density.py`, `compute/frontier/thmC_rounding.py` (each < 10 s).
Units k = 1, c = N − 1, ω = N − 1 − t, Z = [N − 2t, 3t − 2] (the Lemma 90.1 window).
Tags: [VERIFIED], [LEAN] as in LEDGER; [proved by hand] = new here, not yet checked by a verifier;
[computed float]; [heuristic]. Nothing here is committed.

## 0. Verdict

**No new upper bound follows. The smallest t* that can be rigorously justified is 7/8 (FKW 1999, external).**
There are three independent reasons. Any one of them is enough to block t* < 7/8.

- **(A) Structural, for every t: the N-case split is a statement about confined families.**
  - CP, TWIN 16.A and the bottom strip (§90–§91) are statements about k-uniform families whose whole vertex set has
    N·k points (TWIN 16.2; CORE §1 "all replies inside V").
  - The verified transfer to general families (TWIN §13, Theorem A; PROOFS item 5(a)) needs the **three anchors to be
    among the final seven**. None of these three certificates contains them. 16.A builds seven fresh replies; 90.1 uses
    a pair plus five requests; CP allows any seven.
  - The open-game gap this leaves is TWIN's G2 (far replies; TWIN 11 and 17.2–17.3, PETAL 9.3–9.4). It is not closed
    at any t.
- **(B) At t >= 5/6, the confined stretch 3t − 1/2 < N < 3 − t is open.**
  - Lemma 90.1 applies throughout it (2.2), but nothing verified forces the pair.
  - Frankl–Rödl needs ε <= ε_0, which is ineffective. Frankl–Wilson misses by a margin of at least 0.218 in the exponent.
  - More strongly, **no density-only theorem can force a Z-pair anywhere in the stretch for t >= 0.8095** (Prop. 2.3).
- **(C) The petal side N >= 3 − t is not closed for general adversaries.**
  - The verified petal theorems (J, J′, J″, AP, DS-b, PS–PS3, FF) close specific adversary classes: two-class 𝒞(c, μ),
    arena and pooled-arena families.
  - The stateless anchored wins (C, D, L, K, Theorem T on anchors) cover only some anchor shapes.
  - Theorem F hands the adversary every near-copy shape, and no verified steering lemma (STEP 1) reaches a winning shape
    at any t < 7/8.

**Missing lemmas, and the t* they would give (§5):**
- ML-1 (confined stretch pair) gives any t > 5/6, but **for confined families only**.
- ML-1 + ML-2 (lift) + ML-3 (spread side) gives f(k,7) <= (5/6 + o(1))k, which is below 11/13.
- The independent anchored route ML-R1 (certify R1 at 0.85) gives f(k,7) <= (17/20 + o(1))k. That is below 7/8 and
  6/7, but above 11/13.

## 1. Which results transfer to general families

The anchored reduction [VERIFIED W1; PROOFS §8 item 5]:
- A requester win of G(V) transfers to every family, with the same requests.
- G(V) is the game after three anchors with empty common intersection, V their union, the anchors kept among the seven.
- Proviso 5(a): "a strategy that discards an anchor is outside the reduction".
- TWIN 11 says the same in words: "a certified requester win in the confined game would NOT by itself prove anything
  about general families".

| result | form | contains the anchors? | transfers to f(k,7)? |
|---|---|---|---|
| Theorem C (\|V\| <= 2T − 6), Theorem D (p <= t − 1/3), Prop. E | anchored game, 4 requests | yes | yes [VERIFIED] |
| Theorem T with g = ∅ (anchors; needs p <= t and p − 2p_ab >= 1 − t for every pair) | anchored, 4 static requests | yes | yes [VERIFIED W2, specialised] |
| Theorems L, K (fourth petal + design) | anchored | yes | yes [VERIFIED W3] |
| J, J′, J″ (two-class 𝒞(c, μ)), AP, DS-b, PS, PS2, PS3 | game against a restricted class | yes | only against that class |
| TWIN 16.A (N <= 3t − 1/2) | confined: "all replies lie in a known V" | no (7 fresh) | **no** |
| Lemma 90.1 + Frankl–Rödl (strip) | family on n points | no (pair + 5) | **no** |
| CP / (Σ) shapes | family on V | no (any seven) | **no**, except the pencil (b), which is Theorem C (CORE 35.1) |

So the verified confined results prove: **every (7,2)-family on n vertices has τ <= T** for
- n <= 3T − k/2 − 6, at every t (16.A with the rounding of 2.1), and
- n <= 5T − 2k, for ε <= ε_0 (§91).

These are statements about bounded vertex sets. Nothing reduces f(k,7) to them.
- A τ-critical subfamily can have about C(k + T, k) edges.
- Lemma 17.A lifts a confined strategy only at extra cost ν, the mass of outside points lying in two fed replies. The
  adversary controls ν (G2).

## 2. The confined world at 5/6 <= t < 7/8, region by region

### 2.0 Summary table (confined families on V, |V| = N)
| region | covered by | t-range | constants | status at 5/6 <= t < 7/8 |
|---|---|---|---|---|
| N < 1 + t | vacuous: c < t, so no member holds a t-set | all t | exact | closed [proved by hand] |
| 1 + t <= N <= 3t − 1/2 | TWIN 16.A | every t >= 1/2 (the algebra in 2.1 uses only that) | effective: 7 requests, n <= 3T − k/2 − 6 | closed [VERIFIED W1 + 2.1] |
| 3t − 1/2 < N <= 5t − 2 (strip) | Lemma 90.1 + Frankl–Rödl | ε <= ε_0 only (ineffective); FW gives about 0.0088 [FLOAT/HEUR] | ineffective | **not covered** (ε >= 1/12) |
| 5t − 2 < N < 3 − t (core window) | — | — | — | empty for t >= 5/6 [proved by hand: 5t − 2 >= 3 − t iff t >= 5/6] |
| N >= 3 − t | anchored stateless wins on some shapes; restricted-class theorems | — | — | **not closed** (§3) |

At t >= 5/6 the stretch 3t − 1/2 < N < 3 − t (width 7/2 − 4t; (2, 13/6) at t = 5/6) lies inside the pair range
N <= 5t − 2. It vanishes at t = 7/8, where 16.A alone covers N < 3 − t: a sanity match with FKW's 7/8.

### 2.1 16.A at finite k, rounding fixed [proved by hand; `thmC_rounding.py` checks 3000 random shapes]
The verifier's GAP is that "half of every part" in Theorem C is not integral.

**The split.**
- Split each P_ab into two halves of sizes ⌈p/2⌉ and ⌊p/2⌋.
- Split Q_c into four near-equal parts on the 4-cycle of admissible pairs. The four pairs avoiding the two types of
  P_ab form a 4-cycle on {4, 5, 6, 7}, and round r is a vertex of it.
- Put the extra points on non-adjacent edges.

**Loads.** Each round requests one half of every P_ab and two adjacent Q-parts. So every load is at most
Σ ⌈p_ab/2⌉ + Σ ⌈q_c/2⌉ <= |U|/2 + 3, and Theorem C wins when |U| <= 2T − 6.

**Consequence for 16.A.** Take the kernel a_0 of mass n − 2T + 6. Then |U| <= 2T − 6, and |S_3| <= 2(n − 2T + 6) + k − T
<= T iff n <= 3T − k/2 − 6. This is consistent with the verifier's counterexample K(9,5) at n = 3T − k/2 − 1/2.

### 2.2 Lemma 90.1 holds for every t [re-derived by hand]
- The cells are O = o, A = B = c − o, G = 2 − N + o >= 0.
- The line loads are |L_2| = 2o + 2 − N − y and |L_3| = … = |L_6| = (y + N − o)/2.
- A valid y exists iff N − 2t <= o <= 3t − 2. The side conditions o <= N + t − 2 and o >= N − 2 hold automatically.

So in the stretch at t >= 5/6, a Z-pair gives a good seven. |Z| = 5t − 2 − N >= 6t − 5 > 0 for t > 5/6, so Z_k contains
integers for large k. **What is missing is only the forcing of the pair.**

### 2.3 Density cannot force the pair [proved by hand; numbers computed float]
**Proposition.** Fix 0.8095 <= t < 7/8 and N with 3t − 1/2 < N <= min(5t − 2, 3 − t). Let Y ⊆ V with |Y| = 3t − 2 + 1/k.
The star 𝒮 = {K ∈ C(V, c) : Y ⊆ K} has
- no two members meeting in Z, since every intersection is >= |Y| > max Z, and
- density e^{−ρk + o(k)} with ρ = N h(c/N) − (N − |Y|) h((c − |Y|)/(N − |Y|)) < γ = (N − t) h(ω/(N − t)).

γ is the T-covering density guarantee of 91.1 step 1. So 𝒮 is denser than every T-covering family is guaranteed to be,
and it has no Z-pair. Hence no theorem of the form "density >= e^{−γk} ⟹ Z-pair" exists, whether explicit or ineffective,
global or in a link (the link of a set A ⊆ Y is again a star).

Margins (`stretch_density.py`), with min over the stretch of γ − ρ:

| t | stretch | γ − δ_FW (best FW, worst N) | γ − ρ_star (min over N) |
|---|---|---|---|
| 5/6 | (2, 2.167) | +0.218 | +0.048 |
| 0.84 | (2.02, 2.16) | +0.235 | +0.060 |
| 11/13 | (2.038, 2.154) | +0.251 | +0.070 |
| 0.85 | (2.05, 2.15) | +0.260 | +0.076 |
| 6/7 | (2.071, 2.143) | +0.277 | +0.086 |
| 0.87 | (2.11, 2.13) | +0.305 | +0.105 |

- **Frankl–Wilson is also beaten directly.** It needs ℓ <= max(c/2, N − 3/2) and c − ℓ a prime power. The best choice
  ℓ* = min(3t − 2, max(c/2, N − 3/2)) gives δ_FW in the range 0.26–0.31, against γ in the range 0.48–0.63.
- The modular variant (FW / Deza–Frankl–Füredi with a prime p, forbidding the whole interval Z) reduces to the same
  single ℓ = c − p [proved by hand]. Two residues c − p, c − 2p in Z would need N < 7t/2 − 1 < 3t − 1/2.

**Consequence.** Any proof of the stretch must use T-covering itself, i.e. requests. The star is not T-covering:
3t − 2 > ω iff N < 4t − 1.

### 2.4 Request-steering of the pair stops at 3t − 1/2 [proved by hand for the two request types stated]
**One fixed member K_1.** A request S with |S ∩ K_1| = s gives |K ∩ K_1| ∈ [s, s + ω], and the adversary chooses the
value. The window is forced inside Z iff ω <= |Z| iff N <= 3t − 1/2. That is exactly 16.A's range.

**Two members K_1, K_2.** Take o_12 < min Z and a request S ⊇ K_1 ∩ K_2 with s_i = |S ∩ K_i| ∈ Z.
- The adversary must give both d_i = |D ∩ K_i| > 3t − 2 − s_i.
- D misses K_1 ∩ K_2, so this is impossible iff 2(3t − 2) >= c + o_12 − g_S, where g_S <= 2 − N + o_12 is the requested
  mass outside K_1 ∪ K_2.
- With g_S at its maximum (affordable since N <= 5t − 2) this reads N <= 3t − 1/2 again.

So neither one nor two reference members moves the steering boundary. A proof of ML-1 needs either many members (the
adversary then concentrates D on points of high multiplicity) or a non-steering argument.

## 3. The petal side N >= 3 − t at large t

What is verified:
- **Stateless anchored wins:**
  - D: p <= t − 1/3.
  - L: p_ab <= t − 1/2 and p_ab + p_ac − p_bc <= 3t − 2.
  - T on anchors: p <= t and p − 2p_ab >= 1 − t for all pairs.
  - K: an exact design criterion once a fourth triple-free petal exists.
- **Steering:**
  - S1–S3 (TWIN 14.2; checked in PROOFS §9, not a LEDGER item): for t >= t₁ = (√17 − 1)/4 ≈ 0.781, three requests give
    anchors with all p_ab <= t².
  - J/J′/J″ beat every two-class adversary.
- **Adversary shapes:**
  - Theorem F: any p_ab > t² wins the anchored game for the adversary.
  - Theorem H (TWIN 15.0): the shapes (0, b, 1 − b), but only for t < 4/5.

What is missing at every t < 7/8: TWIN 14.5(3), i.e. STEP 1. This is a bounded-request strategy that reaches an anchor
triple in the anchored requester region, against an adversary who controls overlaps from below (fresh points). The two
attempts on record:
- PETAL §8's design table (computed on grids k = 12, 16, not verified) suggests dominant-pair spread triples become wins
  from about t ≈ 0.78–0.80. It concerns only the four-petal continuation from a given triple, not steering to it.
- Exact small cases (FRESH_C 14.3): requester wins with m = 8 at (6,5), (7,6), (8,7). Their T = k − 1 makes them
  uninformative for a ratio. FAST Part 3 records adversary wins at (10,8) and (11,9) with J = 4.

The residues the brief lists for the petal side (pooled 𝒜 for t < 7/9; SL1 for t < 63/79) are indeed empty at t >= 5/6.
But they are residues of restricted classes, so their emptiness does not close the side.

## 4. The parked record path (R1/R1b; notes/archive/R1_RESULTS.md, R1b_RESULTS.md)

**Route.**
- Take the sparsest good triple of H: the minimiser of c·s1 + s2 over good triples, class 'all' or 'half'.
- Make one adaptive request.
- Finish with the Q closure (E, F, G, K + 3) or a T_c re-anchoring, or reach a contradiction with minimality.

**Transfer.** The route is anchor-keeping and family-level, since the minimiser is taken over the fixed family H. So it
does transfer to f(k,7). This is the only route with evidence below 7/8.

**Status.**
- t = 0.85: every grid profile is won (c = 3: 1/20 and 1/40 grids; class 'all', c = 4: 1 stuck profile at depth 1,
  (0.6, 0.05, 0.05), which a depth-2 run at 0.825 wins) [C].
- About 40–50% of the non-static wins are pure contradictions, re-proved in exact rationals [E]. This is the "third
  certified".
- The closures are float MILP per grid profile, and there is no continuum statement.
- t = 0.84 fails on the 1/50 grid (six stuck profiles for c = 4).

**Untracked runs at 0.83 and 0.84** (`compute/r1b/out/multi_0.8{3,4}_p2000_40_1_*`, not from this pass) report depth-2
wins for the depth-1 stuck profiles. They use the lexicographic potential 2000·s1 + 40·s2 + s3, which NEW_PATHS §1.1
proves void in the continuum model (a level-set move costs o(k)). No soundness control for that potential is logged,
so these runs carry no weight.

**Do the new tools complete it? No.**
- Q′ and Theorem T are already R1's closures.
- Lemma 90.1 and 16.A are confined and do not keep E, F, G (§1).
- Theorems S, S⁺, W, H, R restrict the family's structure. R1 needs a statement about every response to one request.
- What R1 needs is computational and analytic: ML-R1 below.

## 5. Missing lemmas and the t* each gives

**ML-1 (confined stretch pair), for fixed t > 5/6.** For k >= k_0 and 3T − k/2 − 6 < n < 3k − T, every T-covering family
of (n − k)-subsets of an n-set contains two members meeting in an integer of Z_k ∩ [n − 2T + 2, 3T − 2k − 2].
- In that interior range the 90.2 rounding has linear slack [proved by hand].
- With 16.A (2.1) and 90.1 this gives: every (7,2)-family on fewer than (3 − t)k vertices has τ <= (t + o(1))k, for every
  t > 5/6, so t*_conf = 5/6.
- By 2.3 and 2.4, ML-1 must use T-covering beyond density and beyond one- or two-member steering.

**ML-2 (lift), any t.** Either
- an anchor-keeping version of the 16.A and 90.1 certificates, or
- G2: an adversary whose outside mass ν (Lemma 17.A) is large loses at budget T.

**ML-3 (spread side), at t.** STEP 1 of TWIN 14.5(3): from any play, boundedly many requests reach an anchor triple won by
the anchored game. Equivalently: the requester region at t contains every shape she can force with S1/S3 and
re-anchoring.

ML-1 + ML-2 + ML-3 at every t > 5/6 would give **f(k,7) <= (5/6 + o(1))k**, below 11/13 and 6/7. Without ML-1 the core
window is empty but the stretch is not, so 5/6 is not reached by the case split.

**ML-R1 (certify R1 at t = 17/20), independent of ML-1–3.**
- (i) An exact (rational MILP or branch-and-bound) certificate for every closure win.
- (ii) A cover of the continuum profile region by polytopes on each of which one request wins. This needs a uniform
  margin. None is recorded; the 0.84 fine-grid failures show that grid wins do not extend automatically.
- (iii) Integer rounding at finite k, of order O(1/k).

This would give **f(k,7) <= (17/20 + o(1))k**. That improves on 7/8 (FKW) and on the unrefereed 6/7, but not on the
unrefereed 11/13.

## 6. Self-check
- 2.2 and 2.1 were re-derived twice. `thmC_rounding.py` asserts the load bound and Theorem B's criterion on 3000 random
  integer shapes; the worst excess over |U|/2 is exactly 3.
- The 2.3 exponents are first-order entropies (natural log), using the floor of 91.1 step 1. They are float, so the sign
  is reliable only to the printed margins (>= 0.048). The 0.8095 threshold is a 10^-4 grid in t with 200 points in N.
- §1 rests on PROOFS item 5(a) and TWIN 11 and 17. If a reviewer knows a reduction from general (7,2)-families to vertex
  sets of size < (3 − t)k, verdict (A) falls, but (B) and (C) still block t* < 7/8.
- Not verified by an independent checker. Not committed.
