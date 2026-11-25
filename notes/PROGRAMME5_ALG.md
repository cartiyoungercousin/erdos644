# Programme 5: the algebraic angle on (S<)

Tags: [proved by hand], [computed], [heuristic], [open]. Nothing here is independently verified. Nothing committed.
Code: `compute/programme5/alg/` (§5). Setting as in PROGRAMME5_SEVEN: H k-uniform on V, n = (7/4+δ)k < 11k/6,
(k+r)-covering, T = n−k−r = (3/4+ε)k, τ = T+1. U = up-set of H in F₂^V, Z = F₂^V∖U. No colouring laws here.

## 0. Verdict
- **NO-GO as a proof route.** Every algebraic tool tested fails for a stated reason, and the four reasons are
  different. (i) Slice and partition rank need translation invariance, and the PG(2,2) system lacks it (§2.1).
  (ii) Chevalley–Warning and Ax–Katz need a degree budget that fails by the factor 7k/3n > 1 (§2.2).
  (iii) GL-invariant data (critical number, PG(2,2)-freeness, size) allow crit ≥ (4/7−o(1))n. Up-sets are capped
  at 3n/7, so such data cannot even recover the trivial bound (§2.3). (iv) MacWilliams carries no information
  off cosets (§2.4).
- **The natural algebraic induction collapses to pencils.** Bose–Burton (PG(1,2) ⇒ PG(2,2) via an anchor quotient),
  the one algebraic argument that uses monotonicity, run with A0 gives exactly P1′'s threshold w ≤ 4T−3k (§3)
  [proved by hand]: a pencil argument, under the INV-P cap of slope ≈0.18 [heuristic].
- **Positive by-products** [proved by hand unless tagged]: an exact ceiling n − M(n) for arbitrary PG(2,2)-free
  up-sets (§2.5); Fano-type seven ⟺ a Fano plane in the *pencil 3-graph* P(H) (§1); a new proof of P1′ (§3);
  [computed] the seven-free complete families have Fano-free, 3-colourable but **not 2-colourable** pencil
  3-graphs, so Fano-Turán stability (near-bipartite extremisers) is absent (§1.3).
- **Exact reason the algebraic angle is blind.** The content of (S<) is the k-uniformity of the generators, i.e.
  "every (n,k,k+r) covering design with n < 11k/6 has a Fano plane in its pencil 3-graph" (§1.2, §2.5). Rank,
  degree and invariant methods see U only through quantities that cannot tell a covering design from a layer or a
  random set (§2.1–2.4). The one method that sees coordinates (§3) inputs a single pencil per step. A proof needs
  an object seeing all seven members jointly *and* the covering structure (e.g. a rank statement for the 7-fold
  inclusion tensor restricted to H). None is known, and it cannot be a Turán/colouring statement (§1.3).

## 1. Reformulations
**1.1 Line-free lemma** [proved by hand; computed (a)]. J ⊆ F₂³∖0 has a c with ⟨c,u⟩ = 1 on J iff J has no line
{u,v,u+v} (summing gives 1 = 0; conversely a line-free J lies in a line complement {⟨c,·⟩ = 1}).

**1.2 Pencil 3-graph** [proved by hand]. P(H): vertices H, edges the triples with empty common intersection.
- Apply 1.1 pointwise to J_p = {u : p ∈ B_u}. Then B_u (u ∈ F₂³∖0) is Fano-type iff
  **B_u ∩ B_v ∩ B_{u+v} = ∅ for all 7 lines**, i.e. iff u ↦ B_u embeds the Fano plane in P(H).
- A repeat B_u = B_v needs two disjoint members, which is impossible for n < 2k.
- So in the Fano range (Corollary fanorange), **H is (7,2) ⟺ P(H) is Fano-free**. This was cross-checked on the
  complete families, where a seven exists iff M(n) ≥ k (§2.5): 10/10 pairs, k ≤ 6, n ≤ 11 [computed (c)].
- P1 is the de Caen–Füredi local configuration: an edge plus four vertices whose links realise the 3 matchings of K₄.

**1.3 Turán comparison.**
- π(Fano) = 3/4 (de Caen–Füredi), and the extremisers are 2-colourable (Füredi–Simonovits, Keevash–Sudakov).
- P(H) is far too sparse for this [heuristic]. Three random members share ≈ n(k/n)³ ≈ k/3 points, so the pencil
  density is 2^{−Θ(k)}. It is already 0.004 at K^(8)_13.
- q-colourable P(H) gives τ ≤ q(k+1)/2 (A0 per class), so a 2-colourable P allows τ up to k+1 (realised in 1.4):
  bipartiteness is not what caps τ near 3k/4. A star split 2-colours P(K^(k)_n) when 2(n−1) < 3k [proved by hand].
- [computed, `pencil_graph.py`]:

| family (seven-free) | \|H\| | pencils | 2-colourable | 3-colourable |
|---|---|---|---|---|
| K^(4)_6, K^(5)_8 | 15, 56 | 15, 840 | yes (star split) | — |
| K^(5)_9 ("stuck", e = 5/4), K^(6)_10 | 126, 210 | 31 500, 37 450 | **no** | yes |
| K^(7)_12 (f(7,7) = 6 extremal), K^(8)_13 | 792, 1287 | 1 561 560, 1 336 335 | **no** | yes |

So extremal (7,2) families are Fano-free *non-bipartite* 3-graphs: no Turán-type stability, no colouring property.

**1.4 Outside the Fano range the matroid relaxation fails** [proved by hand]. Take X₁, X₂ ⊆ V with
|X_i| = m = ⌈3k/2⌉−1 and |X₁∩X₂| = j ≤ m−k+1, and let H = K^(k)(X₁) ∪ K^(k)(X₂).
- Each part is 3-wise intersecting (3(m−k) < m), so P(H) is 2-colourable, hence Fano-free, and U is PG(2,2)-free.
- τ = 2(m−k+1) − j = n − 2k + 2 for m+k−1 ≤ n ≤ 2m. This exceeds 3k/4 once n > 11k/4 − 2. For even k it reaches
  τ = k at n = 3k−2.
- So "U PG(2,2)-free ⇒ crit ≤ 3k/4+o(k)" is false for general n: a proof must use n < 11k/6 (or (7,2) itself).

## 2. Why rank, degree and invariant methods are blind
**2.1 Slice and partition rank** [proved by hand, standard]. The PG(2,2) pattern is the system
y_u + y_v + y_{u+v} = 0, whose coefficient sums are 3 ≡ 1 (mod 2).
- The constant tuple is not a solution, so there is no diagonal, and the cap-set mechanism
  (Ellenberg–Gijswijt, Tao, Sawin) has nothing to bound.
- PG(2,2)-free sets of density 3/4 exist (Bose–Burton), even among up-sets: {y : y₁ = 1 or y₂ = 1}.
  In family terms, every H with τ ≤ 2 is seven-free, and these reach density 1 − (3/7)² in the k-layer at n = 7k/4.
- So no "size ⇒ PG(2,2)" statement exists below density 3/4, while U has density 2^{−Ω(n)} (toy: 1/2).

**2.2 Degree barrier** [proved by hand unless tagged].
- **Lemma.** If P : F₂^V → F (any field) vanishes off U, then every monomial of its multilinear form has
  degree ≥ k. Proof: P vanishes on B_{k−1} ⊆ Z, and the Möbius coefficient c_S = Σ_{T⊆S} ±P(1_T) is 0 for |S| < k.
- Encode a plane by φ ∈ F₂^{3n}. A system g_u(φ) = 1 + P(φ(u)) = 0 (u ≠ 0) whose solutions are good planes has
  Σ deg g_u ≥ 7k. Chevalley–Warning and Ax–Katz need Σ deg < 3n, i.e. n > 7k/3, which fails throughout
  n < 11k/6. Even where it holds it gives only parity, and GL₃ acts freely on good φ, so their number is ≡ 0
  (mod 168).
- [heuristic] Combinatorial Nullstellensatz: on the Boolean grid the top coefficient of Π_u P(φ(u)) is a signed
  count of good φ (no shortcut). Member variables b_B (covering linear, Fano-freeness degree 7) give SA/SOS, the
  dead SDP route (FAILED_ROUTES 11).

**2.3 GL-invariance barrier** [proved by hand]. Fix β < 4/7 and put p = 2^{(β−1)n}. Let A ⊆ F₂^n∖0 contain each
vector independently with probability p.
- E[#planes in A] ≤ 2^{3n}p⁷ = 2^{(7β−4)n} → 0.
- For c = ⌈βn − 3log₂n⌉, a fixed subspace W of codimension c−1 misses A with probability
  (1−p)^{|W|−1} ≤ exp(−p2^{n−c+1}/2) ≤ exp(−n³/2). There are ≤ 2^{n²} such W.
- So w.h.p. **A is PG(2,2)-free with crit(A) ≥ βn − 3log₂n**, while every PG(2,2)-free up-set has
  crit ≤ 3n/7 + 2 (§2.5).
- So crit, PG(2,2)-freeness and size (even at density 2^{−(3/7)n}) cannot recover 3n/7: a valid argument must use
  coordinates (monotonicity). Geelen–Nelson/Tidor are GL-invariant, so they fail for this reason as well as density.
- [open] Whether density 2^{−o(n)} also allows crit > 3n/7 (random sets do not: planes then abound).

**2.4 MacWilliams / weight enumerators** [proved by hand].
- A 3-dim subcode φ has nonzero weights w_u = Σ_{⟨c,u⟩=1} m_c, where (m_c) are the colour-class sizes. The map
  m ↦ w is invertible (a Hadamard transform). Every m ≥ 0 with Σm ≤ n occurs, and the number of φ is a multinomial.
- U is not a code, so weight-enumerator identities hold no information beyond this class-size LP, which is the
  slope-3/7 union bound (PROGRAMME5_SEVEN §1). Linear structure exists only when H ⊆ a + C, which is Programme 2
  (Theorems D and 9′); Lemma F‴ concerns cosets and does not transfer.

**2.5 Exact ceiling for arbitrary up-sets** [proved by hand; computed (b)].
- Let **M(n) = 4⌊n/7⌋ + (0,0,0,1,2,2,3)[n mod 7]**, the maximum of min_u|R_u| over class sizes with Σm ≤ n.
  Averaging gives the upper bound ⌊4n/7⌋, attained except at n ≡ 2 (mod 7). There, an excess vector x with Σx = 2
  would need every line sum ≤ 1, but a point with x_p ≥ 1 forces Σx ≤ 3 − 2x_p ≤ 1. The closed form matches full
  enumeration for n ≤ 13.
- For an up-set, crit(U) = τ ≥ c ⟺ U ⊇ {wt ≥ n−c+1}. So **the largest critical number of a PG(2,2)-free up-set
  in F₂^n is exactly n − M(n) = ⌊3n/7⌋ + {0,1,2}**, attained by the layer {wt > M(n)}. With generators of any
  size ≥ k this is independent of k: all of (S<)'s k-dependence is k-uniformity (H an (n,k,k+r) covering design).

## 3. Bose–Burton induction is the anchor quotient, and it lands on P1′
**3.1 Up-set version of Bose–Burton** (for a ∈ A, A∩(A+a) mod ⟨a⟩ is triangle-free, so |A| ≤ ¾·2^n)
[proved by hand]. Fix a member A, W = V∖A, and quarters Q_c (c ∈ F₂²) of A. For v ∈ F₂²∖0 put
A_v¹ = ∪_{⟨c,v⟩=1} Q_c and A_v⁰ = A∖A_v¹; the three splits are the perfect matchings of the quarters. The *derived
family* H′_v consists of the minimal Y ⊆ W such that Y∪A_v⁰ and Y∪A_v¹ both contain members.
- (i) **Rainbow pencil ⇒ seven.** Suppose Y_v ∈ H′_v with Y₁∩Y₂∩Y₃ = ∅. Colour Q_c by (c,1), and colour p ∈ W by
  (c′,0) with ⟨c′,v⟩ = 1 for all v with p ∈ Y_v (possible by 1.1). Then R_{(v,0)} ⊇ Y_v∪A_v¹,
  R_{(v,1)} ⊇ Y_v∪A_v⁰ and R_{(0,0,1)} ⊇ A.
- (ii) τ(H′_v) ≥ τ − h_v, where h_v = max|A_v^i|: if X ⊆ W meets every Y, then X∪A_v⁰ or X∪A_v¹ is a transversal
  of H.
- (iii) **Cross-A0.** If F₁, F₂, F₃ have no rainbow pencil, then τ(F₂) + τ(F₃) ≤ |G₁| + 1 for every G₁ ∈ F₁,
  since each G₁∩G₂ must be a transversal of F₃.
- (iv) If {A,G,G′} is a pencil with G∩A ⊆ A_{v₁}¹ and G′∩A ⊆ A_{v₁}⁰, then Y = (G∪G′)∩W has
  **|Y| = (k+w)/2**, where w = wt(A+G+G′).
- **Corollary** (k even, quarters of size k/4). A pencil of weight w ≤ 4τ−3k−4 = 4T−3k gives a Fano-type seven.
  Taking as A the member that meets both others in ≤ k/2 always works, and the construction is explicit, with four
  requests of size < τ. This is exactly P1′ (PROGRAMME4_P1 §2) [computed (d): 70/70 random instances, k ∈ {4,6}].

**3.2 Why it stops there.**
- The recursion τ_t(k) = k/2 + τ_{t−1}(k/2) gives (1−2^{1−t})k: the Bose–Burton density, the value of K^(k)_n at
  its PG(t−1,2) threshold for every t, A0 at t = 2, and 3/4 at t = 3 [proved for the constructions; open as a
  theorem].
- But the derived members have size (k+w)/2, not k/2, and in a seven-free family w ≥ 4T−3k−5 ≈ 4εk. The derived
  toy instance therefore has k′ = k/2 + 2εk + O(1) and τ′ ≥ k/4 + εk = (k′+1)/2 − O(1): **exactly at the A0
  boundary**, with zero excess.
- A0 is tight for general toy families. Beating cross-A0 would need a rainbow-triangle theorem for three derived
  families that uses their common origin in a seven-free H, which is a 7-term input. The induction supplies one
  pencil per step.
- In the random coset unions (PROGRAMME4_INVP §3) every pencil has weight ≥ λr with λ ≈ 0.83–0.90, so no step
  fires for ε ≲ 0.18δ [heuristic].

## 4. Open items
- [open] c(n,k) = max crit of PG(2,2)-free up-sets generated by k-sets. Known: c ≥ max(3k/4+O(1), n−2k+2) for
  n ≤ 3k−2 (§1.4); c ≤ (n−k)/3 + 2⌈k/4⌉ (one anchor), and c ≤ (3n+3k+21)/11 for n ≤ 2k, since these proofs build
  Fano-type sevens. Where c leaves 3k/4+O(1) is (S<) below 11k/6, and unknown above.
- [open] A bounded-level Sherali–Adams lower bound for the member-variable system (§2.2) would make §0 a theorem.
- [open] Is P(H) 3-colourable for every seven-free family in the Fano range? (True for all computed ones.)

## 5. Reproduction (`compute/programme5/alg/`, `py -3.14`, single core)
`alg_checks.py 300` (a–d) → `logs/alg_checks.log`. `pencil_graph.py k n` → `logs/pencil_graph_small.log` (4 6, 5 8,
5 9, 6 10) and `logs/pencil_graph_mid.log` (7 12, 8 13; ~5 s). Uses pysat (CaDiCaL 1.5.3).
