# FABLE_C: reformulation of the core-window target (Erdős #644)

Scope: find a better target than (Σ), or an equivalent statement, that is easier to force from T-covering and
adaptivity. Units as in CORE §33: k = 1, t = 3/4 + ε, c = N − 1, ω = N − 1 − t, δ = N − 7/4.
Tags: [proved by hand] / [computed exact] / [computed float] / [literature, checked] / [heuristic].
Files: this note and `compute/fableC/` only. Data are read (never written) from `compute/core12/`.
No SAT searches at window instances are run here; forced sevens are consumed from
`compute/core12/forced_sevens.jsonl` (exact-search agent).

## 1. Plan

**Starting observations (from the reading; all to be re-derived in §2 before use).**
- `compute/core12/logs/seven_shapes_all.log` [computed exact, other agent]: of 3002 forced good sevens in window
  profile families, 926 contain no (Σ)-shape among their own members; their deficits are 1/2 to 1 point, and most
  have non-Fano triple co-types. This is seven-level, not family-level. So (a) is live.
- For members K_1..K_j put U_j = {x : I_x is empty or disjoint from some I_y} (the points lying in an uncovered
  pair). In edge form U_j is the union of the 2-covers of B_1..B_j. Then [heuristic until written out]:
  - K_1..K_6 extend to a good seven iff U_6 lies in a member; with T-covering, |U_6| <= t suffices;
  - H has (7,2) iff for every six edges U_6 is a transversal of H. So τ <= min over sixes of |U_6|;
  - more generally Σ_q := "q members whose uncovered-pair graph is a union of 7 − q cliques of mass <= t" gives a
    chain (Σ) ⊂ Σ_3 ∪ Σ_4 ⇒ Σ_5 ⇒ Σ_6 ⇒ CP, with budgets S_q of Theorem 102.1. Σ_6 is the weakest static target,
    with budget 3δ + ε, which does not vanish with ε. Its Fano form is a blown-up Pasch quadrilateral.
- On the exact pool family every class, static or adaptive, has slack exactly 4ε (waste identity 2.1 and
  |∩K_i| >= ω). So an adaptive class can beat the static budget only on *near*-pool families, and the gain must be
  measured against the mass of Y that members miss.

**Order of work.**

1. **(a) first: the Σ_q / U classification (data gate, cheap).** Consume `forced_sevens.jsonl`.
   - For every forced seven compute the essential parts E_i = {x ∈ K_i : some pair through x is covered only by
     K_i}, q_min = #{i : |E_i| > T}, and the least q for which it is Σ_q-static, with margins.
   - Family level: take the other agent's `sigma_profile` verdicts ((Σ)-shape present or not in each logged
     family); for shape-free families only, a small cell-level MILP (not a SAT search) for the least q and the
     Σ_6 margin T − min|U_6|.
   - Deliverable: (Σ⁺) = list of minimal finishing configurations by (q, clique-cover type of the uncovered
     graph), and a verdict on "CP ⇔ Σ_6 on forced data".
   - Why first: it decides whether (Σ) is too narrow before any theory is built on it, and it costs minutes.
2. **(b) second: adaptive certificates, mine alone.** Define the class A_q: q members in full plus a request tree
   of depth 7 − q whose replies range over members of 𝒞 only (family-consistent), all leaves good.
   - Prove the reduction "a reply helps exactly through D ∩ U" (monotonicity 1.1), so A_6 = Σ_6 and A_q is
     governed by how dumps meet U.
   - Exact budgets on pool and near-pool profile families at (13,10,25) and (10,8,21): LP/MILP over cell
     profiles, with members missing mass η of Y. Question: does A_q gain Θ(η) while S_3 stays 4ε?
   - This is the stability problem of §33(4), stated as a budget inequality instead of a structure theorem.
3. **(c) third: the dual statement.** Write out the six-edge transversal form and the star form (N stars in the
   universe 𝒞, any T with a common point, want 7 points piercing all pairwise intersections). Check honestly
   which machinery applies; the (p,q)/LP reading is the dead pair-cover LP (§115–119) and will be marked so.

**How this avoids the failed routes.**
- Not a bounded-request game against an arbitrary adversary (route 1): replies are family members, exploration is
  unbounded, and only the certificate has seven members.
- Not density-only (routes 5, 6, 10, 12): Theorem 96.1's family has U_6 = V, so Σ_6 cannot follow from density;
  T-covering is used for the seventh member in full, for an arbitrary set U.
- Respects Theorem 102.1 instead of fighting it (route 13): the target moves to q = 6 (largest static budget) and
  to adaptive leaves (q = 7), and the pool is treated by a budget-versus-η statement.
- Not the pair-cover LP (route 9) and not symmetrisation (route 3): everything is integral and on the family.

**Kill criteria.**
- If every shape-free forced seven lives in a family that does contain a (Σ)-shape with margin, (Σ) stands and
  step 1 stops there.
- If the Σ_6 margin on near-pool families is O(ε) for every η, Σ_6 is no better than the pencil; go to (b) only.
- If A_q gains nothing over S_q on near-pool families [computed exact], report that as a negative theorem.

**Risk stated in advance.** Σ_6 may be CP restated. It earns its place only if the data show an ε-independent
margin away from the pool, or if (b) turns it into a provable budget inequality.

---------------------------------------------------------------------------------------------

## 2. The six-member form Σ_6: statement and proof of Σ_6 ⇒ CP [proved by hand]

Everything in this section is finite and exact (no first-order limit). V is a finite set, |V| = n, 1 <= T <= c < n,
and 𝒞 is a family of c-subsets of V that is T-covering (every T-subset of V lies in a member).

**Definition 2.1.** Let A_1, …, A_m ⊆ V be any sets and I_x = {i : x ∈ A_i}. A pair {x, y} ⊆ V (x = y allowed) is
*covered* if I_x ∩ I_y ≠ ∅. Put
  U(A_1, …, A_m) := {x ∈ V : some pair {x, y}, y ∈ V, is not covered}.
The sets cover all pairs iff U = ∅ (this is "good" in the sense of CORE 1.1 when m = 7). If some x lies in no
A_i, then U = V.

**Lemma 2.2 (monotone).** If A_i ⊆ A_i′ for all i, then U(A_1′, …, A_m′) ⊆ U(A_1, …, A_m).
*Proof.* A pair covered by the A_i is covered by the A_i′. ∎

**Lemma 2.3 (last set).** For A_1, …, A_m, A ⊆ V: the sets A_1, …, A_m, A cover all pairs iff U(A_1, …, A_m) ⊆ A.
*Proof.* (⇐) If {x, y} is not covered by A_1..A_m, then x and y both lie in U (the definition is symmetric in x, y),
so x, y ∈ A and A covers the pair. (⇒) If x ∈ U, some {x, y} is not covered by A_1..A_m, so A covers it, so x ∈ A. ∎

**Theorem 2.4 (Σ_6 ⇒ good seven).** Let 𝒞 be T-covering. If K_1, …, K_6 ∈ 𝒞 (repetitions allowed) satisfy
|U(K_1, …, K_6)| <= T, then there is K_7 ∈ 𝒞 such that K_1, …, K_7 cover all pairs of V.
*Proof.* Since T <= n, extend U to a T-set S. T-covering gives K_7 ∈ 𝒞 with K_7 ⊇ S ⊇ U. Apply Lemma 2.3. ∎

**Statement (Σ_6).** *For t = 3/4 + ε, ε small, and 5t − 2 < N < 3 − t: every T-covering family of co-edges contains
six members with |U(K_1, …, K_6)| <= t.* By Theorem 2.4 and CORE 1.1, **(Σ_6) ⇒ (CP)**.

**Theorem 2.5 (edge form, no confinement, no uniformity).** Let H be any hypergraph with property (7,2) (every at
most seven edges have a cover of size <= 2). For edges B_1, …, B_6 put
  W(B_1, …, B_6) := ⋃ {P : |P| <= 2, P ∩ B_i ≠ ∅ for i = 1..6}.
Then W is a transversal of H. Hence τ(H) <= min over all six edges of |W(B_1, …, B_6)|.
*Proof.* Let B be an edge. By (7,2) some P with |P| <= 2 meets B_1, …, B_6 and B. Then P ⊆ W and P ∩ B ≠ ∅. ∎
- So: *if every k-uniform H with τ(H) > T has six edges with |W| <= T, then f(k,7) <= T.* This is Σ_6 in the
  original language; it needs neither confinement nor the window.
- Link with 2.1: for edges inside V with co-edges K_i = V ∖ B_i, a pair {x, y} ⊆ V covers B_1..B_6 iff no K_i
  contains both, so W ∩ V = U(K_1, …, K_6). (If a single point covers all six edges, W is everything and U = V.)
- The same proof gives τ <= |W(B_1, …, B_{p−1})| under (p, 2). For p = 3 it is the remark that a (3,2)-family has
  no three pairwise disjoint edges.

**Theorem 2.6 (Σ_6 = "some certificate with at least one request").** For a T-covering 𝒞 with c < n the following
are equivalent.
1. 𝒞 has six members with |U(K_1, …, K_6)| <= T.
2. 𝒞 contains the members of a static r-certificate (CORE §96) for some r <= 6: members K_1..K_r ∈ 𝒞 and sets
   L_{r+1}, …, L_7 with |L_j| <= T such that K_1, …, K_r, L_{r+1}, …, L_7 cover all pairs.
3. 𝒞 contains the root of an adaptive certificate valid against arbitrary replies: members K_1..K_r ∈ 𝒞, r <= 6,
   and a rule choosing S_j (|S_j| <= T) from K_1, …, K_{j−1} for j = r+1..7, such that for *all* c-sets
   K_j ⊇ S_j (members of 𝒞 or not) the final seven cover all pairs.

*Proof.* (1 ⇒ 2) r = 6, L_7 = U, by 2.3. (2 ⇒ 3) A static certificate is an adaptive one with a constant rule; it is
valid for all replies by 2.2. (3 ⇒ 1) Play the rule against 𝒞: T-covering gives members K_{r+1}, …, K_6 ∈ 𝒞 with
K_j ⊇ S_j. Now S_7 is fixed and every c-set K ⊇ S_7 finishes, so by 2.3 U(K_1..K_6) ⊆ K for every such K. Because
c < n, the intersection of all c-supersets of S_7 is S_7. So U(K_1..K_6) ⊆ S_7 and |U| <= T. ∎

**Corollary 2.7.**
- (Σ) ⇒ (Σ_6): Q′, the pencil and the Theorem-T triangle are static 4-, 3-, 3-certificates.
- If the requester wins the seven-request game against every adversary (r = 0 in 2.6(3)), then every T-covering
  family satisfies Σ_6.
- Conversely Σ_6 for all T-covering families is equivalent to: in the game with unboundedly many kept replies she
  can always reach six replies with |U| <= T. (Ask every T-set; the replies form a T-covering family.) So

    seven-request game won  ⇒  (Σ) or any other static/adaptive certificate class  ⇒  (Σ_6)  ⇒  (CP),

  and Σ_6 is the weakest statement that any certificate with at least one request can prove. What separates Σ_6
  from CP is exactly one thing: good sevens in which *every* member is needed on more than T points (§3).

**2.8 Essential parts.** For a good seven put E_i := U(K_1, …, K̂_i, …, K_7) ⊆ K_i (by 2.3). x ∈ E_i iff i ∈ I_x and
some present co-type J has I_x ∩ J = {i}. The seven is a Σ_6 witness iff min_i |E_i| <= T. Call member i *light* then.

**2.9 Budget [proved by hand, from Theorem 102.1 with q = 6].** A Σ_6 configuration with all co-types of size >= 3
(automatic for N < 2) satisfies Σ_x (|J_x| − 3) <= 3δ + ε, where J_x is taken over K_1..K_6 and the line U. This is
the largest budget of any certificate class with a request, and it does not vanish with ε.
- Fano form: the six members are the points of a Fano plane other than one point p. The four lines not through p
  form a Pasch configuration; their classes L_1..L_4 carry the finished points, K_{ab} ⊇ L_a ∪ L_b, and
  U is the union of the three classes of the lines through p (co-types = the three perfect matchings of K_4).
  With equal classes λ, μ: 4λ + 3μ = N, 2λ + μ <= c, 3μ <= t, i.e. μ ∈ [2 − N, t/3], an interval of length
  δ + ε/3 [computed by hand; not machine-checked, and moot after 2.10].
- On a pool family P_Y the Y-points lie in all six members and not in the line, so they cost 3ω and the
  remaining budget is 3δ + ε − 3ω = 4ε, the same as the pencil. More generally (waste identity 2.1 of CORE) every
  good seven of P_Y has Σ over V ∖ Y of (|I_x| − 3) = 4δ − 4ω = 4ε. **On an exact pool no certificate class, static
  or adaptive, has more than 4ε of slack.**

**2.10 Status after the referee's review (`notes/verify/dead_routes.md`, "FABLE_C plan review").**
- Theorems 2.4–2.6 stand [checked by the referee]. The chain of §1 must read: Σ_q := "q members whose uncovered
  pairs are *covered by* 7 − q sets of mass <= t".
- **Σ_6 is dropped as a target.** It is CP with one member used only through its request. The budget in 2.9 is an
  upper bound on waste, not a margin: net of a baseline dump of ω per full member beyond the second it is
  5ε − δ for every q, and on the pool the Σ_6 margin is t − 3(1 + t)/7 = 4ε/7 per line. Kill criterion 2 of §1 fires.
- 2.6(3) is about *arbitrary* replies. For replies restricted to a family the last step is
  U(K_1..K_6) ⊆ cl(S_7) := ⋂{K ∈ 𝒞 : K ⊇ S_7} (§5.1), which can have mass > t (Theorem P's forced dumps).
- 2.9 uses Theorem 102.1, whose hypothesis |J_x| >= 3 fails for N > 2, q >= 4. See §3.

---------------------------------------------------------------------------------------------

## 3. Size-2 co-types in the upper window 2 < N < 3 − t: not forced, not steerable [proved by hand; computed exact]

Question (referee, GAP 4): the true static budget is S_q + m_2, m_2 = mass of points with a co-type of size 2. Must
T-covering families with N > 2 have, or can they be steered to, enough m_2 for a static q >= 4 certificate?
**Answer: no, on both counts.** Code: `compute/fableC/m2_stats.py`, log `logs/m2_stats.log`.

**Lemma 3.1 (what a size-2 co-type is) [proved by hand].** In seven sets (members of mass c, lines of mass <= t,
t < 1) that cover all pairs, suppose some point has co-type {i, j}. Then:
1. A_i ∪ A_j = V (every other co-type meets {i, j}). So both are members (c + t < N, 2t < N), their edges
   B_i, B_j are disjoint, |K_i ∩ K_j| = N − 2, and the points of co-type {i, j} lie in K_i ∩ K_j: mass <= N − 2.
2. The size-2 co-types pairwise intersect, so they form a star {1, j}, j ∈ J (a triangle would be three pairwise
   disjoint edges, N >= 3). Every leaf K_j contains B_1 = V ∖ K_1, a set of mass 1 > t. So m_2 <= |J|(N − 2).
3. A seven with a size-2 co-type contains a disjoint pair of edges. This is the keep-mode of TWIN §5 and §11.2:
   by the rectangle lemma (TWIN 5.1) the other five must cover B_1 × B_2 by the rectangles
   (K_j ∩ B_1) × (K_j ∩ B_2), of semi-perimeter c − |K_j ∩ K_1 ∩ K_2| >= 1, with equality when K_j ⊇ K_1 ∩ K_2.
[computed exact: items 1 and 2 hold for all 3083 forced sevens; 143 of them have m_2 > 0, at most 4 leaves.]

**Proposition 3.2 (not forced) [proved by hand; computed exact].** For every N < 3 there are T-covering,
nondegenerate families (three members with empty common intersection) whose edges pairwise intersect. Every seven
of such a family has m_2 = 0, so only the old budget S_q is available.
- *First-order witness.* P_Y⁺ := P_Y ∪ {K_1, K_2, K_3}: the pool family with |Y| = ω, plus three members with
  K_i ∩ Y = Y ∖ Y^i, where Y = Y^1 ⊔ Y^2 ⊔ Y^3, |Y^i| = ω/3. Pool edges are the unit-mass subsets of
  V′ = V ∖ Y, |V′| = 1 + t < 2, so they pairwise intersect. A pool edge meets B_i = V ∖ K_i because
  1 + (1 − ω/3) > 1 + t (ω < 3(1 − t) in the window). The three sets B_i ∩ V′ have total mass 3 − ω >= 1 + t
  with 3 − N > 0 to spare, so they can cover V′, pairwise intersect and have no common point.
- *Exact witnesses* (`logs/m2_stats.log`): among the logged minimal T-covering profile families, nondegenerate
  and with no two disjoint edges: 124 at (10,8,21), 254 at (14,11,29), 23 at (14,11,30), 37 at (15,12,31),
  25 at (15,12,32), 19 at (16,13,34). All of them have good sevens (pencils; `sigma_profile_all.log`).
- *Literal (degenerate) form.* Padding by a common core lifts any family at N′ to N′ + y with the same k, T
  (CORE 112.1, TWIN 11.1). A lift of a family with N′ < 2 has all edges inside a set of mass < 2, so m_2 ≡ 0.
  Hence the literal CP at any N > 2 implies the literal CP at every smaller N: **in the literal form the upper
  window is the hardest part, not an easier one**, and no argument special to N > 2 can close it alone.

**Proposition 3.3 (not steerable) [proved by hand].** A size-2 co-type {i, j} needs K_j ⊇ V ∖ K_i. The request for
K_j has mass <= t < 1 = |V ∖ K_i|, so the dump of K_j must contain a *prescribed* set of mass >= 1 − t = 1/4 − ε.
- The adversary avoids it at no first-order cost: he leaves one point of B_i ∖ S_j out of every reply. With a
  bounded number of kept replies this changes O(1) points per reply. As a family: 3.2.
- Of the dump ω of a leaf, 1 − t is prescribed and only ω − (1 − t) = N − 2 is free. That free part is exactly
  the m_2 the leaf can contribute. So **m_2 is the by-product of a useful dump of mass 1 − t, not a substitute for
  one.** Counting it as extra budget double-counts.
- After a disjoint pair the five remaining sets must cover B_1 × B_2, so Σ_j a_j b_j >= 1 with
  a_j + b_j = (semi-perimeter of set j). Her requests control t of each semi-perimeter and 5t²/4 < 1 (the q = 2
  count of 102.1), so the rectangles need useful dumps as well. With semi-perimeter exactly 1 (replies containing
  K_1 ∩ K_2) a cover exists with nothing to spare in the pattern I found: B_1-types the edges of a 5-cycle,
  B_2-types the five non-consecutive triples, loads 2/5 + 3/5 [by hand; not claimed optimal]. TWIN 5.2 draws the
  same conclusion: against an adversary who confines later replies to the union of the pair, a winning requester
  below 4k/5 must discard one edge of the pair.

**3.4 Verdict.** The corrected invariant "waste + 4|S| <= S_q + m_2" is right as arithmetic, but it opens no
certificate class for the upper window: m_2 > 0 forces a kept disjoint pair, which a family need not contain and
a requester cannot force. FAILED_ROUTES item 13 needs only the wording fix, not a reversal.
**Dead:** static q >= 4 certificates with size-2 co-types as a way to close 2 < N < 3 − t.

---------------------------------------------------------------------------------------------

## 4. (a) The data gate: forced sevens and (Σ)-shapes [computed exact]

Data: `compute/core12/forced_sevens.jsonl` (3083 forced good sevens of profile families at window instances;
exact-search agent). Code: `compute/fableC/classify_sevens.py`, `summarize_sevens.py`; output
`logs/classified_sevens.jsonl` (records 0–600), `logs/classified_sevens_from601.jsonl`, `logs/summarize_sevens.log`.
Note on the export: its integer key `T` is overwritten by the Theorem-T shape list; T is read from `source`.

**Definitions.** For a forced seven: E_i as in 2.8; member i is *light* if |E_i| <= T. r_min := the least r such that
some r of the seven members, used in full, together with 7 − r *free* lines (any sets of size <= T) cover all
pairs. This is the exact test "these r members are a static r-certificate", of which pencil, Theorem T and Q′ are
sufficient special cases. One MILP per r-subset (co-types inside a maximal intersecting family of subsets of [7],
plus the fixing "a present co-type J needs the union of its sets to be V"); every positive answer is rebuilt as
explicit lines and re-checked by plain code; negative answers are solver-certified only. No MILP was undecided.
For records 601+ the r = 3 MILPs were skipped when the export already tags a pencil or a Theorem-T triple.

**4.1 Family level: (Σ) stands on this data.** The other agent's `sigma_profile_all.log` reports a pencil in all
2896 logged candidate families. So no forced window family is (Σ)-free, as Theorem S predicts for profile families.
Kill criterion 1 of §1 fires: the shape-free sevens below are artefacts of which seven the MILP returned.

**4.2 Seven level.**

| (k, T, n) | sevens | r_min = 3 / 4 / 5 / 6 / 7 | no light member | shape-free | of these r_min = 3 / 4 / 5 / 6 / 7 |
|---|---|---|---|---|---|
| (10, 8, 21) | 679 | 615 / 49 / 13 / 2 / 0 | 8 | 191 | 127 / 49 / 13 / 2 / 0 |
| (14, 11, 28) | 589 | 468 / 26 / 48 / 39 / 8 | 27 | 157 | 41 / 21 / 48 / 39 / 8 |
| (14, 11, 29) | 617 | 492 / 54 / 52 / 17 / 2 | 15 | 169 | 51 / 47 / 52 / 17 / 2 |
| (14, 11, 30) | 108 | 62 / 43 / 3 / 0 / 0 | 4 | 59 | 16 / 40 / 3 / 0 / 0 |
| (15, 12, 31) | 106 | 90 / 12 / 2 / 2 / 0 | 2 | 24 | 9 / 11 / 2 / 2 / 0 |
| (15, 12, 32) | 136 | 114 / 16 / 6 / 0 / 0 | 3 | 50 | 29 / 15 / 6 / 0 / 0 |
| (16, 13, 34) | 170 | 154 / 9 / 5 / 1 / 1 | 5 | 57 | 41 / 9 / 5 / 1 / 1 |
| (13, 10, 25–28) (degenerate, 112.1) | 678 | 412 / 125 / 49 / 46 / 46 | 99 | 242 | 0 / 101 / 49 / 46 / 46 |
| all | 3083 | 2407 / 334 / 178 / 107 / 57 | 163 | 949 | 314 / 293 / 178 / 107 / 57 |

Readings.
- **No seven has r_min <= 2** (0 of 3083). This agrees with the q = 2 case of Theorem 102.1 above the strip.
- **(Σ⁺), q = 3.** 314 shape-free sevens contain a static 3-certificate that is neither a tagged pencil nor a
  tagged Theorem-T triple. Their witness triples are far from a pencil (deficit 4 to 8 points) and close to a
  Theorem-T triangle (deficit 1/2 to 3 points, against a budget 4εk of 2 to 4 points): a small kernel, or one
  pair intersection above (T + n − 2k)/2. So the exact class of finishing triples is an O(ε)-thickening of the
  Theorem-T triangle. It is a real enlargement of (Σ)(c) at finite k, with the same O(ε) tolerance.
  Likewise 154 of the 195 sevens tagged Q′-only contain a static 3-certificate.
- **(Σ⁺), q >= 4.** 293 + 178 + 107 shape-free sevens have least static sub-certificates with 4, 5 and 6 members
  in full. A static certificate may need any number of full members from 3 to 6.
- **Good sevens with no static certificate at all exist** (r_min = 7): 57 in total, 11 of them at genuine
  instances ((14,11,28): 8, (14,11,29): 2, (16,13,34): 1). In the (16,13,34) example every member is essential
  on all of its 18 points (co-types: 4 points of size 2, 16 of size 3, 14 of size 5). Such a seven is not a
  Σ_6 witness and cannot be the output of any certificate with a request (2.6). So, seven by seven, CP is
  strictly more than "some certificate exists". Family by family this data shows no gap (4.1).
- 163 sevens have no light member; 106 of them still contain a static certificate on at most five members.
  So "light member" (Σ_6 witness) and "contains a static certificate" differ: the lines of a certificate need
  not be subsets of the seven's own members.

**4.3 Answer to (a).** Yes at the level of sevens (949 of 3083 are (Σ)-shape-free, and 57 contain no static
certificate of any order). No at the level of families (0 of 2896). The minimal finishing configurations met are:
thickened Theorem-T triangles and pencils (q = 3), and static certificates on 4, 5 or 6 full members that are
not Q′. Since every one of these families has a pencil, the data give no reason to replace (Σ) by a wider target,
and the referee's point stands that seven-level data cannot decide a family-level statement.

---------------------------------------------------------------------------------------------

## 5. (b) Adaptive certificates [proved by hand unless tagged]

A *reply space* is a set ℳ of c-sets; the adversary may
use any T-covering 𝒞 ⊆ ℳ. ℳ = all c-sets is the arbitrary adversary. P_Y = {K ⊇ Y} is the pool. The η-near-pool
space is ℳ_{Y,η} := {K : |Y ∖ K| <= η}, with |Y| = ω unless said otherwise. cl_ℳ(S) := ⋂{K ∈ ℳ : K ⊇ S}.

**5.1 The tree, and its last step.** Put 𝒲_7 := good sevens in ℳ⁷ and, for j < 7,
  𝒲_j := {(K_1..K_j) : there is S, |S| <= t, with (K_1..K_j, K) ∈ 𝒲_{j+1} for every K ∈ ℳ, K ⊇ S}.
An adaptive certificate with r free members and 7 − r requests is exactly an element of 𝒲_r. By Lemma 2.3,
  (K_1..K_6) ∈ 𝒲_6  ⟺  U(K_1..K_6) ⊆ cl_ℳ(S) for some S with |S| <= t.
- ℳ = all c-sets: cl(S) = S, so 𝒲_6 = {|U_6| <= t} (Theorem 2.6). Every certificate against arbitrary replies has a
  static last step.
- ℳ = P_Y: cl(S) = S ∪ Y. Theorem P's forced dumps are closures of the same kind (requests that fill the pool up
  to ω).
- ℳ = ℳ_{Y,η}, η > 0: cl(S) = S again. No single point is guaranteed. What is guaranteed is a *count*
  (all but η of Y), and only an adaptive rule can use a count: it must look at which points were missed. This is
  the precise sense in which near-pool families need adaptivity.

**Lemma 5.2 (certain waste; exhaustion).** Let F := V ∖ U(K_1..K_j) be the finished points. For any S and any
D ⊆ F: U(K_1..K_j, S ∪ D) = U(K_1..K_j, S).
*Proof.* Every pair through a point of D is already covered by K_1..K_j. ∎
- So against arbitrary replies, step j + 1 with request S is no better than static whenever |F ∖ S| >= c − |S|,
  i.e. |F ∪ S| >= c.
- Conversely, if |F ∪ S| < c, every reply puts at least c − |F ∪ S| of its dump on unfinished points. With a full
  request inside U that is ω − |F|. Blocking finished points by requesting them trades request mass for dump mass
  one for one [heuristic: so it gains nothing].
- Limit of the lemma: a dump on unfinished points need not help the final seven. "Wasted" has an intrinsic meaning
  only for dumps in F. In the pool, Y ⊆ F from the first cover of V on, and |Y| = ω: every step is static, which
  is the 4ε of 2.9.

**5.3 Exact pool: no class beats 4ε.** (2.9.) Every good seven of P_Y has Σ over V ∖ Y of (|I_x| − 3) = 4ε.

**Proposition 5.4 (near-pool, collinear repair).** Let |Y| = y and let every reply contain all but at most η of Y.
If 3(N − y) + 7η <= 7t — for y = ω this is **η <= 4ε/7** — the requester obtains a good seven in seven requests.
*Proof.* Label members by the points 1..7 of a Fano plane with lines 123, 145, 167, 246, 257, 347, 356. Let
r_i := number of lines whose largest point is i, so (r_1..r_7) = (0, 0, 1, 0, 1, 2, 3) and Σ r_i = 7.
1. Put ℓ_i := t − θ − r_i η with θ >= 0 chosen so that Σ ℓ_i = 3(N − y) (possible by hypothesis). Split
   V′ = V ∖ Y into classes V_λ, one per line λ, with |V_λ| = ½ Σ_{i ∈ λ} ℓ_i − ⅙ Σ_i ℓ_i (the inverse of the
   incidence system, since MᵀM = 2I + J). The smallest class is that of line 167, of mass (N − y)/7 − η, so the
   classes are non-negative as soon as η <= (N − y)/7, which holds here. Then L_i := ⋃_{λ ∋ i} V_λ has mass ℓ_i.
2. In the order i = 1..7 request S_i := L_i ∪ R_i, where R_i := ⋃ over lines {a, b, i} with a, b < i of
   (M_a ∩ M_b) and M_a := Y ∖ K_a. Since |M_a| <= η, |R_i| <= r_i η and |S_i| <= t.
3. A point of V_λ has co-type ⊇ λ. For y ∈ Y let Z_y := {i : y ∉ K_i}. If Z_y contained a line {a, b, i},
   a < b < i, then y ∈ M_a ∩ M_b ⊆ R_i ⊆ K_i, a contradiction. A set containing no line is not a blocking set of
   the Fano plane, so some line λ′ misses Z_y, i.e. I_y ⊇ λ′.
4. Every co-type contains a line, and two lines meet. ∎
- The certificate is adaptive only through the repair sets R_i. [Plain-code check, `nearpool_sim.py`, log
  `logs/nearpool_sim.log`: k = 140, T = 110, n = 280, |Y| = 30, η = 2 <= 20/7; 6000 games against four adversary
  heuristics, all good sevens. At η = 3 the count 7T − 7η = 749 < 750 = 3(n − |Y|) and no plan exists.]
- The pencil route has the same threshold: requests κ ∪ Q_i with repair give kernel >= |κ| + ω − 3η and
  Σ|S_i| = 1 + t + 2|κ| + η <= 3t, so 1 − t + 3η <= |κ| <= t − ½ − η/2, i.e. η <= 4ε/7 [by hand, first order].

**Remark 5.5 (fixed plans tolerate no misses) [count of guaranteed incidences only; not a full proof].** Against
ℳ_{Y,η} let the adversary miss, in every reply, the same set M of the η least-requested points of Y. A point of M
is then guaranteed only in the members whose requests contain it. A non-adaptive plan S_1..S_7 that is to be safe
on guaranteed incidences alone must request all but η of Y on three collinear members. That costs 3(ω − η) of
request mass against a total slack of 4ε, so it needs η >= ω − 4ε/3. (Not proved: that the adversary can always
place his free dump, of mass η per reply, without effect.)

**Proposition 5.6 (near-pool is self-similar).** For M ⊆ Y with |M| = η, ℳ_{Y,η} contains every family
{(Y ∖ M) ∪ K″ : K″ ∈ 𝒞″}, 𝒞″ any T-covering family on V″ = V ∖ (Y ∖ M) with co-edge mass t + η. So

    the requester beats ℳ_{Y,η}  ⟹  literal CP at (N″, t) = (1 + t + η, t), i.e. at ω″ = η, δ″ = ε + η.

- η <= 2ε: N″ <= 3t − ½, the crowded region (closed, VERIFIED at first order).
- η <= 4ε: the bottom strip (closed for small ε).
- η > 4ε: the open window with ω replaced by η.
- Plans that rely on guaranteed incidences only stop earlier: against the common miss M they need
  7t >= 3(1 + t + η), i.e. η <= 4ε/3 [count, as in 5.5].

**5.7 Answers to (b).**
1. *Minimal adaptive certificates.* Against arbitrary replies they are the elements of 𝒲_r, and each ends in a
   static last step |U_6| <= t (5.1). An adaptive step differs from a static one only while the finished mass
   outside the request is below the dump size (5.2).
2. *Does an adaptive class beat the static budget on near-pool families?*
   - On the exact pool: no. Every class has 4ε (5.3).
   - On η-near-pools: adaptivity is what works at the ε scale. Adaptive repair tolerates η <= 4ε/7 (5.4,
     proved). By the count of 5.5 fixed plans tolerate η = 0 only, and no plan relying on guaranteed incidences
     tolerates η > 4ε/3 (5.6) [counts, not full proofs].
   - Beyond the ε scale there is no "near-pool case": it is CP at ω = η (5.6). So the stability statement of
     §33(4) is useful only in the form *"no good seven ⟹ every member contains all but O(ε) of some Y"*, with the
     constant at most 4/7 for the explicit certificate (2 or 4 if the crowded-region or strip theorems are
     applied inside V″; I have not checked that those apply to varying misses).
3. Nothing here forces a useful dump outside the pool mechanism. The referee's net count 5ε − δ stands.

## 6. (c) Dual statements

**6.1 Edge form [proved by hand, Theorem 2.5].** H has (7,2) iff for every six edges the union W of their covers of
size <= 2 is a transversal. So a counterexample satisfies |W(B_1..B_6)| > T for *every* six edges: a statement
about six members and a set size, with no seventh quantifier. It is equivalent to "no good seven with a light
member" and weaker than "no good seven". I found no machinery that uses it beyond the request game.

**6.2 Star form [proved by hand; reduction to a dead route].** Put 𝒮_x := {K ∈ 𝒞 : x ∈ K}. Every K lies in exactly
c stars; T-covering says any T stars have a common element; a good seven is a 7-point transversal of the family
{𝒮_x ∩ 𝒮_y}. That family is ⌊T/2⌋-wise intersecting. Its fractional transversal number is the pair-cover value ρ*
of §115–§119, which is <= (N/t)² < 7 on every T-covering family while ρ can be 8 one point outside T-covering
(118.1). So a (p,q) or Helly-type theorem here would have to round ρ* to 7 exactly: it is CP (route 9).

**6.3 Co-type system.** For a single seven the co-types I_x form an intersecting family on [7]; the only general
identity is the waste count Σ(|I_x| − 3) = 4δ (+ m_2 corrections, §3). I have no dual with new content.

**Verdict on (c).** No dual statement was found to which known machinery applies.

---------------------------------------------------------------------------------------------

## 7. Status, dead routes, what remains; self-check

**Status.**
- (a) Answered (§4): shape-free good sevens exist, shape-free families do not, on the profile data.
- New lead (size-2 co-types, N > 2): dead (§3). Literal CP is monotone in N, so the upper window is the hardest
  part of the literal statement.
- (b) §5: last-step theorem with closures; certain-waste lemma; exact pool at 4ε for every class; near-pool repair
  certificate for misses <= 4ε/7 (proved, simulated); near-pool beyond the ε scale is CP at ω = η.
- (c) §6: no dual with usable machinery.
- Σ_6 (§2): correct, dropped as a target after review.

**Dead (for LEDGER).**
- Σ_6 as a target (CP with one inessential dump; net budget 5ε − δ).
- Static q >= 4 certificates through size-2 co-types in 2 < N < 3 − t.
- "Near-pool" as a separate case beyond misses of order ε.
- Star / (p,q) dual: it is the pair-cover LP.

**What remains.** The same open statement: force one useful dump outside the pool mechanism. The only new
positive tool here is collinear repair (5.4), which makes the pool finish robust to misses of 4ε/7.

**Self-check.**
- Lemmas 2.2, 2.3, 5.2 and Theorem 2.5 (in the (3,2) form) brute-forced on random small systems
  (`lemma_checks.py`, `logs/lemma_checks.log`): 20000 + 20000 + 20000 + 23474 cases, no failure.
- Lemma 3.1 items 1–2 asserted on all 3083 forced sevens (`m2_stats.py`).
- Proposition 5.4: 6000 exact games at (140, 110, 280) (`nearpool_sim.py`); adversaries are heuristic.
- Classification: r_min never exceeds 3 when a pencil or T-triple is tagged, never exceeds 4 when Q′ is tagged
  (0 violations); negative MILP answers are not independently certified.
- Not verified by anyone else: §3, §5. Remark 5.5 and the 4ε/3 bound of 5.6 are counts, not proofs.
- Not done: the first-order region of all static 3-certificates; the family-level Σ_6 margins
  (`family_u6.py` is written but was not run to completion); any exact game for near-pool misses above 4ε/7.
