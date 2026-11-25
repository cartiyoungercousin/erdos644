# SATURATION: Task 1 of MINIMAL_FRAME (incidence saturation, U_z sets, private sets)

Code: `compute/saturation/`. Logs: `compute/saturation/logs/`. Tags: [proved by hand], [computed exact] (exhaustive
enumeration by our code, or an explicit object re-checked by plain code), [solver-only] (one SAT/MILP refutation, no
checked certificate). MINIMAL_FRAME itself is unverified (Task 0); everything below uses only its definitions.

**Reading (coordinator's correction, adopted).**
- Looseness is defined only for genuine families: (7,2) and τ > T.
- At ε = 0 such families exist (FKW). Greedy shrinking of one always ends at a saturated family, so (a) cannot fail. It
  is a **template** for the disproof side, not a test.
- Near-pool and hash-like models are not (7,2)-families above 3k/4, so "saturating" them is undefined.
- (c) is replaced by: do the **consequences** of minimality contradict near-pool structure at (10,8,21)? The
  consequences tested are Corollary 5's sets U_z, the private sets S_K (Lemma 3) and the antichain property.

**Verdict.**
- The U_z consequences do **not** contradict near-pool structure. They hold class by class in every near-pool profile
  family at (10,8,21), with one exception (§3.1).
- The private-set consequence (Lemma 3) **does** exclude every near-pool profile family with η ≥ 1 [proved by hand,
  checked exactly]. It also excludes FKW itself. So it is a symmetry effect, not a near-pool effect (§3.2).
- FKW (m = 3) has exactly one loose class. One orbit-wise greedy step gives a saturated antichain H1 with τ = 10 > 9.
  H1 is not deletion-minimal (§1.4).

## 0. Facts used [proved by hand]
- **Co-edge form.** A set of edges has no transversal of size ≤ 2 iff their co-edges cover every pair {u, v} of V, with
  u = v allowed (FABLE_C 2.1–2.3).
- **Saturation test.** (z, B) is saturated iff K_B ∪ {z} and at most six co-edges cover all pairs.
- **Shrinking only grows co-edges.** So good sevens survive, and a saturation certificate stays valid after other
  members are shrunk, as long as B itself remains.
- **Spectrum model.** A good seven is, up to relabelling points, the same as co-type counts with pairwise-intersecting
  support and the right degrees.
  - |I| = 1 is impossible when every member has size < n.
  - I = {i, j} is impossible when s_i + s_j < n.
  - Hence Σ_v (|I_v| − 3) = Σ s_i − 3n.

## 1. (a) The FKW parity family at m = 3: template

V = X ⊔ Y with |X| = 12 and |Y| = 10. The edges are the 12-sets A with j = |A ∩ X| odd, j ∈ {3, 5, 7, 9, 11}. τ = 10 and
T = 9.

**1.1 Incidence classes [proved by hand].** Sym(X) × Sym(Y) acts transitively on the incidences (z, A) with fixed j and
fixed side of z.
- An incidence class is the same thing as the profile of K′ = K ∪ {z}, an 11-set, with e = |K′ ∩ X|.
- z ∈ X gives e = 13 − j, which is even: e ∈ {2, 4, 6, 8, 10}.
- z ∈ Y gives e = 12 − j, which is odd: e ∈ {1, 3, 5, 7, 9}.
- So there are 10 classes, not 2.

**1.2 Results** (`spectrum_gen.js`, a generalised exhaustive co-type enumerator; controls reproduce CORE 110.3:
m = 3 gives 312 leaves and 0 realizable, m = 2 gives a good seven).

| j = \|A∩X\| | z ∈ X | z ∈ Y |
|---|---|---|
| 11 | saturated (e = 2) | **LOOSE** (e = 1): 3 482 degree-feasible leaves, 0 split-feasible [computed exact] |
| 9 | saturated (e = 4) | saturated (e = 3) |
| 7 | saturated (e = 6) | saturated (e = 5) |
| 5 | saturated (e = 8) | saturated (e = 7) |
| 3 | saturated (e = 10) | saturated (e = 9) |

- Saturation certificates: 3 explicit sevens per class, in `logs/fkw_m3_shrunk_e*.log`.
- `verify_fkw.py` re-checks each certificate independently. B∖{z} together with six FKW edges has no 2-transversal.
  B together with the same six does have one, and every such transversal P satisfies P ∩ B = {z} (Lemma 4(ii))
  [computed exact].
- The loose class: A = (X∖x) ∪ {y}, shrunk to X∖x. Equivalently, K′ = Y ∪ {x} plus six FKW co-edges never cover all
  pairs.

**1.3 The greedy step, done orbit-wise.** The step:
- Shrink all 120 loose edges.
- The edges (X∖x) ∪ {y′} then contain X∖x. Delete them, since a minimal family is an antichain.
- The result is H1 = {edges with j ∈ {3, 5, 7, 9}} ∪ {X∖x : x ∈ X}.

Checks on H1:
- **(7,2) holds** for every number r of shrunk co-edges Y ∪ {x_i} in a seven.
  - r = 0 is FKW itself [exact].
  - r = 1 is the e = 1 run [exact; the run allowed every odd profile, which is a superset].
  - r ≥ 2 by an incidence count [proved by hand]:
    - u ∈ X0 = X∖{x_i} lies in at least 3 regular blocks, since Σ(10 − a) ≥ 10 and Σ(a − 1) ≥ 11 give 9d ≥ 21.
    - Each x_i lies in at least 2 regular blocks.
    - Each y lies in at least 2 regular blocks while |X0| > 9, and in at least 1 otherwise.
    - The total size 10(7 − r) is then too small: for r = 2, 34 + 20 > 50; for r = 3, 33 + 10 > 40; for r = 4,
      32 > 30; for r = 5, 31 > 20; for r = 6, d ≥ 3 > 1 block.
  - Cross-check: a HiGHS MILP for r = 1..6 finds all of them infeasible [solver-only, `logs/fkw_h1_milp.log`].
  - A direct 7-free-member SAT on H1 timed out at 1800 s.
- τ(H1) = 10 [computed exact, by profiles].
- Antichain: yes.
- **Saturated: all 10 classes certified in H1** [computed exact, `logs/h1_saturation.log`].
  - The 9 surviving FKW classes and the new class (z, X∖x), whose co-edge is Y ∪ {x, z}.
  - Each certificate is an explicit seven found by `sat_profile.py` and re-checked by plain code.
  - `sat_profile.py` was first validated against the exact results: e = 1 gives UNSAT and e = 2 gives SAT.

**1.4 Shape of the saturated template H1.** [computed exact, `h1_structure.py`]
- 323 236 members (FKW has 323 344), total size 3 878 820. Edge profiles (j, 12 − j) for j = 3, 5, 7, 9, plus (11, 0).
  Non-uniform: sizes 12 and 11.
- Degrees: each X point has degree 176 385 and each Y point 176 220. These are nearly balanced.
- (Σ)(b) as a literal condition (three co-edges with union V and κ ≥ n − 2T = 4) **appears**, at co-edge profiles
  ((7,3), (7,3), (1,10)). FKW has κ ≤ 3.
  - H1 is nevertheless (7,2).
  - So (Σ)(b) gives no good seven for non-uniform families, which is the MINIMAL_FRAME caution made concrete.
  - Theorem T and Q′ were not evaluated, since their forms are uniform.
- **Not minimal.** Regular members have no private 9-set (Lemma 3 fails), so each one can be deleted alone with τ > 9
  kept. Only the 12 shrunk members have private sets [computed exact, `logs/private_sets_fkw_h1.log`].
  - FKW itself has no private sets either.
  - The true minimal counterexample below H1 is therefore a sparse, asymmetric subfamily. Greedy deletion over 3·10⁵
    members was not attempted.
- What looks extendable to ε > 0:
  - the parity bulk keeps saturation in every class except j = 11 with z ∈ Y;
  - the extreme edges collapse onto the 11-sets X∖x.
  - This rests on m = 3 only.

## 2. (b) The pencil-free two-class selector family at k = 8 (core9 `fam_8_6_15_rev`)

- This is a template at ε = 0. Whether the family is (7,2) is **still undecided** (CORE 55.5), so its looseness is not
  even defined yet.
- An UNSAT here would only mean "loose, if the family is (7,2)".
- `k8_sat.py`: 18 816 incidences fall into 5 147 distinct 8-sets S = K ∪ {z}. CaDiCaL was run per S, with a time limit
  and a plain-code re-check of every SAT answer.
- On a random sample of 240 of the S (seed 1, 120 s each; `logs/k8_sat_sample_s1.log`, certificates in
  `logs/k8_sat_certs_-1.jsonl`):
  - **112/240 S saturated** (381 incidences, certificates checked) [computed exact].
  - 0 UNSAT.
  - 128 undecided (459 incidences).
  - **No loose incidence was found.** The undecided S are hard instances, not refutations.

## 3. (c) Consequences of minimality versus near-pool structure at (10,8,21)

Model: 2-cell profile families on A ⊔ Y, with |A| = 18, |Y| = 3 = ω and co-edges of size 11.
- T-covering forces (8,3) ∈ P [proved by hand]: an 8-set of profile (5,3) lies only in co-edges of profile (a, 3).
- The other profiles (9,2), (10,1), (11,0) are free, and η = 3 − min b.
- That gives 8 families and 32 incidence classes (K, z). Each family is the whole near-pool space of its type.

**3.1 U_z sets (Corollary 5).** `uz_profile.py` encodes the conditions on U = U(K_1..K_6) exactly: z ∈ U, U ⊆ K ∪ {z},
|U| ≥ 9, and U inside no co-edge.
- Controls on FKW: the loose class gives UNSAT, and two saturated classes give SAT.
- Result: **31/32 classes have U_z** [computed exact; witnesses re-checked]. The witnesses have |U| = 9..12, usually
  with U ⊇ Y.
- The single exception is P = {(8,3), (11,0)} with K of profile (11,0) and z ∈ Y: UNSAT [solver-only].
- So Corollary 5 alone does not contradict near-pool structure, even at η = 1. The same holds outside profile
  families: for a single pool incidence, local witnesses exist at η = 1 at both (10,8,21) and (13,10,25)
  [computed exact witnesses, `nearpool_sat_milp.py`, `logs/nearpool_sat.log`].
  - The fewest K_i that miss y is 1 at (10,8,21) and 2 at (13,10,25) [solver-only optimality].
  - η = 0 is impossible by hand, since K ∪ {y} would have to miss −1 pool points.

**3.2 Private sets (Lemma 3)** [proved by hand; computed exact, `private_sets.py`].
- For every P with η ≥ 1, no co-edge of any profile has a private 8-set: every S ⊆ K with |S| ≤ 8 lies in another
  member.
- Only the exact pool {(8,3)} has private sets. It is degenerate: its Y points lie in no edge.
- This kills symmetric near-pool families as minimal counterexamples. FKW fails the same test (§1.4), so the mechanism
  is high symmetry, not the pool.

**3.3 Hash-like models.** There is no T-covering pencil-free hash-like family at (10,8,21) to test: every selector for
the tested orders leaves a pencil (CORE 113.2, solver-only). At k = 8, see §2.

## 4. Status
- **(a) Template.** One loose class, then a saturated (7,2) antichain H1 with τ = 10. H1 is not deletion-minimal.
- **(b)** Partly certified saturated. No looseness found. (7,2) of the family is undecided.
- **(c)** The U_z consequences are compatible with near-pool structure. Private sets exclude symmetric near-pool
  families, but also FKW, so the open class does not shrink from this alone.
- A real test needs asymmetric (non-profile) families with private sets, i.e. the deletion step.
