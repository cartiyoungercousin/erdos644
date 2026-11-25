# TASK 2: proof side of Statement (G) in the minimal frame (uniform variant first)

Code: `compute/task2/`. Logs: `compute/task2/logs/`. Tags: [proved by hand], [computed exact] (explicit objects re-checked
by plain code), [solver-only] (one UNSAT answer from CaDiCaL), [heuristic]. Nothing is in Lean. No commits.

**Verdict: NEGATIVE.** The uniform variant changes nothing in the near-pool test. Questions (a)–(c) give only
restatements of known facts (CORE 2.1, the CP statement) or fail at finite k on explicit saturated families.
Per the coordinator's 60-minute rule, the work stops here.

## U. Uniform variant: Corollary 5U and what Lemma 4U (ii) adds

**U.0 [proved by hand].** The swap argument in MINIMAL_FRAME "Uniform variant" is correct as written. τ does not
drop, the measure drops when deg z ≥ 2, and B' cannot coincide with another member because z' is fresh. Lemma 3U
holds.

**U.1 Lemma 4U (ii) is implied by (i) [proved by hand].**
- Suppose a point u covers all of B₂..B_m.
- Pick any v ∈ B∖{z}; this is possible because |B| = k ≥ 2.
- Then {u, v} is a 2-cover of B∖{z}, B₂..B_m, which contradicts (i).
- In co-edge form: if some u lies in no K_i, then I_u = ∅ and U(K₂..K_m) = V, which contradicts U ⊆ K ∪ {z}.

So condition (ii) adds nothing. Lemma 4U is exactly Lemma 4 (i)+(ii) of the old frame, restricted to incidences
with deg z ≥ 2. What the variant does give is uniformity, so the uniform tools apply again.

**U.2 Corollary 5U [proved by hand].** Let H be a uniform-minimal counterexample, K = V∖B a co-edge, z ∈ B with
deg z ≥ 2, and F_z = {B₂..B_m} the members given by Lemma 4U. Put U_z = U(K₂..K_m).
- U_z is the union of the 2-point transversals of F_z. It has no loops: ∩_{i≥2} B_i = ∅.
- U_z ∩ B = {z}.
- U_z is a transversal of H, so |U_z| ≥ τ = T+1. This gives Cor 5's size bound directly. Also τ(H) = T+1 exactly,
  because S_B ∪ {z} is a transversal.
- z has a partner: there is w ∈ K such that {z, w} is a 2-cover of B, B₂..B_m. Every member of F_z that misses z
  contains w.
- For n < 2k, m ≥ 4, since three members are needed for an empty intersection.

**U.3 Near-pool test at (10,8,21) with condition (ii)** (`uz_driver_u.py`, `uz_profile_u.py`;
log `logs/uz_uniform_10_8_21.log`).
- **31/32 classes still have U_z** [computed exact; every witness re-checked, including ∪K_i = V].
- The single UNSAT is the same class as before: P = {(8,3), (11,0)}, K of profile (11,0), z ∈ Y [solver-only].
- Power control (`LOOPCTRL=1`, demanding the opposite of (ii)): UNSAT in all 32 classes
  (`logs/uz_uniform_loopctrl.log`). This matches U.1: Cor 5 already excludes loops.
- So the uniform frame does not bite on near-pool families any more than the original frame did. These models are
  uniform, so Task 1's private-set result (SATURATION §3.2) carries over unchanged. That result also kills FKW, so
  it is a symmetry effect, not a near-pool effect.

## A. Saturated, locally minimal uniform families with t > 3/4 (the finite-k kill)

Let k ≡ 1 (mod 4), N = ⌈7k/4⌉, T = N − k (so 4T = 3k+1), and C(N,k) = all k-subsets of [N].
- C(N,k) is (7,2): this is cited from FRESH_C 14.1 (exact ILP), not re-run here.
- τ = T+1.
- Every member B has the private T-set K_B, so Lemma 3U holds.
- **Every incidence is saturated** [computed exact, `complete.py`; Sym(N) is transitive on incidences; explicit
  certificates in `logs/complete.log`]. This holds for k = 5, 9, 13, that is, t = 0.800, 0.778, 0.769.
- So these families satisfy Lemma 3U, Lemma 4U and Corollary 5U, which are all the frame uses. They are not known to
  be measure-minimal.

What happens to each question in these families:
- (a) U_z ⊆ K ∪ {z} and |U_z| ≥ T+1 = |K|+1 force U_z = K ∪ {z} for every witness. So the common part is all of
  K = S_K, of mass T. But ω = N − k − T = 0.
  - Theorem P cannot be applied: its finite-k form P′ fails exactly at 4T = 3k+1 (FINITE_K §1, Prop 1.1). These
    families are P's counterexample case.
- (b) and (c) are satisfied trivially: every degree is C(N−1, k−1), and the budget is as in B.1.

This defeats (a)–(c) at finite k (an O(1) integrality effect, εk = 1/4). It does not refute an asymptotic argument
that uses εk → ∞.

## B. The three questions

**(a) Common part of the U_z and S_K.**
- [proved by hand] For distinct z, z′ ∈ B, U_z ∩ U_z′ ⊆ K. Each U_z ∖ {z} meets every member not containing z.
  Nothing forces a common part of mass about ω.
- Even a common part Y would not make H a pool adversary. Theorem P in family form needs the *pool rule* on the
  co-edges covering each T-set, and the U_z put no constraint on those co-edges. Turning a common core into the pool
  rule is the CP statement itself (restatement).
- [computed exact, 5 tiny non-uniform locally minimal families, k = 4, T = 2, n = 7, 40 co-edges]
  (`small_frame.py`, `logs/small_4_2_8_s1.log`):
  - The forced core ∩_{z,F} U_{z,F} always contains a minimal private set S_K.
  - min over choice functions of |∩_z (U_z ∖ z)| is 2..3 = T..T+1.
  - The complete families above show the same pattern (core = K = S_K).
  - [heuristic] This is suggestive but tiny. I did not prove "S_K ⊆ U_z" and did not test it at larger n. It is the
    one lead worth a check, but it carries no ω-sized pool information.
- The greedy deletion of H1 at (12,9,22) (`h2_delete.py`) gives a deletion-minimal subfamily with 100 541 members.
  - Its saturation was not checked: there are 1.2·10⁶ incidences, each a large SAT instance.
  - Not used.

**(b) Summed slack [proved by hand].**
- Uniform frame: n ≥ k + T. Each enlarged seven {K ∪ {z}, K₂..K₇} has Σ|K′_i| − 3n = 4n − 7k + 1 ≥ 4T − 3k + 1 > 0.
- For n < 2k every co-type has |I_x| ≥ 3, so the waste is exactly 4δ + 1 (δ = n − 7k/4).
- Summing over all (K, z) gives ‖H‖(4δ + 1): an identity (CORE 2.1 plus one point), not an inequality that can fail.
- The essentiality of z only says that z's co-type meets its partner's co-type only in the first set. That does not
  change the count.
- The non-uniform form (old frame): co-types of size 2 occur only for disjoint members, and the waste is at least
  −#(co-type-2 points). This is again consistent (budgets −3..2 seen in the tiny families).
- To get a contradiction one needs a *lower* bound on waste, which is the adversarial-dumping heuristic (CORE §6).
  Saturation supplies *covering* sevens, that is, the budget being met. So (b) cannot contradict.

**(c) Low-degree points.**
- [proved by hand] Fix y ∈ B with deg y ≥ 2 and its witness F.
  - The members of F missing y share a point w ∉ B.
  - For every x ∈ B ∖ {y}, some member of F that contains y misses both x and w.
  - Hence y lies in some member of F; this holds automatically when deg y ≥ 2.
  - Old frame: points of degree 1 occur only in singleton members.
- In the uniform frame, degree-1 incidences carry no condition. Minimising Σ C(deg, 2) *favours* low degrees.
- [heuristic] So Lemma 4U gives no injection from low-degree points into anything bounded, and no bound on N beyond
  Bollobás (|H| ≤ C(k+T, k)).
- Bounding N by O(k) needs the petal/far-reply side, which is not touched here.

## Files
- `compute/task2/uz_profile_u.py`, `uz_driver_u.py`: U.3 (with the `LOOPCTRL` power control).
- `compute/task2/complete.py`: §A saturation certificates.
- `compute/task2/small_frame.py`: exhaustive Lemma-4 witness analysis on small families.
- `compute/task2/h2_delete.py`: deletion step from H1. Its output is not kept; it regenerates in 15 s.
