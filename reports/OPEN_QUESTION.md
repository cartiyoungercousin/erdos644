# Erdős Problem #644: the open question, and what has been tried

This brief is self-contained, for an outside reader or agent. Every claim carries a status:
- **VERIFIED**: a hand proof that passed an independent adversarial check.
- **EXACT**: exact computation.
- **HAND**: a hand proof, not independently checked.
- **HEURISTIC**: an argument or computation that is not a proof.
- **OPEN**: unknown.

The full write-up is the paper draft `reports/PAPER.pdf` (15 pages) in the project repository. Status as of 2026-11-25: **not solved**.

---

## 1. The problem

Let H be a family of k-element sets (*members*) on a ground set V with |V| = n. Write τ(H) for its transversal number. H has **property (7,2)** if every at most 7 members have a transversal of size at most 2. Put

  f(k,7) = max{ τ(H) : H k-uniform with property (7,2) }.

- **Known.** f(k,7) ≤ ⌈7k/8⌉, and f(4m,7) ≥ 3m+1 for m ≥ 10 (Fon-Der-Flaass, Kostochka, Woodall 1999).
- **Erdős's question.** Is f(k,7) = (3/4 + o(1))k?
- **Good seven.** A *good seven* is seven members (repeats allowed) with no 2-point transversal. So a (7,2) family is exactly a family with no good seven.

**Proof or counterexample.** A proof shows that τ ≥ (3/4+ε)k forces a good seven for large k. A counterexample is a sequence of (7,2) families with τ − 3k/4 ≥ εk.

**Working conjecture (exact form, from a reviewer).** f(k,7) = ⌊(3k+5)/4⌋ for k ≥ 9.
- It is consistent with all known values: f(6,7) = 5 and f(7,7) = 6 (EXACT), and f(9,7) = 8 (HAND).
- No (7,2) family with τ − 3k/4 > 5/4 is known.

## 2. Reformulations used throughout

**Covering form.** τ(H) ≥ T+1 iff every (n−T)-subset of V contains a member. Put T = τ − 1 and r = n − k − T. Then *every (k+r)-set contains a member* (H is (k+r)-covering), and r is the **covering radius**. Define:
- s = n − 7k/4 (the size of the ground set above 7k/4);
- e = τ − 3k/4 = s − r + 1 (the **excess**).

The conjecture says e = o(k) for every (7,2) family.

**Fano type.** Let Π be the Fano plane, and let χ: V → Π be a colouring of the points. For each line ℓ put R_ℓ = V ∖ χ^{-1}(ℓ). Seven members B_ℓ with B_ℓ ⊆ R_ℓ form a *Fano-type seven*; it has no 2-point transversal.
- **Classification (VERIFIED, exact computer-assisted LP).** If seven sets of size ≥ k have union smaller than 11k/6, every good seven among them is Fano-type.
- Above 11k/6, other types exist.
- **Fano sufficiency (EXACT data, profile families).** Families whose good sevens are all non-Fano exist with τ above ⌊(3k+5)/4⌋, but in all data only at n ≥ 2k (k ≥ 9).

**Linear form.** Identify sets with vectors of F_2^V. A Fano-type seven means R_u = φ(u) for a linear φ: F_2^3 → F_2^V, with B_u ⊆ R_u for all seven u ≠ 0.
- **Matroid / critical-number form (HAND).** Let U = {y : supp(y) ⊇ some member}. Then τ(H) is the critical number of U (the least codimension of a subspace avoiding U). A Fano-type seven exists iff U contains a copy of PG(2,2).
- So below 11k/6 the question is: does a k-uniform covering up-set U with no PG(2,2) have critical number ≤ (3/4+o(1))k?
- U is exponentially sparse, so the dense theory (Geelen–Nelson, Tidor) does not apply.

**Pencil form.** A *pencil* is three members with empty common intersection. Its *weight* is |x1 Δ x2 Δ x3|. Define the *pencil 3-graph* on H to have the pencils as its edges.
- **(HAND)** A Fano plane in the pencil 3-graph is exactly a Fano-type good seven. So below 11k/6, (7,2) ⟺ the pencil 3-graph is Fano-free.
- For the seven-free complete families this graph is 3-colourable but not 2-colourable, so Fano-Turán stability does not apply.

**Pencil-sum identity (VERIFIED).** For a Fano-type seven, Σ_p wt(Σ_{ℓ∋p} B_ℓ) = Σ_x j_x(4−j_x) ≤ 3(4|∪B_ℓ| − Σ|B_ℓ|), where j_x counts the members of the seven containing x. When the right side is 0, the seven together with ∅ is a 3-dimensional linear subspace.

## 3. What is proved

| Result | Statement | Status |
|---|---|---|
| Lemma P1 | If T < τ and some pencil has weight ≤ 4T − 3k − 6, H has a Fano-type good seven (any n). | VERIFIED |
| Theorem RA ("rich") | τ*_b ≤ 7/3 − η and τ > (k+1)/2 + 49/(3η) ⇒ not (7,2). Here τ*_b is the least total weight y(V) such that every transversal has weight ≥ 1. | VERIFIED |
| Theorem NC (near-complete block) | If every (k+d)-subset of some W (|W| = w ≥ k+d+2) contains a member, and τ > (k+1)/2 + max(0, 2k+2d+3−w), then not (7,2). | VERIFIED |
| Theorem D, Theorem 9′ | Coset/linear-layer families (members = k-sets of a coset of a code) are closed in the Fano range when there are few classes. | VERIFIED |
| Pencil bound | A (k+r)-covering family with 4T ≥ 2k+5r+3 and 3r ≤ 2k−2 has a pencil of weight ≤ ⌊3r/2⌋ + 1 (equivalently a pair with ‖x1Δx2| − (k+r)| ≤ r/2 + 1). The size conditions are needed (SAT counterexample at (12,6,3)). | VERIFIED |
| **Main bound (new)** | Every (7,2) family with n ≤ 2k has τ ≤ (3n+3k+21)/11, i.e. e ≤ (3/11)s + 21/11. | VERIFIED |
| **Frankl–Wilson bound (new)** | For r ≤ c0(ν)k (c0 = 0.0298, 0.0401, 0.0598 at ν = n/k = 7/4, 11/6, 2) there is a pencil of weight ≤ r + o(k), so e ≤ s/5 + o(k) for n ≤ 1.794k. Proof: covering families exceed the modular Frankl–Wilson bound for avoiding intersection k−p. | VERIFIED |
| Extended main bound | The 3/11 bound holds up to n ≤ (8k+11)/3 (two-stage dump). | HAND |
| Reduction | The conjecture ⟺ Statement (S): every k-uniform family with τ ≥ (3/4+ε)k+1 that is not rich and has no large near-complete block has a good seven. | Derived from VERIFIED results |
| Large n | Adding a private point to every member keeps (7,2) and keeps τ. So the problem restricted to n ≥ ν0·k is equivalent to the whole problem, for every ν0. | HAND |
| Relative pencil lemma NC-P | A partly complete block forces a good seven even when the block's own τ is well below 3k/4 (e.g. 0.640k against NC's 0.728k at ε = 0.05, w = 7k/4). | HAND |
| HUB lemma | A non-Fano analogue of P1, giving a good seven of class 195 from a pencil with a weighted distance condition. Valid for every n. | HAND |
| Small values | f(6,7) = 5, f(7,7) = 6; two-cell profile families confirm max τ = ⌊(3k+5)/4⌋ for 9 ≤ k ≤ 20 (certificates). | EXACT |

**Unconditional excess bounds (slope c in e ≤ c·s + O(1)):**
- 1/5 for n ≤ 1.794k;
- 3/11 up to n = 2k (HAND up to about 2.67k);
- 1/3 beyond, and the published e ≤ k/8 + 1 everywhere.

The conjecture is slope 0.

## 4. What was tried and why it failed

Each item says exactly why it dies. Please don't propose these again unless you see how to escape the stated reason.

1. **Pencil-only arguments, a barrier near slope 0.18 (HEURISTIC, exact binomial margins).**
   - *Construction:* random unions of about n³ cosets of a random linear code.
   - *Properties:* covering, thin, no near-complete block, far from every coset, and every triple sum heavy.
   - *Why it is a barrier:* they still have abundant good sevens. So no argument that only forces light pencils (or light triples) can go below about τ ≤ 3k/4 + 0.18 s.
   - *Consequence:* a proof must use seven-freeness as a genuine 7-term condition.
2. **Raising P1's constant 4 (HAND + ILP).** The constant 4 is exact for every "one pencil + covering" argument (local sharpness families checked over 6925 instances). Beating it needs a *blocked-pencil lemma*: if a lightest pencil cannot be completed, a lighter pencil exists. This is OPEN, and heuristically as hard as PEN(η < 1/2).
3. **PEN(η) for η < 1/2 across the whole window.** A single auxiliary set can be dodged by the adversary. Counting-only arguments cannot pass r ≈ 0.108k (a star family is the witness). A sharper forbidden-intersection theorem would be needed.
4. **Light triples / Lemma Q / BAND.** Settled: a light triple (even a pencil) always exists. So the linear "Lemma Q" certificate never produces a counterexample (HAND).
5. **Random Fano colouring + union bound or Janson (HAND).** Gives only slope 3/7. Bounds that see only the seven marginals cannot beat it; the FKW family has all marginals ≥ 1/2 yet no good colouring.
6. **Coarse-threshold structure (CTS) is false (HAND).** Random covering families have sharp, not coarse, thresholds, and none of the structures CTS predicts.
7. **INV-P (structure: heavy pencils ⇒ coset) (HAND).** Vacuous as written, since every family lies in the parity coset. In its usable form it is broken by the random coset unions of item 1.
8. **Inverse theorem with coset structure (7INV) (HAND + EXACT).**
   - *Complexity:* the Fano pattern has Cauchy–Schwarz and true complexity 2. Any quadratic form sums to 0 over its seven forms, so quadratic level sets contain no PG(2,2).
   - *Majorant:* no usable pseudorandom majorant exists for transference. Symmetric ones have relative density 2^{−Θ(k)}; the member-count majorant's linear-forms condition is circular.
   - *Thinness:* the Fano count lives on an exponentially thin set of co-realisable member tuples.
9. **Quadratic obstructions (Theorem QK, HAND).** For any degree-≤2 polynomial q, once 4n − 7k ≥ 128 the full level set {|B| = k, q(B) = a} has a good seven or τ ≤ 26. So quadratic families cannot be counterexamples.
   - *Caveat:* this covers full level sets only. Subfamilies of a level set are arbitrary.
   - *Expected:* degree d gives slack ≤ C_d (OPEN).
10. **Polynomial method / slice rank / Chevalley–Warning / MacWilliams (HAND).**
    - Slice rank: the pattern is not translation-invariant.
    - Chevalley–Warning: polynomials supported on U have degree ≥ k.
    - MacWilliams: U is not a code.
    - Overall: the maximum critical number of a PG(2,2)-free up-set is ⌊3n/7⌋ + O(1), independent of k. So all the content lies in the k-uniform covering structure.
11. **Topological rainbow criterion (HAND).**
    - *What holds:* if the complex of compatible Fano-coloured members is F_7-homologically 5-connected, there is a good seven (via Volovikov's theorem).
    - *Why it fails:* for intersecting families (all families here), two monochromatic vertices dominate the incompatibility graph. So domination bounds give only connectivity 0, and even the triple case (Lemma A0) is not recovered.
12. **Compression to n ≤ 2k.**
    - τ-critical subfamilies fail: a (7,2) family has ≥ 7τ/2 − 6 members.
    - Merging points, random restriction and padding tricks also fail.
    - Equivalent to "the conjecture for n ≤ 2k implies it everywhere". OPEN.
13. **Also dead** (details in `reports/FAILED_ROUTES.pdf`): bounded-depth request games; junta and spread lemmas; fractional relaxation with rounding; hypergraph containers (every container of a counterexample is itself covering); regularity and sparse removal; flag algebras; entropy and dependent random choice; linear (BLR) gluing; counting with density increment (fails at density e^{−γk}).
14. **Counterexample searches.** None found.
    - Two-cell profile families have max τ = ⌊(3k+5)/4⌋ for k ≤ 20.
    - Three cells: none above the table at k = 8, 9, 10.
    - BCH/Reed–Muller/Kerdock cosets fail covering or have low τ.
    - 459 quadratic level sets (k = 8, 10, 12) all have sevens.

## 5. The open questions

**Q1 (the core, below 11k/6).** Fix ε > 0 and let k be large. Let H be k-uniform and (k+r)-covering on n < 11k/6 points with r ≤ s − εk (i.e. τ ≥ (3/4+ε)k + 1). Must H contain a Fano-type good seven? Three equivalent forms:
- a seven-member configuration B_ℓ ⊆ R_ℓ for a Fano colouring;
- a Fano plane in the pencil 3-graph;
- a PG(2,2) in the up-set U.

You may assume:
- H is not rich and has no near-complete block (Theorems RA, NC);
- every pencil has weight ≥ 4T − 3k − 5 (P1);
- e ≤ 3s/11 + O(1).

The open range is 0 < ε ≤ (3/11)(s/k) (and ≤ (1/5)(s/k) for n ≤ 1.794k). What is missing is a **supersaturation argument for the 7-term Fano pattern in an exponentially sparse k-uniform family**, using the covering property, not density.

**Q2 (n ≥ 2k).** The same question where good sevens need not be Fano-type. In the data, the sevens that occur there are "Fano minus a line" types; the HUB lemma is their P1 analogue. Large n is equivalent to the whole problem (§3).

**Q3 (intermediate theorems; each would be new):**
- **PEN\*:** every covering family has a pencil of weight ≤ λ·r + O(1) with λ < 1 (best possible λ ≈ 0.85 by item 1). This gives slope ≈ 0.18.
- **PEN(η):** a pair with ‖x1 Δ x2| − (k+r)| ≤ ηr for some η < 1/2, across the whole window. This gives slope (1+η)/(5+η).
- **Blocked-pencil lemma** (raises the P1 constant).
- **A robust Piece B:** a family containing a heavy coset sub-layer has a good seven.
- **Degree-d closure:** full level sets of degree-d polynomials have sevens once the slack 4n − 7k ≥ C_d.
- **A bound below 7k/8 for n ≥ 2.2k**, where FKW's 7/8 is the only bound. In progress here.

**What a counterexample must look like.** By the results above, a counterexample:
- is thin (not rich) and has no near-complete block;
- has every pencil heavier than about 4εk;
- is far from every coset layer;
- is not a full level set of a quadratic;
- has covering radius at least about (8/3)εk;
- lies at n where e ≤ 3s/11, so s ≥ (11/3)εk;
- must defeat the 7-term condition itself, not just pencils.

The random coset unions of item 1 meet every one of these conditions except the last.

## 6. What we are asking for

Any of the following, with your own status tags:
- **(a)** A mechanism for Q1: a known theorem or technique that forces a 7-term linear pattern (PG(2,2) / Fano plane in a 3-graph) in a sparse set using a covering or local-density hypothesis rather than global density.
- **(b)** A proof of any Q3 item.
- **(c)** A construction defeating the 7-term condition: a covering family with τ − 3k/4 growing, or even exceeding 5/4 at some k, and no good seven.
- **(d)** A reason why Q1 is false or out of reach of known methods.

Please distinguish proofs from heuristics, and check any construction exactly: τ by ILP, seven-freeness by an independent exhaustive or SAT check.
