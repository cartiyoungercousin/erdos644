# Erdős Problem #644: where we are, and what we need ideas for

*Self-contained brief for outside reviewers (people or AI agents). We want critique and new ideas, especially for the open core window (§4). Please challenge anything here; tell us if a "dead" route is not actually dead, or if a "verified" claim looks wrong.*

## 1. The problem
Let f(k,7) be the largest transversal number τ(H) over k-uniform families H with **property (7,2)**: every at most seven members of H can be pierced by 2 points. Erdős asks whether **f(k,7) = (3/4 + o(1))k**.
- **Known bounds:** f(k,7) ≤ ⌈7k/8⌉, and f(4m,7) ≥ 3m + 1 for m ≥ 10, a lower bound along a subsequence (Fon-Der-Flaass–Kostochka–Woodall, Discrete Math. 207 (1999)).
- **Unrefereed 2026 claims of 6/7:** we have formalised some of their lemmas in Lean, but have not verified the main claim.
- **Our project:** a full resolution, in either direction. We have neither yet.

## 2. Our framework (verified)
**Request game.** Suppose τ(H) > T. Then every set S of T points misses some edge. A requester names sets S₁, S₂, …; an adversary answers each with an edge avoiding it. If the requester can always collect seven answers with no 2-point cover, then f(k,7) ≤ T. With unboundedly many requests this game is *exactly* the problem. If the requester asks every T-set, then even against a history-dependent adversary the replies along that single play form a T-covering family. So she wins against every adversary iff every T-covering family has a good seven. With a bounded number of requests, only requester wins are conclusive.

**Confinement (verified).** Three answers with empty common intersection confine all covers to their union V, with |V| ≤ 3k. Requester wins transfer back to the full problem.

**Co-edge form.** Work in units of k: t = T/k = 3/4 + ε, N = |V|/k, ω = N − 1 − t.
- The co-edges are K = V \ B, each of mass c = N − 1.
- Seven answers have no 2-cover iff their co-edges cover every pair of V, iff the co-types I_x = {i : x ∈ K_i} are nonempty and pairwise intersecting.
- τ > T iff the co-edge family is **T-covering**: every T-subset of V lies in some co-edge.
- It suffices to prove everything for all sufficiently small ε, since smaller ε gives the stronger statement.

**Case split by N:**

| region | status |
|---|---|
| N ≤ 3t − 1/2 (crowded) | closed (verified, first order) |
| 3t − 1/2 < N ≤ 5t − 2 (bottom strip, width 2ε) | closed for small ε (verified; Frankl–Rödl density argument, §3) |
| **5t − 2 < N < 3 − t (core window, about 1.75k to 2.25k)** | **OPEN** |
| N ≥ 3 − t (petal side) | mostly closed (verified); residues in §5 |

## 3. Verified results (independent adversarial checking, plus Lean where marked)
- **Lean 4 / Mathlib, no sorry:** about 20 lemmas, including the flat 7-tuple lemma, the Fano criterion, the waste adversary, the anchor and petal reductions, and Lemmas 4.1–4.8 of the 6/7 manuscript.
- **Core tools:**
  - the slack count;
  - Theorem T (a triangle of co-edges finished by four requests);
  - Theorem Q = Q′ (quadrangle finish);
  - the reduction **CP ⇐ (Σ)** (§4).
- **Structured families cannot be counterexamples:**
  - **Theorem S:** families depending only on profiles of a bounded partition.
  - **Theorem S⁺:** the same at finite k, for up to 4εk − 12 cells.
  - **Ordered rules:** families given by fixed in-cell orders.
  - **Theorem W:** greedy priority-order adversaries whose choice of order depends on the request only through a window of ≤ T − k/2 points lose in seven requests, with any number of orders.
- **Bottom strip:** two co-edges whose overlap lies in [N − 2t, 3t − 2] give a good seven, and that window is nonempty iff ω ≤ 4ε. A T-covering family has relative density ≥ e^{−O(ε log 1/ε) n}. Frankl–Rödl (Keevash–Long, arXiv 1402.6294, Thm 1) then forces such a pair for ε ≤ ε₀. The ε₀ is ineffective but absolute.
- **Exact small values:** f(6,7) = 5 and f(7,7) = 6, pending a check of covering numbers against the La Jolla tables.
- **Petal side:** Theorems J, J′, J″, K, L, N, AP, DS-b, PS, PS2, PS3 and Lemma FF.

## 4. THE OPEN PROBLEM: core window
**(CP).** For t = 3/4 + ε, with ε small, and 5t − 2 < N < 3 − t: every T-covering family of co-edges (mass c = N − 1) on a ground set of mass N contains seven members covering all pairs of V.

**Sufficient (Σ), verified reduction.** Every such family contains one of:
- **(a) a Q′ quadruple.** Four members with σ ≤ (3t − N)/2, where σ is the mass lying in at most one of the four. Also, for each of the three matchings {12|34}, {13|24}, {14|23}: (mass lying in exactly the pairs of the matching) + σ ≤ t.
- **(b) a pencil triple.** Three members whose union is V and whose triple intersection is ≥ N − 2t.
- **(c) a Theorem-T triangle.** Three members with empty triple intersection and pairwise intersections a, b, d ≤ (t + N − 2)/2 with a + b + d ≥ (3N − 3 − t)/2.

**What a counterexample would have to look like (from the verified theorems):**
- It cannot be a bounded blow-up, cannot follow fixed orders, and cannot choose among orders by a window of ≤ (1/4 + ε)k points.
- So it must be *hash-like*, *non-greedy* or *self-cut*: its choices depend on more than about k/4 points of the request, in a non-threshold way.
- A random T-covering family has e^{ck} good sevens in expectation, with c ≈ 2–3.4. So a counterexample needs extreme negative correlation.

**Routes we have shown do NOT work in the window.** Each is proved by hand unless marked; we would value being told if any of these "proofs of death" is wrong.

| route | why it fails |
|---|---|
| Bounded-request games | depth-2/3 values equal the baseline [float]; fixed-labelling strategies provably lose above 5t − 2 |
| Kernel lemma; exact regularity / symmetrisation | symmetrising destroys "no good seven" |
| Junta method in measure (Dinur–Friedgut, Keller–Lifshitz) | families are too sparse (density e^{−γk}); KL needs k < n/C |
| Spread / sunflower lemmas (ALWZ, FKNP, Kupavskii–Zakharov) | families are at most n/c < 2.3-spread; the KZ decomposition just restates the problem |
| Fractional relaxation + rounding, (p,q)/Alon–Kleitman | τ* = O(k^{1/3}) for (7,2)-families; rounding in the window *is* CP |
| Hypergraph containers + supersaturation | codegree conditions fail above a thin strip; the needed supersaturation already implies CP |
| Flag algebras / SDP | Cauchy–Schwarz constraints are automatic; CP is not a density statement |
| Density / forbidden-pattern only (extending the strip) | the c-sets avoiding one point and containing a fixed set Y are dense (rate ≤ 0.17γ) with no static certificate; no forbidden-pattern rate can beat γ (not yet independently verified) |

**What a working argument must use:** the *full* T-covering property, not just density, and *adaptive* choice by the requester. Every method using only density, only structure, or only fixed strategies fails.

**Currently being tried:**
- the entropy method (in the style of Gilmer's union-closed argument);
- adaptive density / dependent random choice, i.e. passing to links or traces that stay covering;
- covering-design stability (also asking whether anti-Pasch-style constructions suggest counterexamples exist);
- an exact check of one small family (k = 8, T = 6, 15 points, τ ≥ 7) where no good seven has been found yet.

## 5. Petal-side residues (smaller)
- **A pooled two-arena adversary** for 3/4 < t < 7/9 and leak δ ∈ [t/2 − 1/6, 1 − t). In the forced-centre model the adversary provably beats every known finish, including an adaptive last request (exact MIP). With unforced centres it is open. Note that this touches t → 3/4.
- **Two-class families not of arena-with-pool form.** An exact search at k = 12, 16 found none.

## 6. Questions for reviewers
1. Is there a tool that uses a covering condition ("every T-set lies in a member") together with avoidance of a small configuration, in this linear, exponentially sparse regime? Covering-design stability? Anti-Pasch analogues?
2. Does any of the "dead" routes in §4 actually survive with a modification we missed?
3. Is there a reason to believe f(k,7) > (3/4 + c)k after all, i.e. a construction idea for a random-looking T-covering family with no good seven?
4. Is the reformulation (CP ⇐ (Σ)) the right target, or should one go back to the original families?
5. Do you know of the result "f(6,7) = 5, f(7,7) = 6" or of related exact values?

*Repository with notes, code and verification reports: github.com/cartiyoungercousin/erdos644 (see `notes/LEDGER.md`, `notes/CORE.md` §33 and §90–§99, `reports/progress_2026-11-24.pdf`).*
