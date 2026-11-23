# Erdős #644 — research log

## Problem (erdosproblems.com/644)
Let f(k,r) be minimal such that: if A_1, A_2, ... is a family of k-sets such that every r of
them can be hit by some pair {x,y}, then the whole family has a hitting set (transversal)
of size f(k,r).

Questions:
1. Is f(k,7) = (1 + o(1)) (3/4) k?
2. For every r >= 3, is there c_r with f(k,r) = (1 + o(1)) c_r k?

Literature notation: f(k,r) = f(k, r, 2) = max tau(H) over k-uniform H with "property (r,2)":
every r edges of H have a transversal of size <= 2.

## Known
| r | f(k,r)            | source |
|---|-------------------|--------|
| 3 | 2k                | EFKT92 |
| 4 | floor(3k/2)       | EFKT92 |
| 5 | floor(5k/4)       | EFKT92 |
| 6 | k                 | EFKT92 |
| 7 | 3m+1 <= f(4m,7) (m >= 10);  f(k,7) <= ceil(7k/8)  | FKW99 (secondhand, VERIFY) |
| p | general (p,2) bounds | Kostochka 2002, Combinatorica 22 |

So the open gap for r = 7 is roughly 0.75k .. 0.875k.
Answering Q1 means either: an upper bound (3/4 + o(1))k  [proof], or a family with
tau >= (3/4 + eps)k  [counter-construction]. Either one fully settles Q1.

## References
- EFKT92: Erdős, Fon-Der-Flaass, Kostochka, Tuza, Small transversals in uniform hypergraphs,
  Siberian Adv. Math. 2 (1992) 82-88.
- FKW99: Fon-Der-Flaass, Kostochka, Woodall, Transversals in uniform hypergraphs with
  property (7,2), Discrete Math 207 (1999) 277-284. PDF on Kostochka's homepage.
- K02: Kostochka, Transversals in uniform hypergraphs with property (p,2), Combinatorica 22
  (2002) 275-285. PDF on Kostochka's homepage.
- Bucić–Korándi–Sudakov, arXiv:1902.05055 (Section 5, App. A): local-to-global covering.
- Füredi 1981 (fractional matchings; intersecting 3-graphs other than Fano have nu* <= 2).

## Others working on it (as of 2026-11-23)
- the-omega-institute/trureturing issue #9792 (AI-driven, no proof claimed). Notes there:
  * FKW lower-bound family is the weight-k layer of a binary parity code ("parity family on
    7m+1 vertices").
  * For 7 k-sets on n < 9k/5 points with no 2-point transversal: every point has degree <= 4,
    degree-4 points' omitted triples form a Fano plane (via Füredi).
  * Limitations of FKW's Lemma 1 blocker architecture for reaching 3/4.
  Treat all of this as unverified until checked.

## FKW99 — VERIFIED by reading the paper (2026-11-23)
- Definition: B has property (p,t) if tau(F) <= t for every F ⊂ B with |F| = p.
  f(r,p,t) = max tau over r-uniform families with property (p,t). (r = uniformity.)
- Complete hypergraphs: tau(K_n^(r)) = n - r + 1. K_{7k-1}^{(4k)} has (7,2) => f(4k,7) >= 3k.
  K_{7k}^{(4k)} fails (7,2): complements of Fano lines, blown up by k.
- Thm 1 (lower bound): k >= 10, |S| = 7k+1, X ⊂ S, |X| = 4k. B = all 4k-subsets A of S with
  |A ∩ X| odd. Then B has (7,2) and tau(B) = 3k+1. Remark: works for k >= 4; fails for k = 2.
  Proof structure: a bad 7-tuple must have almost all points of degree exactly 4, the
  "standard" points split into 7 classes D_1..D_7 and the A_i are complements of Fano lines on
  the D_j; then a parity argument over X kills it.
- Thm 2 (upper bound): f(r,7) <= ceil(7r/8) (r = 8k+s, k >= 1). Tool: "good triple"
  (A1,A2,A3 with empty common intersection) + Lemma 1 constructing blockers A4..A7 using
  tau(B) > 7k+s to find edges avoiding chosen sets. 4 cases on pairwise intersection sizes.
- Paper notes: if the lower bound held for k = 2 the upper bound would be exact at r = 8.
- For p <= 6 the extremal families are complete hypergraphs; p = 7 is the first where not.

## Still missing
- Kostochka 2002 (property (p,2)) — the homepage link labeled comb02.pdf actually serves a
  different paper (Gyárfás–Sárközy–Szemerédi 2010). Need another source.

## Log
- 2026-11-23: chose #644. Gathered statement + bounds. Read FKW99 in full. Installed elan;
  Mathlib project erdos644/Lean644 building.

## Phase A results (2026-11-23)
Tools: compute/typefam.py (block-type families, signature ILP for bad 7-tuples, exact tau),
compute/validate.py, parity_variants.py, search.py (branch & bound over allowed types),
coarse.py (asymptotic/normalized version).

- Checker reproduces all FKW99 facts: K_{7k-1}^{(4k)} has (7,2), K_{7k}^{(4k)} fails (k=1,2,3);
  parity family fails at k=2 (witness brute-force verified).
- NEW (solver-certified, not yet proof-certified): parity family works at k=3:
  f(12,7) >= 10. Also k=4,5 confirmed (tau = 13, 16).
- r=8: no 2-block family (any allowed-type subset, n <= 15) reaches tau = 7. Best 6.
- r=12: parity variants reaching tau = 10: |X| = 10, 11, 12 on 22 points. None reaches 11
  (= ceil(7*12/8), the FKW upper bound). So 10 <= f(12,7) <= 11.
- Coarse 2-block families (quarter grids): best ROBUST tau/r = 1/2 < 3/4. Evidence that
  beating 3/4 needs more than block structure; parity-type tricks give only +O(1).

## Insight: bad 7-tuples = intersecting families of miss-patterns
miss(x) = {i : x not in A_i}. Two points cover all 7 sets iff their miss-patterns are disjoint.
So A_1..A_7 have no 2-point transversal iff {miss(x)} is an intersecting family on [7]
(and no i lies in every miss-pattern, i.e. all A_i nonempty). WLOG upward closed => maximal
non-star intersecting families on [7] are the "shapes" of bad 7-tuples. Fano lines = the
FKW shape. For a fixed shape, existence of a (coarse) bad tuple is an LP => checkable
Farkas certificates.

## Solve track: new results proved in Lean (2026-11-23)
- `Lean644/TightTriple.lean`: **tight-triple lemma** — a good triple closes with four "Fano line"
  requests when 3k + 2 <= 2T + S. Corollary `goodTriple_S_le`: if tau > T, every good triple has
  S <= 3k - 2T + 1. (Roadmap §3(c); size formula checked on 865k triples.)
- `Lean644/TheoremA.lean`: **Theorem A** — tau(H) <= ceil((n-k)/3) + 2 ceil(k/4) for a k-uniform
  (7,2)-family with all edges inside an n-set V. Tight for K_{7m-1}^{(4m)} and the FKW parity
  family. Also `request_cover_V` (request-cover relative to a ground set).
  Axioms: propext, Classical.choice, Quot.sound only.
Novelty: neither construction appears in FKW99 (its Lemma 1 is an adaptive good-triple
construction) nor in the 6/7 manuscript; EFKT92 not yet checked (unavailable).

## R2 literature check: Frankl–Rödl (2026-11-23)
Frankl–Rödl 1987 "Forbidden intersections" (TAMS 300): for 0 < eta < 1/4 there is eps > 0 with:
a family of subsets of [n] with no two members meeting in exactly l points, eta n <= l <= (1/2-eta) n,
has size <= (2-eps)^n; the k-uniform version (k, l linear in n, l away from 0 and k) gives
|F| <= (1-eps)^n C(n,k). Surveys: Frankl–Tokushige arXiv:2107.06371; Keevash's dependent-random-
choice proof (people.maths.ox.ac.uk/keevash/papers/franklrodl-journal.pdf).
Fit with roadmap L4: tau > T on n = n points makes H a Turán system (every (n-T)-set contains an
edge), so density |H|/C(n,k) >= 1/C(n-T, k). In the near-complete regime n - T = k + s with
s = o(k) this is e^{-o(n)}, above (1-eps)^n, so FR yields a pair meeting in exactly l points for
any single l in the linear window — the hypotheses look satisfiable. TODO: confirm the exact
uniform statement (which paper/theorem) before relying on it. Scope caveat: this only covers
n <= (7/4 + o(1))k and gives tau <= (n+2k)/5 + O(1) there; it is one regime, not the whole problem.
