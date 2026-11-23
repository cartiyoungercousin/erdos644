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
