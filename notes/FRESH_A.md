# FRESH_A — structure / stability angle on Erdős #644

Fresh-eyes pass (about one hour), no earlier notes read. Status: **no full solution.**
Result summary: one new proved inequality (sparse triples), an exact rigidity gap for 7-tuple
obstructions (7/4 vs 11/6), a proof that shifting cannot help or hurt, and a negative search over
"piecewise-complete" candidate counterexamples. Code: `compute/fresh_a/`.

Notation: H is k-uniform with property (7,2), tau(H) = T+1 (so every D with |D| <= T misses an edge).
Good triple: E∩F∩G = ∅; P = points in exactly two of E,F,G (|P| = S); Q = points in exactly one.

---

## 1. Sparse-triple inequality (new, complements Fact 5)

**Theorem 1 [proved by hand].** For every good triple, tau <= S + (k+2)/3.
More precisely, if S <= T then 3(T - S) <= k - 1.

Proof. If S > T then tau = T+1 <= S. Otherwise let b = T - S and suppose 3b >= k.
Request D1 = P: edge A1 with A1∩P = ∅. For i = 2,3,4 request Di = P ∪ Bi where Bi is a set of
min(b, |A1∩...∩A(i-1)|) points of A1∩...∩A(i-1); |Di| <= T. Then |A1∩...∩Ai| <= max(0, k-(i-1)b),
so A1∩A2∩A3∩A4 = ∅. Consider the <= 7 edges E,F,G,A1..A4 and a 2-transversal {x,y}. Two points
hit three sets E,F,G, so one of them (say x) lies in two of them, i.e. x ∈ P. Then x misses every Ai,
so y ∈ A1∩A2∩A3∩A4 = ∅. Contradiction. ∎

Structural reading: **for a good triple with S <= T, the family H − P = {A : A∩P = ∅} is 4-wise
intersecting** (indeed its common points must lie in Q), while tau(H − P) >= tau − S.

**Corollary 2 [proved by hand, using Fact 5].** In a counterexample with tau >= (3/4+eps)k,
the minimum S over good triples satisfies

    (5/12 + eps)k - 1  <=  sigma  <  (5/4 - 11 eps/7)k + O(1),

and *every* good triple has S >= (5/12+eps)k - 1, hence a pair meeting in >= 5k/36 points.
So counterexamples cannot be "spread out": Theorem 1 kills S < 5k/12, Fact 5 kills sigma >= 5k/4.
Theorem 1 beats Fact 3 exactly when S < 7k/9, and beats the 7k/8 bound when S < 13k/24.

**Generalisation (vertex-cover principle) [proved by hand].** For edges E1..Ej (j <= 5) let Γ be
the graph of all their 2-transversals. If C meets every edge of Γ and |C| <= T, then
H − C is (7−j)-wise intersecting, so (6−j)(T − |C|) <= k − 1. (j = 3, C = P is Theorem 1.)
Also: for any 6 edges, the union of all their 2-transversals is a transversal of H (size >= tau).
In the Fano blow-up minus one line this union is exactly the 3 classes on the missing line (3k/4).

## 2. Rigidity of the obstruction (why the extremal example is rigid)

Seven sets A1..A7; type of a point = set of indices i with x ∈ Ai. The 7-tuple has no 2-point
transversal iff no two occurring types cover [7] [proved by hand, trivial].

* [proved by hand] Fact 2 is an *iff* in blow-up form: the Fano criterion holds iff the union can be
  7-coloured by Fano points with A_L ⊂ (classes off L). (A type contains no pencil iff it avoids all
  lines through some point, because the only minimal blocking sets of the Fano plane are lines.)
* [proved by hand] Fixed templates: for any fixed assignment of types to the n ground points the
  largest request has size >= 3n/7 (if all seven sets had measure > 4n/7 some point lies in >= 5 of
  them and the other two sets intersect). So fixed colourings give exactly tau <= 3n/7 + 1 and
  Fano is the optimal template; every improvement must be adaptive.
* **[computed, floating-point MILP, `rigidity.py`]** min |union|/k of a non-2-coverable 7-tuple of
  k-sets is 7/4 (unique optimum = Fano, all 7 types weight 1/4). If the 7-tuple is *not* a Fano
  sub-blow-up (for each of the 30 Fano planes on the index set some occurring type contains a line),
  then |union| >= 11k/6; if types violating each Fano plane carry mass >= delta·k the bound is
  11/6 + delta/6 (delta = 0.01, 0.05, 0.1; 1.875 at delta = 0.25).
  **So every obstruction on fewer than 11k/6 points is a Fano sub-blow-up.**
* [proved by hand] A Fano sub-blow-up on u = (7/4+eta)k points has every class size in
  [(1/4 − 5 eta)k, (1/4 + eta)k] and each A_L misses <= 4 eta k points of its four classes.
  (W_L = sum of classes on L <= u − k; v_q = ½ Σ_{L∋q} W_L − (1/6) Σ_L W_L since M^{-1} = ½M^T − J/6.)

Cheapest witness of non-rigidity: a non-Fano obstruction costs 1/12 k extra ground points; inside
< 11k/6 points, (7,2) is equivalent to "no Fano sub-blow-up".

## 3. Shifting [proved by hand]

* Shifting does not preserve tau ({23},{14} -> {13},{14}), so there is no reduction to shifted families.
* If H is shifted and tau > T then some edge lies in {T+1, T+2, ...}, hence every k-subset of [T+k]
  is an edge (down-closure in the componentwise order). K^k_n is not (7,2) once n >= 7⌈k/4⌉.
  So shifted (7,2)-families have tau <= 7⌈k/4⌉ − k (= 3k/4 if 4 | k): the conjecture holds for
  shifted families, and any counterexample is far from shifted.
* f(k,7) is unchanged if edges are allowed to have size <= k (pad with private points), so extra
  "new" points never help the adversary by themselves; only overlaps matter.

## 4. Candidate counterexamples: piecewise-complete families [computed, MILP, `piecewise.py`]

H = union over "pieces" X of all k-subsets of X, pieces = unions of classes. tau/k is an LP; the
threshold class size s* at which a non-2-coverable 7-tuple first appears is a MILP (any real
obstruction gives a feasible point, so s < s* certifies (7,2)). Checker validated on one piece
(s* = 7/4, tau = 3/4). Values of tau/k at the (7,2) threshold:

| design (classes; pieces)                  | s*      | ground/k | tau/k  |
|-------------------------------------------|---------|----------|--------|
| 1 class; itself (K_n)                     | 7/4     | 1.75     | 0.750  |
| 3 equal classes; pairs (triangle)         | 21/32   | 1.969    | 0.469  |
| 3 classes (1,1,t), pairs: t = 1/4         | 0.848   | 1.909    | 0.697  |
| t = 1/2 / 3/4 / 3/2 / 2                   |         |          | 0.600 / 0.464 / 0.409 / 0.500 |
| 4 equal classes; pairs                    | 1/2     | 2.0      | 0      |
| 4 equal classes; triples                  | 7/15    | 1.867    | 0.533  |
| 5 equal classes; 4-subsets                | 13/36   | 1.806    | 0.556  |
| 5 equal classes; cyclic triples           | 7/17    | 2.059    | 0.392  |

No design beats 3/4; mixing pieces creates obstructions long before tau gains. [numerical evidence
only for the conjecture; small design space.] By hand: the triangle family at s = 3k/4 (which would
have tau = 3k/4 on 9k/4 points) already fails (6,2) via E,F,G (one per piece) plus three edges.

## 5. What is missing / decisive next step

Fact 5 handles sigma >= 5k/4 − o(k); Theorem 1 handles S < 5k/12. The whole problem is now the
**middle range**: a good triple with 5k/12 <= S <= 5k/4 − delta·k. There P is too big to request
(S may exceed T) or leaves too little budget (T − S < k/3).
Target lemma: *a good triple with |E∪F∪G| >= (7/4 + delta)k forces tau <= 3k/4 + o(k).*
Together with Fact 5 this is equivalent to the conjecture [proved by hand: trivial combination].
Concrete attack: solve exactly the 4-round "trace game" on the 2-transversal graph of a good triple
(tripartite on P_a,P_b,P_c plus bicliques P_a–Q_E, P_b–Q_F, P_c–Q_G; adversary answers with traces
of size <= k missing the request) as a function F(a,b,c); the conjecture follows if
max_S min((17k − 7S)/11, F) <= 3k/4, and otherwise the adversary's optimal strategy is the blueprint
for a counterexample (which by §3–§4 must be far from shifted and not piecewise-complete of the
types above, and by Fact 4 must live on more than (7/4 + 3 eps)k points).
