# Roadmap for Erdős #644: f(k,7) = (3/4 + o(1)) k ?

Written 2026-11-23. Scripts for every computation quoted here: `compute/roadmap/`.
Status tags: **[P]** proved here by a short hand argument (should be Lean-checked),
**[C]** computed (floating-point MILP/LP or SAT; not yet an exact certificate),
**[H]** heuristic / conjecture, **[U]** unverified second-hand.

Notation: k = edge size, T = budget (we assume tau(H) > T and look for <= 7 edges with no
2-point transversal, a "bad tuple"), t = T/k, n = |V(H)|. A *request* is a set D of <= T points,
a *response* an edge disjoint from D. For edges E,F,G with empty common intersection ("good
triple"): X = E∩F, Y = E∩G, Z = F∩G, x,y,z their sizes, S = x+y+z, U = |E∪F∪G| = 3k − S.

---------------------------------------------------------------------------------------------

## 0. Summary

1. **Why everybody stalls (new, [C] + short argument).** Run any of the existing proofs on the
   complete family K_N, N = (1+t)k. It must output a bad 7-tuple *of K_N*. For t < 5/6 every bad
   7-tuple inside (1+t)k points contains a full Fano plane of miss-patterns (the next shape needs
   11k/6 points), and **no such tuple contains a good triple whose third edge is the response to a
   request inside E∪F** (the complete family answers with an edge containing all of V∖(E∪F)).
   FKW, the 6/7 manuscript and (as far as I can tell from its PROOF.md) the 11/13 argument all
   anchor on exactly such triples. So the whole family of methods has a hard floor at **5/6**,
   caused by the complete family itself, not by an exotic adversary. 11/13 = 0.846 is already close
   to it. Retuning cannot pass 5/6.
2. **6/7 explained in one line ([C]).** On symmetric good triples (a,a,a) the best *static*
   closure is max of two branches: a non-Fano shape, T >= (3k+S)/5, and the Fano shape,
   T >= (3k−S)/2. They cross at S = 9k/7, T = 6k/7. Moreover a triple (3k/7,3k/7,3k/7) lying in a
   complete family is in *no* bad 7-tuple unless N >= 13k/7: any strategy that keeps it is stuck
   at 6/7, adaptivity or not.
3. **The Fano branch is trivial once you ask for it ([P], sanity-checked by simulation).**
   *Fano template lemma* (Section 3). Corollaries, none of which is in the 6/7 manuscript:
   - tau(H) <= min over good triples of |E∪F∪G|/2 + 1. (Tight up to the additive constant for
     complete and parity families.)
   - tau(H) <= ceil((n−k)/3) + k/2 for 4 | k. (Tight for both; e.g. tau = 11 at k = 12 needs
     n >= 25, so our 22-point searches could never have found it.)
   - no two edges meet in m points with 2(k−T) <= m <= (T+2k−n)/2.
4. **Reduction.** Put S_max = max S over good triples. The first corollary settles every family
   with S_max >= 3k − 2T. So, up to O(1),
   > f(k,7) <= T  <=>  every (7,2)-family in which all good triples are "loose"
   > (union > 2T, i.e. S_max < 3k − 2T) has tau <= T.
   Loose families exclude all complete families with N >= 3k/2, hence all the obstructions in
   items 1–2. For T = 6k/7 the loose families are those with S_max < 9k/7: **to beat 6/7 it is
   enough to beat it for families all of whose good triples have S <= (9/7 + delta)k**, and to
   prove 3/4 it is enough to prove it for families with S_max <= (3/2 − delta)k, for each delta.
5. **Top recommendation.** Route R1 (Section 5): anchor on the max-S good triple, close the Fano
   side with the template lemma, and attack the loose side with a looseness-constrained request
   game, driven by a strategy/adversary refinement loop in which stuck adversaries are tested for
   realizability as block-type families whose blocks are the Venn cells of the stuck
   configuration. In parallel R2 (near-complete regime n <= (7/4+delta)k), which is the sharpest
   place to look for a counterexample and has a finite-dimensional structure.
6. **No error found in the 6/7 manuscript** in the parts I re-derived by hand (Cor 3.2, Lemma 4.8,
   Thm 5.2, Prop 5.3, and the proofs of 4.2/4.3 at the level of reading). See Section 1.

---------------------------------------------------------------------------------------------

## 1. Audit notes

### 1.1 six_sevenths_v3.tex
Read in full. Re-derived by hand, line by line:
- Cor 3.2 from Lemma 3.1; Prop 5.1 Case 1.
- Thm 5.2 (finishing theorem), all three cases including the discard-F branch and every inequality
  fed into Lemma 4.8. OK. (Distinctness of responses from earlier edges, which the proof uses when
  invoking maximality of M, holds in each place: the response always avoids a nonempty part of
  the earlier edge.)
- Lemma 4.8 (two large opposite cells) including the size of the first request (exactly T) and
  the second request's bound. OK.
- Prop 5.3 (rank seven), every request size and every covering claim in all 2 x 3 sub-cases. OK.
This closes, at the level of a careful human read, the three items PLAN_6_7.md lists as "NOT yet
audited" except the internal arithmetic of Lemmas 4.1, 4.5–4.7 (Lean will cover it).

Observations (not errors):
- The two static allocations (Hall, symmetric) are not the full static optimum. The optimal
  static 4-request closure (`static_phi.py`) also contains the *Fano/matching allocation*: split
  each pair cell in two, give the six half-classes the labels {1,2},{3,4} / {1,3},{2,4} /
  {1,4},{2,3} (three perfect matchings of K_4), put each private point into a class of one of the
  two pair cells of its edge. All four requests have size (3k−S)/2. The manuscript never needs it
  because it excludes pair cells in (T/2, k/2] by gap arguments, but it is the only static
  allocation that is tight on complete families, and it is what Section 3 builds on.
- Section 8's "three independent constraints coincide at 6/7" is one phenomenon, not three: see
  item 2 of the summary and Section 2.4.

### 1.2 11/13 PROOF.md  [U]
Read through a fetch summary only (the written reduction, not the 919-clause certificate). It
anchors on a "lexicographically least good profile" and four response queries. It does not say
why it stops at 11/13. My reading: 5/6 is the floor for that architecture (Section 2.3) and
11/13 − 5/6 = 1/78. I have **not** verified the certificate or the rounding step in its
Section 8 (the excess-load claim there is the step I would check first).

### 1.3 Omega-institute notes  [U] -> partly checked
- "7 k-sets on n < 9k/5 points with no 2-cover are Fano-supported": correct argument (degree <= 4
  because n < 2k forces pairwise intersecting edges; Füredi). My MILP gives the sharp threshold
  **11k/6**, not 9k/5 (Section 2.2).
- Their bound t < 3n/7 + 1 is the j = 0 case of the template lemma; Theorem A (j = 1) is stronger.

---------------------------------------------------------------------------------------------

## 2. What any 3/4 proof must see

### 2.1 The request method is complete  [P]
If tau(H) > T, a branching tree of depth T (request the current partial transversal P, branch on
the k points of the response) collects at most (k^{T+1}−1)/(k−1) edges whose transversal number
is still > T. Hence

> f(k,7) <= T  <=>  the requester wins the request game with unboundedly many rounds and the
> right to discard responses.

So nothing outside the request method is *needed*. What limits the published arguments is that
they use 7 responses and keep (almost) all of them. Extremal choices ("take the pair with the
largest intersection <= k/2") are the standard way to encode unboundedly many rounds.

### 2.2 Shapes of bad 7-tuples  [C] (`shapes.py`)
miss(x) = {i : x ∉ A_i}; bad <=> the miss patterns pairwise intersect. Normalizing k = 1:
- min union of a bad 7-tuple = 7/4 (Fano, 7 classes of mass 1/4).
- min union when not all 7 lines of a Fano plane occur as miss patterns = **11/6** (six lines plus
  a 4-set containing the seventh; masses 1/6,1/6,1/6,1/3,1/3,1/3,1/3).
- inside a universe of (1+t)k points, 3/4 <= t <= 0.82, every pair of edges of a bad 7-tuple
  meets in (1/2 ± 2(t − 3/4))k points. Equivalently: **a kept pair with intersection m k costs
  t >= 3/4 + |m − 1/2|/2** against the complete family (m = 1/4 gives 7/8, the FKW constant).

Consequence. At t = 3/4 + eps, whenever H is (close to) a complete family, the proof has to
exhibit a near-Fano tuple: all pair intersections k/2 ± 2 eps k, triples either "concurrent"
(empty common intersection, S ≈ 3k/2, union ≈ 3k/2, no private points) or "triangles" (common
intersection ≈ k/4). 28 of the 35 triples of a Fano tuple are triangles; only 7 are good triples.

### 2.3 The complete-family test and the 5/6 barrier  [C] (`complete_test.py`)
Adversary K_N, N = (1+t)k, tau = tk + 1. A response to a request D with |D| = T inside the known
points is forced: it is N∖D. More generally the adversary may always answer a request D ⊆ E∪F
with an edge G ⊇ V∖(E∪F).

> **Barrier.** For t < 5/6 there is no bad 7-tuple in K_{(1+t)k} containing three edges E,F,G with
> E∩F∩G = ∅ and G ⊇ V∖(E∪F), whatever |E∩F| is. (MILP minimum over |E∩F|: t = 0.83333, attained
> for every |E∩F| in [0.35k, k/2]; it is 0.85 at 0.3k and 7/8 at k/4.)

So an argument of the form "two edges of the family, then a request containing their intersection,
then close the resulting good triple with four more responses" cannot prove t < 5/6. To get
below 5/6 one must do at least one of: (a) choose the third edge by an extremal principle rather
than as a response; (b) anchor on a triangle (non-empty core) instead of a good triple;
(c) discard edges systematically.

The same test gives a lower bound chi(x,y,z) for any strategy that keeps a good triple with cells
(x,y,z) (`chi.py`): chi = (min union of a bad 7-tuple through the triple) − 1.
On the diagonal: chi(a,a,a) = 0.84, 0.857, 0.825, 0.7875, 0.75 at a = 0.4, 3/7, 0.45, 0.475, 0.5,
equal to the static optimum there. In K_N only triples within O(eps) of (1/2,1/2,1/2) can be kept.

### 2.4 The static landscape  [C] (`static_phi.py`)
phi(x,y,z) = least t at which four static requests close the triple (all label allocations).
- phi(a,a,a) = 3/4 for a <= 1/4; (3+3a)/5 for 1/4 <= a <= 3/7; (3−3a)/2 for a >= 3/7.
  Maximum 6/7 at a = 3/7.
- on a grid of step 0.05, phi <= 3/4 exactly on a "sparse" region (all cells <= k/4, roughly
  balanced) and at the single "dense" point (1/2,1/2,1/2).
(Caveat: the script forces a label on private parts whose opposite pair cell is empty, so its
values on the boundary faces y = 0 or z = 0 are upper bounds only.)

So there are two worlds where 3/4 is easy: sparse (small intersections, lots of new points) and
Fano (tight). 6/7 is where the two static branches cross. A 3/4 proof has to interpolate.

### 2.5 Is the parity family a constraint on the shape of the argument?  No.
The request method only uses "tau > T". At T = 3k/4 the parity family (tau = 3k/4 + 1) is a
legitimate adversary and wins; at T = 3k/4 + 1 it is no longer an adversary. Cell-size data cannot
distinguish it from K_{7m+1}^{(4m)}, and does not need to: the hypothesis tau > T does.
The parity family only says the exact answer is not 3k/4. For the asymptotic question the
constraint with teeth is the complete family, through Sections 2.2–2.3. Parity-type (2-adic)
obstructions are O(1): one defect point repairs every parity condition of every check it lies in,
so r checks do not cost r times as many defects (Section 5, R4).

---------------------------------------------------------------------------------------------

## 3. The Fano template lemma and three corollaries  [P]

Let 𝔽 be the Fano plane (7 points, 7 lines).

> **Lemma (Fano template).** Let A_1,…,A_j be edges of H, assigned to distinct lines L_1,…,L_j,
> and let W ⊆ V be a set of points such that every point outside W lies in none of the A_i and
> either W = V or three of the lines L_i are concurrent. Let pi : W → points of 𝔽 satisfy
> (i) pi(x) ∉ L_i whenever x ∈ A_i, and
> (ii) |pi^{-1}(L)| <= T for each of the other 7 − j lines L.
> If tau(H) > T, then A_1,…,A_j together with responses to the requests pi^{-1}(L) form a bad
> subfamily of at most 7 edges.

Proof. A point x of W misses every edge indexed by a line through pi(x): for i <= j by (i), for
a response because x is in its request. Two points of 𝔽 lie on a common line, so for x,y ∈ W
some edge misses both (take x = y for single points). A point outside W misses A_1,…,A_j; if
three of these are concurrent at p it behaves like a point with pi = p, and the same argument
applies. ∎
The map pi may be re-chosen after each response (a response is a new anchor for its line); this
gives an adaptive "template game".

(a) **One anchor, W = V (Theorem A).** L_1 = {b_1,b_2,b_3}; split V∖A_1 into three parts B_j and
A_1 into four parts a_1..a_4 (the four points off L_1). The six other lines are b_j plus a pair
of the j-th perfect matching of {a_1..a_4}. Hence
    tau(H) <= ceil((n−k)/3) + k/2     (4 | k;  + O(1) in general).
Tight for K_{7m−1}^{(4m)} (3m) and for the parity family (3m+1). It beats 6k/7 whenever
n < 29k/14. A family with tau > tk has n > (3t − 1/2)k.

(b) **Two anchors, W = V.** L_1∩L_2 = p. V∖(A_1∪A_2) → p; A_2∖A_1 → two halves on L_1∖p;
A_1∖A_2 → two halves on L_2∖p; A_1∩A_2 → the two remaining points. The line through p has
n − 2k + 2m points (m = |A_1∩A_2|), the four others k − m/2. So tau > T forbids
    2(k−T) <= |A_1∩A_2| <= (T + 2k − n)/2.
With n <= 2T one can force a pair into the window by one request; this gives 7k/8 at n = 7k/4.

(c) **Three concurrent anchors = good triple, W = E∪F∪G, no assumption on V.** Lines L_E,L_F,L_G
through p. X → the two points of L_G∖p, Y → L_F∖p, Z → L_E∖p, each private part into either of
the two pairs belonging to its edge, each pair split evenly. Every point outside E∪F∪G misses
E,F,G, i.e. behaves like a point of class p, which lies on no remaining line. The four remaining
lines each carry half of E∪F∪G. Hence

> **Tight-triple lemma.** tau(H) <= |E∪F∪G|/2 + 1 for every good triple.
> Equivalently, if tau > T then every good triple has S <= 3k − 2T + 1.

No balance condition on x,y,z is needed. (`template_check.py`, `theoremA_check.py`: random
responses, including responses using new points; 0 failures.)

Remarks.
- (c) is the only universe-free case: with a triangle anchor every Fano point lies on a remaining
  line, so outside points cost load and n enters.
- In terms of membership sets K(x) = {i : x ∈ A_i}: a tuple is bad with Fano support iff every
  K(x) is a cap (contains no three concurrent lines). Caps have <= 4 lines; the 4-caps are the
  complements of stars. This is the clean combinatorial form of the near-complete regime (R2).

---------------------------------------------------------------------------------------------

## 4. The reduction

Define, for a (7,2)-family H, S_max(H) = max S over good triples and its looseness
lambda = 3/2 − S_max/k. Let B(lambda) = sup tau/k over (7,2)-families of looseness >= lambda
(non-increasing in lambda). By the tight-triple lemma, a family of looseness exactly lambda has
tau <= (3/4 + lambda/2)k + 1, so

    limsup f(k,7)/k  <=  sup_lambda  min( 3/4 + lambda/2 ,  B(lambda) ).

- Conjecture 3/4  <=>  B(lambda) <= 3/4 for every lambda > 0.
- Known: B <= 6/7 (if the manuscript is right). The supremum above is then attained at
  lambda = 3/14 (S_max = 9k/7). To improve 6/7 one needs B(lambda) < 6/7 for lambda slightly
  below 3/14, i.e. a better bound for families in which every good triple has
  S <= (9/7 + delta)k. More generally, a proof of "tau <= tk" only has to handle families with
  S_max < (3 − 2t)k.
- Complete families K_N with N >= 3k/2 have lambda = 0. So for lambda > 0 none of the
  complete-family obstructions (5/6 barrier, chi, the 6/7 corner) applies. Whatever obstruction
  remains must come from a genuinely different family, and we know of none: every construction
  we have (complete, parity, block-type) has tight or nearly tight good triples.
- **Stability conjecture [H].** B(lambda) < 3/4 for every lambda > 0: near-extremal families
  contain near-tight good triples. This is the natural strong form; I have no evidence for it
  beyond the absence of loose examples, and R1 is designed to test it.

In a loose family the adversary is constrained in every round: if a response K avoids X, then
(E,F,K) is good, so |K∩E| + |K∩F| <= S_max − x; likewise for Y, Z, and for every good triple among
the edges in play. The manuscripts use pair gaps (bootstrapped); this is a triple gap that comes
for free from the anchor choice. Caveat: at S_max = 9k/7 and x ≈ 3k/7 the inequality reads
|K∩E| + |K∩F| <= 6k/7, which is a mild restriction on a single response; the leverage, if there
is any, comes from applying it to all triples over several rounds.

---------------------------------------------------------------------------------------------

## 5. Routes

### R1. Max-S anchor + looseness-constrained request game  (primary)
*Key lemmas.*
- L1 (done): tight-triple lemma.
- L2 (first target, beats 6/7): B(lambda) <= b < 6/7 for lambda >= 3/14 − delta, i.e. for
  families with S_max <= (9/7 + delta)k. Proof format as in the 6/7 manuscript (integer
  inequalities, adaptive requests) but with the constraint "every good triple among the edges in
  play has S <= S_max" available to bound responses, and with the right to re-anchor: a response
  that creates a good triple with larger S contradicts maximality.
- L3 (final target): B(lambda) <= 3/4 for every fixed lambda > 0. Families with small lambda need
  nothing: tau <= (3/4 + lambda/2)k already.
*Why it might pass the barriers.* The barriers of Section 2 are all realized by complete
families, which are not loose. The manuscript's own stuck configurations (a cell slightly above
T/2 next to a medium cell) have S below about 0.9k, far from tight; the open question is whether the
adversary behaviour that defeats four requests there is compatible with *every* good triple in
the family having S <= S_max, across many rounds. In the 6/7 corner triple (3/7,3/7,3/7) the
constraint does not bind in the first adaptive round (privates are only k/7), so the gain, if
any, must come from re-anchoring over several rounds: that is the first thing to test.
*Main risk.* The looseness constraint is too weak and the value 6/7 persists for
lambda near 3/14 with a pseudo-adversary that no real family realizes. Then one needs a second
extremal parameter (e.g. FKW's M, or min |E∪F| over pairs with |E∩F| <= k/2).
*Cheap first test (2–3 days, computation).* Extend `static_phi.py` to four anchors and three
requests (12 sub-cells, labels on [3]); wrap it in a one-adaptive-round minimax: requester picks
the first request from a small menu (X∪Y∪part of Z; Y∪halves; caps-type), adversary ranges over
the response polytope cut by the looseness inequalities, value = static closure of the four
edges or re-anchoring. Evaluate on a grid of (x,y,z; S_max) at t = 0.85, 0.84, 5/6, 0.82, 0.80.
 - Success: value < 6/7 for all profiles with S_max <= (9/7 + delta)k → new record below 6/7
   after turning the numerics into inequalities (or LP certificates as the 11/13 group did).
 - Failure: value stays >= 6/7 there → extract the worst response pattern and go to R3's
   realizability test.

### R2. The near-complete regime  n <= (7/4 + delta)k
Write n = 7k/4 + c, T = 3k/4 + g, s = c − g: every (k+s)-set contains an edge, and responses are
"offered set minus s points". All bad tuples are Fano-supported (n < 11k/6), so this regime is the
caps game of Section 3. The parity family lives here (c = 1). Known: g <= 3c/7 (static),
g <= c/3 (Theorem A). The pattern is g <= c(3−j)/(7−j) with j exact anchors, so:
*Key lemmas.*
- L4 (pair existence): if g > c/5 + O(1) some two edges meet in the window of 3(b). **Likely
  provable now** from the Frankl–Rödl forbidden-intersection theorem: H has density at least
  1/C(k+s, s) in C(V,k), which is e^{−o(n)} when s = o(k), and the window is in the linear range.
  Gives tau <= (n+2k)/5 + O(1) for n <= (7/4+delta)k, k large. [H until the FR hypotheses are
  checked: need 2k − n + eta n <= l <= k − eta n and the exact form of the density threshold.]
- L5 (triangle existence): if g >= g_0 then H contains three edges with
  |A_1∩A_2∩A_3| ≈ k/4 − c/2, pair intersections ≈ k/2 − c/2, and at most 4g points outside the
  union. With L5 the static template closes with g = O(g_0): this would prove the conjecture in
  the near-complete regime. The difficulty is a degenerate Venn cell (the outside has only O(g)
  points), which is exactly the scale at which "complete on V minus a junk set Y" lives; a
  Frankl–Rödl-type statement at density e^{−Theta(c log(k/c))} with a cell of size Theta(c) is
  needed, or an adaptive argument.
*Why it matters.* If the conjecture is false, the smallest counterexamples in terms of n/k live
here or just above; if it is true, the mechanism that forces a Fano triangle here is the
mechanism a general proof needs on its dense side. It is also the only regime where the game is
finite-dimensional after linearizing around the Fano blow-up (all quantities are O(c)).
*Main risk.* Junk vertices (vertices in few edges) make every counting argument degenerate.
*Cheap first tests.*
 (i) Solve the 7-round template game exactly for small parameters with an adaptive adversary
     (state = Venn cell counts; leaves decided by the flow-feasibility of a static completion):
     (k,n) = (8,15), (8,16), (12,23), (12,25), (16,29..32). Question: is the 7-round value
     g_7(c) linear in c? If the adaptive adversary wins with g ≈ c/3 or c/5, then proofs in this
     regime must use the fixed-family property (many rounds), and L5 is the right formulation.
 (ii) Exact small values by SAT (`small_exact.py`): f(4,7) ∈ {3,4}, f(5,7) ∈ {4,5},
     f(6,7) ∈ {5,6}, f(8,7) ∈ {6,7}. By Theorem A, tau = 4 at k = 4 needs n >= 8 and tau = 7 at
     k = 8 needs n >= 15. First runs: Section 6.1.

### R3. Strategy/adversary refinement loop (the engine for R1 and R2)
The 6/7 and 11/13 groups ran a requester-side optimization against an unconstrained adversary.
What is missing is the other half: **is a stuck adversary an actual family?**
- Given a stuck configuration (anchors + responses, with its Venn cell sizes), build the block-type
  family whose blocks are those Venn cells (8–16 blocks) and whose allowed types are the edge
  profiles the adversary used, closed under what tau > T requires; run `typefam.py`'s bad-tuple
  ILP on it. This is a principled way to go beyond 2–3 blocks: the blocks come from the proof
  obstruction instead of from guessing.
- Outcome 1: the ILP finds a bad tuple. Its shape is a strategy the requester did not have
  (typically with a discarded edge or a different anchor). Add it to the menu, repeat.
- Outcome 2: no bad tuple and tau > (3/4+eps)k. That is a counterexample.
*Key lemma to aim for.* A finite list of intersecting-family shapes on [7] and of extremal
parameters such that the loop terminates at 3/4. The shape list can be made finite a priori: the
miss patterns form an up-closed intersecting family; only the minimal-union shapes at each
profile matter (`shapes.py` is the starting point; enumerate maximal intersecting families on [7]
up to symmetry, ~10^4–10^5 classes, and keep those that are LP-extremal for some profile).
*Risk.* Explosion of cases; mitigated by the reduction of Section 4 (only loose families) and by
exact LP certificates per case.
*Cheap first test.* Run the loop once by hand on the manuscript's stuck configuration at
t = 0.855 (Section 8, second kind: M slightly above t/2 with a medium cell).

### R4. Disproof search, guided by necessary conditions
Any family with tau > (3/4 + eps)k must satisfy: n > (7/4 + 3 eps)k (Theorem A); every good
triple has union > (3/2 + 2 eps)k − 1; no pair intersection in the window of 3(b); it is
exponentially sparse in C(V,k) if a multi-set Frankl–Rödl theorem applies (R5). Our block
searches never imposed n > 7k/4 + 3 eps k together with looseness, and several of them
(e.g. k = 12 on 22 points) were looking where Theorem A forbids success.
- Search A: group-invariant families via SAT (variables = orbits of k-sets under Z_n, Z_n ⋊ Z_n^*,
  PSL(2,7) on 14/21 points, AGL(1,q), AGL(m,2)); CEGAR on bad tuples with orbit clauses. Targets
  from Theorem A: (k,n,tau) = (8,15..17,7), (12,25..27,11), (16,32..34,14).
- Search B: binary cosets with r = 2,3 checks = block-type families on 4 / 8 blocks with parity
  types. Expectation: nothing beyond +O(1) (Section 2.5), but it is one afternoon with typefam.py.
- Search C: code route. Needed: a coset whose weight-k layer has the covering property with slack
  s while 7 d > 12 (s+g); a swap argument gives d <= 2s + 2, so g < s/6 is not excluded by
  counting. This asks for asymptotically near-perfect codes with a restricted-support covering
  property; I consider existence very unlikely, and the Omega notes report that random matrices
  fail with exponentially small probability. Low priority; keep as a one-page note.
*Decision rule.* If Search A/B find a family with tau >= ceil(3k/4) + 2 for some k, switch all
effort to generalizing it. Otherwise record the negative results with the exact search spaces.

### R5. Density / forbidden-configuration route
(7,2) says: no 7 edges with pairwise intersecting miss patterns. In the near-complete regime H
has subexponential density, so a Frankl–Rödl-type theorem for a prescribed Venn diagram of
several sets (Frankl–Rödl 1987; Keevash–Long on vector-valued forbidden intersections) would
force near-Fano sub-configurations whenever the pattern is non-degenerate (all Venn cells
linear). The exact Fano blow-up is degenerate (outside cell of size c), which is why this gives
only qualitative statements at present; the pair case (L4) is the non-degenerate instance.
*Key lemma.* A supersaturated, cross-family version for triples: given many pairs (A_1,A_2) with
intersection in the window, some edge A_3 completes a Fano triangle with O(g) outside points.
*Cheap first test.* Literature check (one day): exact statements of Frankl–Rödl Thm 1.4 and its
cross version; whether Keevash–Long covers three sets with one small cell.

### Not recommended
- Induction on k: no canonical way to peel a Fano layer; traces do not preserve (7,2).
- Fractional/LP duality on tau: the problem lives where tau >> tau* (tau* is O(1) for complete
  families), so fractional relaxations of the transversal lose everything. LP duality is useful
  only inside the request game (allocation of requests), where it is already used.
- More rounds without an extremal principle: Section 2.2 shows that even the second edge must
  be chosen (not requested) to pass the complete-family test.

---------------------------------------------------------------------------------------------

## 6. Ranking and first two weeks

Ranking by (probability of a publishable step) x (information about 3/4):
1. R1 + R3 (they are one program). 2. R2. 3. R4 Search A/B. 4. R5. 5. R4 Search C.

**Days 1–2 (hand + Lean).** Formalize the Fano template lemma and corollaries (a), (c) on top of
`Framework.request_cover`. Deliverables: `tau <= ceil((n−k)/3) + k/2` and
`tau <= |E∪F∪G|/2 + 1`. Success = both compile with no new axioms. These are short and give the
project two new, clean, verifiable statements independent of the 6/7 manuscript.
Also check FKW99 Lemma 1 against (c): if FKW already has it, cite; if not, it is a small new lemma.

**Day 2 (computation, exact).** Replace the floating MILPs of `shapes.py`, `complete_test.py` by
exact certificates: enumerate maximal intersecting families on [7] up to S_7, solve each LP in
rationals, and record (i) min union 7/4, next 11/6; (ii) the 5/6 barrier; (iii) the pair law.
Success = a table reproducible in exact arithmetic; then write the 1-page hand proof of
"Fano-supported below 11k/6" (Füredi + a short argument for 4-sets).

**Days 3–6 (computation).** R1 first test: four-anchor static solver, one-adaptive-round minimax
with looseness constraints and re-anchoring, grid over (x,y,z; S_max; t).
Decision D1 (end of day 6):
 - value < 6/7 on all profiles with S_max <= (9/7 + delta)k: go for a written bound below 6/7
   (days 7–10: extract inequalities, audit by exhaustive integer check as in `audit_cases.py`,
   start Lean).
 - no gain: run R3 on the worst configuration (day 7); then add the second extremal parameter
   (FKW's M) and repeat once (days 8–9).

**Days 3–5 in parallel (computation, cheap).** `small_exact.py` for k = 4 (n = 8,9,10), k = 5,
k = 6 with orbit clauses; R4 Search B (4- and 8-block parity types at k = 8, 12, 16 with n from
Theorem A).
Decision D2: any family with tau >= ceil(3k/4) + 2 → drop everything else and study it.

**Days 7–10 (computation + reading).** R2 test (i): exact 7-round template game at
(8,15), (8,16), (12,23), (12,25). R5 literature check; write up L4 if Frankl–Rödl applies.
Decision D3: if L4 holds, we have tau <= (n+2k)/5 + O(1) near n = 7k/4; decide whether L5
(triangle existence) is approachable by the same tool or needs the adaptive game.

**Days 11–14.** Consolidate: (1) the barrier note (Sections 2–4 as a short paper-quality text:
"why avoidance proofs stall at 5/6, and a reduction to loose families"); (2) status of D1–D3;
(3) choose between pushing R1 to a full theorem below 6/7 or R2 to a near-complete-regime theorem.

What success looks like after two weeks: Lean-checked template corollaries; exact certificates
for the barrier; either a numerical strategy beating 6/7 on loose families or a concrete
candidate adversary family; exact value of f(4,7) (and possibly f(5,7), f(6,7)).

### 6.1 First runs of the small-case searches (inconclusive)  [C]
- k = 4, T = 3, n = 7: no family (trivially: tau > 3 on 7 points forces the complete family).
- k = 4, T = 3, n = 8, 9, 10, families invariant under Z_n, under Z_{n−1} with a fixed point, and
  (n = 8) under the dihedral group: none exists (`small_invariant.py`, < 1 s each).
- k = 4, T = 3, n = 8, unrestricted (`small_exact.py`, orbit clauses under S_8): not finished in
  9 minutes (9M clauses after 60 refinements); n = 10 without orbit clauses: 100k refinements,
  undecided. k = 5, T = 4, n = 9 cyclic: undecided after 2 minutes.
So f(4,7) ∈ {3,4} is still open here. The CEGAR needs engineering before it is useful: minimal
bad subfamilies as clauses, images under the normalizer for invariant searches, and a canonical
symmetry break (or a direct QBF/2-level encoding) for the unrestricted case.

---------------------------------------------------------------------------------------------

## 7. Honest caveats

- Everything tagged [C] is floating-point MILP on the continuous (k = 1) relaxation. Infeasibility
  of the relaxation implies integer infeasibility, so the barrier statements go in the right
  direction, but they need exact certificates before being quoted.
- The 5/6 barrier is a statement about an architecture ("keep a good triple whose third edge is a
  response to a request inside E∪F containing E∩F"), established by running it on K_N. I checked
  that FKW and the 6/7 manuscript are of this type in every branch except the discard-F branch of
  Thm 5.2 (which is in the sparse regime M <= k − T). For 11/13 I rely on a summary: its anchor is
  chosen by a lexicographic extremal rule, and I have not checked which triple that rule selects
  in K_N. The numerical closeness of 11/13 to 5/6 is suggestive, not a proof.
- The template lemma proofs are short and were simulated, but they are not yet Lean-checked.
  The O(1) terms (+1 in the tight-triple lemma, rounding in Theorem A when 4 ∤ k) should be pinned
  down in Lean.
- Section 4 is a reformulation, not progress on the hard half. I have no bound on B(lambda) better
  than 6/7 for any lambda > 0, and it is possible that looseness alone does not help; the
  first test of R1 is designed to find that out quickly.
- L4 depends on the precise hypotheses of the Frankl–Rödl theorem, which I quoted from memory.
- I did not find a new construction. The code/near-perfect route (R4-C) is not excluded by any
  counting argument I know; I just think it is unlikely.
- Novelty: the template lemma may be implicit in FKW99's Lemma 1 (I only have our summary of it).
  Theorem A and the tight-triple bound are not in the 6/7 manuscript.

## 8. Files
- `compute/roadmap/shapes.py`: shapes of bad 7-tuples, pair-intersection law.
- `compute/roadmap/complete_test.py`: complete-family test, 5/6 barrier.
- `compute/roadmap/chi.py`: lower bound chi(x,y,z) for strategies keeping a good triple.
- `compute/roadmap/static_phi.py`: optimal static four-request closure.
- `compute/roadmap/theoremA_check.py`, `template_check.py`: randomized checks of Section 3.
- `compute/roadmap/small_exact.py`, `small_invariant.py`: CEGAR-SAT for exact small cases
  (unrestricted / group-invariant).
