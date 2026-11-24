# FRESH_B — method transfer for Erdős #644 (f(k,7) vs 3k/4)

Written blind (no reading of `notes/` or `compute/` other than `compute/fresh_b/`), about one hour.
Tags: [proved by hand] / [computed exact] / [numerical] / [heuristic] / [literature: ...].
Notation: H is k-uniform with property (7,2); tau(H) > T; "request principle" = every set of <= T points is missed by an edge.
A *good triple* is E1,E2,E3 with empty common intersection; a_i = |E_j ∩ E_l| (the pairwise intersection opposite i),
S = a_1+a_2+a_3, u_i = k - a_j - a_l = |E_i \ (E_j ∪ E_l)|, W = E1∪E2∪E3, |W| = 3k - S.

## 0. Bottom line

* No off-the-shelf "local covering => global covering" machine (Alon–Kleitman, fractional Helly, LP rounding, flag algebras,
  set-pair, shifting, topological Kneser bounds) can see the constant 3/4; each fails for an identifiable reason (Section 2).
* The one transfer that does bite is **pair-covering-design theory (Mills) run in reverse, combined with Frankl's
  iterated-request argument for r-wise intersecting families**. It gives an exact dictionary (Section 1):
  seven edges have no 2-point transversal **iff** the "miss-labels" I(x) = {i : x not in E_i} form a pairwise intersecting
  family on [7]. So the possible *shapes* of a (7,2)-violation are exactly the intersecting families on [7];
  the Fano criterion (Fact 2) is one shape among many.
* Optimising over all shapes by a small MILP (Section 3) gives, for a symmetric good triple, the non-adaptive
  request size  L*(S)/k = 3/4 (S <= 3k/4),  (3k+S)/5k (3k/4 <= S <= 9k/7),  (3k-S)/2k (S >= 9k/7),
  with maximum exactly 6/7 at S = 9k/7. Two of the three regimes use non-Fano shapes, both verified by hand
  (Lemmas 3.1, 3.2). In particular **every good triple with S <= 3k/4 that is not too lopsided already kills (7,2) at
  T = 3k/4** — a counterexample needs its sparse triples to be lopsided or to have S > T.
* It breaks at lopsided triples in the window T < S < 3k - 2T (Section 3.4): non-adaptive completion of a *given* triple
  cannot do better than the LP value, and the adversary chooses the triple's shape.

## 1. The covering-design dictionary

**1.1 Label criterion.** [proved by hand] For edges E_1..E_7 and a point x put I(x) = {i : x ∉ E_i}.
{x,y} is a 2-point transversal iff I(x) ∩ I(y) = ∅. Hence
> E_1..E_7 have no 2-point transversal  <=>  { I(x) : x a point } is a pairwise intersecting family of subsets of [7]
> <=> for every point x, the edges missing x have empty common intersection.

(Points outside all edges have I = [7]; harmless.) Since all edges have size k, every index i has the same load
|{x in U : i in I(x)}| = |U| - k, where U is the union of the seven edges. So a violation is a *regular* weighting of an
intersecting family on [7].

**1.2 Union bound.** [proved by hand] A probability weighting of an intersecting family on [7] has some index of marginal
>= 3/7 (if all sets have size >= 3 the marginals sum to >= 3; if a set {a,b} or {a} has positive weight, every set meets
it, so marginal(a)+marginal(b) >= 1). Hence any seven edges with no 2-point transversal have union >= 7k/4.
The Fano family (lines and their supersets) attains 3/7; this is why Fano is the only shape available inside 7k/4 points.

**1.3 Complete families = Mills' covering numbers.** [proved by hand] The complete k-graph on n points has property (p,2)
iff no p sets of size n-k cover all pairs of points, i.e. iff the pair-covering number C(n, n-k, 2) > p. Its tau is n-k+1.
[literature: W. H. Mills, "Covering designs I: coverings by a small number of subsets", Ars Combin. 8 (1979) — thresholds
quoted from memory, NOT re-read] C(v,c,2) <= p iff v/c <= g(p) with g(3..13) = 3/2, 5/3, 9/5, 2, 7/3, 12/5, 5/2, 8/3, 14/5, 3, 13/4.
Complete families therefore give tau/k -> 1/(g(p)-1) = 2, 3/2, 5/4, 1, 3/4 for p = 3..7.
[literature: Erdős–Fon-Der-Flaass–Kostochka–Tuza 1992, values as listed on the Chung–Graham Erdős-problems page]
f(r,3,2)=2r, f(r,4,2)=ceil(3r/2), f(r,5,2)=ceil(5r/4), f(r,6,2)=r — exactly the Mills values, which cross-checks the
thresholds for p <= 6. So **Erdős' conjecture for p=7 is the statement that complete families stay asymptotically extremal
at the Fano threshold g(7)=7/3**; the same heuristic predicts 5/7, 2/3, 3/5, 5/9, 1/2, 4/9 for p = 8..13 [heuristic].
The p=7 threshold itself: if 7c < 3n then each point lies in >= 3 of the seven co-edges (two co-edges cannot cover n
points), so 3n <= 7c, contradiction [proved by hand].

**1.4 n-point bound.** [proved by hand] If all edges lie in an n-set then tau <= 3*ceil(n/7): split the n points into
seven classes indexed by Fano points, request the union of the three classes on each line; any two points lie in a common
request, so the seven answering edges have no 2-point transversal. This beats Fact 4 for n < 7k/4 and loses for n > 7k/4;
together: a counterexample at T = (3/4+eps)k needs more than 7k/4 + 3 eps k points.

**1.5 Single-profile blow-ups never beat complete families.** [proved by hand] Let V = V_1 ⊔ ... ⊔ V_m and let H be all
k-sets with |E ∩ V_i| = t_i. Put c_i = |V_i| - t_i. If every class has c_i >= 3*ceil(|V_i|/7), aligned Fano partitions of
all classes give seven edges with all pairs missed, so (7,2) fails. If (7,2) holds, some class has 7c_i < 3|V_i| up to
rounding, i.e. c_i < 3t_i/4 + O(1), and tau <= c_i + 1 <= 3k/4 + O(1). Any construction beating 3/4 needs several
profiles on the same classes.

**1.6 Multi-profile templates are a finite problem.** [proved by hand, asymptotic form] For profiles t^1..t^7 (repeats
allowed), seven edges with those profiles and no 2-point transversal exist iff there is an intersecting family F on [7]
and, for each class i, a probability distribution on F whose marginal at j is <= 1 - t^j_i/|V_i|. So a template has (7,2)
iff for every 7-multiset of profiles and every maximal intersecting F some class is LP-infeasible (Farkas certificate
= a Mills-type weighted count). This is the correct "limit object"; what is missing is a symmetrisation theorem reducing
arbitrary H to templates (Section 2).

## 2. Survey: what transfers and where each method breaks

| Method | What it gives here | Where it breaks |
|---|---|---|
| Alon–Kleitman (p,q), fractional Helly | tau* <= (35k)^{1/3} [proved by hand: draw 7 edges i.i.d. from any measure mu; some 4 share a point, so 1 <= 35 * sum_x d(x)^4 <= 35 k D^3; LP duality] | In the extremal family tau* = n/k < 7/4 while tau = 3k/4: integrality gap Theta(k). No rounding of the covering LP can see 3/4. |
| Weak eps-nets / greedy rounding | tau <= tau* (1 + ln Delta) | Same gap; constant is lost. |
| Frankl's bound for r-wise intersecting families (tau <= (k-1)/(r-1) + 1) | It *is* the request principle iterated: m_{j+1} <= m_j - (tau-1) for the minimum j-fold intersection [literature: Frankl; proof reproduced by hand]. Gives good triples with a_1 <= k - T. Also: for a good triple with Z = union of pairwise intersections, the edges avoiding Z are 4-wise intersecting, so tau <= S + (k-1)/3 + 1 [proved by hand]. | Paying for Z costs S >= 5k/4 near the extremal family; useless there. Useful only inside the request game. |
| Mills pair-covering designs | Sections 1 and 3: the exact shape dictionary, all known values for p <= 6, and new request designs. | It is non-adaptive; the unbounded ground set forces adaptivity (requests are defined relative to earlier answers). |
| Bollobás set-pair / tau-critical | In a tau-critical H with tau = T+1 every edge E has a T-set X_E whose *only* missed edge is E (X_E is a transversal of H - E) [proved by hand, standard]. Gives requests with forced answers. | The set-pair inequality bounds |H| <= C(k+T,k), not tau/k. |
| Shifting / compression | — | Shifting can decrease tau ({12,34} -> {12,14}) [proved by hand]; Zykov-type cloning breaks k-uniformity. No known symmetrisation preserves (7,2), uniformity and tau together. |
| Flag algebras / Razborov SDP | The template LP of 1.6 is the analogue of a finite flag computation. | No density limit: in the extremal family a random edge misses a fixed T-set with probability exp(-Omega(k)), so edge-configuration densities do not see tau; the ground set is unbounded. |
| Local-vs-global chromatic number (Erdős–Hajnal type) | tau(H) = chromatic number of the hypergraph M_H of minimal empty-intersection subfamilies; (p,2) = every p-vertex induced subhypergraph of M_H is 2-colourable [proved by hand]. | Topological tools (Lovász, Dol'nikov, Kříž) bound chi from *below*; we need an upper bound. |
| Entropy / Shearer | — | The counting side (Mills) is already linear and tight; the hard direction is existence of seven edges, not counting. |
| EFKT 1992 / Kostochka 2002 / FKW 1999 | Could not access full texts (paywalled). Only the values above were confirmed. | — |

## 3. The attempted argument: shape-optimised completion of a good triple

Fix a good triple. Points of W fall into atoms A_i = E_j ∩ E_l (label {i}) and U_i (label {j,l}). Four further requests
X_4..X_7 ⊆ W add J(x) = {j : x in X_j} to the label. By 1.1 the answering edges E_4..E_7 (anything missing the requests)
complete a violation iff
> J(x) ∩ J(y) ≠ ∅ whenever x ∈ A_i, y ∈ A_j (i ≠ j), or x ∈ A_i, y ∈ U_i.

(Other pairs already share one of 1,2,3.) Minimising L = max_j |X_j| is a MILP (`compute/fresh_b/shape_lp.py`).
If L <= T, tau > T contradicts (7,2).

**Lemma 3.1 (sparse shape).** [proved by hand] X_4 = A_1∪A_2∪A_3 ∪ U_1'∪U_2'∪U_3', X_{4+i} = A_i ∪ (U_i \ U_i') with
U_i' ⊆ U_i arbitrary. If all four sizes are <= T then (7,2) fails. Proof: a 2-point transversal {x,y} of E1,E2,E3 has,
say, x ∈ A_1, y ∈ E_1; E_4 and E_5 miss x, so y ∈ E_1∩E_4∩E_5; but E_1 = U_1∪A_2∪A_3, E_4 misses A_2, A_3, U_1' and E_5
misses U_1 \ U_1'. Symmetric for A_2, A_3.
Optimising U_i': a violation exists as soon as
> sum_i ( a_j + a_l - a_i - (k - T) )_+  <=  4T - 3k.

For T >= 3k/4 and a symmetric triple this is just S <= T.

**Lemma 3.2 (hybrid shape).** [proved by hand] Split A_i = P_i ⊔ Q_i, Q = Q_1∪Q_2∪Q_3. Requests
X_5 = P_1∪P_2∪P_3, X_6 = P_1∪Q∪U_1, X_4 = P_2∪Q∪U_2, X_7 = P_3∪Q∪U_3. If all are <= T then (7,2) fails.
Proof: x ∈ P_1: E_5, E_6 miss x and E_1∩E_5∩E_6 = ∅ (E_5 misses P_2,P_3; E_6 misses Q_2,Q_3,U_1). x ∈ Q_1: E_4,E_6,E_7
miss x; E_6 misses Q_2,Q_3,U_1, E_4 misses P_2, E_7 misses P_3. The cases x ∈ P_2,Q_2,P_3,Q_3 are identical after
permuting (4,6,7). Symmetric triple: |P_i| = (k + S/3)/5 gives all four requests equal to (3k+S)/5.

**Lemma 3.3 (Fano shape = Fact 3).** [proved by hand] Halve each A_i = A_i^0 ⊔ A_i^1, give each U_i-point one request from
each of the two pairs opposite A_i; all four requests have size |W|/2 = (3k-S)/2.

**3.4 MILP output.** [numerical: HiGHS MILP, floating point; the three upper bounds are the hand-proved lemmas, the
matching lower bounds are solver output only] Symmetric triples (`out_sym.txt`, S in steps of k/24):
L*/k = 3/4 on [0, 3/4]; (3+S/k)/5 on [3/4, 9/7]; (3-S/k)/2 on [9/7, 3/2]. Maximum 6/7 at S = 9k/7.
So IF a symmetric good triple were always available, non-adaptive completion would give tau <= 6k/7 + O(1) and no
more. The constant coincides with the unrefereed 2026 claim, which suggests (not checked) [heuristic] that the claim
uses a shape of this kind. For lopsided triples L* exceeds 6/7 (addendum), so this is NOT by itself a proof of 6k/7.
Lopsided triples: see `out_grid8.txt` (grid of step k/8) and the addendum below.

**3.5 Where it breaks.**
1. The triple is only partly ours. Frankl iteration gives a_1 <= k - T and lets us forbid T - a_1 further points of
   E_2 △ E_3 to E_1, so S <= 2k - T; the adversary then picks (a_2, a_3). At T = 3k/4 the extremal-looking answer
   (k/4, k/2, k/2) has S = 5k/4, inside the window T < S < 3k - 2T where neither Lemma 3.1 nor 3.3 applies, and it is
   lopsided, where Lemma 3.2 degrades (hand computation: hybrid needs L >= 11k/12 there; Fano gives 7k/8).
2. Completion is non-adaptive. In the complete family on 7k/4 - 1 points every good triple has S >= 5k/4 + 1 and
   L* >= 3k/4, so the window cannot be closed by any triple-independent design; the gain must come from choosing each
   request after seeing the previous answer (the answer's trace on W refines the atoms) and from using 1.4 / Fact 4-type
   arguments when answers stay inside a small set.
3. The MILP has only the three anchor edges fixed. Anchoring on two edges or on a good quadruple gives other atom
   structures; these were not run.

## 4. Single most decisive next step

Run the shape MILP **adaptively and over the adversary's feasible triples**: stage 1, minimum-intersection pair plus our
choice of E_1's request; stage 2, the adversary's (a_2,a_3) subject to Fact 3, Fact 5, Lemma B and Lemma 3.1's new
constraint; stage 3, requests X_4..X_7 chosen one at a time, each after the previous answer's trace on the atoms, with
the label family free to be any intersecting family on [7] rather than Fano. The value of that finite game is the best
bound this method can give. If it is 3/4 the conjecture follows; if it stalls above 3/4, its optimal adversary strategy
is an explicit multi-profile template (1.6) to test as a counterexample — single-profile ones are excluded by 1.5.

## Addendum: lopsided grid

[numerical: HiGHS MILP, grid step k/8, `compute/fresh_b/out_grid8.txt`; L* = optimum over ALL shapes, in units of k]

| (a_1,a_2,a_3)/k | S/k | L*/k | Fano (3-S)/2 |
|---|---|---|---|
| (1/4,1/4,1/4) | 0.75 | 0.7500 | 1.125 |
| (1/8,1/4,1/4) | 0.625 | 0.7917 (= Lemma 3.1 threshold exactly) | 1.1875 |
| (1/4,3/8,3/8) | 1.0 | 0.8333 | 1.0 |
| (3/8,3/8,1/2) | 1.25 | 0.8500 | 0.875 |
| (1/4,3/8,5/8) | 1.25 | 0.8542 | 0.875 |
| **(1/4,1/2,1/2)** | 1.25 | **0.8750** | 0.875 |
| (1/8,1/2,1/2) | 1.125 | 0.8750 | 0.9375 |
| (0,1/2,1/2) | 1.0 | 0.9000 | 1.0 |
| (0,0,3/4) | 0.75 | 1.0000 | 1.125 |

Reading:
* For the triple the Frankl iteration naturally produces near the extremal family, (k/4, k/2, k/2), the optimum over
  all shapes is 7k/8 — exactly the Fon-Der-Flaass–Kostochka–Woodall constant, and Fano is already optimal there.
  Non-Fano shapes help only for balanced or sparse triples.
* L* is not a function of S: lopsidedness costs up to k/4 at fixed S. Triples with a disjoint pair (a_1 = 0) are the
  worst for this anchoring and must be handled by a different anchor (two disjoint edges force every other edge to
  meet both, a bipartite rectangle-covering game).
* Lemma 3.1's inequality reproduces the MILP value exactly at every sparse grid point checked ((1/8,1/8,1/4),
  (1/8,1/4,1/4), symmetric S <= 3/4), so in the sparse regime the sparse shape is optimal [numerical agreement].
* All MILP values here are floating-point solver output on a coarse grid; none is a certified lower bound.
