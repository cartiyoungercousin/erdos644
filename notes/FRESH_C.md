# FRESH_C — constructions attack on Erdős #644 (fresh eyes, ~1 hour)

Goal: a (7,2)-family with tau >= (3/4 + c)k. Outcome: **no counterexample found**; instead a
clean structural obstruction (Lemma 3) that explains why every "counting-certified"
construction is capped at exactly ceil(3k/4), and a sharp description of what a counterexample
must look like (Corollary 4). Code: `compute/fresh_c/`.

Tags: [proved by hand] / [computed exact] (exact MILP in the stated model) / [heuristic].

Notation: for edges A_1..A_7 and a point x, M(x) = {i : x not in A_i}; deg(x) = 7 - |M(x)|.

---------------------------------------------------------------------------------------------

## 1. Main structural result: the 5-fold-point barrier

**Lemma 3 (top-degree requests) [proved by hand].**
Let H be k-uniform with tau(H) > T, where 4T >= 3k. Then H contains edges A_1..A_7 such that
every point lies in at most 4 of them.

*Proof.* Request strategy: A_1 arbitrary; for i >= 1 let S_{i+1} be T points of highest current
degree (w.r.t. A_1..A_i) and let A_{i+1} be an edge missing S_{i+1} (request principle).
Let N_j(i) = #points of degree >= j after i edges, r = k - T (so 3r <= T).
A point is promoted to degree >= j+1 at step i+1 only if it had degree exactly j and is
outside S_{i+1}; since S_{i+1} is a top-T set, the number of such promotions is
<= max(0, N_j(i) - T), and trivially <= k. Hence
- N_2(2) <= k - T = r;
- N_3(3) <= max(0, N_2(2) - T) = 0,  N_2(3) <= r + k;
- N_3(4) <= N_2(3) - T <= 2r,        N_4(4) = 0;
- N_4(5) <= max(0, N_3(4) - T) = 0 (2r <= T),  N_3(5) <= 2r + k;
- N_4(6) <= N_3(5) - T <= 3r,        N_5(6) = 0;
- N_5(7) <= max(0, N_4(6) - T) = 0   because 3r <= T.  ∎

**Corollary 3a [proved by hand].** Say H has property (7;5) if every 7 edges have a point in
at least 5 of them. Then tau(H) <= ceil(3k/4). This is *tight*: the complete family on
ceil(7k/4) - 1 points has (7;5) (sum of degrees 7k > 4n) and tau = ceil(3k/4).

**Corollary 3b (single/multi-measure certificates) [proved by hand].** If for every 7 edges there is
*some* weight mu >= 0 on V (allowed to depend on the 7-tuple) with sum_i mu(A_i) > 4 mu(V), then a
5-fold point exists, so tau <= ceil(3k/4). In particular: threshold families
{A : mu(A) > (4/7) mu(V)}, families "dense in one of several blocks" certified by per-block
counting, and every block-symmetric family with a *convex* profile set (by separating the profile
set from the box {a_j <= (4/7) n_j}; if the profile set meets the box, 7 equal-profile edges in a
blockwise Fano blow-up are a bad tuple) — all are capped at 3k/4.
Equivalently (minimax): tau > ceil(3k/4) forces a probability distribution on edges under which
every point has edge-degree <= 4/7 ("4/7-spread").

**Corollary 4 (what a counterexample must look like) [proved by hand].**
For a 7-tuple with max degree <= 4, a 2-cover {x,y} needs deg x + deg y >= 7, so:
*a max-degree-<=4 tuple is 2-coverable iff there is a 4-fold point x (edge set I, |I| = 4) and a
point y lying in all three edges of the complementary triple [7] \ I.*
So in any (7,2)-family with tau > ceil(3k/4) — in particular the FKW parity example with
tau = 3k/4 + 1, and any counterexample — the tuples produced by Lemma 3 are covered **only** by
such complementary (4,3) pairs. Moreover in the top-degree game all (4,3) conflicts are created at
step 7: after six edges, the adversary wins iff the set
  D = {deg-4 points} ∪ {deg-3 points with edge-triple J ⊂ [6] whose complementary triple [6]\J
      also has a common point} ∪ {deg-2 points with pair J whose complement [6]\J is a realized 4-set}
has |D| <= T. A counterexample is exactly a family that forces |D| > (3/4+c)k against every
6-edge play; the six-edge configuration must be rich in *complementary realized triples*.

## 2. Other necessary conditions found

**Lemma 2 (link condition) [proved by hand].** If H is (7,2) then for every edge A the family
{B in H : B ∩ A = ∅} is 6-wise intersecting (an edge A plus six edges disjoint from A with empty
common intersection is not 2-coverable: one point is spent on A). This "6+1 star" is the pattern
that the MILP adversary uses most often against two-type families on n >= 2k points.

**Box condition [proved by hand].** In a block-symmetric family (blocks of sizes n_j k, edges = all
k-sets with profile in P) no profile may satisfy a_j <= (4/7) n_j for all j. So every edge is
> 4/7-dense in some block ("types"); 7 edges of one type are always fine, mixed types are the
whole issue.

**Random sparse families fail [heuristic, first moment].** A random family just dense enough that
every (n-T)-set contains an edge (p ≈ n / C(n-T,k)) contains bad 7-tuples through every edge:
e.g. n = 2k, T = 0.8k: log-count of bad completions of a fixed edge ≈ (6.66 - 1.39)k versus
6·log(1/p) ≈ 3.24k. (7,2) must come from structure, not sparsity.

## 3. Computation: block-symmetric ("profile") families, scale-free MILP

Model: V = V_1 ∪ ... ∪ V_m, |V_j| = n_j k; H(P) = all k-sets with profile in P (union of boxes).
`profile_milp.py`:
- `bad7`: exact MILP for "exist 7 edges of H(P) with pairwise-intersecting M-family"
  (63 binaries encode an arbitrary maximal intersecting family on [7]; w[j][S] = measure of
  points of block j with M(x) = S). Feasible ⇒ H(P) is not (7,2) for large k.
- `tau`: exact MILP for the transversal number of H(P) (in units of k).

Results [computed exact, in this model]:
- Sanity: one block, complete family: not bad at n = 1.70, 1.74; bad at n = 1.75 (Fano), 1.80.
  This also re-derives "every intersecting family on [7] has fractional cover <= 7/3".
- Two symmetric blocks (size h each), two interval types "a_j >= alpha in own block"
  (tau = min(2(h-alpha), 2h-1)): **all tested parameter points with tau >= 0.76 are bad**:
  (h,alpha) = (1.15,.77), (1.2,.81) [tau .76,.78; broken by the 6+1 star];
  (0.9,.52), (0.95,.55), (0.95,.57), (0.98,.57), (0.98,.60), (0.99,.60) [tau .76–.82; n < 2k,
  broken by 6+1 or 5+2 type splits with non-Fano intersecting families].
  Also (1,.6), (1,.68), (1.05,.71), (1.08,.73) (tau .64–.80) are bad.
- `cegar2.py` (exhaustive search over *all* discrete two-block profile sets on a 0.05 grid, T = 0.76,
  MILP-witness-driven pruning): for n = (1,1) all 29 candidate profile sets examined were bad before
  the 240 s budget ran out (search not exhausted); remaining block sizes not run. `scan2.py` was
  stopped unfinished with no unbroken family reported. Inconclusive as an exhaustive statement.
- `lemma3_sim.py` [numerical sanity check of Lemma 3]: top-degree requests with T = ceil(3k/4) against
  greedy / random / mixed responders, k in {4,...,30}, n from k+T to 3k: 8820 plays, max degree
  never exceeds 4; with T = 5 < 3k/4 (k = 8, n = 13) the greedy responder forces a 5-fold point.

No family with tau > 3k/4 + O(1) survived any exact check. **Best verified construction remains
the known one (tau/k -> 3/4).**

## 4. Why constructions fail — summary

Every natural way to *guarantee* 2-covers (pigeonhole on a small ground set, weight thresholds,
density in a block, any mixture of linear counting certificates) produces a 5-fold point, and
Lemma 3 shows 5-fold points cannot be forced once tau > ceil(3k/4): the top-degree request game
spreads 7 edges with max degree 4. Beating 3/4 therefore requires a family in which every
"flat" 7-tuple (max degree 4) has a 4-fold point and a point in the complementary triple — a
genuinely non-counting, Fano-avoiding incidence structure. Block-symmetric families with two
types do not provide it (computed), because the adversary can place edges freely inside blocks.

## 5. Most decisive next step

Analyse the **six-edge endgame** of Lemma 3: bound |D| (Corollary 4) for the top-degree strategy
(or a refinement that also keeps complementary triples unrealized). Either
(a) prove |D| <= 3k/4 + o(k) is always achievable — this would prove f(k,7) = (3/4+o(1))k — or
(b) find the six-edge configurations maximising |D|; these are the only possible seeds of a
counterexample and tell exactly which incidence structure (many complementary realized triples
among 6 edges with max degree 4 and deg-4 mass <= 3(k-T)) a construction must have.
(b) is a finite LP/MILP over point-types S ⊂ [6] (64 types) with the game constraints, directly
computable with the `profile_milp.py` machinery.

---------------------------------------------------------------------------------------------

## 6. Six-edge endgame (follow-up requested by coordinator)

Code: `compute/fresh_c/endgame.py` (model + exact MILPs), `endgame_runs.py`, `endgame_runs2.py`,
`endgame_runs3.py` (experiments).

### 6.1 The exact blocking set D (correction of §1, Cor. 4) [proved by hand]

Type of a point = J ⊂ [6], the set of edges among A_1..A_6 containing it. Call a type *realized* if
at least one point has it; let U = up-closure of the realized types. For any A_7 the 7-tuple is
2-coverable iff some y ∈ A_7 (type J_y) and some point x (type J_x, any point, x = y allowed) have
J_x ∪ J_y ⊇ [6]. Hence A_7 must avoid exactly

    D = { points whose type J satisfies [6] \ J ∈ U },   and the requester wins iff |D| <= T
        (and type [6] is not realized: otherwise even fresh points are forbidden).

D is an up-set of types. Differences from the earlier informal D: (i) deg-5/6 points are always in
D; (ii) a deg-4 point is in D iff the complementary *pair* of edges intersects (in the game this is
always the case: T < k means no edge can be fully blocked, so every pair gets a common point);
(iii) deg-3 / deg-2 / deg-1 points are in D iff the complementary triple / 4-set / 5-set is
contained in a realized type. "Realized" needs ONE point, not positive mass.

### 6.2 Scale-free game model

State after i edges: masses m[J] (units of k) plus a realized flag per type. Round i+1: requester
chooses s[J] <= m[J], sum <= T; adversary chooses y[J] <= m[J] - s[J] and fresh mass, total 1.
Type J ∪ {i+1} becomes realized iff m[J] - s[J] > 0 (one unrequested point suffices), with mass y[J].
Zero-mass realized types cost o(k) to request, so they are always fully requested (never promoted).
Consequence [proved by hand]: **to keep a type unrealized the requester must request ALL the mass
of every type it could be promoted from** — realization is a combinatorial (0/1) resource, mass is
the budget. This is what makes the game hard for degree-counting strategies.

`endgame.py` solves exactly (MILP, tolerance 1e-4 on "positive") the best response of one player
when the other follows a fixed priority policy (greedy fill in a given order of types).
A full free-vs-free solution (4 nested min-max levels over ~60 continuous dimensions) was NOT
obtained in the time box.

### 6.3 Results [computed exact, for the stated policies]

Soundness check (requested): adversary = complete family on a ground set of mass N (degree-greedy
responses), requester free.
- N = 1.745, T = 0.74 (tau = N-1 > T, N < 7/4): min mass(D) = 0.78 > T — adversary wins. ✓
- N = 1.77, T = 0.76: min mass(D) = 0.72 <= T — requester wins, by steering into a Fano blow-up
  (three 4-types of mass 0.24, four 3-types of mass 0.26). ✓

Requester restricted to top-degree (fixed tie-break order; five variants incl. ties left to the
adversary), adversary free: **the adversary wins at every T tested (0.74, 0.76, 0.85, 0.875, 0.95)
with mass(D) ≈ 2.0–2.2**, i.e. essentially all points end in D. Mechanism (T = 0.76 trace):
A_2 meets A_1 in o(k); the fixed-order requester wastes budget on old deg-2 types, leaving the new
pairs 14, 24, 34 unblocked, so deg-3 mass before round 6 is 0.84 > T; an unblocked sliver of 345 and
245 realizes the 4-sets 3456, 2456 with zero mass, which puts the heavy deg-2 types 12, 13 in D, and
every heavy triple has a realized complementary triple. So Lemma 3's strategy by itself is useless
for the endgame regardless of T: **any winning requester must choose requests by realization
pattern, not by degree.** [computed exact]

Requester free, adversary degree-greedy on ground set N ∈ {1.8, 2.0, 2.5, ∞}, T = 0.76: requester
wins every time with mass(D) = 0.72 = 3(1 - T), always by steering the greedy adversary into a
weighted Fano blow-up of total mass 7(1-T) (e.g. by requesting only half of A_1). Against the
low-degree-first adversary on N ∈ {1.8, 2.0, 2.5} the requester also wins (mass(D) = 0.72, 0.24, 0).
So simple adversary policies do not give a counterexample seed; against steerable adversaries the
requester's margin is exactly T - 3(1-T) = 4T - 3, positive iff T > 3/4. [computed exact]

### 6.4 Status of the coordinator's question

**Undecided.** Neither side's certificate was found:
- no requester policy that beats every adversary at some T < 1 (all fixed-priority policies lose);
- no adversary policy that beats every requester at T = 0.76 (both tested policies lose), hence
  **no counterexample seed** and nothing to feed into the block-symmetric MILP.
What is established: the correct D; the zero-mass realization rule; the top-degree requester loses
the endgame at all T; steerable adversaries lose with margin 4T - 3.

### 6.5 Next step

A genuine game solver for the free-vs-free endgame. Two workable routes:
(a) skeleton search: the requester's decision each round is "which positive types to block fully"
    (finite) plus an LP split of the remaining budget; the adversary's is "which unblocked types
    get mass" plus an LP. Alternating cut generation on the last two rounds (round 6 has a closed
    form given the block set) and enumeration of skeletons for rounds 3–5;
(b) encode an adaptive requester strategy of FKW type (the proof of tau <= 7k/8 must be such a
    strategy) as a state-dependent policy and compute the adversary's exact best response; then
    tighten it. The smallest T at which some adaptive requester policy survives the adversary MILP
    is a rigorous upper bound for f(k,7)/k, and the surviving adversary responses just below that T
    are the seeds to test.

---------------------------------------------------------------------------------------------

## 7. Game solver for the six-edge endgame, and explicit Fano-steering policies

Code: `compute/fresh_c/game_tree.py` (tree solver), `cegar5.py` (counterexample-guided growth of the
adversary's round-5 menu), `fano_steer.py` (explicit Fano-template policies), `verify_seed.py`.
Logs: `cegar5_T076_N18_{lo,hi}.log`, `tree_T07*_N*.log`.

**Scope, stated plainly.** A solver in which BOTH players are unrestricted was not achieved. What was
built is one-sided exact: the requester is completely free and adaptive; the adversary plays the
complete family on a ground set of mass N (slack sigma = N - T - 1: after each request he must take
mass 1 from the unrequested 1 + sigma, i.e. he chooses which sigma to omit), restricted in rounds 2–5
to a finite menu of omission rules, with round 6 and all realization flags exact. One MILP gives
z* = min over requester trees of max over menu leaves of (mass(D) - T). z* > 0 would be a rigorous
"this adversary beats every requester"; z* <= 0 only says the requester beats that menu. The planned
enumeration of the requester's block-sets with symmetry pruning was not implemented (the MILP
branches on them instead). The machine was heavily loaded by unrelated jobs, and trees with more than
one or two leaves did not solve to optimality inside 150–200 s, so menus stayed tiny.

### 7.1 Why bounded ground sets are the right adversary [proved by hand]

If the adversary never leaves U = A_1 ∪ A_2 (mass 2 - |A_1∩A_2| >= 1 + T) he has zero slack, his
replies are forced complements, and a weighted Fano blow-up of U (three classes of mass h, four of
mass (1-2h)/2, lines = requests) gives mass(D) = 3h <= 3(1-T). This is the mechanism behind every
"3(1-T)" below. Non-adaptive Fano requests fit a ground set N iff 3N/7 <= T, and the
"first edge arbitrary, then Fano" strategy iff (N-1)/3 + 1/2 <= T. So a dangerous adversary needs
N > max(7T/3, 3T - 1/2) (N > 1.78 at T = 0.76; N > 1.84 at T = 0.78) and must use his slack well.

### 7.2 Results of the tree solver [computed, MILP float tolerance; not rational-certified]

| T | N | adversary menu (rounds 2–5) | result |
|---|---|---|---|
| 0.74 | 1.745 | take-high-degree rule, 1 item/round | z* = +0.04 optimal: adversary wins (control ✓; equals 3(1-T) - T) |
| 0.76 | 1.77 | same | z* = -0.04 optimal: requester wins, mass(D) = 0.72 = 3(1-T) (control ✓) |
| 0.76 | 1.80 | same | z* = -0.04 optimal: requester wins, mass(D) = 0.72 |
| 0.76 | 1.80 | take-low-degree in rounds 2–4; round 5 ∈ {take-high, take-low} | requester tree with mass(D) = 0.72 on both leaves (feasible ⇒ rigorous win vs this menu); and with his round-5 request fixed, EVERY "omit type J first" round-5 reply (both tails), with exact round 6, still gives 0.72 |
| 0.76 | 1.80 | take-high in rounds 2–4; round 5 ∈ {take-high, take-low} | UNRESOLVED at the 200 s limit (incumbent +0.22, bound -0.44) |
| 0.74 | 1.745 | 2,2,1,1 items | unresolved at 150 s (control not completed at this size) |

| 0.76 | 2.00 | take-high-degree rule, 1 item/round | z* = -0.04 optimal: requester wins, mass(D) = 0.72 |
| 0.78 | 1.86 | same | z* = -0.12 optimal: requester wins, mass(D) = 0.66 = 3(1-T) |
| 0.78 | 2.00 | same | z* = -0.12 optimal: requester wins, mass(D) = 0.66 |

At T = 0.78 only these single-rule menus were run (no branching menus).

So far **no menu adversary beats the free requester at T = 0.76**, and whenever the solve finished the
requester's value is exactly 3(1-T) — including on N = 1.80, where neither non-adaptive Fano
(needs 0.771) nor first-edge-then-Fano (needs 0.767) fits in T = 0.76. That last point is the one
piece of new evidence: adaptivity recovers 3(1-T) beyond the range of the two known strategies, at
least against rule-following adversaries. It is NOT evidence about optimal adversaries: the menus
here are one or two rules deep.

### 7.3 Explicit Fano-steering policy: beaten [computed exact; configuration checked in rationals]

Policy tested (12 variants: 4 labelings × 3 extras rules): edges labelled by Fano points, pairs =
lines through the 7th point; each round first request every type whose promotion would contain a
transversal line (the mandatory Fano-template blocks), then spend the rest in a fixed priority order
(by degree / partner edge first / pair-containing types first). The adversary's exact best response
beats all 12 at T = 0.76 and at T = 0.90, with mass(D) >= 2. Seed configuration (T = 19/25, exact):

    A_1 = A_4 = A_5 = X,  A_2 = A_3 = A_6 = Y,  |X| = |Y| = k,  |X ∩ Y| = O(1);
    types 145 and 236 of mass 1 each, realized family ⊇ {12, 23, 1456, 236, 145};  mass(D) = 2 > T.

The adversary simply returns an old edge again whenever the fixed order leaves it unrequested. This
is not a counterexample seed (three distinct edges only; it does not extend to a (7,2)-family with
large tau — X, Y disjoint forces everything else to meet both). Its content is negative: **a
state-independent priority order cannot implement Fano steering; a correct strategy must split the
budget across all existing edges as a function of the current masses.** No explicit strategy with a
proof of mass(D) <= 3(1-T) against all adversaries was obtained, so there is no candidate theorem to
hand over yet. Note also (counting, by hand): against nearly-disjoint edges the pure Fano template
fails for T < 4/5 (after two disjoint edges the five unrequested lines carry total mass >= 4), while
the true terminal condition D is trivially fine there (D = ∅) — the winning strategy cannot be
"Fano only"; it must switch template with the amount of overlap the adversary offers.

### 7.4 Next step

(1) Rerun `cegar5.py` and deeper menus on an idle machine with a 30–60 min limit per MILP; extend the
CEGAR to rounds 3–4 (same code path: `Tree(start=...)` evaluates a candidate reply exactly given the
requester's request). (2) Read the requester's winning trees on N = 1.80 (they are explicit rational
request tables per node) and extract the rule that produces 3(1-T) off the Fano range — that rule,
not the fixed-priority template, is the candidate strategy to formalise. (3) For certification,
replace the float MILP at the leaves by exact LPs once the 0/1 skeleton is fixed.

---------------------------------------------------------------------------------------------

## 8. Phase 1 result: the 3(1-T) rule is FALSE against a real adversary (hand proof + exact check)

Code: `compute/fresh_c/waste_check.py`. **Bottom line: in the seven-request game (all seven replies
must be used) the adversary wins for every T < 4k/5 [proved by hand, exact, discrete], and for every
T < 5k/6 [computed exact].** No adaptive rule can keep mass(D) <= 3(1-T) against every adversary; the
3(1-T) values of §6–§7 were produced only because the tested adversaries never "wasted" an early edge.
The theory twin should not try to prove the endgame claim as stated.

### 8.1 What the winning tables show (rule extraction) [read off the logged runs]

- Every recorded requester win ends in the same pattern: a weighted Fano blow-up with three 4-types
  P_b ∪ P_c of mass h = r (pairs P_1,P_2,P_3 a perfect matching of [6]) and the four transversal triples
  of one parity, mass (1-2r)/2 each; total mass 2 - r = 1 + T; D = the three 4-types = exactly Lemma 3's
  degree-4 points (the coordinator's hint is correct). E.g. T = 0.76, greedy adversary: final types
  234, 135, 126, 456 (0.26 each) and 1245, 1346, 2356 (0.24 each), pairs (14)(25)(36).
- Blocking pattern: each round the request is a Fano line of the current blow-up (one 4-type class
  plus two triple classes, mass 1 - h = T), i.e. all points whose class does not contain the new edge;
  no complementary pair of types is ever realized.
- **In every recorded win A_1 ∩ A_2 has mass between 0.24 and 0.5** (0.5, 0.48, 0.38, 0.24): the
  requester obtains this either from the adversary's own rule (greedy takes old points) or, on a bounded
  ground set, by requesting the pool so that the reply must overlap A_1. The pattern needs the whole
  play to live on a ground set of mass 1 + T (zero slack, replies forced).
- The rule, where it applies [proved by hand, = non-adaptive Fano]: if the adversary's replies stay
  in a ground set of mass 1 + T + s, take classes of mass r + s (three) and (1 - 2r - s)/2 (four);
  every line has mass T, so all requests fit and mass(D) <= 3(r + s). This is <= T iff s <= (4T-3)/3.

### 8.2 The breaking adversary [proved by hand]

**Theorem 8.** Let T < 4k/5. In the seven-request game the adversary has a strategy after which the
seven replies are 2-coverable, whatever the requester does.

*Strategy.* A_1 arbitrary. A_2 := k fresh points (disjoint from A_1; no request can prevent this).
Fix Z ⊂ A_1 with |Z| = k - T, put X = A_1 \ Z (|X| = T), Y = A_2, V' = X ∪ Y (|V'| = k + T).
For t = 3..6 answer request S_t with any k-set B_t ⊂ V' \ S_t (exists since |V' \ S_t| >= k).

*Proof.* Put P_t = X \ B_t, Q_t = Y \ B_t; then |P_t| + |Q_t| = |V' \ B_t| = T, so |P_t||Q_t| <= T²/4.
A pair (x,y) ∈ X × Y covers A_1 (x), A_2 (y), and covers B_t unless (x,y) ∈ P_t × Q_t. Let E_X (E_Y) be
the x (y) lying in some pair not in any P_t × Q_t; such pairs cover all six edges, so E_X ∪ E_Y ⊂ D.
Every pair outside E_X × E_Y lies in some P_t × Q_t, hence Tk - |E_X||E_Y| <= 4·T²/4 = T².
If |E_X| + |E_Y| <= T then |E_X||E_Y| <= T²/4 and Tk <= 5T²/4, i.e. T >= 4k/5. So for T < 4k/5,
|D| >= |E_X| + |E_Y| > T, the 7th request cannot contain D, and the adversary answers with a k-set
containing some x ∈ D \ S_7 (rest fresh): x and its partner cover all seven edges. ∎

All replies lie in the family {A_1} ∪ (all k-subsets of V'), which has tau = T + 1 > T, so this is a
legitimate responder. (That family is of course not (7,2): the requester is beaten only because he is
forced to keep the two wasted edges A_1, A_2.)

*Exact check* [computed exact; requester completely free, replies forced, one MILP, ~1 s each]:
min over requesters of mass(D) - T = +0.1867, +0.1467, +0.1067, +0.0667, +0.0267, +0.0067 at
T = 0.74, 0.76, 0.78, 0.80, 0.82, 0.83, and -0.0002, -0.02 at T = 0.8334, 0.84. I.e. the requester's
best is mass(D) = 5/3 - T and this adversary wins exactly for T < 5/6. Discrete sanity instance
k = 25, T = 19: 475 cross pairs, at most 360 killed, 115 > 90 forces |D| >= 22 > 19.

### 8.3 Other deviations examined by hand (why slack is the issue) [proved by hand]

- Cover-graph form of the game: let G_j be the graph of pairs {x,y} covering the first j edges and D_j
  its non-isolated points. Then G_{j+1} = edges of G_j meeting A_{j+1}; D_{j+1} = L ∪ N_{G_j}(L) with
  L = A_{j+1} ∩ D_j; only requests inside D_j matter; the requester wins iff some |D_j| <= T.
- Last round: the requester wins from G_5 iff there is C ⊂ D_5, |C| <= T, with |O ∪ N(O)| <= T for
  O = D_5 \ C. For a complete bipartite G_5 = K(X,Y) this is |X| + |Y| + min(|X|,|Y|) <= 2T; for the
  K4/Fano value |X| = |Y| = 1/2 it reads T >= 3/4 — the conjectured threshold again.
- One leaked point is enough to endanger a whole class: a single point of a triple type J makes every
  point of type [6] \ J dangerous. In the K4 pattern on A_1 ⊔ A_2 the mandatory sets at rounds 5 and
  6 have mass 1 > T, and a one-point leak at round 5 already forces mass(D) >= 1 at round 6.
  This is the mechanism Theorem 8 exploits wholesale.

### 8.4 Consequences

1. The seven-request game with no discards has value >= 5/6 (>= 4/5 by hand): it cannot prove
   anything below the level of the known bounds. Lemma 3 / Corollary 4 remain true but the endgame
   cannot be closed inside that game.
2. The right game lets the requester DISCARD replies: he makes m >= 8 requests and wins if some seven
   replies are bad. Against Theorem 8's adversary one discard suffices (drop A_1; the remaining replies
   are forced inside V' of size k + T and a Fano blow-up of V' with A_2 as one line-complement works
   iff T >= 3k/4). With unboundedly many requests this game is equivalent to the conjecture itself
   (a surviving adversary's replies to all T-sets form a (7,2)-family with tau > T).
3. Phase 2 as originally specified (stress-testing the rule in the seven-request game) is settled by
   the above: the rule is broken exactly. Re-scoped Phase 2: the m = 8 (then 9) discard game — state =
   all replies, terminal test = min over 6-subsets of mass(D) <= T — to see whether the adversary can
   still hold a level above 3/4 once wasting an edge is free for the requester to undo.

---------------------------------------------------------------------------------------------

## 9. The discard game with m = 8 requests

Code: `compute/fresh_c/discard.py` (free start, then forced replies), `pivot.py` (scripted pivot play on the
2k-point ground set), `pivot_tree.py` (adaptive switching between rules), `control.py` (per-discard
decomposition). Logs: `control_*.log`, `pivot_m8_*.log`, `ptree_*.log`.

**Game.** The requester makes 8 adaptive requests; he wins iff some 7 of the 8 replies are not 2-coverable.
Implemented terminal test: after 7 replies he chooses which one to discard and needs mass(D) <= T for
the remaining six (the 8th request then contains D). (The other way to win — the first seven replies
already bad — is not modelled; this only weakens the requester.)

**What was and was not solved — read this first.** In every computation below the requester is
completely free and the result is exact for the stated adversary. The adversary, however, is always
*deterministic given a rule*: either forced (zero slack) or a fixed omission rule, with or without
adaptive switching between a few rules. **The unrestricted adversary (any reply avoiding the request)
was NOT solved**, so "the requester wins at T = 0.76 with m = 8 against every adversary" is **not
established**. Sections 6–8 showed twice that wins against rule-following adversaries can vanish
against a real one; the same caveat applies here in full.

### 9.1 Two clarifications about §8

- Theorem 8's hand proof gives an adversary win for T < 4k/5; it is only a lower bound. The exact
  solve against that same adversary gives requester's best mass(D) = 5/3 - T, i.e. the adversary wins
  exactly for T < 5k/6 [computed exact]. Variants do even better in the 7-request game at T = 0.76:
  balanced waste +0.187, "A_1 ∩ A_2 = r" +0.307 (versus +0.147).
- 5/6 is also the one-anchor bound (n-k)/3 + k/2 at n = 2k, and the two disjoint replies do span 2k
  points. But the anchor-Fano template itself is NOT what the requester uses there: with both
  disjoint replies kept, the four mixed lines would need total weight 4 <= 4T. His optimal play at
  T = 0.76 is a different pattern (types 1456, 256, 2346 of mass 1/3 each plus 13, 245, 2345). So the
  values coincide; I could not confirm that the mechanism is the same without the other notes.

### 9.2 Results, m = 8, one discard [computed exact for each listed adversary]

Entries are min over requesters of mass(D) - T (negative = requester wins).

**(a) Free start, then forced replies inside a fixed set V' of (1+T)k points** (per-discard MILPs, all optimal):

| adversary | T = 0.74 | T = 0.76 | T = 0.80 | discard used |
|---|---|---|---|---|
| CONTROL: complete family on (1+T)k points, zero slack, all replies inside | **+0.040 (adversary wins)** | -0.040 | -0.200 | any (all equal) |
| A_1 ∩ A_2 = r, V' = A_1 ∪ A_2 (same family, other start) | **+0.040 (adversary wins)** | -0.040 | -0.200 | reply 1 or 2 |
| Theorem 8 (A_1 = X ∪ Z sticks out, A_2 disjoint) | -0.220 | -0.280 | -0.400 | reply 2 |
| balanced waste (Z split between A_1, A_2) | -0.090 | -0.160 | -0.300 | reply 1 or 2 |

The control behaves as required: the genuine (7,2)-family wins at 0.74 with value 3(1-T) - T and loses
at 0.76. The Theorem-8 adversaries lose even at 0.74: their family {A_1} ∪ (k-subsets of V') is not
(7,2) because of the short edge, and with one discard the requester exposes this.

**(b) Scripted pivot play on the 2k points A_1 ⊔ A_2 (slack r each round)**, rules for replies 3,4,…:
T8 (freeze Z ⊂ A_1, then forced), L (omit lowest degree), H (omit highest degree), LH, HL (alternating),
L4, H4, L5 (one or two slack rounds, then freeze lowest degree and forced).
T = 0.76: requester wins against all eight: T8 -0.28, L -0.28 (both optimal); H <= -0.43, LH <= -0.52,
HL <= -0.28, L4 <= -0.28 (feasible solutions at the time limit, which suffice for "requester wins");
H4, L5 were not run to completion at 0.76. T = 0.80: all six that ran are requester wins (<= -0.40).
T = 0.74 (per-discard, all optimal): the requester also wins against all eight scripts (-0.22 or -0.48),
as he must be allowed to: none of these scripts is a (7,2)-family (two disjoint replies plus a
complete family on 2k points). So the scripted pivots are weak adversaries at every T; only the
control in (a) is a genuine one.
Without a discard (7-request game) T8, L, L4, H4 beat the requester at 0.76 by +0.147.

**(c) Adaptive switching** (`pivot_tree.py`): reply 3 ∈ {Z1 freeze, L, H}, reply 4 ∈ {ZL freeze, L, H},
then L; 7 leaves; requester free at every node and choosing his discard per leaf. Result: UNRESOLVED
at the 1100 s limit at both T = 0.76 (incumbent +0.70, bound -0.88) and T = 0.80 (incumbent +0.56,
bound -1.82). The tree MILP does not scale; nothing can be concluded from these two runs.

### 9.3 Why one discard kills waste-type adversaries [proved by hand]

Discard A_2 and keep the wasted edge A_1 as an *anchor*: inside V' its complement Y has mass 1, so in a
Fano blow-up of V' it may sit opposite a line of weight up to 1, while the five requested lines have
weight <= T. Total line weight is 3(1+T), hence mass(D) = 3(1+T) - 1 - 5T = 2(1-T), which is <= T for
T >= 2/3. This is exactly the computed value (-0.28 at 0.76, -0.40 at 0.80, -0.22 at 0.74). In general,
if all but w replies are forced inside one fixed set of (1+T)k points, 7 + w requests suffice for
T >= 3k/4, and a wasted short edge is a gift once its disjoint partner is dropped.
Also: a single pair covering all eight replies (Theorem 8's method) needs (m-2)T < 4k, i.e. T < 2k/3
at m = 8 — in agreement with the twin; waste-type play is not the binding adversary.

### 9.4 The binding adversary is not solved

The dangerous play is the one the twin describes: all replies are complete-family answers on the 2k
points A_1 ∪ A_2 with slack k - T used *adaptively*. Its three scripted versions above (L, H, switching)
lose, but an adaptive adversary can choose each omission after seeing the request, and no rule of mine
captures that. Hand heuristic only [heuristic, Fano-type requesters]: on 2k points seven edges need
3·2 = 6 units of useful incidence; an anchor supplies 1, each request T, and the adversary can (i) waste
r in the third edge by omitting inside W_1 ∩ W_2 and (ii) place later omissions on points that do not
need the current index. That leaves 3 - r + 4T >= 6, i.e. T >= 4/5 — so at T = 0.76 I expect the
unrestricted pivot adversary to beat the 8-request requester, and 0.80 to be borderline. This is a
prediction, not a result.

### 9.5 Next step

A solver in which the adversary's omission is a free variable in at least the last two or three rounds
(the twin's closed form for the final round removes one level; a CEGAR over omission vectors, as in
`cegar5.py`, can handle one more), applied to the 2k-point pivot play at T = 0.76 and 0.80. Until that
exists, the m = 8 question is open in both directions.

### 9.6 Counterexample-guided loop for the unrestricted adversary (T = 0.76, m = 8, 2k points) — did NOT close

Code `do_loop.py`, log `do_loop_T0.76.log` (first run: `do_loop_T0.76_run1.log`). Pool = reply rules attached
to nodes of the game tree (vertices of the adversary's reply polytope, chosen after seeing the request);
requester free at every node; discards restricted to reply 1 or 2 (the only ones ever optimal in §9.2 —
a restriction on the requester, so "requester wins" statements stay rigorous, an adversary win would have
to be re-checked with all seven discards). Oracle: every single-type-first deviation at every node, valued
by the requester's exact best continuation.

| iteration | pool | requester vs pool (certified lower bound / incumbent) | best single deviation | gap |
|---|---|---|---|---|
| 0 | rule L everywhere (1 leaf) | -0.2800 / -0.2800 (optimal) | +0.2400 at reply 5: "omit type 23 (or 24) first" | +0.52 |
| 1 | + three rules at the reply-5 node (4 leaves) | -0.7600 / **-0.0100** (19-min limit, not optimal) | — | open |

Reading: against the 4-rule pool the requester still has a winning tree (value <= -0.01 < 0, a feasible
solution, hence rigorous), but his margin, 0.28 against the single rule, is now only known to lie between 0.01 and 0.76 — the
MILP did not close, so even this small pool's value is not known. The deviation that hurts is exactly the
twin's pivot: at reply 5 the adversary stops omitting the never-used set Z ⊂ A_1 and omits points of
A_2 ∩ A_3 instead. **No adversary win was found at 0.76 and no certified value was obtained; the
unrestricted m = 8 question remains open.** The tree MILP (≈10^4 variables at 4–7 leaves) is the
bottleneck; a certified loop needs a decomposition (one MILP per branch with the shared prefix
requests as complicating variables) rather than one monolithic model.

## 10. The threshold t*(m) as a function of the number of requests

t*(m) = the smallest T/k at which the requester wins the m-request discard game. Every number below
names its adversary class; **no number is against the unrestricted adversary.**

| m | adversary class | t*(m) | status |
|---|---|---|---|
| 7 | Theorem-8 waste; scripted pivots T8, L, L4, H4 | 5/6 | [computed exact] |
| 7 | balanced waste (Z split between A_1, A_2), then forced | 0.8461… = 11/13 to four digits | [computed exact] |
| 7 | complete family on (1+T)k points whose first two replies meet in exactly k-T points, then forced | **7/8** (sign change between 0.874 and 0.876, value 0 at 0.875) | [computed exact] |
| 8 | all forced classes of §9.2(a) and all eight scripts of §9.2(b) | **3/4** (control: +0.04 at 0.74, -0.04 at 0.76) | [computed exact] |
| >= 9 | same classes | 3/4 | [proved: more requests cannot hurt the requester; below 3/4 the control wins for every m] |
| 8 | scripts + one adaptive fork at reply 5 (the 4-rule pool of §9.6) | <= 0.76 | [computed: feasible requester tree, margin >= 0.01] |
| 8, 9, 10, 12 | unrestricted adaptive pivot on 2k points | **unknown** | not solved |

Observations.
1. The seven-request game has value >= 7/8 already against a genuine complete family (third row): the
   requester cannot recover from a first pair of replies with minimal intersection. So 7/8 — the FKW
   bound — is exactly where the no-discard game stops, and the three seven-request thresholds found
   (5/6, 11/13, 7/8) are the numbers that appear as upper bounds in the literature. Any proof below
   7/8 must use more than seven requests (or information beyond the request principle).
2. Against every adversary I can solve, a single discard brings the threshold straight to 3/4: there
   is no gradual 3/4 + c/m decay in these classes — it is a jump from 7/8 to 3/4 at m = 8.
3. That jump is an artefact of solvable adversaries being forced or rule-following after their start.
   For the adaptive pivot the only evidence is §9.6 (margin shrinking from 0.28 to possibly 0.01 after
   one adaptive fork) and the incidence heuristic. Generalised to m requests the heuristic reads:
   on 2k points seven kept edges need 6 units of useful incidence; an anchor gives 1, a request T, and
   each adversarial omission that the requester can turn to use gives 1 - T. With u usable omissions
   the requester needs T >= (5-u)/(6-u): 5/6, 4/5, 3/4 for u = 0, 1, 2. Extra requests help only by
   raising u (more replies to choose anchors from, re-rolling a wasted reply); the heuristic does not
   say how u grows with m, so it cannot distinguish "t*(m) → 3/4" from "plateau at 4/5". It is also
   not reliable as a bound: it predicts 6/7 or 5/6 at m = 7 where the exact value is 7/8.

**Answer to the trend question: not determined.** The data fit "3/4 for all m >= 8" only against
adversaries that are too weak to matter, and nothing computed so far shows a level above 3/4 at m = 8.
The decisive computation is still the certified value of the m = 8 game against the adaptive pivot
at T = 0.76 and 0.80; it needs a branch-decomposed solver, not the monolithic MILP used here.

---------------------------------------------------------------------------------------------

## 11. Attempt at a certified solver for the m = 8 confined game — NOT achieved

Code: `compute/fresh_c/cert.py` (discard-pattern decomposition), `do_loop.py` (pool loop), `ntable.py`
(values per (T, N) against scripts). Logs: `do_loop_T0.76.log`, `ntable.log`.

**Bottom line.** No certified value of the m = 8 game against the unrestricted confined adversary was
obtained, at T = 0.76 or anywhere else; consequently no t*(9), t*(10) and no N-dependence against that
adversary. What follows is what was tried, why it failed, and what is certified.

### 11.1 Why the loop cannot be certified with the present models

1. *Lower-bound side (requester versus a pool).* The requester's problem against a pool with L leaves
   is one MILP whose LP relaxation is useless: the 0/1 "realized" flags are bounded below only by the
   unrequested mass, so the relaxation makes every flag tiny and the bound stays at the trivial -T
   until essentially all block decisions are fixed. Tried:
   - monolithic MILP, 4-rule fork at reply 5 (4 leaves), T = 0.76, 19 min: incumbent -0.01, bound -0.76;
   - **decomposition over the requester's discard pattern** (`cert.py`: 16 MILPs with the discard of
     every leaf fixed, in parallel, 400 s each): 0 of 16 closed; best incumbents +0.22 … +0.48, bounds
     -0.76 (two at -0.73, -0.63). Fixing the discards does not make the tree easier; the incumbents are
     in fact worse than the monolithic one, so these runs prove nothing in either direction;
   - Benders-type decomposition over the branches with the prefix requests as complicating variables
     was NOT implemented: the branch value is not convex in the prefix requests (the realized family is
     a 0/1 function of which types are fully requested), so ordinary Benders cuts are invalid, and
     integer (combinatorial) cuts amount to enumerating block patterns.
   What is needed is a purpose-built branch-and-bound that branches on the *block pattern* (which
   types are fully requested at each node) and solves an LP at each leaf of that search, with
   dominance pruning. That is a different program from anything here.
2. *Upper-bound side.* A pool of vertex replies is not known to be without loss of generality: the
   requester's continuation value is not quasi-convex in the adversary's omission (averaging two
   continuations unites their realized families). So even a loop that closes over all single-type-first
   deviations certifies only "value against adaptive vertex replies, one deviation deep". A certified
   requester win needs an explicit policy defined on all states and an exact adversary best response
   to it; I have no such policy.

### 11.2 Certified facts gathered on the way

- **Reduction [proved by hand].** In the confined game (replies 1, 2 disjoint, V their union) a requester
  who commits to discarding reply 2 plays exactly the 7-request game on the 2k-point ground set whose
  first reply is A_1 and whose other k points are untouched. Hence value(m = 8 confined) <= value of
  that 7-request game, and it is the latter (5 adaptive adversary replies, last one in closed form) that a
  purpose-built solver should attack first; discard patterns are then unnecessary for a requester win.
- **Two bad templates exist on 2k points, not one [proved by hand].** Besides sub-Fano families, the ten
  blocks of the 2-(6,3,2) design are pairwise intersecting with every index in exactly half of them, so
  ten classes of mass k/5 give SIX replies with no 2-cover on 2k points. A correct requester rule (and
  any rigidity argument) must allow for both templates; the twin's "Fano up-set is the natural one"
  (TWIN §7.3) is not forced.
- Seven-request thresholds 5/6, ≈11/13, 7/8 and the m = 8 control (§10) stand.
- Loop log at T = 0.76 (§9.6): iteration 0 value -0.28 (optimal), best deviation +0.24; iteration 1
  value in [-0.76, -0.01]; the oracle after iteration 1 proposes three more rules at the reply-7 node
  (deviation +0.23). Gap never closed.

### 11.3 Values per (T, N) against scripted adversaries [computed exact; requester free; discards 1 or 2]

See the table appended below (`ntable.log`). Scripts on a ground set of mass N (untouched pool N-1 after
reply 1): reply 2 disjoint ("W"), then T8 / L / H / G as in §9, and PF (never a fresh point).

Table for §11.3 (T = 0.76; value = mass(D) - T, requester free, discards 1 or 2; `ntable.log`; the run was
stopped before the T = 0.80 rows finished):

| script | N = 2 | N = 2.15 | N = 7/3 |
|---|---|---|---|
| W,T8 (disjoint reply 2, freeze Z, forced) | -0.28 | -0.43 | -0.76 |
| W,L (disjoint reply 2, then omit lowest degree) | -0.28 | -0.28 | -0.28 |
| W,H (disjoint reply 2, then omit highest degree) | <= -0.52 | -0.76 | -0.76 |
| W,G (disjoint reply 2, fresh points first) | -0.28 | -0.43 | -0.61 |
| PF (never a fresh point) | -0.04 | -0.04 | -0.04 |

All are requester wins at every N; against these scripts a larger ground set only helps him. As everywhere
in §9–§11, this says nothing about an adaptive adversary.

---------------------------------------------------------------------------------------------

## 12. Which earlier results assumed a restricted adversary; exact small-k solution of the 7-request game

### 12.1 Audit of §6–§11: what kind of adversary each result is against

"Optimistic" = the requester's win or value was obtained against a scripted / menu / vertex-reply
adversary and may disappear against an adversary who mixes (replies that are not corner points of his
reply polytope, or that switch rule after seeing the request).

| result | adversary | status |
|---|---|---|
| §1 Lemma 3, Cor. 3a/3b/4; §2 Lemma 2; §8 Thm 8; §8.3; §9.3; §11.2 reduction | arbitrary (hand proofs) | unaffected |
| §3 block-symmetric families (bad 7-tuple MILP) | the family itself; the 7 edges are chosen freely | unaffected (statement about families) |
| §6.3 control: complete family on 1.745k beats requester at 0.74 | scripted, but the claim is an adversary win | unaffected |
| §6.3 top-degree requester loses at every T; §7.3 Fano-steering policies beaten | adversary FREE (continuous replies), requester scripted | unaffected (rigorous losses of those policies) |
| §6.3 free requester reaches 3(1-T) against degree-greedy / low-degree-first | scripted | **optimistic** |
| §7.2 tree solver: 3(1-T) on N = 1.77, 1.80, 2.00 at T = 0.76, 0.78 | menu of 1–2 corner rules (last round exact) | **optimistic** |
| §8.2 exact value 5/3 - T against Theorem 8's adversary; §10 thresholds 5/6, 11/13, 7/8 at m = 7 | deterministic by definition (forced replies) | exact for those adversaries; as statements about the 7-request game they are valid LOWER bounds on its threshold |
| §9.2(a) m = 8: 3(1-T) / 2(1-T) against forced adversaries; control wins at 0.74 | forced | requester wins **optimistic**; the 0.74 control unaffected |
| §9.2(b), §11.3 scripted pivots, all N | scripted corner rules | **optimistic** |
| §9.6 loop: requester still <= -0.01 against the 4-rule pool | adaptive choice among corner rules | **optimistic** (and not even closed) |
| §10 "t*(m) = 3/4 for m >= 8" | forced + scripted classes only | **optimistic**; only "t*(m) >= 3/4" is solid |

So every piece of "exactly 3/4" evidence above 3/4 is optimistic. The solid facts are: thresholds 5/6,
11/13, 7/8 are lower bounds for the 7-request game; 3/4 is a lower bound for every m; nothing rigorous
bounds the m >= 8 games from above below 7/8.

### 12.2 Exact solution of the simplified game for small k

Game: ground set of 2k points, A_1 = k of them fixed; six requests of at most T points; each reply is ANY
k-subset avoiding the request; requester wins iff the seven edges have no 2-cover. This is exactly the
m = 8 confined game after committing to discard the second of the two disjoint replies (§11.2).
Solvers: `exact7.py` (reference), `exact7.js`/`exact7d.js` (Node ports; identical results), `exact7_naive.py`
(brute force over actual point sets, no reductions).

Exactness. The search works on membership types of the points still in a covering pair, uses only
(i) interchangeability of points of equal type, (ii) "points outside D_j never matter again",
(iii) monotonicity (requests of full size inside D_j; the adversary takes as many points of D_j as he can),
(iv) canonical relabelling of edges, (v) a closed form for the last request. Checks: brute force on
actual sets agrees for k = 2, 3 and every T; the closed form (v) agrees with plain enumeration on every
state of the k = 4, 5, 6 searches; the Python and Node versions agree; a pair-counting prune (a sound
adversary-win certificate) changes no outcome.
