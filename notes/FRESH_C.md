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
