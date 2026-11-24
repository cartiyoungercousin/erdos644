# New paths to 3/4 (research-lead pass, 2026-11-23)

Tags: **[proved by hand]** (short argument given here, not Lean-checked), **[computed exact]**,
**[numerical]**, **[heuristic]**. Notation as in ROADMAP: k, T, t = T/k, good triple (E,F,G) with pair
cells x >= y >= z, S = x+y+z, W = E∪F∪G, |W| = 3k − S. "lex-min anchor" = good triple whose sorted
profile (u,v,w) is lexicographically least (the 11/13 repo's rule; LIT_11_13.md). Code:
`compute/newpaths/check_lemmas.py` (randomized sanity checks of Lemmas B and 3+3; 0 failures in
3000 trials each **[numerical]**).

---------------------------------------------------------------------------------------------

## 0. Verdict in five lines

1. Tie-breakers cannot fix the level-set escape (§1.1). The escape disappears only where the
   family has a *gap*, i.e. where an eps-perturbation of a cell is impossible.
2. The lex-min value u has a natural threshold u* = (2k − T)/3: it is exactly the lex-min profile
   of the complete family K_{(1+t)k}, and exactly the point where the pair-gap window opens
   (§1.2). This gives a trichotomy: **gap regime** u > u*, **complete-like regime** u ≈ u*,
   **sparse regime** u < u*. The two stuck clusters of R1b are the first two: lopsided
   (0.5–0.6, small, small) = gap regime; middle (0.35–0.45, …) straddles u* = 0.392 (t = 0.825)
   … 0.417 (t = 3/4).
3. Gap regime: rigid two-cluster structure, discrete (close/far) invariants, and every model
   family I can build has tau <= 2k/5. This is the place where a clean new lemma valid for ALL
   t > 3/4 looks provable now (Path 1).
4. Complete-like regime: the anchor triple cannot be kept (chi, ROADMAP §2.3); at most one anchor
   edge survives. The right tool is Theorem A's template run on W = anchor union, which has
   exactly the right size (|W| <= (1+t)k iff S >= 3u*), plus a new trace lemma (Lemma B) that
   bounds how far responses can leave W (Path 2).
5. No candidate counterexample: the stuck adversaries are not close to any family I can write
   down (Path 4). I believe the conjecture is true.

---------------------------------------------------------------------------------------------

## 1. Facts established in this pass

### 1.1 Tie-breakers are void in the continuum model  [proved by hand]
Let the anchor minimize Phi, ties broken by Psi. A response whose new triple has Phi' = Phi and
"bad" Psi can be replaced by one with Phi' = Phi + o(1) (move o(k) points), which the rule
allows. So in the k → infinity cell model, (Phi, Psi) and Phi have the same stuck set; the same
holds for lexicographic rules beyond their first coordinate *unless the adversary's cells are
pinned by a gap*. Consequences:
- The (1600,40,1) idea and any "level set + tie-break" rule gain nothing even when implemented
  soundly. Do not spend grid time on them.
- What does help against a level-set move: the new triple is itself a (near-)minimizer, so
  every consequence of minimality (Lemma A, the pair gap below, Lemma B) holds *at the new
  triple and at every triple the adversary ever shows*. The object to study is the family of
  near-minimal triples, not one anchor. The novelty relative to the 11/13 repo (which already
  uses lex-min, non-strict) must come from this multi-round use.

### 1.2 Pair gap and the threshold u*  [proved by hand; the gap itself is (9) of the 11/13 repo]
Let u = largest cell of the lex-min anchor (so every good triple has a cell >= u). If two edges
A, B meet in t0 < u points, request D = (A∩B) ∪ D_A ∪ D_B with |D_A| = |D_B| = k − t0 − u + 1.
The response K gives a good triple (A,B,K) with all cells < u: contradiction. |D| <= T iff
t0 >= 2k − 2u − T + 2. Hence

> **no pair intersection lies in [2k − 2u − T + 2, u).**

The window is non-empty iff u > u* := (2k − T + 2)/3. For K_N, N = (1+t)k, the lex-min triple is
balanced with u = (3k − N)/3 = (2k − T)/3 = u*: the complete family sits exactly at the
threshold (soundness: the window is empty there, as it must be, since K_N has all intersection
sizes). At T = 3k/4: u* = 5k/12, and for u >= k/2 the window is [k − T + 2, k/2), i.e. every
pair is **far** (< k/4) or **close** (>= k/2).

### 1.3 Lemma B (trace lemma)  [proved by hand; randomized check passes]
> Let tau(H) > T, (E,F,G) a good triple with union W, and K ANY edge. Then
> |K ∩ W| > (3T − |W|)/2 − O(1).

Proof. Put c = |K∩W|; if |W| − c <= 3(T − c), partition W∖K into P_1,P_2,P_3 with
|P_i| <= T − c and request D_i = (K∩W) ∪ P_i, responses R_i. Every point misses one of E,F,G;
points outside W miss all three, so they are compatible with everything. Two points of W∖K both
miss K. A point of K∩W misses R_1,R_2,R_3; a point of P_i misses R_i. So E,F,G,K,R_1,R_2,R_3 have
no 2-point transversal. ∎
Sanity: in K_N every edge lies in W. At the stuck anchor (0.5,0.15,0.05), t = 0.825 the bound
is 0.0875k and the adversary's "80% new" answers (trace 0.2k) respect it. At a complete-like
anchor (|W| = 7k/4, T = 3k/4) every edge of H has trace > k/4 on W. It is an instance of the
covering principle (4 anchors, 3 blocks) but is used here as a *global* statement about all
edges, not only responses.

### 1.4 Link lemma and Lemma 3+3  [proved by hand]
- For an edge E, the edges disjoint from E are 6-wise intersecting (a 2-cover of E and six of
  them spends a point on E), hence have tau <= (k−1)/5 + 1. More generally, for R ⊆ E, any six
  edges meeting E only inside R have a common point or a 2-cover with a point in R.
- If A_1,A_2,A_3 is a good triple with union W and B_1,B_2,B_3 are edges whose pairwise
  intersections avoid W, the six edges have no 2-cover (randomized check passes).

### 1.5 Forced moves in the gap regime (u >= k/2, T >= 3k/4 + O(1))  [proved by hand]
Good triples have exactly one or two close pairs (three far pairs contradict u >= k/2; three
close pairs give S >= 3k/2, contradicting the tight-triple lemma). Far pairs exist (request
k/2 + 1 points of E). Let E, K be far, m = |E∩K| < k − T + 2.
(a) Any edge avoiding E∩K is close to E or to K.
(b) Request (E∩K) ∪ (k/2 − m + 1 points of E∖K) ∪ (T − k/2 − 1 points of K∖E): the response K'
    is far from E and close to K, with |K∩K'| <= 3k/2 − T − m + 1.
(c) Request (K∩K') ∪ (E∩K) (affordable: <= 3k/2 − T + 1 <= T): the response K3 is far from K
    and K' (if |K∩K'| = k/2 exactly, add one point of each), hence close to E by (a).
(d) Two edges K', K'' far from E: if E∩K'∩K'' = ∅ they are close; if K∩K'∩K'' = ∅ (both close
    to K) they are far. So they always share a point of E∪K.
Result: four edges in two clusters {E,K3}, {K,K'}, cross pairs far, three of the four triple
intersections empty by construction. The only heavy candidate pairs are
(E∩K3) × (K∩K'); three static requests with labels = the 2-subsets of [3] on both sides cost
(2/3)(|E∩K3| + |K∩K'|) + (small cells), which is <= 3k/4 when both close cells are near k/2.

### 1.6 Two-cluster model families have tau < 2k/5  [proved by hand]
(Correction, see §5.3: a tuple is bad iff ONE side has empty common intersection; threshold and bound unchanged.)
H = all k-subsets of V_1 together with all k-subsets of V_2, V_1∩V_2 = ∅. A 7-tuple with i >= 1
edges in V_1 and 7 − i >= 1 in V_2 is bad iff neither part has a common point, so H is (7,2)
iff max|V_i| < 6k/5, and tau = |V_1| + |V_2| − 2k + 2 < 2k/5 + 2. Relaxing to "at least
(1−gamma)k points in V_i" only lowers this. So the natural realization of the lopsided stuck
adversary is far below 3/4.

### 1.7 Fractional transversals are useless  [proved by hand, sketch]
For a fractional matching of value nu*, four iid edges share a vertex with probability
<= k/nu*^3, while every 7 edges contain 4 through a point; so nu* = tau* = O(k^{1/3}). The
problem lives at tau >> tau*; no LP-rounding route.

---------------------------------------------------------------------------------------------

## 2. Ranked paths

### Path 1 (top; UPDATED by §5: the 2+2 closure below is refuted, the star game of §5.6 replaces it). Lemma G: the gap regime closes at 3/4  — kills the lopsided cluster and the "class may be empty" hole for every t > 3/4
**Key lemma (G).** For every eps > 0 and k >= k_0(eps): if H is (7,2) and tau(H) > (3/4+eps)k,
then H has a good triple with all pair cells < k/2. Stronger target (G'): the lex-min anchor
has u <= u* + delta(eps) k.
**Why it is the best next step.**
- It is the only regime where a discrete potential exists (number of close pairs, cluster
  membership), so the level-set escape of §1.1 is structurally impossible: cells cannot move
  through the window. [heuristic]
- It removes the lopsided stuck cluster and R1_RESULTS limitation 4 at once, for all t, not
  just 0.825. The 6/7 manuscript handles its small-M regime only at 6/7.
- Structure already forced: §1.5 (two clusters, four edges, cheap sealing) and §1.4 (link
  lemma); model families have tau <= 2k/5 (§1.6), so there is a lot of room.
**Evidence against.** In §1.5 the requester cannot yet force both close cells below ~9k/16
when m is small (|K∩K'| <= 3k/2 − T − m + 1 is only <= 3k/4 at m = 0), and sealing the fourth
triple intersection costs up to 5k/6. The adversary's options there are few but not yet
enumerated. R1b still has (0.5–0.6, small, small) anchors unresolved at depth 2–3.
**Cheapest decisive test (hours, LP only, no grid over profiles).** The "two-cluster game":
state = sizes of the Venn cells of E, K, K', K3 as in §1.5 (cells are small < 1 − t or large
>= 1/2; about 10 real parameters, most pinned by the window). Solve min over the requester's
two free split parameters of max over the adversary's cell sizes of the 3-request closure LP on
the four edges (R1's pattern-table generator already handles four edges with empty triple
cells), at t = 0.76, 0.78, 0.80. Win at 0.76 → write the proof (linear arithmetic, Lean-able
like Lemma A). Stuck → the stuck cell vector is a concrete 4-edge two-cluster configuration;
feed it to Path 4.
**Difficulty.** Medium. 1–2 weeks to a hand proof if the test wins; it is the same type of
statement as Lemma A with one more round.

### Path 2. Complete-like regime: template on W with trace control (stability at u ≈ u*)
**Setting.** A good triple with S >= 7k/2 − 3T (at T = 3k/4: S >= 5k/4, |W| <= 7k/4) is
"medium-tight". If every response to a Theorem-A template request on W (anchor edge E, classes
W∖E → 3 parts, E → 4 parts; request size (|W| − k)/3 + k/2 <= T) stayed inside W, the seven
edges would be bad. [proved by hand: Theorem A with V := W.] Responses fail this only through
outside points lying in three concurrent responses.
**Key lemma (O, outside-overlap).** In the adaptive template game on a medium-tight W, with the
rule "before asking line L, add to D_L every outside point lying in both other responses
through a point of L", the total extra load is o(k) — or else two responses share >= delta k
outside points O and W' = (W ∪ O) minus a compensating part carries a triple that is tighter or
lex-smaller (re-anchor).
**Evidence for.** (i) u* is exactly where |W| = (1+t)k: the template budget and the lex-min
threshold coincide, which is what one expects of the true proof. (ii) Lemma B already forbids
responses with trace <= (3T − |W|)/2 on W. (iii) Near u* the anchor cannot be kept as a triple
or even as a pair (pair law: keeping a pair with intersection 5k/12 costs t >= 0.79), so any
proof must be a one-anchor template here; the 5/6 barrier of ROADMAP §2.3 does not apply to it.
**Evidence against.** Responses with trace between k/4 and k on W are unconstrained so far;
this is the real "interpolation" problem and the middle stuck cluster lives here.
**Cheapest decisive test (1–2 days).** Exact adaptive template game at one profile:
anchor (5/12,5/12,5/12) + delta, t = 0.76: adversary = response traces on the 7 Fano classes of
W plus new points with a membership pattern; requester = the overlap rule above. LP over
traces per round, 6 rounds, depth-first with the adversary's extreme points only. Question:
is the adversary's best total outside overlap forced to be < eps k, and if not, what is the
profile of the triple formed by two overlapping responses and E?
**Difficulty.** Hard; this is the heart of the conjecture. But the test is cheap and its
failure mode is informative (it outputs the re-anchoring triple).

### Path 3. Multi-round use of the minimal class (what Path A becomes after §1.1)
**Key lemma (M).** Let 𝓜 be the set of good triples within eta·k of lex-min. Every request
that seals a cell of a triple in 𝓜 and cuts the two edges through it by more than
k − (cell) − u returns a triple in 𝓜 or a contradiction; so 𝓜 is closed under such moves and
all edges that appear satisfy the pair gap and Lemma B simultaneously with respect to every
triple of 𝓜 already seen.
**Evidence.** R1b: depth 2–3 clears 12 of 26 at t = 0.825; the adversary's answers are members
of 𝓜 (same potential). **Against:** in the sparse regime u < u* there is no gap, 𝓜 is a
continuum and I have no finiteness argument; below 5/6 one-round provably fails, and nothing
bounds the number of rounds needed.
**Cheapest test.** In the R1b engine add Lemma B and the pair gap as constraints on *every*
response with respect to *every* sealed triple in play (two extra rows per triple), and rerun
only the 14 still-stuck anchors at 0.825. If they clear at depth 2, the sparse regime is in
reach of the current engine; if not, the stuck responses define the sparse-regime obstruction.
**Difficulty.** Medium for a record below 11/13; unknown for 3/4.

### Path 4. Obstruction side: do stuck configurations extend to families?
**Statement to test.** There is a (7,2)-family with tau > (3/4+eps)k whose lex-min anchor is in
the gap regime (cluster family), or whose every good triple is loose and sparse (u < u*).
**Evidence against existence.** §1.6 (two clusters: 2k/5); R3 (block family on the Venn cells of
a stuck configuration has response-only bad tuples); Lemma B (no edge can be nearly disjoint
from any good-triple union, which rules out "many almost-new edges" as a sustained strategy);
every known extremal family is complete-like. Exact search is hopeless at the sizes where a
counterexample must live (beating the parity family needs tau >= 3k/4 + 2, i.e. k >= 12).
**Cheapest decisive test.** Continuous block-type LP on r clusters with overlaps: blocks = the
Venn cells of the Path-1 four-edge configuration (about 10), edge types = the two cluster
profiles with slack gamma; maximize tau/k subject to "no bad shape" via `typefam`/`coarse`
with shapes from `roadmap/shapes.py`. Expected outcome: maximum <= 1/2. A value > 3/4 would
be a counterexample; a value in (2/5, 3/4) tells Path 1 which closure it is missing.
**Difficulty.** Low (2–3 days), low prior of a disproof (< 5% [heuristic]).

### Path 5. Saturation as an extra move
WLOG H is a maximal (7,2)-family (adding edges never lowers tau). Then for every k-set B:
B ∈ H, or there are six edges of H all of whose 2-covers avoid B. [proved by hand, trivial]
The requester may therefore *propose* an edge (e.g. B = E Δ F when |E∩F| = k/2, which would
complete a tight triple) and either gets it or gets six edges with a strong covering property.
No request game has this move. **Test:** in K_N-like and parity families, compute what the six
edges look like for B completing a tight triple (small exact computation with typefam at
k = 8, 12). **Difficulty/priority:** speculative; keep as a tool for Path 2, where the missing
ingredient is exactly "force a prescribed edge".

### Not recommended
- Scalar-potential search and tie-breakers (§1.1).
- Fractional transversals / LP rounding (§1.7).
- Larger profile grids at fixed architecture: the stuck sets are explained by §1.2 and will
  not move.

---------------------------------------------------------------------------------------------

## 3. Soundness of everything proposed
- Pair gap: window empty at the lex-min triple of K_N for every N (u = u*). The parity family
  equals K_{7k/4} in the continuum model.
- Lemma B: edges of K_N lie inside W; bound is <= k whenever |W| >= 3T − 2k.
- Lemma G: K_N has u = u* < k/2, so the statement is true for it; it does not claim a win.
- Path 2 template: on K_N with N < 7k/4 and budget t < N/k − 1 the request size
  (N − k)/3 + k/2 exceeds T, so the template does not "win" at a genuine family.

## 4. Caveats
- §1.5 assumes u >= k/2 exactly; for u in (u*, k/2) the window is narrower and (a)–(d) need
  the general window [2k − 2u − T + 2, u). Not worked out.
- All O(1) terms are unchecked; nothing here is Lean-verified.
- Lemma B and the gap may already be implicit in the 11/13 repo's certificate; I only claim
  the organization (threshold u*, trichotomy, global use of Lemma B) as possibly new.

---------------------------------------------------------------------------------------------

## 5. Decisive test for Lemma G: the 4-edge two-cluster game  — RESULT: STUCK at 0.76, 0.78, 0.80

Code: `compute/newpaths/two_cluster_game.py` (exact rationals, no solver),
`compute/newpaths/overlap_family.py` (floating MILP). **This section corrects §1.5 and Path 1:
the 2+2 closure proposed there is the wrong shape.**

### 5.1 The forced configuration and every constraint used
Standing hypothesis (H0): tau(H) > T and no good triple has all pair cells < k/2 (lex-min
u >= k/2). Normalisation k = 1, g := 1 − t.

| # | constraint (on every edge / triple that appears) | justification |
|---|---|---|
| C1 | every pair intersection is <= g ("far") or >= 1/2 ("close") | pair gap §1.2, from H0 (minimality) + one request of size k − t0 + 2 <= T |
| C2 | every good triple has a cell >= 1/2 | H0 (minimality) |
| C3 | every good triple has S <= 3 − 2t | tight-triple lemma (Lean) |
| C4 | every edge meets every good-triple union W in >= (3t − |W|)/2 | Lemma B §1.3 |
| C5 | a cell is empty only if it lies inside the request ("sealing", as in R1 §1.3) | modelling convention, adversary-favourable |
Lemma A is not used (it concerns x <= k/2 anchors).

Moves (m = |E∩K|; the adversary's best choice is m = 0, which is what the certificate uses):
1. E any edge. Request 1/2 (+1 point) of E → K with |E∩K| < 1/2, hence far (C1).
2. Request (E∩K) ∪ (1/2 − m of E∖K) ∪ (t − 1/2 of K∖E) → K' avoids E∩K, is far from E
   (cap < 1/2, C1), hence close to K (C2 on the good triple (E,K,K')); b = |K∩K'| <= 3/2 − t − m.
   With m = 0 the requester has no free split left: forcing "far from E" costs 1/2.
3. Request (K∩K') ∪ (E∩K) ∪ (t − b − m of E) → K3 avoids K∩K', so |K3∩K|, |K3∩K'| <= 1 − b <= 1/2,
   far (C1; one extra point each if b = 1/2); (E,K,K3) is good, so K3 is close to E (C2);
   r = |E∩K3| <= 1 − t + b − (cut used elsewhere).
4. Closure: three static requests on E, K, K', K3.

### 5.2 Verdict  [computed exact]
Adversary: m = 0, b = 3/2 − t, r = 5/2 − 2t, all other pair cells 0 (C1–C4 verified exactly by the
script). Only candidate pair of classes: (E∩K3) × (K∩K'). Certified lower bound on the closure
value = min over all 3 969 cross-intersecting pairs of label families on [3] of the dual bound
at 10 rational multipliers:

| t | b | r | closure >= | verdict |
|---|---|---|---|---|
| 0.76 | 37/50 | 49/50 | 209/200 = 1.045 | stuck |
| 0.78 | 18/25 | 47/50 | 101/100 = 1.010 | stuck |
| 0.80 | 7/10 | 9/10 | 39/40 = 0.975 | stuck |

Even if the adversary used the smallest close cells available to him (b = 1 − t/2) the bound is
0.895, 0.8725, 0.85, still > t. The requester has no free parameter at m = 0, so this is a stuck
verdict for the game as specified, not for a grid of it.

### 5.3 Why: the witness is a genuine family, and it explains the R1b lopsided cluster  [proved by hand]
H2(N) := all k-subsets of V_1 and all k-subsets of V_2, V_1∩V_2 = ∅, |V_i| = N.
- tau = 2(N − k) + 2. For N = (1 + t/2)k + 1: tau > T. It satisfies H0: inside a cluster every
  three edges meet (N < 3k/2), so good triples are (two in one cluster, one in the other) with
  profile (x, 0, 0), x >= 2k − N = (1 − t/2)k >= k/2. **Lex-min anchor (1 − t/2, 0, 0): 0.5875 at
  t = 0.825, 0.62 at 0.76 — the R1b lopsided cluster.**
- The play of §5.2 is exactly this family's play (K' = K minus the request, K3 = E minus the
  request), so every constraint anyone could add that is true of genuine tau > T families is
  satisfied by the witness. The stuck verdict is robust against adding constraints.
- H2(N) is not (7,2) for N >= 6k/5, but a tuple is bad iff the edges of one cluster have empty
  common intersection (corrected statement of §1.6; same threshold 6k/5, same tau < 2k/5 + 2 for
  (7,2) members). That needs ceil(N/(N−k)) = 4 edges in one cluster (for 2/3 <= t < 1).
  A 2+2 configuration has to get the missing edges from *static* requests, and the closure LP
  says that is too expensive. So **any game whose kept configuration has at most 3 named edges
  per cluster before the static phase is beaten by H2(N)**; in particular R1b's "triple + one or
  two responses + static" at lopsided anchors. This is an architectural obstruction of the same
  kind as the 5/6 barrier, from a different family.
- The winning shape is a **star**: centre E in V_1 and four petals in V_2. Requests
  (t/2 + 1 points of V_1-side, i.e. half of E suffices: V_1∖(half of E) has < k points) ∪
  (t − 1/2 of the current common intersection of the petals): the core shrinks 1 → 3/2 − t →
  2 − 2t → 5/2 − 3t <= t − 1/2 for t >= 3/4, then is sealed. Five edges, bad. [proved by hand;
  script prints 4 petals for all three t]

### 5.4 Soundness check (requirement 3)
- Genuine (7,2) families with a lex-min cell >= k/2 that I know: H2(N), N < 6k/5 (tau < 2k/5 + 2),
  and K_N with N <= 3k/2 (tau <= k/2 + 1; for N < 3k/2 there is no good triple at all). All have
  tau/k <= 1/2, and the game's first move already costs k/2 + 1 points, so at any t < tau/k the
  game cannot start: no false win, trivially. [proved by hand]
- I know no (7,2) family with u >= k/2 and tau > k/2. Overlapped two-cluster families
  (V_1∩V_2 = O ≠ ∅) are the natural candidates; scan in §5.6.
- The star strategy does not win against H2(N) with N < 6k/5 at t < 2(N−k)/k: the core after j
  petals is >= k − j(T − k/2)… it needs 6 petals with empty intersection, which do not exist.

### 5.5 Gaps (requirement 2)
- u >= k/2 is assumed exactly. For u in (u*, k/2) the window is [2k − 2u − T + 2, u) and "close"
  means >= u; step 3 then needs 1 − b < u, false for b near u < 1/2. Not handled.
- O(1) terms: +1 point in move 1, +2 in the window, +1 per boundary case b = k/2 in move 3,
  rounding of the label split (<= 3 points). All favour the adversary by O(1) and do not affect
  a stuck verdict; they would have to be tracked in a win.
- The closure bound is a lower bound from 10 multipliers; it is exact by R1's Λ_3 argument but
  only the lower bound is needed here.

### 5.6 What replaces the test: the star game, and its real obstacle
**Corrected key lemma (G*).** In the gap regime, for T >= 3k/4 + eps k there are a centre C and
s <= 6 edges P_1..P_s, each meeting C in < k/2 points, such that no point x of C and point y
satisfy "y lies in every P_j not containing x" (then {C,P_1..P_s} is bad; for x in no petal this
says the petals have empty common intersection). Link lemma §1.4 is the case of empty traces.
**Obstacle [proved by hand].** With C5 the adversary gives every petal a trace point on C
unless that part of C is requested. If petal i has a private trace point, the other s − 1 petals
need empty common intersection. So with traces everywhere all (s−1)-wise intersections must be
sealed, while the budget beyond the k/2 spent on C is only T − k/2 ≈ k/4 per request and three
petals with pairwise disjoint traces are pairwise close and have a common point (C2 + C3).
Counting for s = 6 fails by a factor ~2 if the adversary can combine large traces with large
overlaps. Whether he can is exactly the question of whether overlapped two-cluster families
are (7,2) with large tau.
**Next decisive test.** (i) `overlap_family.py`: max tau/k over (7,2) families
H2(alpha, o, beta) (blocks V_1∖V_2, V_1∩V_2, V_2∖V_1). (ii) The star game as an LP with sealing
semantics on the 2^s Venn cells of the petals × {in C, out of C}, s = 5, 6, constraints C1–C5.

### 5.7 Overlapped two-cluster scan  [numerical; floating MILP, coarse grid]
`overlap_family.py`, sanity: reproduces K_N (7,2) iff N < 7k/4 (1.7 yes, 1.8 no) and H2(N)
(7,2) iff N < 6k/5 (1.15 yes, 1.25 no).
- Grid step 0.1 on (|V_1∖V_2|, |V_1∩V_2|, |V_2∖V_1|) in [0,2]^3, searching only for improvements:
  the best (7,2) member is the complete family K_{1.7k} (tau = 0.7k); **no member with
  tau > 0.7k is (7,2)** (`out_overlap_0.1.txt`).
- Gap-type members (overlap 0.1k or 0.2k, parts 0.8k..1.4k): the only (7,2) member with
  tau > 0.4k found is degenerate (one cluster has fewer than k points, i.e. K_{1.5k},
  tau = 0.5k); nothing above 0.5k.
So this three-block class contains no counterexample candidate and no (7,2) gap family with
tau > k/2 at this resolution. Consistent with a strong form of Lemma G: **(7,2) + u >= k/2
implies tau <= k/2 + O(1)** [heuristic; would follow from G* with much room to spare].

### 5.8 Status of Path 1 after the test
- 2+2 two-cluster closure: refuted as a route (stuck, exact, structural).
- No win at 0.76, hence no Lemma-A-style hand proof of Lemma G yet.
- Hand-proved and usable: the H2(N) obstruction (any proof below 6/7-type thresholds in the
  lopsided regime must build >= 4 same-cluster edges with empty common intersection, i.e. must
  spend its adaptive rounds inside ONE cluster, anchored by a single far edge); the star
  strategy against trace-free clusters; the trace obstacle.
- Recommendation to the R1b agent: for lopsided anchors (x >= 1/2, y,z small) add the star
  continuation: keep G (the far edge) as centre, drop nothing from the E-cluster, and request
  (half of G) ∪ (part of the current common intersection of the E-cluster edges). Depth needed
  against H2(N): 2 more responses after the anchor (E, F, F3, F4 + centre G) and no static
  phase; the present engine's drop-and-re-anchor move keeps only three edges and cannot see it.

---------------------------------------------------------------------------------------------

## 6. Petal traces on the centre: a lemma that neutralises them, a partial closure, and what remains

Code: `compute/newpaths/check_double_star.py` (randomized check of Lemma 6.1: 0 failures in 8000
trials; negative control with two centres finds 2-covers in about half of the trials) **[numerical]**.
u = largest cell of the lex-min anchor; "far" = intersection < u, "close" = >= u.

### 6.1 Lemma 6.1 (s+3, "three centres")  [proved by hand]
> Let P_1..P_s be edges with empty common intersection, U their union, and C_1,C_2,C_3 edges with
> C_i ∩ C_j ∩ U = ∅ for i ≠ j. Then the s+3 edges have no 2-point cover.

Proof. Let {a,b} be a cover. A point in two centres lies outside U, so it is in no P_i. If
neither a nor b lies in two centres they cover at most two of C_1,C_2,C_3. So say a lies in two
centres; then a covers no petal and b lies in every P_i, contradiction. ∎
(s = 3 is Lemma 3+3 of §1.4; s = 4 gives 7 edges. No "far", no cluster, and no sealing of the
petals' traces on the centres is needed: a point of a single centre cannot help cover the
other two.)

**Answer to the question.** One centre is the wrong count. With one centre G, every private
trace point u in G∩P_i creates the cover {u, common point of the other petals}; with three
centres whose traces on U are pairwise disjoint, no trace matters. The price is no longer
"seal G" but the following.

> **Corollary 6.2 (trace pairs) [proved by hand].** If tau > T and P_1..P_s (s <= 4) have empty
> common intersection and union U, then any two edges B_1,B_2 with B_1∩B_2∩U = ∅ satisfy
> |B_1∩U| + |B_2∩U| > T. In particular (5+2 closure): if some edge G has |G∩U| = beta and
> |U| + beta <= 2T, contradiction (request (G∩U) ∪ (T − beta points of U) to get C_2, then
> (G∩U) ∪ (C_2∩U) to get C_3).

So small traces are cheap for the requester; what the adversary must do instead is make the
union U of four same-cluster petals larger than 2T − beta. Corollary 6.2 holds in every family
with tau > T and can be added to the R1b engine as a response constraint or as a closure.

### 6.2 Lemma 6.3: the lex-min cell is at most k − T/2 + 1  [proved by hand]
If u > k − T/2 + 1 the pair-gap window [2k − 2u − T + 2, u) of §1.2 contains [0,u), but
requesting k − u + 1 <= T points of an edge produces a pair meeting in < u points. ∎
Write delta := k − T/2 − u >= −1. Then **far pairs meet in fewer than 2 delta + 2 points**.
H2(N) with N = k + T/2 + 1 has delta = 0: it is the extreme point of the gap regime and its
far pairs are disjoint. Consequences: the R1b anchor (0.6,0.05,0.05) at t = 0.85 cannot be a
lex-min anchor (u <= 0.575k); at t = 0.825 lopsided anchors have x <= 0.5875k, as observed.

### 6.3 Theorem 6.4 (top of the gap regime)  [proved by hand; O(1) terms as written, not machine-checked]
> Let tau(H) > T, u the lex-min cell, delta = k − T/2 − u. If
> **3T >= 2k + 30 delta + 24**, contradiction (7 edges: 4 petals, 3 centres).
> Equivalently, every family with tau > T has u <= (16k − 9T)/15 + O(1).

Proof. Take E,F with |E∩F| = u (the lex-min anchor has such a pair). Requesting k − u + 1
points of E∩F gives G far from E and F, so |G∩E|, |G∩F| < 2 delta + 2.
(This needs k − u + 1 <= u; automatic under the hypothesis when T <= 0.94k.)
*Petals.* Let S ⊆ G, |S| = k − u + 1, S ⊇ G∩(E∪F). D_3 = S ∪ Q_3 with Q_3 ⊆ E∩F,
|Q_3| = b_3 := T − (k−u+1) = T/2 − delta − 1. The response P_3 has |P_3∩G| < u, so it is far from
G; (E,G,P_3) and (F,G,P_3) are good triples (E∩G, F∩G ⊆ S) with two far pairs, so P_3 is close
to E and to F (minimality). D_4 = S ∪ (G∩P_3) ∪ Q_4 with Q_4 ⊆ E∩F, Q_4 ⊇ E∩F∩P_3,
|Q_4| = b_4 := b_3 − 2 delta − 2; possible since |E∩F∩P_3| <= u − b_3 = k − T + 1 <= b_4 by the
hypothesis. P_4 is far from G, close to E, F and (via the good triple (G,P_3,P_4)) to P_3, and
E∩F∩P_3∩P_4 = ∅.
*Union.* U = E∪F∪P_3∪P_4 has no point of degree 4, so |U| = 4k − (sum of pairs) + (sum of
triples). All six pairs are >= u and |E∩F| = u; the two triple cells inside E∩F total
<= 2u − b_3 − b_4; the two others are disjoint subsets of P_3∩P_4. Hence
|U| <= 4k − 5u + (2u − b_3 − b_4) = k + T/2 + 7 delta + 4. (For H2: N = k + T/2 + 1.)
*Centres.* beta = |G∩U| < 4(2 delta + 2). Corollary 6.2 needs |U| + beta <= 2T, i.e.
k + T/2 + 15 delta + 12 <= 2T. ∎

| t | closes lex-min anchors with u >= | H2 anchor 1 − t/2 |
|---|---|---|
| 0.76 | 0.6107 k | 0.62 k |
| 0.80 | 0.5867 k | 0.60 k |
| 0.825 | 0.5717 k | 0.5875 k |
| 0.846 | 0.5591 k | 0.577 k |

In particular **the pure two-cluster anchor (1 − t/2, 0, 0), where R1b's star is stuck for
n = 5, 6, is closed for every t > 2/3 with honest traces**, by a 7-edge configuration the
fixed-plan star search did not reach (n = 7 timed out). This is a result below 11/13 in a
regime, but only for a sliver of it: (0.5, 0.15, 0.05) and (0.5, 0.1, 0.05) at t = 0.825 have
delta = 0.0875k and are NOT covered.
Soundness: for genuine (7,2) families the hypothesis fails. H2(N), N < 6k/5: T < 2k/5 + 2 < 2k/3.
K_N with T = N − k: delta = k/2 − N/6 and the hypothesis reads N >= 5k/2, where K_N is not
(7,2).  [proved by hand]

### 6.4 The remaining obstruction, precisely
An adversary with u in (max(u*, k/2), (16k − 9T)/15) must satisfy all of: C1–C4 of §5.1 with
"close" = >= u and far < 2 delta + 2; Lemma 6.3; Corollary 6.2 for every 3 or 4 edges with empty
common intersection; (7,2) on everything shown. It can defeat Theorem 6.4 in one way only:
**four pairwise-close edges with empty common intersection whose union exceeds 2T − beta.**
The proof bounds |U| by k + T/2 + 7 delta; the constant 30 has three improvable sources:
 (i) the traces of G on the four petals are bounded separately (8 delta);
 (ii) the union bound uses only pair sizes, not Lemma B or Corollary 6.2 on sub-configurations;
 (iii) b_4 pays 2 delta + 2 to seal G∩P_3; using complementary sets S for P_3 and P_4 is free
     only when 2(k − u + 1) >= k, i.e. u <= k/2 + 1 (so not at the top of the regime).
I have no configuration that provably survives all constraints at delta ≈ 0.09k; the R1b stuck
responses at (0.5,0.15,0.05) were computed without Corollary 6.2, so they are not yet one.
**Realizability.**
- Overlapped two-cluster families (far pairs meet inside the overlap): no (7,2) member with
  tau > k/2 on the §5.7 grid [numerical].
- Block-type "one trace point per edge" families (profiles (k−1,1) and (1,k−1) on two blocks of
  size about 11k/8, tau about 3k/4 + 4) are NOT (7,2): four petals with empty common core and
  three centres that avoid the petals' trace points and have distinct trace points form a bad
  7-tuple (Lemma 6.1), and the requester can force it, every sealing costing O(1)
  [proved by hand]. So the O(1)-trace adversary of R1b §3.4 does not extend to a family.
- Exact SAT is not informative (a counterexample needs tau >= 3k/4 + 2, i.e. k >= 12).

### 6.5 Next steps (cheap, in order)
1. R1b engine: add the 4+3 closure (Lemma 6.1) and Corollary 6.2 as response constraints; rerun
   only the six lopsided anchors at t = 0.825. Prediction: (0.5875,0,0) wins; the
   delta = 0.0875k anchors decide whether the constant 30 is an artifact.
2. Replace the union bound of Theorem 6.4 by an exact LP over the 11 Venn cells of E,F,P_3,P_4
   and G's traces with all constraints of §6.4; its optimum replaces "30".
3. Lean: Lemma 6.1 and Lemma 6.3 are short and independent of everything unverified.

---------------------------------------------------------------------------------------------

## 7. Exact LP for the escape of Theorem 6.4  — RESULT: the constant is 26, not an artifact; u ≈ 0.5 anchors do NOT close this way

Code: `compute/newpaths/union_lp.py`. Continuum model, k = 1, u = 1 − t/2 − delta.

### 7.1 Model: variables and every constraint
Edges E, F, P_3, P_4 (petals) and G (far edge), obtained as in the proof of Theorem 6.4.
Variables: m_c >= 0 for the 14 Venn cells c of the four petals (the 4-wise cell is sealed by
D_4), g_c >= 0 = mass of G inside cell c, for the cells G can reach.

| constraint | justification |
|---|---|
| each petal has mass 1 | uniformity |
| \|E∩F\| = u | choice of E,F: the lex-min anchor contains a pair meeting in exactly u |
| \|E∩P_j\|, \|F∩P_j\| >= u (j = 3,4) | minimality: (E,G,P_j), (F,G,P_j) are good (E∩G, F∩G ⊆ S ⊆ D_j) with two far pairs |
| G∩E, G∩F, G∩P_3, G∩P_4 <= 2 delta | pair gap §1.2 (trace < u forces trace < 2 delta + 2); closed inequality, adversary-favourable |
| m_{EF3} <= 1 − t | D_3 = S ∪ Q_3, \|S\| = 1 − u, Q_3 ⊆ E∩F, \|Q_3\| = b_3 = t − 1 + u |
| variant A: m_{EF4} <= 1 − t + g_3, m_{EF3} + g_3 <= b_3, \|P_3∩P_4\| >= u, G∩P_3∩P_4 = ∅ | D_4 also seals G∩P_3; (G,P_3,P_4) good ⇒ close; second row = sealing affordable |
| variant B: m_{EF4} <= 1 − t; \|P_3∩P_4\| >= u **or** <= 2 delta (two LPs); G may meet P_3∩P_4 | D_4 does not seal G∩P_3; only the gap is available for (P_3,P_4) |
| g_c <= m_c; g = 0 on cells in (E∪F)∩(P_3∪P_4) | G∩(E∪F) ⊆ S is requested in D_3, D_4 |
Objective: adversary maximises |U| + beta = Σ m_c + Σ g_c. The requester's 5+2 closure
(Corollary 6.2) wins iff the maximum is <= 2t.
Valid but not imposed (checked to be vacuous or non-linear here): tight-triple lemma on the good
triples through G (reads "close cell <= 3 − 2t", slack); Lemma B; "pairwise-close triples have a
common point" (a single point; no mass).

### 7.2 Certification
HiGHS proposes the optimum; the exact rational two-phase simplex of
`compute/r1/exact_infeasible.py` (Fractions, Bland) then decides feasibility of the constraint
system together with "objective >= target". Stuck verdict = exact feasibility of
"|U| + beta >= 2t + 10^-5"; closure verdict = exact infeasibility of the same system; optimum
values are bracketed exactly within ±10^-5. [computed exact] (The simplex returns a decision,
not a printed Farkas vector; that is the certificate format, as in R1.)

### 7.3 Results  [computed exact]
| t | variant A closes iff | variant B closes iff | hand formula (B) |
|---|---|---|---|
| 0.825 | delta <= 0.01575, u >= 0.57175 | delta <= 0.01825, u >= 0.56925 | delta <= (3t − 2)/26 = 0.01827 |
| 0.846 | delta <= 0.01775, u >= 0.55925 | delta <= 0.0205, u >= 0.5565 | 0.02069 |
(delta on a 1/4000 grid.) In variant B the "P_3, P_4 far" branch is infeasible at every delta tested,
so closeness of P_3, P_4 is automatic and sealing G∩P_3 is wasted budget.

At u = 0.5 (the anchors (0.5,0.15,0.05), (0.5,0.1,0.05); delta = 0.0875 at t = 0.825):
| t | max \|U\| + beta (A) | (B) | max \|U\| with beta forced to 0 (B) | 2t |
|---|---|---|---|---|
| 0.825 | 13/5 | 51/20 | 1.85 | 1.65 |
| 0.846 | 63/25 | 303/125 | 1.808 | 1.692 |
At u = 0.55: 1.975 / 1.90 (t = 0.825) and 1.828 / 1.774 (t = 0.846), also above 2t.
**Verdict: stuck at u ≈ 0.5 and u = 0.55 for both t, by a wide margin, even if G had no trace
at all.** The constant 30 of Theorem 6.4 improves only to 26.

### 7.4 Theorem 7.1 (sharp form of Theorem 6.4 for this configuration)  [proved by hand; matches the LP]
> If tau > T and **3T >= 2k + 26 delta + O(1)**, contradiction. Without traces (beta = 0) the same
> configuration needs exactly 5u >= 6k − 4T + O(1).

Proof sketch: as Theorem 6.4 with D_4 = S ∪ Q_4, |Q_4| = b_3 (do not seal G∩P_3). P_3 and P_4
are close: the far branch of the gap is infeasible in the LP at every parameter tested
[computed exact]; a general hand argument for this step is still missing (variant A, which
proves closeness by sealing G∩P_3, gives the same theorem with 30 in place of 26). |U| = 4 − Σ_pairs + Σ_triples <= 4 − 5u − p + 2(1 − t) + p = 6 − 5u − 2t
(p = |P_3∩P_4|; the two triple cells outside E∩F are disjoint subsets of P_3∩P_4), beta <= 8 delta,
and 6 − 5u − 2t + 8 delta <= 2t is 3t >= 2 + 26 delta. The LP optimum equals this bound, so the
estimate cannot be improved without changing the requests. ∎

### 7.5 Why u ≈ k/2 escapes, and what that says  [proved by hand / heuristic as marked]
- The LP witness at u = 1/2, t = 0.825 (beta = 0): cells E 0.175, F 0.025, EF 0.15, P_3 0.175,
  FP_3 0.15, EFP_3 0.175, P_4 0.175, FP_4 0.15, EFP_4 0.175, EP_3P_4 0.325, FP_3P_4 0.175.
  Four edges, every pair meeting in at least half, triple cells of size about k/4 or more,
  union 1.85k. This is what four edges of a complete family K_N, N ≈ 7k/4, look like (pairs k/2,
  triples k/4). [computed exact for the cells; interpretation heuristic]
- So at u = k/2 the cluster of E is not a small complete cluster (as in H2) but can be locally
  complete-like, and "four petals with empty common intersection and small union" is the wrong
  target: inside a complete-like cluster the bad tuple is the Fano one. This is the same
  phenomenon as §2 Path 2 (u ≈ u*), now inside one cluster of a gap family.
- Budget reason, in one line [proved by hand]: sealing the core E∩F costs u and blocking G's
  cluster costs k − u; both together cost k > T. Theorem 7.1 works only where two partial cuts
  (T − (k − u) each) exhaust a core of size u, i.e. near u = k − T/2.
- Gaps: continuum model; all O(1) terms (the +2 in the window, +1 per request, 10^-5 margins)
  are ignored in §7.3 and favour the adversary in a closure, so Theorem 7.1's O(1) must be
  tracked before Lean (Theorem 6.4's explicit "+24" is an upper bound for it). Only this
  requester strategy was optimised: D_3 and D_4 put all free budget on E∩F. Putting part of
  D_4 on P_3∖(E∩F) changes |U| by at most T − (k − u) − (k − T) ≈ 0.15k at u = k/2, t = 0.825,
  which does not obviously bridge the 0.2k gap; not computed.

### 7.6 Consequence for the plan
The lopsided regime splits: **top** (u >= k − T/2 − (3T − 2k)/26): closed, Theorem 7.1, valid for
all t > 2/3. **Bottom** (u near k/2): open, and it is a complete-like-cluster problem, so it
should be merged with Path 2 (template on a medium-tight union) rather than attacked with
stars. The cheapest next test is the Path 2 template game run inside the cluster: anchor E,
W = E∪F∪P_3 with core sealed as far as the budget allows, requests of size T, with G kept as a
free centre to absorb outside points via Lemma 6.1.

---------------------------------------------------------------------------------------------

## 8. The complete-like core (Path 2, merged with u ≈ k/2)

Code: `compute/newpaths/relative_theoremA.py`. Lex-min anchor (E,F,G), sorted cells
u >= v >= w, S = u+v+w, W = E∪F∪G, u* = (2k − T)/3, eps = T/k − 3/4.

### 8.1 Fano criterion  [proved by hand; computed exact by exhaustion over the 128 line-sets]
> Seven edges indexed by the lines of the Fano plane have no 2-cover **if** for each of the 7
> points p the three edges on the lines through p have empty common intersection. (Conversely a
> point lying in three concurrent edges is one half of a 2-cover as soon as some point lies in
> the other four edges.)

Reason: the 64 line-sets containing no three concurrent lines are pairwise non-covering, and
every other line-set is completed to all 7 lines by one of them. So a Fano-type bad tuple is
exactly "seven concurrent triples, all good", and the only thing a request for line L must
contain is, for each p in L whose other two lines are already placed, the intersection of
those two edges. Everything else in a request is the requester's choice, made to keep later
forced sets small. Theorem A, the tight-triple lemma and Lemma 6.1 are three ways of paying
for the forced sets.

### 8.2 Theorem 8.1 (Theorem A relative to a set W)  [proved by hand; simulation: 0 failures in 3000]
> Let E be an edge, W ⊇ E any set, and rho_W := max |A∩A'∖W| over pairs of distinct edges.
> Then tau(H) <= ceil((|W| − k + 2 rho_W)/3) + 2 ceil(k/4) + O(1).
> (Adaptive form: tau <= ceil((|W| − k)/3) + 2 ceil(k/4) + 2 rho, rho = the largest of the four
> outside overlaps that actually occur.)

Proof. Theorem A's template on W: W∖E → B_1,B_2,B_3, E → a_1..a_4; group-j requests
B_j ∪ a_p ∪ a_q. Ask groups 1, 2, then 3; to a group-3 request through a_p, a_q add
(R∩R'∖W) for the two earlier responses through a_p, and the same for a_q. Check 8.1: at b_j the
edges E and the two group-j responses have no common point (the two requests cover E). At a_p
the three responses have no common point in E (their requests cover E), none in W∖E (the
requests contain B_1, B_2, B_3 respectively), none outside W (forced set). Sizes: groups 1, 2:
|B_j| + k/2; group 3: |B_3| + k/2 + 2 rho; balance |B_3| = |B_1| − 2 rho. ∎
W = V gives Theorem A. The point is that *points outside W cost only through pairwise
overlaps of two specific responses*, counted twice, not through |V∖W|.

**Region covered.** With W = anchor union (|W| = 3k − S): contradiction whenever
> S >= 7k/2 − 3T + 2 rho_W + O(1),  i.e.  u + v + w >= (5/4 − 3 eps) k + 2 rho_W.
In (u,v,w,t)-space this is a half-space cut by the unknown rho_W. With rho_W = 0 it contains
the whole complete-like corner (u,v,w) ≈ (u*,u*,u*) (S = 3u* = (5/4 − eps)k, slack 2 eps k) and
more generally every profile with S >= (5/4 − 3 eps)k: for instance (0.5, 0.45, 0.3) or the
§7 clusters if the *cluster's* union is used as W (|W| <= (7/4 + 3 eps)k − 2 rho).
For comparison the tight-triple lemma needs S >= (3/2 − 2 eps)k. So the gain over what is in
Lean is the band (5/4 − 3 eps)k + 2 rho_W <= S < (3/2 − 2 eps)k, conditional on rho_W.

### 8.3 Rigidity at a complete-like anchor  [proved by hand]
Let theta := (2k − T − 2u − w)/2. Minimality gives theta >= −O(1) (this is (8) of the 11/13 repo:
2u + w <= 2k − T), with equality exactly for the balanced anchor of K_{(1+t)k}.
> **Lemma 8.2.** Let F, G be the anchor edges with |F∩G| = w. For all D_F ⊆ F∖G, D_G ⊆ G∖F with
> |D_F| = |D_G| = (T − w)/2, the response K to (F∩G) ∪ D_F ∪ D_G contains all but at most theta
> points of F∖(G ∪ D_F), or all but at most theta points of G∖(F ∪ D_G).

Proof. (F,G,K) is good with cells w, a = |K∩F|, b = |K∩G|, a, b <= k − w − (T−w)/2 = u + theta.
Lex-minimality of (u,v,w) forces max(a,b) >= u. ∎
So when theta = o(k) the family is *locally complete*: the requester can prescribe u points of
an edge (any (u + theta)-subset of F∖G of the form F∖(G∪D_F), up to theta errors and up to the
adversary's choice of side). This is the stability statement that is actually available:
**complete-like profile ⇒ complete-like responses on the anchor**, with no density theorem.
What it does not give: the remaining k − u − b points of K (k/6 in K_N) may lie outside W.

### 8.4 Does tau > (3/4 + eps)k force H to be far from complete?  [proved by hand, weak]
Yes, but only at scale eps k. By Theorem 8.1, for every edge E and every W ⊇ E with
|W| <= (7/4 + 3 eps)k − 2 rho there are two edges sharing more than rho points outside W.
Taking |W| = 7k/4: some two edges share > 3 eps k/2 points outside any such W. Combined with
Lemma B (every edge keeps > (3T − |W|)/2 ≈ k/4 points in W) this says H cannot be a subfamily of
a complete family on about 7k/4 points, and its edges leave any candidate ground set in a
*correlated* way (large pairwise overlaps outside). It does not say more: all the forced
quantities are of order eps k, which is also the slack of the template (2 eps k/3 per request).

### 8.5 The remaining gap, and the cheapest decisive test
Gap: bound the four outside overlaps |R∩R'∖W| (R, R' the group-1 and group-2 responses through
a common point a_p) by c·eps·k with c < 1/3, at a complete-like anchor, or re-anchor when they
are large. Known constraints on such a pair: (R,R',R'') is a good triple for the third
response through a_p (so |R∪R'∪R''| > 2T: tight-triple lemma); Lemma B; Corollary 6.2; and
Lemma 8.2 if the requests are of sealing type. None of them bounds the overlap yet.
The natural adversary [heuristic]: answers of the form (prescribed part inside W, of size about
u) ∪ (points of a fixed outside pool P), all answers using the same pool, so outside overlaps
are of order k/6. Two such answers and an anchor edge they avoid form a good triple with one
cell about u and two small ones, so this adversary pushes the position into the lopsided
regime of §6–7 with the pool as a second "cluster". That is why §7's bottom (u ≈ k/2) and this
regime are the same problem.
**Decisive test (small LP, exact).** Position: balanced anchor (u*,u*,u*) at t = 0.76 and 0.78.
Requester: Theorem 8.1's six requests, with group 1, 2 requests of sealing type where
possible. Adversary variables: for each of the six responses its masses on the 7 template
classes and on the cells of an outside Venn diagram generated by the earlier responses.
Constraints: Lemma B, Corollary 6.2 and lex-minimality for every good triple among the edges
in play (in particular the seven concurrent triples and the triples (R,R',anchor edge) whose
core is sealed), tight-triple. Objective: max over the four pairs of the outside overlap.
If the maximum is <= eps k/3: Theorem 8.1 closes the complete-like corner and the proof is
linear arithmetic. If it is >= c k with c independent of eps: the witness is a concrete
pool adversary, to be tested for realizability exactly as in §5.7 (three-block scan with the
pool as a block).

### 8.6 Is this the real 3/4 barrier?  [heuristic]
Yes, in my judgement, for three reasons.
1. Everywhere else there is an eps-independent lever: a gap (§6–7 top), a sparse closure, or a
   tight triple. Here every available inequality has slack O(eps k), the template has slack
   2 eps k/3, and the adversary's free parameter (outside overlap) is of order k.
2. Any proof must produce a near-Fano 7-tuple here (pair law of ROADMAP §2.2), and by 8.1 that
   means seven good concurrent triples; the anchor contributes at most one edge. So six
   responses must be mutually consistent to precision eps k, with only "tau > T" to force them.
3. The lopsided bottom (§7) reduces to it.
What is new and usable: the cost of leaving W is now a single explicit quantity (four pairwise
outside overlaps), and Lemma 8.2 shows the inside part of the responses is already forced.
A proof of 3/4 along this route is "an outside-overlap lemma"; a disproof would be a family
whose edges share a pool of about k/6 outside points in a way compatible with (7,2).
I would not put the probability that the overlap lemma follows from the constraints listed in
8.5 alone above 30%: most likely a second extremal choice (W of minimum size among unions of
near-minimal triples, or the pool itself as part of the ground set) is needed.

---------------------------------------------------------------------------------------------

## 9. Outside-overlap LP at the balanced anchor — RESULT: no bound; max overlap = k − u* ≈ 0.59k versus the needed eps·k

Code: `compute/newpaths/overlap_lp.py` (exact rational decisions via the simplex of
`compute/r1/exact_infeasible.py`); closure values of §9.4 from `compute/r1/game.py` tables
(floating point). k = 1, eps = t − 3/4, u* = (2 − t)/3, |W| = 1 + t.

### 9.1 Model
Theorem 8.1's template at the anchor (u*,u*,u*), centre E. Classes a_1∪a_2 ⊇ X = E∩F and
a_3∪a_4 ⊇ Y = E∩G (so both group-1 requests seal a pair cell; no other request of the template
can seal one: a class pair holds k/2 of E and one B-class holds about t/3 < u*). B-classes cut
Z, PF, PG proportionally, |B_1| = |B_2| = (t + 2 rho)/3 with rho = eps, the largest value the budget
allows (**the requirement is: all four outside overlaps <= eps·k**; the "c < 1/3" of §8.5 is the
unbalanced adaptive form).
Edges in play: E, F, G, R (response to B_1∪a_1∪a_2), R' (response to B_2∪a_1∪a_3); these are
the two earlier responses through a_1. Variables: masses of R and of R' in each of the 17 cells
(8 in E, 9 in W∖E), of R∩R' in each common cell, o = |R∩R'∖W|, and private outside parts.

| constraint | justification |
|---|---|
| R, R' avoid their requests; cell capacities; \|R\| = \|R'\| = 1 | definition |
| \|R∩W\|, \|R'∩W\| >= t − 1/2 | Lemma B on (E,F,G) |
| max(\|R∩E\|, \|R∩F\|) >= u* (two branches) | lex-minimality on the good triple (E,F,R) (X sealed) = Lemma 8.2 type rigidity |
| u* + \|R∩E\| + \|R∩F\| <= 3 − 2t | tight-triple lemma on (E,F,R) |
| \|R'∩(E∪F∪R)\| >= (3t − \|E∪F∪R\|)/2 | Lemma B on the good triple (E,F,R) |
Checked and found vacuous here, hence not rows: pair gap (the window is empty at u = u*);
Corollary 6.2 and Lemma 6.1 closures (they need two traces with empty common part on the
petal union; under the sealing convention the adversary keeps one common point, and with G as
centre the condition |U| + beta <= 2t fails by more than k/4); constraints through the third
response R'' on the line through a_1 ((R,R',R'') is good: tight-triple and minimality are
satisfied by any R'' that is mostly new); minimality for R' (its request seals nothing).

### 9.2 Result  [computed exact]
| t | eps | max outside overlap o | o / eps | needed |
|---|---|---|---|---|
| 0.76 | 0.01 | 44/75 = 0.5867 (= 1 − u*) | 58.7 | <= 1 |
| 0.78 | 0.03 | 89/150 = 0.5933 (= 1 − u*) | 19.8 | <= 1 |
Certified by exact feasibility at the value and exact infeasibility at value + 10^-6.
The branch |R∩F| >= u* is infeasible (F∖(X∪B_1) is smaller than u*), so R is forced to have
|R∩E| >= u* inside a_3∪a_4.
**Binding constraints** (removing either raises the optimum; all others are slack):
|R| = 1 and minimality on (E,F,R). Lemma B is slack for R' (it would allow 3/2 − t).
So the only thing limiting the overlap is that R must spend u* of its points inside E;
everything else of R may lie outside W and R' may contain all of it.

### 9.3 Witness
R = Y ∪ P (Y = E∩G entirely, P a pool of k − u* points outside W), plus O(1) points elsewhere;
R' = S' ∪ P with S' any admissible u*-set in W. Outside overlap |P| = k − u*.
By symmetry the same holds for the pairs through a_2, a_3, a_4.

### 9.4 One added constraint and re-check: the full 4-edge closure  [numerical for the closure values]
Provable additional constraint: each response K must defeat the closure "E,F,G,K plus three
static requests" and, when a cell is sealed, "drop the opposite edge plus four requests"
(R1's Q and T_c). Evaluated on candidate witnesses with R1's pattern tables:
| edge | closure value at t = 0.76 / 0.78 | status |
|---|---|---|
| R = Y ∪ O(1) points ∪ P | 0.806 / 0.804 | survives |
| R' = (X∩a_2) ∪ (Y∩a_4) ∪ P | 0.752 / 0.752 | **closed** |
| R' = (t − 1/2 spread over Z, PF, PG) ∪ P | 0.647 / 0.658 | **closed** |
| R' = (Y∩a_4) ∪ PE-part ∪ Z-part ∪ P | 0.751 / 0.751 | **closed** |
| R' = (u* points of (Z∪PF)∖B_2) ∪ P | 0.816 / 0.815 | survives |
So the closure does cut the response polytope (three natural R' die, as does R when part of
its E-trace is moved from Y to PE at t = 0.78), but one admissible pair (R, R') with the full
overlap k − u* survives. **Re-solved optimum: unchanged, k − u*.** (This is a check of the
optimal witness against the added non-convex constraint, not a full MILP re-optimisation; it
suffices for a stuck verdict.) Shape of the survivors: each is (a dense block of exactly u*
points on one anchor side) ∪ (pool): R fills E∩G, R' fills u* of F∖E.

### 9.5 Is the witness realizable?  [heuristic, with one proved remark]
- As a product it is not a counterexample: a family {S ∪ P : S in a u*k-uniform family on W,
  P a (k − u*k)-subset of a pool} has tau <= the transversal number of its W-part, which is at
  most (7/8)u*k < k/2 if that part is (7,2), and it inherits a bad tuple otherwise.
  [proved by hand, sketch]
- With a single fixed pool P the requester wins trivially (one pool point in every request).
  So a genuine adversary needs a different pool for (almost) every request that touches the
  current one, i.e. a covering structure on the outside as rich as the family itself. The LP
  cannot see this: it has two responses and no request into the pool.
- I therefore do not regard the witness as a counterexample seed, but it is not refuted by
  anything proved so far.

### 9.6 Consequences
1. Theorem 8.1 with the constraints of §8.5 does not close the complete-like corner: the
   outside overlap is unconstrained at scale k, not eps·k. The 30% estimate of §8.6 is
   settled negatively for those constraints.
2. What the witness shows is needed: a *second-round* statement about the pool. The cheapest
   one to test: after R = Y ∪ P is seen, request D'' = (a design part of W) ∪ P_1 with P_1 ⊆ P of
   size about t − u* (all the budget that minimality on a sealed triple leaves); the response
   cannot reuse P_1, and (R, F, ·)-type triples become available because R∩F is O(1):
   every edge avoiding R∩F meets R or F in >= u* points (minimality on the triple with F,
   whose third cell is then compared with u* as well). An LP with three responses and
   requests into the pool (cells: 17 in W, plus P_1, P∖P_1, new) is the next exact test; its
   size is about 3·20 variables and it needs the Q-closure as a MILP constraint, i.e. the R1b
   engine with a pool block rather than a hand LP.
3. Honest status of the 3/4 question: the three regimes are now (i) closed: tight triples,
   top of the gap regime (Theorem 7.1); (ii) open with an explicit pseudo-adversary: bottom
   of the gap regime (§7.5, complete-like cluster) and the complete-like corner (pool
   witness, this section); (iii) not examined here: the sparse regime u < u*. Both open
   pseudo-adversaries are "locally complete piece + correlated outside part", which supports
   §8.6: this is the real barrier, and no finite list of 5-edge constraints I know removes it.

---------------------------------------------------------------------------------------------

## 10. One hand pass on the pool barrier — RESULT: no overlap lemma; two small lemmas, one improvement by changing the potential, and a partial barrier for one-anchor templates

Setting of §9: balanced lex-min anchor (E,F,G), cells u* = (2k − T)/3, privates of size
k − 2u* = (2T − k)/3, W the union. Witness: R = Y ∪ P ∪ O(1) (Y = E∩G, P a pool of k − u* points
outside W), R' = S' ∪ P. No computation was needed in this pass.

### 10.1 What a sampled pool point buys: nothing below cost 1:1  [proved by hand]
A request D with slack s = T − |D| may add s pool points; the response avoids them, so the
overlap with an earlier pool response drops by at most s. The adversary's sub-family of answers
to D only needs transversal number > s, which a pool varying in s + 1 points achieves. In the
template s = O(eps k). So "one pool point per request" beats a *fixed* pool and nothing else:
against a pool that moves by s points per request, hitting it costs as much as it removes.
Blocking the pool completely is always affordable but uses the whole surplus:
> **Lemma 10.1.** |P| = k − u* <= T, and after requesting P the budget left is exactly
> T − (k − u*) = (2T − k)/3, the size of one private cell of the anchor.
So a pool-free response can be forced, but only with about k/6 points of request inside W,
and the adversary may then answer with a near-copy of an anchor edge (an edge containing all
but k/6 points of E, F or G), which carries no information.

### 10.2 Why reusing the pool is consistent: the pool is a "side"  [proved by hand]
> **Lemma 10.2.** Let R be an edge with c_0 := R∩F small. Every edge A avoiding c_0 satisfies
> max(|A∩F|, |A∩R|) >= u* (lex-minimality on the good triple (F,R,A), whose third cell is |c_0|;
> strictly more than u* if |c_0| < u*).
Sealing c_0 costs O(1), so after the first pool response *every* later response is u*-close to
F or to R. An answer that reuses the pool is u*-close to R for free. This is the mechanism
that makes the correlated pool admissible: minimality, the only binding constraint of §9,
is satisfied by the correlation itself. It also means the position after R is a two-sided one
(F-side / R-side) exactly as in the lopsided regime, but with u* < k/2 and no gap.

### 10.3 The potential matters: with a min-S anchor the pool shrinks to one private cell  [proved by hand]
The binding row of §9 depends on the extremal rule. For the lex-min rule a sealed response
needs max(a,b) >= u* (a = |R∩E|, b = |R∩F|). For the rule "anchor = good triple of minimum
S" (the balanced triple is also the minimiser in complete-like families) the same sealed triple
(E,F,R) needs u* + a + b >= 3u*, i.e. **a + b >= 2u***, so
> |R∖W| <= k − 2u* = (2T − k)/3 ≈ k/6 (17 eps k at t = 0.76; 6.2 eps k at t = 0.78),
down from k − u* ≈ 0.59k. This is exactly the K_N value (there the k/6 points lie in PG instead
of outside W). It still exceeds eps k, and it constrains only the two sealing requests of the
template (group 1); R' (group 2) stays unconstrained except by Lemma B. A mixed rule
s_1 + lambda(s_2 + s_3) interpolates: a >= (1 + lambda)u*. Soundness: min-S at K_N, N < 7k/4, is the
balanced triple and the game is stuck there (R1b checks, `poth:-1,-1,-1`).
Consequence for the engine: the complete-like corner should be run with a sum-type potential,
not lex-min and not 4·s_1 + s_2.

### 10.4 Barrier for one-anchor Fano templates  [proved by hand, for the pseudo-adversary described; its admissibility is checked only against the constraints listed]
Pseudo-adversary 𝔓 (pool + copies): a request with fewer than |P| − (k − u*) + O(eps k) points in
the current pool is answered by (an admissible u*-block inside W) ∪ (k − u* pool points);
a request that blocks the pool has at most (2T − k)/3 + O(eps k) points in W (Lemma 10.1) and is
answered by a near-copy of an anchor edge.
Take any 7-tuple of Fano pattern (§8.1) with E on a line L_1 and six responses.
- At each point a_p off L_1 the three responses must have empty common intersection. Two pool
  answers share >= k − u* − O(eps k) pool points, so at each a_p either at most one of the three
  answers is a pool answer or the last of the three requests blocks the pool.
  Either way **every a_p lies on a line whose request is pool-blocking**.
- Lines through the four a's that cover all of them: a matching pair (the two lines of one
  group, both through some b_j), or at least three lines.
- A pool-blocking request has <= (2T − k)/3 + O(eps k) ≈ k/6 points in W. For a matching pair
  through b_j the triple (E, N, N') must be good, so the two requests must together contain
  E∩N, where N is a near-copy of E if the adversary so chooses: cost >= 5k/6 > k/6.
  With three or more pool-blocking lines the same count is NOT conclusive: two of them meet at
  some a_p, but the third line there may be a full-budget request and N∩N' can be as small as
  2k/3 <= T. [open]
Hence **every Fano template around one kept edge in which the pool-blocking requests are the
two lines of one group loses to 𝔓**; this includes Theorem 8.1 in every ordering of its groups.
Templates with three or more pool-blocking (hence W-light) requests are not excluded, but
they are no longer templates on W: half of their requests carry no class structure.
What is not shown: that 𝔓 survives closures of other shapes (three centres with a pool edge
as petal; two kept anchor edges; four-edge tables on (F,R,·,·)). §9.4 checked the four-edge
tables for the first two responses only.

### 10.5 What a new architecture has to do
The failure is one of accounting, and it is the same one in §7.5 and §9: a response has
k − u* points that minimality does not place, the template has surplus O(eps k), and blocking
the free part costs k − u* while leaving k/6. So any proof at 3/4 + eps must make the free part
*pay inside the same request budget*, which in a 7-edge argument means: the free parts of
different responses must be forced to coincide with template classes. Two concrete ways:
1. **Put the pool into the ground set from the start** (second extremal choice). Choose the
   anchor edge E and take W := E ∪ (union of the answers to the six template requests), with
   the answers chosen, among all admissible ones, to minimise |W|. Then Theorem 8.1 has rho = 0 by
   definition and the question becomes a bound |W| <= (7/4 + 3 eps)k: an *upper bound on the
   union of six responses*, which by 8.1 is what a near-Fano tuple is. The lemma to aim for:
   "min over answers of |E ∪ R_1 ∪ … ∪ R_6| <= 7k/4 + O(eps k) at a min-S anchor".
   With min-S, §10.3 already gives |R_i∖W_0| <= k/6 for sealing requests.
2. **Two-sided anchor** (Lemma 10.2): keep the almost disjoint pair (F,R) and classify every
   later response as F-side or R-side; the pool is then inside R, not outside the ground set.
   This is the lopsided game with u* < k/2, where §6's three-centre closure is available
   (petals on one side, centres on the other) but Theorem 7.1's union bound is not.
**Engine-sized test, specified (not run).** R1b engine, potential s_1 + s_2 + s_3, t = 0.76 and
0.78, start position the balanced anchor, depth 3, with: (a) regions = 13 cells of
E,F,G,K_1 plus, for the second and third response, the split of K_1's new part into
"requested / not requested" (one extra block P_1 ⊆ P of size up to T − u*);
(b) closures: Q, T_c, Lemma 6.1 with petals among {anchor edges, K_1} and centres among the
other edges, Theorem 8.1 with W := union of the edges in play; (c) adversary constraints:
min-S on every sealed triple, Lemma 10.2 after every response with an O(1) cell, tight-triple,
Corollary 6.2. Decision: if the root is won at 0.76, extract the three-response line of play
and prove it by hand; if stuck, the response list defines the correlated-pool family to test
for realizability as a 3-block family (W-part, pool, rest) with `overlap_family.py`-style MILP.

---------------------------------------------------------------------------------------------

## 11. New architecture, first pass: min-S rigidity gives a stability inequality  tau <= (17k − 7 sigma)/11

sigma = sigma(H) := min of S = x+y+z over all good triples of H; S_max := the max.
Code for the side check: `compute/newpaths/pool_family.py`.

### 11.1 Three lemmas on sigma  [proved by hand]
Let tau(H) > T.
- **(a) sigma <= 2k − T.** For any two edges A, B with m = |A∩B| <= T and any D ⊆ A∪B of size T
  containing A∩B, the response K gives a good triple with S = m + |K∩(AΔB)| <= m + (2k − m − T).
  Equality for K_{k+T}.
- **(b) every two edges meet in at least sigma − k points** (S(A,B,K) <= m + k for the same K).
- **(c) rigidity for every pair.** Write theta := 2k − T − sigma >= 0. In (a), |K∩(AΔB)| >= sigma − m,
  so K contains all of (A∪B)∖D except at most theta + (m − (k − T)) points, and has at most
  that many points outside A∪B. For a pair with m = k − T − nu (0 <= nu <= theta; such a pair
  exists: request T points of an edge, then use (b)) and any Q ⊆ AΔB with |Q| = k + nu:
  **there is an edge K with K∩(A∪B) ⊆ Q and |K∖Q| <= theta − nu.**
So when theta is small the family is a theta-noisy complete family on the 2T + 2nu points of
AΔB, with all the noise *outside A∪B*: the pool is at most theta. This is the "pool into the
ground set" step of §10.5, obtained by anchoring on a sparse pair (intersection about k/4)
instead of the anchor's own pairs (intersection u*, where the free part is k/6, §10.3).

### 11.2 Theorem 11.1 (stability inequality)  [proved by hand; O(1) explicit]
> For every k-uniform (7,2)-family:  **tau <= (17k − 7 sigma + 16)/11.**
> Equivalently, with T = tau − 1 and theta = 2k − T − sigma: there is a good triple with
> |union| <= 3k/2 + 7 theta/2 + 1/2, i.e. S_max >= 3k/2 − 7 theta/2 − 1/2.

Proof. Take A, B with m = k − T − nu as in (c), eta := theta − nu. Let M ⊆ AΔB with
|M| = ceil((3k + 3nu + eta)/2) (|AΔB| = 2T + 2nu; if M does not fit, then theta > 4T − 3k, so tau < k − sigma/5 + 1, which
is below the claimed bound when sigma <= 5k/4; and for sigma >= 5k/4 the claimed bound already
follows from 11.1(a), tau <= 2k − sigma + 1).
Choose Q_1, Q_2, Q_3 ⊆ M with |Q_1| = |Q_2| = k + nu, |Q_3| = k + nu + eta and
Q_1∩Q_2∩Q_3 = ∅. Requests D_i = (A∪B)∖Q_i for i = 1, 2 (size T) and
D_3 = (A∪B)∖Q_3 ∪ (K_1∩K_2∖(A∪B)) (size <= T − eta + eta). By (c) each response K_i has
K_i∩(A∪B) ⊆ Q_i and at most eta points outside A∪B. So K_1∩K_2∩K_3 = ∅ and
|K_1∪K_2∪K_3| <= |M| + 3 eta <= 3k/2 + 7 theta/2 + 1/2. Tight-triple lemma (Lean): a good
triple with union <= 2T − 2 is impossible, so 3k/2 + 7 theta/2 + 1/2 > 2T − 2, i.e.
11T < 17k − 7 sigma + 5, for every T < tau. ∎

Checks [proved by hand]: K_N has sigma = 3k − N, tau = N − k + 1; the bound reads
N − k + 1 <= (7N − 4k + 16)/11, i.e. N <= 7k/4 + 5/4: **tight (up to O(1)) exactly at the
extremal complete family**, and never violated by a genuine one. H2(N), N < 6k/5: sigma = 2k − N <= k, bound >= 0.9k,
tau < 0.4k.

What it says:
| sigma/k | 1.25 | 1.2 | 1.1 | 1.0 | 0.83 |
|---|---|---|---|---|---|
| tau/k <= | 0.750 | 0.782 | 0.845 | 0.909 | 1.02 |
- **The complete-like corner is closed**: if tau > (3/4 + eps)k then
  sigma < (5/4 − 11 eps/7)k + O(1), i.e. the family has a good triple strictly sparser (in S)
  than every triple of the complete family K_{k+T}, by a margin 4 eps k/7. No pool can prevent
  this, because the argument never uses a request whose response has a large free part.
- Together with the tight-triple lemma: tau <= min((3k − S_max)/2, (17k − 7 sigma)/11) + O(1).
  A counterexample to 3/4 must have BOTH S_max < (3/2 − 2 eps)k and sigma < (5/4 − 11 eps/7)k.
- sigma >= 1.1k already gives tau <= 0.846k (the 11/13 level) by a five-edge argument.
- Region in the language of §8: the hypothesis is on the min-S triple, not the lex-min one.
  The §9 pool witness has triples (E,F,R) with S = 2u* ≈ 0.83k, so it lies far outside the
  region; it is not refuted, it is *relocated*: its min-S anchor is a triple with one empty
  (or O(1)) cell.

### 11.3 Target lemma of part A, and the local version
- Local version suffices [proved by hand]: by the Fano criterion §8.1 only the seven chosen
  edges matter; Theorem 8.1 with W := E ∪ R_1 ∪ … ∪ R_6 has rho = 0. So the target is exactly
  "seven edges, all seven concurrent triples good", and the union need not be bounded for its
  own sake.
- What 11.2 proves of the target: three of the seven (a tight concurrent triple) can be
  placed with all free parts <= theta. The remaining four are then requests of size |U|/2 on the
  triple's union; this is why the loss is (7/4) theta and not O(theta) with a smaller constant.
- Not proved: the target lemma for theta of order k. The swap idea (many answers per request)
  gives nothing beyond 11.1(c): the answers to D only need transversal number > T − |D|.

### 11.4 Part B: the two-sided anchor after relocation  [proved by hand, partial]
If the min-S anchor has an empty cell, say F∩R = ∅:
> **Lemma 11.2.** Every edge A satisfies |A∩F| + |A∩R| >= sigma. (In general: every edge
> avoiding F∩R has at least sigma − |F∩R| points in FΔR.)
(The triple (F,R,A) is good for every A.) So the whole family lives on F∪R up to
k − sigma points per edge: a ground set of 2k points, with outside parts <= k − sigma.
Theorem 8.1 with W = F∪R then gives tau <= 3k/2 − 2 sigma/3 + O(1), which is <= 3k/4 only for
sigma >= 9k/8 (impossible here, sigma <= k). So confinement to 2k points is not enough; one needs
the Fano tuple inside F∪R to discard F or R (a disjoint pair cannot be in a Fano tuple) and
use a pair meeting in about k/2: by Lemma 11.2, a request (k/2 of F) ∪ (T − k/2 of R) gives A
with |A∩F| in [sigma − 3k/2 + T, k/2], which pins |A∩F| near k/2 only when sigma is near k.
Three-centre closures (petals on one side, centres on the other) were not developed in this
pass. Status: open; this is where the pool witness now sits.

### 11.5 Part C: block-type "core + pool" families  [numerical; floating MILP, targeted points only]
H(w,p,c): all k-subsets of a block W_0 (|W_0| = wk) together with all k-sets having ck points in
W_0 and (1−c)k points in a pool block of size pk. `pool_family.py`; sanity: reproduces K_N (7,2)
iff N < 7k/4. The full grid scan was started and stopped unfinished (`out_pool_family.txt`): the only
(7,2) members with tau > k/2 found before it was stopped are degenerate (a pool-only family with
tau = 0.55k and the pure complete families K_{1.6k}, K_{1.7k}); the partial run proves nothing more. Targeted points:
| (w, p, c) | tau/k of the family | bad 7-tuple found with j pool edges |
|---|---|---|
| (1.7, 0.7, 0.4) | 0.8 | j = 1 |
| (1.7, 1.0, 0.4) | 1.1 | j = 1 |
| (1.5, 1.0, 0.5) | 1.0 | j = 2 |
| (1.2, 1.2, 0.5) | 0.7 | j = 4 |
| (1.0, 1.0, 0.5) | 0.5 | j = 6 |
None is (7,2). Structural reason for j = 1 [proved by hand]: by the link lemma §1.4 the core
edges disjoint from a pool edge R must be 6-wise intersecting, which fails as soon as
W_0∖R has at least 6k/5 points, i.e. w − c >= 6/5. A block-type family contains near-copies of
core edges that are *independent of the pool edge*; the pseudo-adversary of §10.4 needs every
near-copy to meet every pool edge in a correlated way, which no profile-defined family
provides. So pool-plus-near-copies is not realizable as a block-type family at these
parameters; a realization, if one exists, must be non-block-type (the trace of a pool edge on
W_0 must determine which near-copies are present).

### 11.6 What remains, and the next decisive step
- Proved: tau <= min((3k − S_max)/2 + 1, (17k − 7 sigma + 16)/11). Open: families with
  sigma < (5/4 − 11 eps/7)k and S_max < (3/2 − 2 eps)k, i.e. a very sparse triple and no tight one.
- The constant 7/11 comes from closing the noisy-complete structure through a tight triple
  only. The structure of 11.1(c) is richer: every (k+nu)-subset of AΔB is an edge up to theta
  outside points, for EVERY pair with intersection near k − T. **Next step (hand + small LP):**
  feed 11.1(c) into the general position: pick the min-S anchor (x,y,z), sigma = x+y+z, and
  compute, as an LP in (x,y,z,theta), the best closure that uses (i) rigidity 11.1(c) on each
  of the anchor's three pairs and on the pair of intersection k − T − nu, (ii) Theorem 8.1 with
  W = a union of such pairs, (iii) Lemma 6.1. The decisive question is whether the bound
  tau <= 3k/4 + c·theta can be replaced by a bound that does not degrade as sigma decreases,
  e.g. tau <= 3k/4 + c·min(theta, something that vanishes for sparse anchors); the sparse end
  (sigma near 0, three almost disjoint edges) is trivially closed, so the bad range is the
  middle, sigma between about k/3 and 5k/4.
- Then Part B (Lemma 11.2: families with an empty min-S cell live on F∪R up to k − sigma points
  per edge) is the special case z = 0 of that LP.

---------------------------------------------------------------------------------------------

## 12. The middle range k/3 <= sigma <= 5k/4 — RESULT: no non-degrading bound; a second rigidity source (noisy copy of K_{k+T}); the middle range identified with "complete family minus tight triples"

No LP was run: the hand analysis below shows that the LP of §11.6 cannot give a bound that is
uniform in theta. Every constraint in it is satisfied by the answers of a complete family K_N
played at a budget below its transversal number, and against those answers the only winning
tuples are a tight triple or a full Fano tuple; the LP's closures (rigidity with free parts
bounded by theta, then Theorem 8.1 or a three-centre closure) are neither.
theta = 2k − T − sigma as in §11.

### 12.1 What theta measures  [proved by hand]
For K_N and any T < tau = N − k + 1: sigma = 3k − N, so **theta = N − k − T = (tau − 1) − T**: theta is
the *slack between the budget and the transversal number*, not a measure of sparseness. Every
rigidity statement of §11.1(c) is exactly tight for K_N: a response to a T-request inside A∪B
may omit theta of the unrequested points because the complete family really has that freedom.
Consequences:
- sigma is small in the middle range not because the family is exotic but because it may be
  *larger than needed*: K_{2k} at T = 0.76k has sigma = k, theta = 0.24k, and is beaten only by
  its tight triples (S_max = 3k/2).
- The arguments of §11 bound the free part of a response by theta and then pay for it; played
  against K_N's answers (free part exactly theta available) they lose Theta(theta) by
  construction. K_N itself is no counterexample to any theorem (it is not (7,2) for
  N >= 7k/4); it shows that **a proof which does not degrade in theta must output, against
  K_N-like answers, either a tight triple or a Fano tuple with defect points**, and with tight
  triples excluded by hypothesis only the second remains. [heuristic as a statement about
  methods; the K_N computation is proved]
- The honest two-parameter statement is therefore the one of §11.2:
  tau <= min((3k − S_max)/2 + 1, (17k − 7 sigma + 16)/11), and the middle range is
  {S_max < (3/2 − 2 eps)k} ∩ {sigma < (5/4 − 11 eps/7)k}.

### 12.2 Second rigidity source: a noisy copy of K_{k+T}  [proved by hand, sketch; constants not optimised]
Let A, B be the sparse pair of §11.1(c), m = k − T − nu, W := A∪B, |W| = k + T + nu.
> **Proposition 12.1.** For every k-subset Q of W there is an edge K with |K∖Q| <= 3 theta + O(1).
Sketch. Depth 1 (§11.1(c)): every (k+nu)-subset of AΔB is an edge up to theta points, the
errors lying outside W. Depth 2: Q misses T + nu points of W, and since 4T >= 3k it misses at
least k − T points of A∖B or of B∖A; say of A∖B. Take a depth-1 edge X that contains k − T of
those missed points of A∖B and T points of B∖A including Q∩(B∖A)... (possible up to theta
errors). Then |A∩X| = k − T up to theta, so (A,X) is again a sparse pair, AΔX contains A∩B, and
11.1(c) for (A,X) with the target Q gives K: inside A∪X it lies in Q up to theta, it may pick up
the at most nu + theta points of W∖(A∪X) and at most theta + |X∖W| <= 2 theta points outside W. ∎
So sigma >= 2k − T − theta forces a 3 theta-noisy copy of the *whole* complete family on k + T
points, not just one tight triple inside AΔB. With Theorem 8.1 on W (outside overlaps
rho <= 3 theta) this gives tau <= 3k/4 + 3 theta + O(1): worse than the 7 theta/4 of Theorem 11.1,
so no new bound; its value is structural (it is the stability statement "sigma near 2k − T
⇒ H contains a noisy K_{k+T}" in full), and it shows that iterating rigidity over several
sparse pairs costs theta per level and cannot beat the one-level argument.

### 12.3 What the absence of tight triples gives  [proved by hand]
> **Lemma 12.2.** For every set M with |M| <= 2T − 2 the edges inside M are 3-wise
> intersecting; in particular tau(H[M]) <= (k+1)/2.
> **Corollary (free parts are pinned from both sides).** For edges A, B with m = |A∩B| <= T and
> every edge K avoiding A∩B:  |K∖(A∪B)| >= m − (2k − 2T) − 1.  If K answers a T-request
> inside A∪B, also  |K∖(A∪B)| <= m − (k − T) + theta.
The lower bound is the tight-triple lemma applied to (A,B,K); the upper bound is 11.1(c).
For m = k/2 the free part lies in [2 eps k, k/4 + eps k + theta]. For the sparse pair
(m = k − T) the lower bound is vacuous: this is why §11 could work inside AΔB.
Two readings:
- In a family that is (k+s)-complete on a ground set of at least 2T points (every (k+s)-subset
  contains an edge), Lemma 12.2 gives s >= 2T − 3k/2 − O(1) = 2 eps k. For n = 7k/4 + c this is
  g <= c/3, the same as Theorem A. So "complete on W up to slack s" is consistent with tau > T
  only for s >= 2 eps k, and theta >= 4 eps k/7 (Theorem 11.1): both are noise floors of order
  eps k, not contradictions.
- The middle-range adversary is thus: **a subfamily H of some K_N, 7k/4 + 3 eps k <= N, in which
  every (N − T)-set contains an edge, every 3 edges inside any (2T − 2)-set have a common
  point, and no 7 edges form a bad tuple.** All of sigma, theta, lex-min profiles, pools are
  coordinates on this one object; N is free (the "pool" is just N − |W|).

### 12.4 Obstruction, stated precisely, and its realizability
Configuration satisfying every constraint proved so far (C1–C5 of §5.1 where applicable,
Lemma B, Corollary 6.2, Lemma 6.3, Theorems 6.4/7.1, 8.1, 11.1, Lemmas 10.2, 11.2, 12.2):
the complete family K_N, 7k/4 + 3 eps k < N <= 2k, **with its tight triples deleted**, i.e. the
pseudo-family whose answers are those of K_N except that no three shown edges with empty
common intersection may have union <= 2T − 2. Against it:
- sparsest-anchor arguments see K_N's balanced triple with theta = N − k − T of order k;
- Theorem A / 8.1 on any W needs |W| <= 7k/4 + 3 eps k < N, and the answers leave W freely;
- the tight-triple lemma is switched off by definition.
Realizability [heuristic + what is proved]: as a genuine family it would be a Turán-type
system (every (N−T)-set contains an edge) with the 3-wise-intersecting property of Lemma 12.2
on all (2T−2)-sets. Proved obstacles to the obvious constructions: threshold families
"|A∩V_0| > 2|V_0|/3" are 3-wise intersecting globally, hence have tau <= (k+1)/2; modular
(parity-type) conditions are repaired by O(1) low-degree points as soon as
N − 7k/4 exceeds the number of conditions (ROADMAP §2.5); block-type families with 2–3 blocks
were scanned in §5.7 and §11.5 with nothing above the complete family. No construction is
known; none is excluded. Exact search is out of reach at the sizes where the question is
non-trivial (k >= 12).

### 12.5 What a proof must now do, and the next decisive step
The reductions of §6–§12 leave one statement, free of pools and anchors:
> **Core conjecture (equivalent to the 3/4 conjecture up to the regimes closed above).**
> If every T-set misses an edge, T >= (3/4 + eps)k, and every good triple has union > 2T − 2,
> then H has 7 edges whose seven concurrent triples (in some Fano labelling) are good.
The seven good concurrent triples then each have union > 2T − 2, i.e. about 1.5k + 2 eps k,
while a Fano tuple on 7k/4 points has concurrent unions exactly 1.5k: so the target tuple must
itself be spread by Theta(eps k) per triple, and the hypothesis "no tight triple" and the
conclusion pull in the same direction only if the tuple lives on about 7k/4 + Theta(eps k)
points. That is a quantitative near-Fano existence statement in a Turán system; none of
the request-game tools in this file produces such a tuple without either a tight triple
(excluded) or completeness up to o(eps k) (not available: the noise floors are 2 eps k and
4 eps k/7).
**Next decisive step.** Decide the near-complete instance, where everything is
finite-dimensional: n = 7k/4 + c, c in (3g, C g) for a constant C, tau = 3k/4 + g.
Concretely the adaptive template game of ROADMAP R2 test (i) with the extra rule
"no shown triple is tight", solved exactly as an LP over the 7 Fano classes plus defect
cells, for c/g = 4, 6, 10. If the requester wins for some fixed ratio c/g, the method is
Theorem A plus a defect-accounting lemma and extends by Proposition 12.1-type propagation;
if the adversary wins for every ratio, his answers are a candidate "complete minus tight
triples" family on 7k/4 + O(g) points, small enough to test by the parity-type MILP of
`compute/typefam.py`. This is engine-sized (about 7·16 cell variables per response, six
responses) and was not run in this pass.

---------------------------------------------------------------------------------------------

## 13. Counting / density architecture — RESULT: it reproduces Theorem A exactly and then stops; precise reasons

Notation: n = |V|, s := n − T − k (tau > T iff every (k+s)-subset of V contains an edge),
g := T − 3k/4, c := n − 7k/4, so s = c − g. No computation in this pass.

### 13.1 Localisation to a set U, done exactly  [proved by hand]
The Turán property passes to subsets with no loss: for any U ⊆ V, every (k+s)-subset of U
contains an edge of H[U], hence tau(H[U]) >= |U| − k − s + 1.
Take |U| = 2T − 2 (possible when n <= 3T − 2). By Lemma 12.2 H[U] is 3-wise intersecting,
so tau(H[U]) <= (k+1)/2. Therefore 2T − 2 − k − s + 1 <= (k+1)/2, i.e.
> s >= 2g − O(1),  equivalently  tau <= (n − k)/3 + k/2 + O(1).
**This is Theorem A, re-derived in two lines from the tight-triple lemma and Frankl's bound
for 3-wise intersecting families.** So ingredients (1)+(2)+(3) of the proposed architecture,
used on one set U, give exactly what is already in Lean and nothing more.

### 13.2 Why size counting on U adds nothing  [proved by hand]
- Lower bound from the Turán property: |H[U]| >= C(u,k)/C(k+s,s) (u = |U|).
- Upper bound for 3-wise intersecting families: C(u−1,k−1) = (k/u)·C(u,k) (valid for
  u >= 3k/2). The two clash only if C(k+s,s) < u/k ≈ 3/2, i.e. s = 0.
- With the transversal number taken into account the comparison is still slack: the local
  extremal structure is H[U] ⊇ all k-subsets of Y_U, with Y_U ⊆ U, |Y_U| = u − s < 3k/2,
  which is 3-wise intersecting, has tau = |Y_U| − k + 1, satisfies the local Turán property
  (possible exactly when s >= 2g − 1), and has C(3k/2,k)-many edges, exponentially more than the lower bound.
So for every single U the hypotheses are jointly satisfiable whenever s >= 2g + 1. A clash can
only come from the *consistency of the sets Y_U over different U* (H may not contain all
k-subsets of any (2T−2)-set's worth of points with empty triple intersection), which is the
original problem again: it is not a counting statement about one U.
Two exact consequences of the local structure that are usable later:
- deletion invariance: for any X ⊆ V, H − X (edges avoiding X) has the same s on n − |X| points;
- if x lies in U and no edge through x lies inside U, then the link of x has a transversal of
  size n − |U|.

### 13.3 Why density (Frankl–Rödl type) arguments are too weak  [proved by hand for the estimates; the FR statements are cited, not re-proved]
- Density: |H|/C(n,k) >= 1/C(k+s,s) = exp(−s·ln(ek/s)(1+o(1))). In general s = Theta(k) and the
  density is exp(−Theta(k)): far below the (1 − delta)^n threshold of every forbidden-intersection
  theorem. Only in the near-complete regime s = o(k) is the density exp(−o(k)).
- What density can force there: a *pair* with a prescribed intersection in the linear range
  (non-degenerate). The two-anchor window (ROADMAP 3(b); improved form: no two edges meet in m
  with k/2 − 2g + 2 <= m <= k/2 + min(2g, 3g − c) − 2, obtained by requesting
  (A∩B) ∪ (V∖(A∪B) minus f points) and applying the tight-triple lemma) is non-empty iff
  c < 5g − O(1). With Frankl–Rödl for pairs this gives, for s <= s_0·k (s_0 an absolute constant
  coming from FR's delta), **g <= c/5 + O(1), i.e. tau <= 3k/4 + s/4 + O(1)** instead of Theorem A's
  s/2. [conditional on the uniform FR theorem; this is ROADMAP L4, same threshold]
- What density cannot force: (i) a triple with *empty* core. Exact emptiness of an intersection
  is never a density statement (stars are dense and 3-wise intersecting); it has to come from
  the transversal hypothesis, i.e. from a request, and each request costs a free part.
  (ii) [heuristic] A degenerate cell of size Theta(g): forcing a prescribed Venn diagram with a cell of
  relative size gamma needs density above exp(−c_1·gamma·ln(1/gamma)·k), while the available
  density is exp(−s·ln(ek/s)) with s >= 2g: the same order of magnitude as the entropy of the
  cell one wants to control, with the constants on the wrong side (s >= 2g against a cell of
  size about g). So the pattern "j exact anchors give g <= c(3−j)/(7−j)" stops at j = 2.
**The weak parameter is the density: the Turán hypothesis guarantees only a
1/C(k+s,s) fraction of the k-sets, and s is at least 2g by 13.1.**

### 13.4 Supersaturation of Fano tuples in a noisy complete family  [proved by hand]
Setting of 11.1(c)/12.1: Q ↦ K_Q with K_Q∩W ⊆ Q and outside part N_Q = K_Q∖W, |N_Q| <= theta'.
A Fano partition of a subset of W gives seven sets Q_L; the tuple (K_{Q_L}) is bad unless for
some point p the three outside parts of the lines through p have a common point. A concurrent
triple of a uniformly random Fano partition is a uniformly random "tight pattern" (three
k-sets, pairwise k/2, empty triple intersection), so the adversary needs
> P( N_Q ∩ N_Q' ∩ N_Q'' ≠ ∅ ) >= 1/7 over random tight patterns (Q, Q', Q'').
This is *not* hard for him: if all answers to requests that avoid a pool P contain P, the
probability is 1, at no cost in density. The number of Fano partitions is irrelevant
because they are all blocked by the same correlated outside set. What constrains the pool is
not counting but the budget: the answers to a request with slack sigma_0 have transversal
number > sigma_0, so the pool must move by sigma_0 points per request, and min-S caps it at theta.
The only gain supersaturation gives is against *uncorrelated* outside parts: if the N_Q were
independent theta'-subsets of a ground set of size much larger than theta'^{3/2}, a random Fano
partition would be bad with positive probability. A single ladder of outside points
(answer contains the first ladder point not requested) is beaten at cost O(1) per request.
So the counting helps exactly when the adversary is not adversarial.

### 13.5 Verdict
- No lemma closing part of the regime came out; the hand-proved by-products are 13.1 (a
  two-line proof of Theorem A, showing Theorem A is the complete content of "no tight triple
  inside one U"), the improved two-anchor window, and the 1/7 criterion of 13.4.
- Reason the architecture fails: (a) per-U counting is consistent with the local structure
  "complete on Y_U ⊂ U, |Y_U| < 3k/2" for every U; (b) the density is exponentially small
  except when s = o(k), and there it controls only non-degenerate pair statistics;
  (c) emptiness of a core is a transversal fact, not a density fact; (d) supersaturation is
  neutralised by correlation of the outside parts.
- What would be needed instead: a statement about the *system* (Y_U)_U, i.e. a stability
  theorem for 3-wise intersecting families with transversal number close to k/2 ("such a
  family is contained in the k-subsets of a set of size < 3k/2, up to small error") followed by
  a consistency argument over overlapping U. The first half is a clean extremal question that
  can be checked in the literature (Frankl's r-wise intersecting families with large covering
  number); the second half is where a contradiction would have to appear, and I do not see it.
- Cheapest decisive step for this route: decide the stability question above in exact form
  for 3-wise intersecting families with tau >= k/2 − j (literature check, then a small exact
  search at k = 6, 8: all 3-wise intersecting k-uniform families on 3k/2 + 2 points with
  tau >= k/2 − 1). If stability fails (there are 3-wise intersecting families with tau near k/2
  not of the "complete on < 3k/2 points" type), they are the building blocks of a candidate
  "complete minus tight triples" family and should be tested for (7,2) directly.
