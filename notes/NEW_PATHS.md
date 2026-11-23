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
