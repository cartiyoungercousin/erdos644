# STRATEGIST — critical review and new candidate approaches for Erdős #644

Fresh strategist pass, about 90 minutes, 2026-11-24. Read: STATUS_AND_PLAN, NEW_PATHS §11–13 (rest by
headings), FRESH_A/B/C (incl. C §11), TWIN (incl. §11–12), LIT_11_13, LITERATURE, ROADMAP excerpts, Lean
theorem headers. No computation was run (nothing cheap enough was decisive; see §4). No full solution.
Tags: [proved by hand] / [computed exact] / [numerical] / [heuristic] / [literature].
"Proved by hand" items below are short and were written in this pass only; none is machine-checked.

---------------------------------------------------------------------------------------------

## 1. Where the team stands (blunt)

**Solid (Lean or short, re-checkable hand proofs).**
- Tight-triple lemma, Theorem A (tau <= (n-k)/3 + k/2), sparse-triple lemma (tau <= S + (k+2)/3), stability
  inequality tau <= (17k - 7 sigma)/11, Lemma 3 (flat 7-tuples), Fano criterion, lopsided top, pair gap.
- Negative results that are real theorems: Theorem 8 / TWIN §3 (the seven-request game without discards
  cannot go below 4/5 by hand, 5/6 computed, 7/8 against a genuine complete family); fixed templates give
  only 3n/7; shifting and fractional covers are useless; one-anchor templates stop at 5/6.

**Evidence only.** Everything quoted against "scripted", "menu" or "rule-following" adversaries (all the
3(1-T) values, t*(8) = 3/4, the lex-anchor grids at 0.84/0.85). FRESH_C itself showed twice that such
wins vanish against a real adversary. These numbers should not be cited as progress towards 3/4.

**True bottlenecks.**
1. *No upper bound below the 2026 claims and no route to one.* All proved tools give 3/4 only when one of
   (n <= 7k/4 + o(k)), (sigma >= 5k/4 - o(k)), (S <= 5k/12) holds. The middle is untouched: by NEW_PATHS
   §12 it is "a T-Turán subfamily of K_N, N > 7k/4 + 3 eps k, with no tight triple and no bad 7-tuple".
2. *The conjecture is open even on a ground set of 2k points* (best: 5k/6 from Theorem A, 6k/7 from
   3n/7). Every game the team could not solve (TWIN §6, FRESH_C §9–11) is this sub-problem in disguise:
   with unbounded requests, "requester beats every adversary confined to N points" is literally
   "no (7,2)-family with tau > T on N points" [proved by hand, FRESH_C §8.4 + TWIN 11.1]. So a game solver
   is not a shortcut around the mathematics; it is the same problem with a worse search space.
3. *The request game has unbounded memory.* Each reply doubles the type space; the MILPs die at 5–7
   replies with 0/1 realisation flags (FRESH_C §11.1). There is no bounded state on which an invariant
   could be stated, hence no candidate theorem.
4. *Nothing uses the fact that H is one fixed family* beyond lex-min / min-S anchors on triples.
   The pool pseudo-adversary (§9–§10) is adaptive; a real family is not. Tools that see consistency
   across all T-sets at once (criticality, saturation, irreducibility) are almost unused.
5. *No counterexample candidate either.* Searches covered 2–3 block profile families and parity types,
   several stopped unfinished (cegar2 at 240 s, pool_family scan, scan2). The disproof side is thin.

My reading of the odds: the conjecture is probably true, but the evidence for that is only "nothing found
in small design spaces"; the team should budget for both directions.

---------------------------------------------------------------------------------------------

## 2. Things missed or worth correcting

**2.1 Two templates, and the range where Fano is the only one.** FRESH_A's rigidity (non-Fano bad
7-tuples need union >= 11k/6, [numerical]) and FRESH_C §11.2 (the ten blocks of the 2-(6,3,2) design give
six edges without a 2-cover on exactly 2k points, [proved by hand]) fit together: for
7k/4 <= N < 11k/6 Fano is the only shape; from 2k on there is a second rigid one. Any "Fano steering"
rule or rigidity argument is therefore only meaningful for N < 11k/6, and TWIN §7.3's "Fano up-set is the
natural one at N = 2" should be read as unproved. Consequence for planning: split the confined problem
into **zone I: 7k/4 < N < 11k/6** (single template, linear-algebraic rigidity available) and
**zone II: 11k/6 <= N <= 7k/3** (mixed templates). Zone I is the right first target; nobody has isolated it.

**2.2 Good-triple 3-graph is Fano-free [proved by hand].** Let G(H) be the 3-graph on the edges of H
whose hyperedges are the good triples (empty common intersection). By the Fano criterion, a copy of the
Fano plane in G(H) is a bad 7-tuple, so
> H (7,2)  ==>  G(H) contains no Fano plane; and if all edges lie in fewer than 11k/6 points this is an
> equivalence (given FRESH_A's rigidity value).
This connects zone I to the hypergraph Turán problem for the Fano plane [literature: de Caen–Füredi 2000
(density 3/4), Füredi–Simonovits and Keevash–Sudakov 2005 (extremal = balanced bipartite, with
stability), Mubayi 2005 (codegree density 1/2), Keevash 2009 / DeBiasio–Jiang 2014 (exact codegree
threshold)]. Because the Fano plane covers pairs, these densities are blow-up invariant, so they hold
for every probability measure nu on H:
> for every nu on a (7,2)-family, P_nu(E∩F∩G = ∅) <= 3/4, and some pair A,B (possibly A = B, to be
> checked against the proof of Mubayi's theorem) has nu{C : A∩B∩C = ∅} <= 1/2 + o(1).
Honest value: in the dense regime (n <= 7k/3) good triples are rare under every natural nu, so the
density theorems do not bite directly [heuristic]; the request principle gives only "every pair with
|A∩B| <= T has codegree >= 1". The use is as a *language*: zone I of the conjecture reads "a T-Turán
subfamily of K_N whose good-triple graph is Fano-free has T <= 3k/4 + o(k)", and bipartite stability
suggests what a counterexample would look like there: H = H_1 ∪ H_2 with each H_i (nearly) 3-wise
intersecting. Note tau(H) <= tau(H_1) + tau(H_2) <= k + 1 for such H, and the complete family
K_{7k/4-1} is very far from 2-colourable (its G needs about k/4 colours, [literature: Sarkaria-type
generalised Kneser bound, quoted from memory, NOT re-read]). So "Fano-free" for G(H) is realised in the
extremal example by sparseness of G, not by bipartiteness; that is a sharp way to say why density
methods fail, and it is the object Candidate C works on.

**2.3 Merge-irreducible normal form [proved by hand].** Identifying two points u, v (edges containing
both lose a point; sizes <= k are allowed, FRESH_A §3) preserves (7,2) (the image of a 2-cover is a
2-cover) and changes tau by at most 1. It leaves tau unchanged iff no minimum transversal contains both,
i.e. iff tau(H - u - v) >= tau - 1. Hence a counterexample with the fewest points satisfies
> every pair of points lies in a common minimum transversal; equivalently for all u != v there is a set D
> of T - 1 points such that every edge avoiding D contains u or v.
Together with tau-criticality (every edge E is the unique edge missed by some T-set X_E) and saturation
(adding any k-set creates a bad 7-tuple) this is a three-part normal form of a minimal counterexample.
TWIN §11.5 ("compression does not work") is about simulating requests in a game; it does not apply to
this operation on a fixed family. The team has criticality (unused) and saturation (NEW_PATHS Path 5,
unused) but not the pair statement.

**2.4 Literature gaps that could change the plan.**
- Kostochka 2002 (Combinatorica 22, 275–285) is still unread; the abstract's formula "for large p and
  huge r" could not be retrieved in this pass either (Springer paywall; search snippets cut off). It
  matters more than EFKT92: if his large-p asymptotics differ from the complete-family (Mills) value
  1/(g(p)-1), then complete families are not extremal in general and his construction is the template
  to test at p = 7; if they agree, his upper-bound method is a non-request technique to import.
  [literature: zbMATH review of EFKT92 says f(r,p,t) is of order r·p^(1-1/t)... quoted from a search
  snippet, unverified and suspicious as written; get the paper.]
- erdosproblems.com/644 returned HTTP 403 to automated fetch; comments there were not checked.
- Hypergraph Turán for the Fano plane (above) and pair-covering design structure theory beyond Mills'
  thresholds (classification of optimal coverings with <= 7 blocks) are not in LITERATURE.md.

**2.5 Small corrections.**
- FRESH_C §10 obs. 1 ("any proof below 7/8 must use more than seven requests") should say "or an
  extremal choice": the 6/7 and 11/13 arguments keep seven edges but choose the anchor by minimality,
  which is an unbounded number of implicit requests.
- A potential that looks natural for local search, mass(D) of six edges, has trivial local minima: six
  equal edges have mass(D) = 1 and every single replacement raises it [proved by hand]. Any
  swap/minimality argument on 6- or 7-tuples needs a potential that penalises repeated edges.
- I re-derived FRESH_A Theorem 1 and Theorem 11.1's K_N tightness check; both are correct as written.

---------------------------------------------------------------------------------------------

## 3. New candidate approaches

Chances are for "yields a full solution" / "yields a publishable partial result"; they are rough.

### Candidate A — Template theorem: settle the conjecture for all block-symmetric (profile) families

*Idea.* In H(P) (blocks V_1..V_m of sizes n_j k, all k-sets with profile in P) the adversary chooses only
the profile of a reply; the requester chooses the placement inside blocks. This removes exactly the
weapon that defeats every current argument (correlated placement of outside parts, the pool) and the
0/1 realisation flags (she never leaves slivers). It is the "limit object" of FRESH_B §1.6, which was
defined but never attacked as a theorem.

*Key lemma (Template lemma).* Let Q ⊂ ∏[0, n_j] be a set of co-profiles, |m| = N - 1 for m ∈ Q, such
that every d with |d| <= T is dominated by some m ∈ Q. If T >= 3/4 + eps then there are m^1..m^7 ∈ Q, a
pairwise intersecting family F on [7] and probability distributions on F for each block j (one common
labelling) with marginal_i <= m^i_j / n_j. (For N < 11/6: F = Fano pencils, i.e. W_j ∈ {W >= 0,
sum 3, pencil sums >= 1}, W_{L,j} <= m^L_j/n_j. From 2k on, the 2-(6,3,2) shape must be allowed.)
Known special cases: m = 1 (complete families), convex P (Cor. 3b), single profiles (FRESH_B 1.5).

*Why it might succeed.* It is finite-dimensional and convex-geometric; Cor. 3b already gives a mixture
lambda on P with mean density <= 4/7 in every block, so the lemma is a rounding statement ("seven
profiles instead of a mixture, with Fano-compatible line sums in each block"). A proof would be a real
theorem (the conjecture for every family invariant under a product of symmetric groups) and would end
all block-type disproof searches. A failure is a counterexample.

*Cheapest decisive test.* Finish what `cegar2.py`/`scan2.py` started, with all intersecting shapes: exact
CEGAR over two- and three-block profile sets on a 0.05 grid, T ∈ {0.76, 0.80}, N ∈ {1.8, 2.0, 2.2}, on an
idle machine with a real time budget (hours, one worker). Either a surviving Q (counterexample
candidate, then verify by exact rational LP and a discrete instance) or an exhausted search that shows
which shapes and which rounding the proof needs.

*Chance / effort.* Template lemma proved or refuted: 30%. Full solution from it: 5% if refuted with a
genuine survivor; a proof does not lift to general H by itself (no symmetrisation), but see B.
Effort: 1–2 days compute + 2–3 hand passes.

### Candidate B — Bounded-register game and a Lyapunov potential (replaces the discard solver)

*Idea.* Give the requester memory of exactly seven edges. A move: pick an index c and a T-set D, replace
B_c by the reply. She wins when the seven are bad. State space: 127 type masses, fixed forever; no game
tree. A proof is a potential Phi on 7-edge Venn profiles with a one-step lemma. This is the
extremal-choice principle (lex-min triple, min-S triple) lifted from triples to 7-tuples: the seven
edges minimising Phi in the fixed family H satisfy, for every c and every edge B' of H,
Phi(swap) >= Phi — constraints of the same kind as the 11/13 repo's (7),(9) but 7·2^7-dimensional
and with nothing left to "close" afterwards.

*Key lemma.* There is a Phi, well-founded on discrete profiles, such that for T >= (3/4+eps)k every
2-coverable 7-profile admits (c, D), |D| <= T, with Phi(new) < Phi(old) for every reply.
First structural facts [proved by hand]: with a Fano labelling and M_c = union of B_a∩B_b over the lines
{a,b,c}, replacing B_c by a reply to D ⊇ M_c empties the three line-triples through c and leaves the
other four untouched; so in a Phi_0-minimal labelled tuple (Phi_0 = total mass of line-triple
intersections) every c on a non-empty line has |M_c| > T and M_c is a transversal of H; moreover
sum_c m_c = sum_x C(deg x, 2), which ties Phi_0 to the pair-overlap energy that Lemma 3 controls.
Phi must combine Phi_0, the energy, and a term for the second template.

*Why it might succeed where the request games stalled.* Unbounded requests are necessary below 7/8
(FRESH_C §10); the discard game makes them available but with exploding state, and its certified
solver failed (FRESH_C §11). The register game has bounded state and its proof object is checkable
(one LP/MILP per face of a piecewise-linear Phi). It also works on the real family, so the hosting
leak of TWIN §12.2 does not arise: caps are paid on real points.

*Cheapest decisive test.* Zone-I linearisation. Around the Fano blow-up on N = (7/4 + c) points all
quantities are O(c): seven class defects, omission masses, 7 + 21 + 35 small cells. Compute (exact LP,
no flags to first order) whether the swap dynamics against K_N with slack s = N - 1 - T contracts for
T - 3/4 = g with c/g ∈ {4, 6, 10} (this is NEW_PATHS §12.5's instance, but as a one-step contraction
test instead of a six-round game). Contraction for some fixed ratio gives the candidate Phi; a
non-contracting direction is an explicit near-Fano pseudo-family to test for realisability.

*Chance / effort.* Useful potential in zone I: 20%. Full solution: 3–5%. Effort: 2–4 days.
Risk: slivers (measure-zero realised types) make Phi discontinuous; in zone I they are the "defect
cells" and must be carried as O(1) terms explicitly.

### Candidate C — Zone I as a Turán problem: T-Turán subfamilies of K_N with Fano-free good-triple graph

*Idea.* For 7k/4 < N < 11k/6 the conjecture is equivalent to: if H ⊂ C([N], k), every (N-T)-set contains
an edge, and G(H) is Fano-free, then T <= 3k/4 + o(k) (by §2.2). Theorem A gives T <= 3k/4 + c/3
(c = N - 7k/4); NEW_PATHS §13.3 has a conditional c/5. Target: o(c)·... i.e. any bound g <= delta·c with
delta -> 0, or a construction with g >= delta_0·c.

*Key lemma (two versions, either decides zone I).*
(C1, proof side) Local 2-colouring: for every U with |U| = 2T - 2 the edges inside U are 3-wise
intersecting (Lemma 12.2). Show that two such sets U, U' with |U ∩ U'| >= 3k/2 + 2g force a common
"core" Y_U ∩ Y_U' of the two local structures, and that three pairwise-compatible cores contradict the
Turán property on U ∪ U' ∪ U''. This is the "consistency of Y_U across U" that §13.2 names as the
whole problem; the new input is the Fano-free/bipartite stability language of §2.2 and the pair
normal form of §2.3 (every pair of points in a minimum transversal kills junk vertices, the main risk
listed in ROADMAP R2).
(C2, disproof side) A subfamily of K_N, N = 7k/4 + c, that is s-Turán with s = c - g, g >= delta_0·c,
all of whose good triples have union > 2T - 2 and whose good-triple graph is Fano-free. By §2.2 such a
family cannot be block-type with few blocks for free; candidates are *geometric*: edges = complements
of structured sets in a design/affine space on N points where "three complements cover" is controlled
algebraically. FKW's parity family is the c = O(1) member of this class.

*Why it might succeed.* It is the only regime where (7,2) is a single forbidden configuration, where
everything is O(c), and where a full answer (either sign) is new and decisive: a zone-I counterexample
disproves the conjecture; a zone-I proof gives the mechanism missing on the dense side.

*Cheapest decisive test.* Exact small instances of the zone-I question at the first non-trivial sizes
with g >= 2: (k, N, T) = (12, 23, 11), (16, 30, 14), (16, 31, 14) via CEGAR-SAT with symmetry
(cyclic or PSL-invariant families, as ROADMAP Search A planned but did not finish). The bad-tuple
oracle is cheap here: only Fano sub-blow-ups need to be searched.

*Chance / effort.* Decide zone I for c/g bounded: 15%. Full solution: 5% (via C2) / 3% (via C1).
Effort: 3–5 days.

### Candidate D — Minimal-counterexample normal form (criticality + saturation + pair-irreducibility)

*Idea.* Stop playing against adaptive pseudo-adversaries; use the fixed family. In the normal form of
§2.3: (i) every edge E has a T-set X_E missed by E only; (ii) every pair u,v has a (T-1)-set D_{uv} with
all replies meeting {u,v}; (iii) every non-edge k-set K has six edges whose dangerous set D_6 misses K.

*Key lemma.* In normal form, the pool of NEW_PATHS §9 cannot exist: if two outside points u, v occur
together in every reply to requests inside W, they are mergeable, so (ii) forces replies that separate
them, i.e. the outside parts of replies are not a common pool but a family with transversal structure
of its own; quantify this as rho <= C·eps·k in Theorem 8.1.
Supporting facts available: (i) gives *forced* replies (requests with a unique answer), which is exactly
what the confined games needed and lacked; (iii) gives, for each T-set, many alternative replies.

*Why it might succeed.* The barrier §9–§10 was established against constraints that never mention
other requests; (i)–(iii) are global consistency constraints and are cheap to add to the existing
exact LP of §9 as linear side conditions on the witness.

*Cheapest decisive test.* Re-run the §9 outside-overlap LP (`compute/newpaths`) with the witness
required to satisfy (ii) for pairs of pool points and (i) for the anchor edges. If the maximal overlap
drops from 0.59k towards eps·k the pool barrier is an artefact; if it stays, write down the witness's
minimum transversals — that is the first explicit description of a putative counterexample.

*Chance / effort.* Kills the pool barrier: 15%. Full solution: 2–3%. Effort: 1–2 days. Cheapest of the four.

### Candidate E (literature, not a method) — get Kostochka 2002 and EFKT92 in full
One library request. Possible outcomes are listed in §2.4; either one changes the priorities above.

---------------------------------------------------------------------------------------------

## 4. Ranking and the single best next experiment

Ranking by (chance × value) / cost:  **A (template theorem)  >  D (normal form vs the pool LP)  >
C (zone I Turán problem)  >  B (register potential)**, with E in parallel at zero cost.

**Best next experiment: the exhaustive block-profile CEGAR of Candidate A** (two and three blocks, all
intersecting shapes including the 2-(6,3,2) one, T = 0.76 and 0.80, N ∈ {1.8, 2.0, 2.2}, exact
re-verification of any survivor). It is the only experiment on the table whose both outcomes are
decisive for a whole class: a survivor is a counterexample candidate with macroscopic structure; an
exhausted search, read for which seven profiles and which shape win, is the statement of the Template
lemma. It reuses `profile_milp.py` and needs machine time, not new theory.

Why no computation was run in this pass: the decisive ones (A's CEGAR, D's LP with side conditions)
need hours on an idle machine or a careful reading of `compute/newpaths` models; a rushed partial run
would add another "stopped unfinished" entry, which the record already has too many of.

Do not spend more on: monolithic MILP game trees with realisation flags (FRESH_C §11.1 is conclusive
about why they fail); seven-request games (value 7/8, settled); density/supersaturation counting
(§13 and §2.2 agree it cannot see the sparse good-triple graph).
