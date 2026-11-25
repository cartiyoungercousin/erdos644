# Programme 4: exact search over profile (cell) families — independent re-implementation

Tags: [computed exact, certificate] / [computed, solver infeasible without certificate] / [proved by hand] /
[heuristic] / [open]. Code: `compute/programme4/cells/` (outputs in `certs/`). Nothing committed.
Brief 4 items 1 (cells) and 4 (rank test). The reviewer's script was not used; everything below is re-derived.

## 1. Setting and the two criteria [proved by hand]
V = X_1 ⊔ … ⊔ X_q, |X_i| = a_i, n = Σa_i; J a set of profiles j (Σ j_i = k, 0 ≤ j_i ≤ a_i);
H_J = {B ∈ C(V,k) : (|B ∩ X_i|)_i ∈ J}. H_J is invariant under Sym(X_1) × … × Sym(X_q).

**(τ) τ(H_J) > T ⟺ for every u with Σu_i = T, 0 ≤ u ≤ a, some j ∈ J has j ≤ a − u.**
τ > T means no set U with |U| ≤ T meets every member; the condition is monotone in U, so |U| = T suffices
(T ≤ n). A member B avoids U iff B ⊆ V∖U; one with profile j exists iff j_i ≤ |X_i ∖ U| = a_i − u_i for all i,
and this depends on U only through u = (|U ∩ X_i|)_i. ∎

**(7) H_J has a good seven ⟺ there are integers x^i_S ≥ 0 (S ranging over the 127 nonempty subsets of [7]) with
Σ_S x^i_S = a_i, support {S : some x^i_S > 0} pairwise intersecting, and for each m ∈ [7] the profile
p_m = (Σ_{S ∌ m} x^i_S)_i lies in J.**
Seven members B_1..B_7 (repetition allowed: "at most seven") have no transversal of size ≤ 2 iff every pair
{x, y} (x = y allowed) is avoided by some B_m, i.e. the co-types I_x = {m : x ∉ B_m} are nonempty and pairwise
intersecting (GLOSSARY "co-type"). (⇒) put x^i_S = #{x ∈ X_i : I_x = S}; then B_m = {x : m ∉ I_x} has profile
p_m ∈ J. (⇐) give the points of X_i co-types with these counts (any assignment: cells are symmetric) and set
B_m = {x : m ∉ I_x}; its profile is p_m ∈ J, so |B_m| = k and B_m ∈ H_J; the co-types are pairwise
intersecting, so this is a good seven. ∎
*Monotone form (used for cuts and by the MILP):* if the support is pairwise intersecting and
A_m = (Σ_{S∌m} x^i_S)_i, then J ∋ j_m ≤ A_m for every m already gives a good seven (choose B_m inside
{x : m ∉ I_x}; the true co-types only grow, so stay intersecting).
*The brief's Fano criterion* is the special case support ⊆ {lines through p : p a Fano point} (a point of colour p
has co-type "the 3 lines through p"; two such triples meet in the line through both points), in monotone form.
*Complete list of seven types.* The 127-co-type statement above IS the complete list; no classification is used.
Equivalently (replace every co-type by a minimal set of a maximal intersecting family containing the support):
the 716 S_7-classes of maximal intersecting families on [7] (one, the dictator, is infeasible: it forces B_1 = ∅).
So the brief's "127 co-types" and PROGRAMME3_BULK's "716 types" are the same complete list. The search does not
use "Fano-type for n < 11k/6"; it checks all types at every n (§3b tests whether Fano types would have sufficed).
*Test* [computed exact]: on 135 random small instances (q ≤ 3, k ≤ 5, n ≤ 11) both criteria agree with explicit
enumeration (`brute.py`: members as bitmasks, τ by exhaustive T-sets, good seven by a SAT search over ≤ 7 members,
no co-types) — 0 mismatches, 54 seven-free / 81 with a seven.

## 2. Method
CEGAR (`cells.py`). SAT (CaDiCaL) over one Boolean per profile: clauses (τ) for every u, plus cuts. Each model J
is minimised to a minimal covering J' ⊆ J and handed to CP-SAT, which searches (7) over all 127 co-types (members
sorted by profile index: relabelling [7]). If a seven is found, its co-types are shrunk greedily (support kept
intersecting) and the cut "J misses one of the seven boxes {j : j ≤ A_m}" is added. End: UNSAT (no (7,2) family
with τ > T on that split) or a seven-free covering J.
Certificates: each UNSAT instance stores its cuts with their witnessing x. `check_cert.py` (imports nothing from
`cells.py`, no solver) re-checks every x (nonempty, pairwise intersecting support, cell sums), recomputes the boxes
and the covering sets C_u, and shows by exhaustive hitting-set branching (both properties monotone, so the
branching is complete) that no J hits every C_u while missing a box of every cut. Mutation test: dropping one cut
or corrupting one x makes the checker fail.
Seven-free verdicts (achievability) are CP-SAT infeasibility, re-checked by an independent HiGHS MILP formulation of
the monotone criterion (`seven_milp.py`) for the complete families (explicit SAT on K(13), K(16) is a hard
symmetric UNSAT and was dropped).
Splits: all a_1 ≤ … ≤ a_q with a_i ≥ 1 (q = 1 is the complete family); n from k + T (below that τ ≤ n − k + 1 ≤ T)
to ⌊2.4k⌋ (two cells) / ⌊2.3k⌋ (three cells).

## 3. Two cells (and one cell): the table — CONFIRMED (k = 8..20, incl. k = 19)
Upper bound: for T = ⌊(3k+5)/4⌋, NO one- or two-cell family with τ > T on any split, n = k+T … ⌊2.4k⌋
[computed exact, certificate]: 1904 instances, every one UNSAT, all certificates re-checked by `check_cert.py`
(`certs/k{k}_T{T}_q{1,2}.jsonl`, log `certs/check_two_cell.txt`). Lower bound: the families below are seven-free
[computed, solver infeasible without certificate: CP-SAT; for K(n), k ≥ 10, also HiGHS MILP, `certs/verify_extremal.jsonl`].

| k | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| largest τ (≤ 2 cells, n ≤ 2.4k) | 6 | 8 | 8 | 9 | 10 | 11 | 11 | 12 | 13 | 14 | 14 | 15 | 16 |
| ⌊(3k+5)/4⌋ | 7 | 8 | 8 | 9 | 10 | 11 | 11 | 12 | 13 | 14 | 14 | 15 | 16 |
| complete family alone (1 cell) | 6 | 8 | 8 | 9 | 9 | 11 | 11 | 12 | 12 | 14 | 14 | 15 | 15 |
| extremal example (n) | K(13) | K(16) | K(17) | K(19) | P(10,12),P(11,11) | K(23) | K(24) | K(26) | P(13,16),P(14,15) | K(30) | K(31) | K(33) | P(16,20),P(17,19),P(18,18) |

K(n) = complete k-uniform family on n points, τ = n − k + 1 (it has a good seven at n + 1, CP-SAT witness).
P(a_1,a_2) = parity family {B : |B ∩ X_1| odd}, at n = 22, 29, 36; these are the first n at which a two-cell
seven-free family with τ = ⌊(3k+5)/4⌋ appears (scan `run_achieve.py`, `certs/ach_*.jsonl`). At k = 8 the
two-cell families also stop at τ = 6 (six splits of n = 13, J an interval — sub-families of K(13)).
**Verdict:** the brief's table is CONFIRMED for k = 8..18, 20; k = 19 (not in the brief) also fits: 15.
Only k ≡ 0 (mod 4) needs a second cell; for k ≢ 0 (mod 4) the complete family already attains ⌊(3k+5)/4⌋.
Excess τ − 3k/4: 5/4 (k ≡ 1), 1/2 (k ≡ 2), 3/4 (k ≡ 3), 1 (k ≡ 0, k ≥ 12), so **C_1 = C_2 = 5/4** on 9 ≤ k ≤ 20,
attained by complete families at k ≡ 1 (mod 4).

## 3b. Fano sufficiency (coordinator's priority item) — FAILS [computed]
Second CEGAR pass (`fano_suff.py`): every proposed covering J is searched first for a Fano-type seven (co-types in
the up-closure of a fixed Fano plane on the member labels = the brief's criterion), and only then over all 127
co-types. All J examined have τ > T, T ∈ {⌊(3k+5)/4⌋ − 1, ⌊(3k+5)/4⌋}. Counts (two cells; one cell: 0 everywhere):

| k | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| J examined, n ≥ 11k/6 (both T) | 289 | 312 | 540 | 643 | 699 | 1051 | 1308 | 1786 | 1795 | 2097 | 3015 | 3323 | 3797 |
| seven only of non-Fano type | 29 | 4 | 23 | 18 | 9 | 9 | 33 | 36 | 22 | 13 | 58 | 46 | 41 |
| … of which τ > max (row of §3) | 11 | 0 | 6 | 4 | 0 | 0 | 10 | 10 | 4 | 0 | 18 | 13 | 10 |
| same, n < 11k/6 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

Examples (J by first coordinate; seven-existence re-checked by building the 7 members on labelled points and
testing every pair; Fano-freeness re-checked SOLVER-FREE by enumerating all class-size vectors, x^1 up to the 168
collineations — `verify_nonfano.py`, `certs/verify_nonfano_all.jsonl`). All 341 two-cell cases: seven re-checked
explicitly; no Fano seven re-checked solver-free in 137 cases [computed exact], by a fresh CP-SAT run (1 h limit,
all NONE) in the 204 larger ones [computed, solver infeasible without certificate]. Examples:
- k = 8, a = (7,8), J = {j_1 odd} (a parity family), τ = 7, n/k = 1.875: good seven with 8 co-types, no Fano seven.
- k = 10, a = (10,13), J = {(1,9),(7,3)}, τ = 9 = ⌊(3k+5)/4⌋ + 1: non-Fano seven only.
- k = 20, a = (19,28), J_1 = {1,13}, τ = 17 = ⌊(3k+5)/4⌋ + 1.
So "τ > max ⇒ Fano-type seven" is FALSE in the cell class for k = 8, 10, 11, 14, 15, 16, 18, 19, 20 (above the
maximum: n/k ∈ [2.28, 2.40] for k ≥ 9; all non-Fano-only families seen have n ≥ 2k for k ≥ 9, n/k ≥ 1.875 at k = 8). Fano types suffice
below n = 2k in every case seen, and the n < 11k/6 row (0 of ~1300) agrees with the project's Fano result.
Caveat: these are the families the CEGAR happened to propose (minimal covering J, often only 2 profiles), not a
census; the counts depend on the search path. They show that a Fano-only statement cannot hold at all n.
Three cells (same pass, n ≤ 2.3k): k = 8 (T = 6): 3082 J examined, 119 non-Fano-only, all τ = 7, n/k ∈ [1.875, 2.25];
k = 9 (T = 8): 2129 examined, 0; k = 10 (T = 8): 8880 examined, 27 non-Fano-only, all τ = 9, n/k = 2.3. All 146:
seven re-checked explicitly, no Fano seven by fresh CP-SAT (`certs/verify_nonfano_q3.jsonl`). k = 11, 12 not run.
**Answer: yes — at n ≥ 11k/6 and τ at or above the maximum, families whose only good sevens are non-Fano exist for
most k (none below n = 11k/6; for k ≥ 9 none below n = 2k).**

## 4. Three and four cells — PARTIAL (dropped on coordinator's request)
No three-cell family with τ = 7 (k = 8, n ≤ 18), τ = 9 (k = 9, n ≤ 20), τ = 9 (k = 10, n ≤ 23): every split UNSAT
(`certs/fano_k{8,9,10}_T*_q3.jsonl`; certificates re-checked by `check_cert.py`: 107 + 114 + 211 instances, 0 failures) [computed exact, certificate].
So for k = 8, 9, 10 three cells add nothing: C_3 = C_2 there (k = 8: 0; k = 9: 5/4; k = 10: 1/2), extremal J are the
one-cell (complete) families, lifted. [open]: k = 11 (τ = 10), k = 12 (τ = 11), four cells; C_3, C_4 in general.
Two Kaggle kernels (plain `cells.py` CEGAR, 3 cells k = 8..12, 4 cells k = 8) were still running at hand-off
(`erdos644-p4cellsa/b`; fetch with `tools/kaggle_run.py fetch`); their results are not in this note.

## 5. Rank test (Route 3) — NOT RUN (dropped on coordinator's request)
Script `rank_test.py` written, run stopped before output. Hand remark [proved by hand, short]: for a profile family
with, in each cell, some j ∈ J having 0 < j_i < a_i, the F_p-kernel of the member–point matrix consists of cell-constant vectors c with
Σ_i j_i c_i = 0 for all j ∈ J; so complete families have deficit 1 iff p | k and parity families deficit 1 over F_2
— the deficit follows the arithmetic of J and k, not seven-freeness (K(n) with p ∤ k is seven-free with full rank).
This predicts no consistent signal; [heuristic] until computed.

## 6. Caveats
- Scope: profile families only, n ≤ 2.4k (two cells) / 2.3k (three, four cells); all splits, all J. Nothing here
  bounds f(k,7) for general families; Conjecture 2 stays [open].
- UNSAT verdicts carry checkable certificates; the final step of each check is an exhaustive hitting-set search in
  plain Python (no solver). Seven-free (lower-bound) verdicts are solver infeasibility only (CP-SAT, and HiGHS MILP
  for the complete families); the parity-family MILP runs did not finish within ~30 min and were stopped, so
  P(…) rests on CP-SAT alone (twice: `run_achieve.py` and `fano_suff.py`, different cut sequences).
- The criteria (τ) and (7) are proved in §1 and were tested against explicit enumeration on small cases; the
  record-verification path (explicit members + SAT) was not needed: no record found.
- Fano-sufficiency counts (§3b) are over CEGAR-proposed families, not a census.
- Brief claims about k = 11, 12 three cells and all four-cell claims: not re-checked here [open].
