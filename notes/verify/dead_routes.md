# Verification: "dead route" proofs (referee audit)

Scope (narrowed by the coordinator): CORE §100–§104 (links, traces, exclusions; Theorem 102.1), plus a review
of the plan in `notes/FABLE_C.md` §1. The entropy (§70–§74) and container (§85–§89) audits were NOT done; they
stay at HAND.
Code (independent of `compute/links/`): `compute/fableD/static_cert.py`, logs in `compute/fableD/logs/`.
Method of the code: a static certificate is counted by co-type (127 integer variables, disjoint co-types may not
both occur), which is exact for each (k, T, n, q). Cross-checked against a point-level SAT model on 10 small
cases (`sat.log`, all agree).
Tags: [checked by hand] / [computed exact] / [not checked].

## Verdict: CORE §100–§104

**PASS for the route's death, with one wrong sentence (100.1(c)) and one scope gap (102.1 for N >= 2, q >= 4).**
Neither reopens a link route.

| item | claim | verdict |
|---|---|---|
| 100.1(a),(b) | a link is (T − s)-covering; a good seven in the link lifts to V | PASS [checked by hand] |
| 100.1(c) | "every link of P_Y ... has no good seven once s > ε" | **FAIL as worded** (see 1) |
| 100.2 | (N, t, ω, ε, δ) ↦ (N − s, t − s, ω, ε − s, δ − s); the three margins drop by 4s, 2s, 2s | PASS [checked by hand] |
| 100.3 | the pool family's link at S disjoint from Y has no good seven once s > ε | PASS [checked by hand; computed exact] (see 2) |
| 101.1 | averaging identity for link densities | PASS [checked by hand] |
| 101.3 | no pair (q = 2) certificate inside any link above the strip | PASS (follows from 102.1, q = 2) |
| 102.1 | slack inequality, as stated with the hypothesis "every co-type has size >= 3" | PASS (one line) |
| 102.1, q = 2 | hypothesis holds for t < 2/√5, so a pair certificate needs ω + 4\|S\| <= 4ε | PASS [checked by hand; computed exact, including N >= 2] (see 3) |
| 102.1 Corollary | "S_q depends on (N, t, q) only", read as a cap on waste for all q | **GAP for N > 2, q >= 4** (see 4) |
| 102.2 | traces: the gain (3 − q)u is not liftable; dead for q = 2 | PASS for q = 2; q >= 3 is a remark, not a proof |
| 102.3 | exclusions cannot be forced | PASS (P_Y has no member avoiding a point of Y) |
| 103.1 | P_Y has no Q′ quadruple above the strip: σ >= 1 − t > (3t − N)/2 | PASS [checked by hand] |
| 103.2 | pencil window in a link is [N − 2t + 2s, N − 3/2], width 2(ε − s) | PASS [checked by hand] |
| 103.3 | hybrids reduce to the §33(4) stability problem | heuristic; not a proof, and tagged so in the source |

### 1. 100.1(c) is false as worded
For a link at S with a = |S ∩ Y|, the link of P_Y is the pool family with core Y ∖ S on V ∖ S; outside the core
it is the complete family of (t − s + a)-sets on a ground of mass 1 + t − s + a. It has a good seven iff
t − s + a >= 3/4, i.e. iff **|S ∖ Y| <= ε**, not s <= ε. 101.2 already uses the correct version (the link at
S = Y is complete and has a good seven), so the source contradicts itself.
[computed exact, `pool.log`, last block: links inside the core at (8,6,16), (12,9,23), (16,13,31) have good
sevens for s > εk.]
Consequence: none for the verdict. The correct reading is "a link is harmless only through points common to all
members of the target seven".

### 2. 100.3
The proof cites the waste identity 2.1, which needs co-types of size >= 3 and was stated for N < 2. It is still
valid here: outside Y the members are (t − s)-sets on a ground of mass 1 + t − s, two of which never cover it.
[computed exact, `pool.log`: 0 violations over 115 instances (k = 8..20); a good seven exists in every tested
instance with s <= εk.]

### 3. Theorem 102.1 at q = 2
The hand argument (two lines, a line and a member, or two members cannot cover V; for N >= 2 the bipartite count
5t²/4 < 1) is correct.
[computed exact, `q2.log`: 115 instances, k ∈ {4, 8, 12, 16, 20}, all T with 3k/4 <= T < k, all n from k + T to
3k − T + 2. A q = 2 certificate exists iff n <= 5T − 2k, and the largest common part always satisfies
4|S| <= 5T − 2k − n. No violation, 42 infeasible instances with n >= 2k included.]

### 4. GAP: the hypothesis of 102.1 fails for N > 2 and q >= 4
Exact line: §102, Corollary, "S_q depends on (N, t, q) only. An operation that only chooses which members of 𝒞
to use ... cannot add slack", and §104 Status (3). Both drop the hypothesis |J_x| >= 3. It is proved only for
q = 2.
- For N > 2 two members can cover V, and a point outside both edges may have a co-type of size 2 (waste −1).
- [computed exact, `q3.log`] Maximum of (waste on co-types of size >= 3) + 4|S| over certificates, against k·S_q:

| (k, T, n) | q = 3 | q = 4 | q = 5 | q = 7 |
|---|---|---|---|---|
| (8, 6, 17) | 0 / 0 | **4** / 3 | **8** / 6 | **16** / 12 |
| (12, 10, 25) | 4 / 4 | **8** / 7 | **12** / 10 | **18** / 16 |
| (16, 13, 34) | 4 / 4 | **11** / 9 | **18** / 14 | **32** / 24 |

  With size-2 co-types forbidden the maximum equals k·S_q in all 40 instances, and for n <= 2k nothing exceeds it.
- Correct statement: waste + 4|S| <= S_q + m_2, where m_2 is the mass of points with a co-type of size 2. Each
  such co-type is a pair of members with disjoint edges, so m_2 <= (N − 2) per pair and m_2 = 0 for N <= 2.
- Effect: in the top quarter of the window, 2 < N < 3 − t, the "static budget" for q >= 4 is larger than S_q by
  up to a multiple of N − 2 <= 1/4 − ε. FAILED_ROUTES item 13 and LEDGER state the invariant without this.
- It does not revive links: the pair route uses only q = 2, and Q′ is blocked by the pool family (103.1), not by
  the budget.

### What "dead" does and does not cover [checked by hand]
Proved:
- no lemma about one link, valid for all T-covering families, can hold once |S ∖ (common core)| > ε (pool family);
- for s <= ε a link is the same problem at (ω, ε − s), which is the stronger statement;
- no q = 2 certificate in any link above the strip;
- Q′ is not forced by covering alone.

Not proved (so external ideas of these forms are not excluded by §100–§104):
- arguments using many links jointly (this is CP, as the source says);
- static certificates with q >= 4 inside links at N > 2, where 102.1's cap is not the right number;
- anything adaptive. The net budget after the baseline dump of ω per free reply beyond the second is
  S_q − (q − 2)ω = 5ε − δ **for every q**, so no choice of q helps against a dumping adversary; the gain must
  come from forcing useful dumps, not from the count.

A repaired link route would have to choose S inside the common part of the final seven (cost 4|S| from the
budget), so it needs a structural reason why such an S of mass > ε exists. In P_Y that is S ⊆ Y. This is the
near-pool stability statement again.

## FABLE_C plan review

Reviewed: `notes/FABLE_C.md` §1 (plan only; no results yet).

**(i) "Σ_6: six members with |U_6| <= t implies CP." Correct** [checked by hand]. T-covering gives a member
K_7 ⊇ U_6, and every uncovered pair has both ends in U_6. The "iff" version (the six extend to a good seven iff
U_6 lies in a member) and the edge form (H has (7,2) iff U_6 is a transversal for every six edges) are also correct.

**(ii) "(Σ) ⇒ Σ_6." Correct only after a wording fix.** Σ_q must read "the uncovered pairs are *covered by*
7 − q sets of mass <= t", not "the uncovered-pair graph *is* a union of 7 − q cliques": after adding a member
around one clique, the rest is a subgraph of a union of cliques. With that reading Σ_q ⇒ Σ_{q+1} is immediate,
and Theorems T and Q′ and the pencil finish are static, so (Σ) ⊂ Σ_3 ∪ Σ_4.

**(iii) "Budget 3δ + ε, not vanishing with ε." Arithmetic correct, claim misleading.**
- S_6 = 6c + t − 3N = 3δ + ε is an upper bound on waste, not an available margin.
- Net of the baseline dump it is 5ε − δ, the same as for every q (identity above). So q = 6 is not a better target
  against a dumping family.
- On the pool family the Σ_6 margin is t − 3(1 + t)/7 = 4ε/7. So the plan's kill criterion 2 already fires on the
  pool, as the plan's own fourth bullet implies.
- For N > 2 the budget S_q itself is wrong for q >= 4 (GAP 4 above).

**Is Σ_6 CP restated?** Nearly. CP ⟺ "six members with U_6 inside a member". Σ_6 adds "|U_6| <= t", i.e. one member
of the good seven is used only through a request. So Σ_6 is CP with one inessential dump, and it is as hard to
force as CP: finding the six is the whole problem.

**Flaw in step 2.** "A_6 = Σ_6" is false for family-consistent replies. If every member containing a request S
also contains a set Z (forced dump), then U_6 ⊆ S ∪ Z finishes with |U_6| > t. Theorem P is exactly this
mechanism. The correct statement is A_6 ⟺ there is S with |S| <= t and U_6 ⊆ ⋂{K ∈ 𝒞 : K ⊇ S}. "A reply helps
exactly through D ∩ U" holds only for a single fixed reply, not for a family-consistent tree.

**Against the failed-routes list.** Step 1 (classification of forced sevens) is seven-level data and cannot decide
a family-level statement; the plan says so. Step 2's budget-versus-η statement is the §33(4) stability problem
(lesson 3), not a new route. Step 3's star form is the pair-cover LP (route 9), as the plan admits.

**Verdict on the plan.** No error in (i). (ii) needs the wording fix. (iii) should be replaced by the net budget
5ε − δ. The only part with new content is step 2, and its first reduction must be restated with the closure
⋂{K ⊇ S} before any budget is computed.
