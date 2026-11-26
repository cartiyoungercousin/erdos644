# Target 3, first question: adaptive play beats the cluster-glue adversary of Theorem O

Response to `reports/CRACK_BRIEF.pdf` (25 Nov 2026). Tags as in the brief: [HAND] = hand proof, not independently
checked; [COMPUTED] = simulation or exact small computation; [HEUR] = heuristic.
Code: `adaptive_vs_clusters.py`, `pool_cost.py` (plain Python 3, no dependencies).

## 0. Verdict

- **Problem #644 is not solved by this note.** No proof of (G) and no counterexample.
- **Target 3, "Question" (exhibit a bounded-depth adaptive strategy that defeats the two-cluster glue adversary):
  answered, yes.** Ten rounds suffice, for every T ≥ 2k/3 + O(1), so in particular at t = 3/4 [HAND, §3;
  COMPUTED, §6]. The seven it produces is "four answers of one cluster with empty common intersection, then three
  answers of the other", the shape BEAT78 §4(b) guessed. The one adaptive ingredient is trivial: *every request
  contains every glue point seen so far*.
- The same idea beats every adversary of this type with any number of regions, in at most 13 rounds [HAND, §4].
- **Consequence for the programme.** Theorem O stays true as a statement about static finishes, but the adversary
  behind it is not evidence that large n is hard: it cannot even defend t = 2/3 against adaptive play, while the
  complete family defends 3/4. The "Better" half of Target 3 (a bound below 7/8 for real families) is untouched:
  real families can answer with *bridges* (members with Θ(k) points in two regions), and nothing below handles them.
- Targets 1 and 2: short audit in §7. Target 1 needs its quantifier fixed before anyone works on it.

## 1. The adversary model

BEAT78 §2.2: disjoint regions R_1, R_2 with |R_i| = s = ⌈(2−c)k⌉. To answer a request U (|U| ≤ T) the adversary
picks i with |R_i ∖ U| ≥ k, takes one *glue* point of x ∩ R_{3−i} ∖ U for each earlier answer x of the other cluster,
and fills up from R_i ∖ U.

Only the following is used, and it is stated for q ≥ 2 regions R_1, …, R_q (pairwise disjoint, sizes s_c):

- **(C1)** every answer B has a cluster c(B); its *main* B° = B ∩ R_{c(B)} and its *glue* γ(B) = B ∖ B°;
- **(C2)** γ(B) ⊆ ⋃{x° : x an earlier answer of another cluster}, and |γ(B)| ≤ the number of such x;
- **(C3)** B ∩ U = ∅ and |B| = k.

The choice of cluster, of the k points and of the glue points is the adversary's. The requester sees only the sets.
Two answers of one cluster share ≥ 2k − s_c − 2·(#rounds) points, two answers of different clusters share at most
2·(#rounds) points, so under the size assumptions below the requester can read off clusters, mains and glue:
γ(B) = B ∩ ⋃{x : x earlier, other cluster} (the mains of B and x are disjoint, and B avoids the glue of x by rule R0).

**Rule R0 (the adaptive ingredient).** Let Γ be the set of all glue points of all answers so far. Every request
contains Γ.

**Consequences of R0.**
- (G1) The glue sets of different answers are pairwise disjoint.
- (G2) A glue point of B lies in no answer later than B.
- (G3) So a point p ∈ R_j lies in: answers of cluster j whose main contains p, and at most one answer Z_p of another
  cluster (the one with p as glue). If Z_p exists, every cluster-j answer containing p is earlier than Z_p.
- Points outside ⋃R_c lie in no answer.

## 2. Three pattern lemmas [HAND]

Let Σ be seven answers (from seven rounds; equal sets allowed) of a play obeying R0, and a_c the number in cluster c.
By (G3) a point of R_j lies in at most a_j + 1 members of Σ.

**P1.** If a_c ≤ 2 for all c, Σ has no transversal of size ≤ 2.
*Proof.* Two points in one region meet ≤ a_j + 2 ≤ 4 members; in two regions ≤ (a_i+1) + (a_j+1) ≤ 6. ∎

**P2.** If one cluster j has a_j = 3, all others have a_c ≤ 2, and the latest member of Σ is in cluster j, then Σ has
no transversal of size ≤ 2.
*Proof.* As in P1 every pair meets ≤ 6 members, except p ∈ R_j, p′ ∈ R_i (i ≠ j), where the bound is 3+1+a_i+1 ≤ 7.
Equality needs p in all three mains of cluster j and Z_p ∈ Σ. By (G3) Z_p is later than those three, contradicting
the hypothesis. ∎

**P3 (4 + 3).** If B_1, …, B_4 ∈ Σ are in cluster 1 with B_1° ∩ B_2° ∩ B_3° ∩ B_4° = ∅, and the other three members
Z_1, Z_2, Z_3 are in other clusters and later than all B_i, then Σ has no transversal of size ≤ 2.
*Proof.* Let {p, p′} be a candidate.
- Both in R_1: they meet the Z's only as glue, so at most two of the three (G1).
- Neither in R_1: they meet the B's only as glue, so at most two of the four (G1).
- p ∈ R_1, p′ ∈ R_j, j ≠ 1. If p′ ∈ γ(B_i) for some i, then by (G2) p′ lies in no Z, and p lies in at most one Z:
  some Z is missed. Otherwise p′ lies in no B_i, so p lies in all four mains, which is impossible. ∎

Remark. No size condition appears. P1 and P3 are the adaptive forms of two static types: "every point in at most
three members" (needs n ≥ 7k/3) and the 4+3 type of §5 (needs n ≥ 17k/9).

## 3. Theorem A: two regions (the adversary of Theorem O) [HAND]

**Theorem A.** Let k ≥ 600, 2⌈k/3⌉ + 45 ≤ T < k, and let the adversary obey (C1)–(C3) with two regions of size
s ≤ 3k/2 + 1 (this covers Theorem O: there s − k ≤ (1−c)k + 1 with c > 1/2, for every t). Then the following
strategy of at most 10 rounds produces seven answers with no transversal of size ≤ 2.

- **Phase 1** (at most 7 rounds). For each cluster c that has answered, let I_c be the intersection of the mains of
  its answers and A_c a set of min(|I_c|, ⌈k/3⌉) points of I_c. Request U = Γ ∪ A_1 ∪ A_2. Stop when some cluster,
  say cluster 1, has four answers B_1, …, B_4.
- **Phase 2** (3 rounds). Request U = Γ ∪ W, where W consists of T − |Γ| points of B_1° ∪ … ∪ B_4° outside Γ (all of
  them if there are fewer). Call the answers Z_1, Z_2, Z_3.
- **Output** {B_1, …, B_4, Z_1, Z_2, Z_3}.

*Proof.* Sizes: an answer has at most as many glue points as there are earlier answers, so |Γ| ≤ 0+1+…+9 = 45 and
every request has size ≤ 45 + 2⌈k/3⌉ ≤ T. Phase 1 stops within 7 rounds by pigeonhole. Each answer of cluster 1 after
the first avoids A_1, so I_1 loses ⌈k/3⌉ points (or everything) each time: after four answers I_1 = ∅. In Phase 2,
|R_1 ∖ U| ≤ s − min(T − 45, k − 54) < k, so the adversary cannot answer in cluster 1; Z_1, Z_2, Z_3 are in cluster 2
and later than the B_i. R0 holds throughout. Apply P3. ∎

Remarks.
- The hypothesis is T ≥ 2k/3 + O(1), not T ≥ 3k/4. Against adaptive play this adversary is weaker than the complete
  family K_{7k/4−1}^{(k)}.
- The output seven contains pencils of profile {ck, 0⁺, 0⁺} (two B's and one Z, when the glue points are chosen
  apart). By Theorem O none of them has a static finish. There is no contradiction: the other four members were not
  obtained from four blocks fixed in advance, but from a fourth anchor and from R0.
- Without R0 the strategy fails: the adversary reuses one hub glue point (control run, §6).

## 4. Theorem B: any number of regions [HAND]

**Theorem B.** Let k be large, 2⌈k/3⌉ + 78 ≤ T < k, and let the adversary obey (C1)–(C3) with q ≥ 2 regions of sizes
s_c with s_c − k < T − 78 and s_c ≤ 2k − 100. Then the following strategy produces, within 13 rounds, seven answers
with no transversal of size ≤ 2.

Let C₂ be the set of clusters with at least two answers; for c ∈ C₂ let I_c be the intersection of the mains of its
answers number 2, 3, … and A_c a set of min(|I_c|, ⌈k/3⌉) points of I_c.
- Request U = Γ ∪ ⋃_{c∈C₂} A_c if |C₂| ≤ 2, and U = Γ if |C₂| ≥ 3.
- Stop as soon as the history contains a seven as in P1, or as in P2 with the latest answer in the 3-cluster.
- If some cluster c reaches five answers, its answers 2–5 have empty common main. Block c as in Phase 2 of Theorem A
  for three rounds and apply P3.

*Proof.* Let n_c be the number of answers of cluster c. P1 applies once Σ_c min(n_c, 2) ≥ 7. P2 applies once the
latest answer lies in a cluster j with n_j ≥ 3 and Σ_{c≠j} min(n_c, 2) ≥ 4.
- If |C₂| ≥ 3, the next answer ends the game: in a new cluster or one with n_c ≤ 1 it gives Σ min ≥ 7 (P1); in a
  cluster of C₂ it gives n_j ≥ 3 with two other clusters of C₂ (P2).
- So until then |C₂| ≤ 2, the request has size ≤ |Γ| + 2⌈k/3⌉ ≤ T, and every answer of c ∈ C₂ from its third on
  avoids A_c. Hence |I_c| ≤ k − (n_c − 2)⌈k/3⌉, which is ≤ 0 at n_c = 5.
- Count: before the end n_c ≤ 4 on C₂ and Σ min(n_c,2) ≤ 6, so at most 4+4+2 = 10 answers; the worst line is
  (4,4,1), then a fifth answer in a 4-cluster, then three blocked rounds: 13 rounds, and |Γ| ≤ 0+…+12 = 78.
- Blocking works: the request contains min(T − 78, k − 90) known points of R_c, and s_c minus this number is
  below k by the two size assumptions. The same assumptions let the requester tell clusters apart (two answers of
  one cluster share at least 76 points, two of different clusters at most 24). ∎

So no adversary built from complete clusters and o(k) glue, whatever the number and sizes of the clusters, survives
bounded adaptive play at any t > 2/3.

## 5. Static forms for real families [HAND, one-line proofs]

These hold for arbitrary members of an arbitrary family.

- **S1 (4 + 3).** If B_1 ∩ B_2 ∩ B_3 ∩ B_4 = ∅ and every C_i ∩ C_j (i < j ≤ 3) is disjoint from B_1 ∪ … ∪ B_4, the
  seven have no 2-point transversal. *Proof:* two points meeting three C's put one point in two C's; it lies in no
  B; the other point would lie in all four B's. ∎ Least ground set: 17k/9 (masses 4k/3 on "three B's and one C",
  5k/9 on "all three C's").
- **S2 (3 + 3, a good six).** If (B_1, B_2, B_3) is a pencil and every C_i ∩ C_j is disjoint from B_1 ∪ B_2 ∪ B_3,
  the six have no 2-point transversal. Same proof. Least ground set 2k.
- **S3.** Seven members with every point in at most three of them have no 2-point transversal. Least ground set 7k/3.

They are among the non-Fano classes already enumerated. What is new is how they are reached: Theorem O fixes three
anchors and four blocks, and S1 needs a fourth anchor plus requests that depend on where earlier replies landed.

## 6. Simulation [COMPUTED]

`python3 adaptive_vs_clusters.py k t trials seed`. Adversary with q ∈ {2,…,5} regions; for q = 2 the parameter c is
drawn from the Theorem O range max(1/2, 4t−3) < c < 1 − t/2. Policies drawn at random per trial:
- cluster choice: largest free region (as in `sim_two_region.py`), random, fewest/most answers so far, alternate,
  prefer new;
- fill: random, or *sticky* (maximise overlap with the cluster's earlier mains);
- glue: random, or *hub* (greedy: fewest glue points, each hitting as many earlier answers as possible).

The requester sees only the answer sets. The final seven is checked by brute force for transversals of size ≤ 2.

| k | t | trials | sevens with a 2-point transversal | max rounds, q = 2 | max rounds, q ≥ 3 |
|---|---|---|---|---|---|
| 600 | 0.75 | 200 | 0 | 10 | 13 |
| 900 | 0.76 | 200 | 0 | 10 | 13 |
| 1200 | 0.80 | 120 | 0 | 10 | 11 |
| 800 | 0.70 | 120 | 0 | 10 | 13 |
| 1000 | 0.875 | 120 | 0 | 10 | 13 |

Negative control (an earlier variant of the script with R0 switched off, k = 900, t = 0.76, 150 trials): 78 of the
150 final sevens had a 2-point transversal. The simulation is a sanity check of §2–§4, not a proof; it does not
search over adversaries.

## 7. Audit of Targets 1 and 2

### Target 1
- **Weighted Fano repair theorem: correct at first order** [HAND, re-derived]. Reason: a point y fails exactly when
  its omission set O_y = {i : y ∉ K_i} meets every line; the strategy guarantees O_y contains no line, hence the
  complement is a blocking set of the Fano plane, hence contains a line.
- **Which omission patterns are free** [COMPUTED, `pool_cost.py`]. For a round order, the repair cost of y is the
  number of lines whose two earlier points both lie in O_y. For the order 0, 1, …, 6 with lines {i, i+1, i+3}, 34 of
  the 64 line-free omission sets cost nothing: all 8 of size ≤ 1, 14 of the 21 pairs, 10 of the 28 triangles and 2
  of the 7 line-complements.
- **The target is ambiguous, and neither reading is a useful intermediate statement.** "Caps valid for every
  history" is a notion of the adversarial game. For a fixed family there are two readings.
  - *Requester chooses the reply* (the true situation for a fixed family). Then branch (i) only says that some Fano
    certificate has r points with free omission patterns. With 34 free patterns this is close to "a Fano certificate
    exists". The target is then the conjecture in the Fano range again, not a reduction.
  - *Worst reply inside the family.* Then branch (i) fails on the brief's own litmus family [HEUR]. In a random
    coset union a request S ⊆ X has polynomially many replies with essentially random dumps in the k+r points
    outside S, so some reply has |D ∩ Y| ≈ r²/(k+r). This gives |M_a ∩ M_b| ≥ r(k−r)/(k+r) for every pool Y, and
    Q ≈ 7r(k−r)/(k+r) > 4T − 3k whenever r exceeds about 4εk/7, which is the whole open region (r > 8εk/3).
    Branches (ii)–(v) fail there by construction. So in this reading the dichotomy is false as stated, although the
    family has good sevens.
- Suggested repair: state branch (i) for a selection of replies made by the requester, and add what forces such a
  selection to exist. That missing statement is the wall of §3 of the brief, not a consequence of the repair theorem.

### Target 2
- **Private-shadow theorem: correct** [HAND, re-derived].
  - τ = T + 1: delete a vertex from all members.
  - Private set S_B: delete B.
  - S_B is a minimum transversal of the members avoiding z, which gives the witnesses C_{z,s}.
  - Seven nonempty shadows E_{z,s_i} always have a 2-point transversal. Take a 2-point transversal {u, v} of the
    seven C_{z,s_i}. A point of S_B lies in at most one of them, so one point, say v, lies outside S_B and meets at
    least six shadows. Add any point of the seventh.
  - Empty shadows are singleton members; three singletons violate (7,2). Hence "T − 2".
- So the row families are (7,2) for a cheap reason, each has only T members, and a row alone carries no lower bound,
  as the brief says. I made no progress on the coupling.
- A sharper form of the same minimality, possibly useful there [HAND]. In a counterexample of minimum total size,
  for every member B with |B| ≥ 2 and every z ∈ B, replacing B by B ∖ {z} must create a good seven. So there are six
  members F_1, …, F_6 whose kernel D(F) (the union of their 2-point transversals) satisfies D(F) ∩ B = {z}, and D(F)
  is a transversal of H. Each incidence (B, z) thus carries six specific members, not only the T-set S_B.

## 8. What I would do next

1. Retire Theorem O as guidance and replace it by the adaptive question it leaves open: is there an adversary with
   *bridges* (answers with Θ(k) points in two regions) that survives bounded adaptive play with R0-type rules?
   That is Game F of BEAT78 §1.4, and it is the first place where a large-n obstruction could really live.
2. Fix the quantifier in Target 1 before spending more agent time on it.
3. S1/S2 suggest a real-family lemma worth one attempt: for a pencil with union W, three members whose pairwise
   intersections avoid W give a good six. Requests inside W give |C ∩ W| ≤ |W| − T, which is not enough by itself;
   the open point is whether replies that stay inside W can be turned into a lighter pencil instead.
