# Programme 4, counterexample ladder: Rungs 0 and 2

Tags: [computed exact, certificate], [computed, solver infeasible without certificate], [proved by hand], [heuristic],
[open]. Code and logs: `compute/programme4/ladder/` (logs in `ladder/logs/`). Committed at wind-down; `logs/orb_psl2_31.json` (16 MB, regenerable by
`orbits_psl2.js`) is git-ignored. Not yet checked by a
fresh-context verifier.

## 0. Verdicts
| instance | verdict |
|---|---|
| Rung 0, (k,n,r) = (8,15,1) | **family found: f(8,7) = 7.** An 8-uniform (7,2)-family on 15 points with τ = 7 (§1) |
| Rung 0, (8,16,2), (8,17,3), (8,18,4) | moot: the (15,1) family is also a family on n ≥ 15 points (extra points unused) |
| Rung 2 | not reported: the Rung 2 results were never written up (placeholder left at wind-down; partial logs `oc_*`, `oclv_*`) |

## 1. Rung 0: f(8,7) = 7

**1.1 Reformulation at (15,1) [proved by hand].** Write co-edges K = [15] ∖ B (7-sets). τ(H) ≥ 7 iff every 6-set
lies in a co-edge (equivalently every 9-set contains a member; so the family is all 8-sets minus a set D containing no
nine 8-subsets of one 9-set: the brief's reformulation is right). τ ≤ 7 holds unless H is complete. A set of members
has no 2-point transversal iff its co-edges cover all pairs of [15]. Six 7-sets never cover K15 (each point needs
r_x ≥ ⌈14/6⌉ = 3, so Σ r_x ≥ 45 > 42), so (7,2) ⟺ no seven co-edges form a pair-covering, and in a pair-covering by
seven 7-sets r_x ≥ 3 and Σ(r_x − 3) = 4.

**1.2 All pair-coverings of K15 by seven 7-sets, up to isomorphism [computed exact; two enumerators].**
A covering is the same as its co-type multiset (15 subsets I_x of [7], |I_x| ≥ 3, pairwise intersecting, each
label in exactly 7), up to S_7. Result: **68 classes, 1 438 653 966 750 labelled coverings** (`pc_15_7_classes.txt`).
- `cotypes2.js` (support first): the ≥ 11 triple co-types have an intersecting support (604 supports up to S_7);
  large co-types follow the partitions of E = 4; dedup under Aut(support). 47 s.
- `cotypes.js` (independent DFS over co-type multisets with the first co-type fixed to {0,1,2}, orbit marking under
  all of S_7): 1.44·10⁹ nodes, 36 612 labelled leaves, **the same 68 classes** (compared after canonicalising both
  lists), 38 min.
- Consistency [computed exact]: the two agree on (n,c) = (7,3) (1 class, the Fano plane, 30 labelled), (11,5) (2),
  (13,6) (6); the DFS leaf counts (396, 3216 at n = 11, 13) equal Σ (5040/|Aut|)·#triples/35 from the class list;
  for n = 15 that identity predicts 36 612 leaves.
- So labelled coverings are far too many (1.4·10¹²) for an explicit hitting-set formulation; the classes are used
  instead as the inner check (1.3), which makes it a few seconds per family.

**1.3 The witness [computed exact].** The CORE 55.5 family (2352 co-edges, `fam_8_15_tau7_coedges.txt`, = core9
`logs/fam_8_6_15_rev.txt`: the two-class reversed-order greedy rule at (k,T,n) = (8,6,15)).
- T-covering, hence τ = 7 (`verify_f87.py`, plain Python: all 5005 six-sets lie in a co-edge; a non-co-edge 7-set
  meets every member).
- No good seven, by two independent embedding methods over the 68 classes:
  - `embed.js`: exhaustive assignment of points to co-types with exact multiplicities and prefix-trace pruning, no
    symmetry breaking, no solver. 68/68 NONE, 2.37·10⁸ nodes, about 2 min. Controls: it finds a covering at once in
    a random family of the same density (2411 sets), re-checked by plain code.
  - `pc_config.py`: CP-SAT per class (row and column table constraints). 68/68 INFEASIBLE, 0.8–16 s each
    [solver, no certificate].
  - Classification-free cross-checks (CaDiCaL point-level model 80 min; CP-SAT table model; plain DFS 4·10⁸ nodes)
    did not finish locally. A 4-core CP-SAT run is on Kaggle (`p4-rev-cpsat`), result KAGGLE_REV.
- Hence H = {[15] ∖ K} is 8-uniform, (7,2), τ = 7: **f(8,7) ≥ 7**, and with FKW's ⌈7k/8⌉ = 7, **f(8,7) = 7**.
  The status rests on the completeness of the 68-class list (two enumerators) and on embed.js (exhaustive).
- Not a record: ⌊(3k+5)/4⌋ = 7 = τ. It is the first k = 8 family with τ = 3k/4 + 1 (FKW's construction needs larger
  k). Structure: every co-edge contains 0 or 14 (degrees 1484 and 1504; the rest 1032 / 1042); it is not
  reversal-invariant. A minimal covering subfamily has 1946 co-edges (`fam_8_15_tau7_coedges_min.txt`; seven-free
  as a subfamily).
- Why the four earlier methods failed (CORE 55.5): they searched sevens member by member or point by point with no
  multiplicity information. Fixing the co-type multiset first makes each case a rigid embedding problem.

**1.4 Larger n [proved by hand].** τ and the (7,2) property do not depend on the ambient ground set, so the (15,1)
family also settles (16,2)–(18,4) for the purpose of f(8,7). Families with full support 16–18 were not searched.

## 2. Rung 2
Not written up before the research phase ended; see the `oc_*` / `oclv_*` logs in `ladder/logs/` (unreviewed).
