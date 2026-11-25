# Small covering numbers behind f(6,7) >= 5 and f(7,7) >= 6

## Link to the claims
FRESH_B 1.3: the complete k-uniform family on n points has property (7,2) iff C(n, n-k, 2) > 7, and its tau is n-k+1.
- f(6,7) >= 5: n = 10, k = 6 needs C(10,4,2) >= 8 (tau = 5).
- f(7,7) >= 6: n = 12, k = 7 needs C(12,5,2) >= 8 (tau = 6).
- Maximality of those n in the FRESH_C 14.1 table (n+1 fails) uses C(11,5,2) <= 7 and C(13,6,2) <= 7.
  Also k = 5: C(9,4,2) >= 8, C(10,5,2) <= 7. These upper bounds are not needed for the lower bounds on f.

## (1) Literature lookup: NOT achieved
- dmgordon.org/covering-designs/ is reachable but only describes the database (no table values).
- ljcr.dmgordon.org/cover/table.html: DNS failure from this environment.
- No value was read from La Jolla, Schoenheim or Mills. The values below are our own computation only.

## (2) Independent recomputation
Code: compute/verify/cover_ilp.py (run with `py -3`, pulp/HiGHS). One binary per k-subset of [v], one
covering row per pair, minimise the count, block {0..k-1} fixed (S_v is transitive on k-sets). This is a
different formulation from complete_int.py (which is the Fano/intersecting-family ILP on 7 requests).
Every witness is re-checked by brute force over all pairs inside the script (witness_ok=True).

| C(v,k,2) | ILP optimum (status Optimal) | needed | witness (blocks on points 0..v-1) |
|---|---|---|---|
| C(9,4,2) | 8 | >= 8 | 0123, 0145, 0168, 0378, 1478, 2346, 2578, 3567 (digits = points) |
| C(10,5,2) | 6 | <= 7 | 01234, 01457, 03689, 14689, 23578, 25679 |
| C(10,4,2) | 9 | >= 8 | 0123, 0169, 0459, 0789, 1468, 1567, 2347, 2358, 2369 |
| C(11,5,2) | 7 | <= 7 | {0..4}, {0,2,5,6,10}, {0,2,7,8,9}, {0,3,7,8,10}, {1,4,5,6,7}, {1,4,8,9,10}, {3,5,6,8,9} |
| C(12,5,2) | 9 | >= 8 | printed by the script |
| C(13,6,2) | 7 | <= 7 | {0..5},{0,1,2,7,11,12},{0,2,6,8,9,10},{1,3,6,8,11,12},{1,4,5,9,10,12},{2,3,7,9,10,11},{4,5,6,7,8,11} |

Run the script to print every witness verbatim. All six agree with the claimed bounds; two are slack
(C(10,5,2) = 6 < 7, C(10,4,2) = 9 > 8, C(12,5,2) = 9 > 8).
A SAT cross-check (python-sat) was attempted but the UNSAT instances did not finish; it was discarded,
so the lower bounds (the "needed >= 8" rows) rest on HiGHS optimality only, i.e. one solver family
(a different formulation, but not a proof certificate). Upper bounds are explicit verified designs.

## (2b) Hand certificate for the two lower bounds (Schoenheim; no solver)
Claim: C(v,k,2) >= ceil(v/k * ceil((v-1)/(k-1))).
Proof: fix a point x. The other v-1 points must each share a block with x, and a block through x holds k-1 others,
so x lies in r >= ceil((v-1)/(k-1)) blocks. Counting point-block incidences, k*b >= v*r, so b >= v*r/k.
- C(10,4,2): r >= ceil(9/3) = 3; b >= 10*3/4 = 7.5, so b >= 8.
- C(12,5,2): r >= ceil(11/4) = 3; b >= 12*3/5 = 7.2, so b >= 8.
Hence no 7-block pair covering exists for (10,4) or (12,5). Both lower bounds are settled by this
two-line counting argument, independent of HiGHS and SAT. The ILP optima (9, 9) are consistent with it, and
only the weaker ">= 8" is needed. No SAT/DRAT run was necessary.

## (3) Status of f(6,7) = 5 and f(7,7) = 6
- Lower bounds f(6,7) >= 5, f(7,7) >= 6: now FULLY certified at the level of the two covering facts
  C(10,4,2) >= 8 and C(12,5,2) >= 8 (hand proof in (2b)); the complete families are (7,2) by FRESH_B 1.3.
  The earlier caveat about reliance on HiGHS optimality is withdrawn.
- Upper bounds f(6,7) <= 5, f(7,7) <= 6: EXACT certificates (FRESH_C 14.3), TWIN section 13 VERIFIED (as stated by the requester).
- Conclusion: f(6,7) = 5 and f(7,7) = 6 hold, given those upper-bound inputs. Remaining caveat: the upper bounds
  are not re-derived here; the literature lookup in (1) was not achieved.
