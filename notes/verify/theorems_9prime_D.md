# Verification: Theorem 9' (Task 3) and Theorem D (Task 2)

Code: `compute/verify/p2_9D/` (own implementations, written from the statements; nothing imported from the
authors' code). Logs: `compute/verify/p2_9D/logs/`. N means n/k throughout.

## Verdicts

| Item | Verdict |
|---|---|
| (1) Theorem 9' (parity + size hypotheses, F2 class system, size-residue repair) | **PASS** as stated |
| (1b) Literal Proposition 9 false (size parity) | **PASS** (confirmed) |
| (1c) "Mild in the Programme regime" Corollary of 9' (c <= 2^r) | **FAIL as stated / GAP** |
| (2) Theorem D: dim C >= k+r  =>  rho_par <= r+1 | **PASS** |
| (3) Counting: dim C >= k+r for omega < 0.188 at t = 3/4, hence all N < 11/6 | **PASS** |
| (3b) Chain "Theorem D + Theorem 9' gives a good seven for all coset families with N < 11/6" | **GAP** |

## (1) Theorem 9'
Re-derived by hand, every step:
- Line matrix: m_p = (Sum t)/4 - (1/2) Sum_{l through p} t_l solves Sum_{p not on l} m_p = t_l (checked by the
  count: each line l' != l has exactly 2 points off l). ker N over F2 = Hamming code (lines lie in the kernel, rank 3).
- The three triangles are inside ANTI(3), ANTI(5), ANTI(6); T* inside ANTI(7). Each line lies in an odd number of T_i
  (124 in three, the rest in one).
- Integrality: s = 4n - 7k - W is 0 or 2 mod 4 using H1; Sum t = 7k - 3W - 6f is 0 mod 4; every t_l is even.
- 4 m_p formulas and the fixer shift (-6 + 4*#) are right. Sum m_p = |V''| = n - W - u - 2f.
- Step 4: pi_{g*} is in Ham, wt(pi_{g*}) is congruent to |V''_{g*}| mod 2 and <= 7 <= |V''_{g*}|; every p gets at most c
  singles and m_p >= c; remainders are even; pairs fill exactly. Classes of B_l = alpha. Good seven: Fano-type, 2-transversal-free,
  distinct (Y_p nonempty because m_p >= c >= 1). No hole found.

Tests (`t9.py`, `t9_edge.py`): the construction implemented from scratch, checked by an independent exact verifier
(membership, distinctness, no transversal of size <= 2, pencil triples). 
- random cell structures: 4 seeds, 616 instances passing the hypotheses, 0 failures;
- boundary-biased (equality in H2/H3/H4', singleton classes up to u, zero class, large cells): 1,191 instances,
  403 with some margin <= 1, 0 failures.

(1b) `parity_example.py`: n = 12, k = 5, X, Y of size 5, two free points. 200 members, V = union of members, every
member meets {z1, z2}, three disjoint Omega_i of size 2 lie in a + C with W = 6 <= 13. So the literal Proposition 9 is
false; H1 is the right repair.

(1c) The Corollary in Task 3 says "C has codimension r (so c <= 2^r)" and needs (1-4 delta)k >= 2Delta + 2^(r+2) + 6
"for k large". With r = omega*k this is false for every fixed omega > 0. Theorem D only gives codim C <= T (about
0.75k), so c can be about n. Then H2 (k >= W + 2Delta + 4c + 6) and H4' (at most u singleton classes) fail. They hold
only when V' has at most about (k - 5r)/4 classes, with few singleton classes. The notes' "mild hypotheses" claim holds
only for codimension O(log k). Task 3's conjecture that H2 and H4' are unnecessary is supported by computation, not proof.

## (2) Theorem D
Re-derived: Lemma A (both cases, x + c is nonzero since a is not in C), Lemma B (the exchange argument is correct:
epsilon additive, three unmatched positions give a pair with epsilon = 0; independence of the new labels checked),
Lemma C, the even/odd w cases, and the passage to C_ev (E unchanged, parity-k half equals a + C_ev, codeword weights
w or w -+ 1 are even so lie in C_ev). The reduction "dim C >= k+r implies e <= min(w,T) and n >= 2e+1" is correct for T < k+r.

Tests (`lemmasBC.py`, `thmD.py`, `thmD_tight.py`, `divisible.py`):
- Lemma B: 1,121 random column sets, 0 failures. Lemma C: 6,660 (columns, w) pairs, full equality of the sum set, 0 failures.
- Theorem D: brute force rho_par and r (exact max independent set), columns random, zero/duplicate-heavy, all-distinct
  (Hamming/simplex-like), even-weight (extended) and subspace-concentrated. Seeds 1-3 plus 11-14: about 2,500 instances
  inside the hypotheses, 0 violations. Threshold cases (e = min(w,T) or n = 2e+1): 511 inside, 0 violations. Just outside
  (e = min+1 or n = 2e): 37 of 1,238 violate, so the side conditions are not slack.
- Extended-Hamming/RM-type columns (1,x), n = 8 and 16, all s, k: 131 inside, 0 violations.

## (3) Counting
`counting.py`, `counting2.py`: exact integer test C(n,w) > 2^(w-1) C(n-k,r) (then |C| >= |H| > 2^(w-1) gives dim C >= w).
- All (k, r, T) with k from 1 to 199, T >= ceil(3k/4), n < 11k/6: 10,098 triples, 0 failures.
- 11k/6 <= n <= 1.938k, k from 40 to 259 (step 3): 28,597 triples, 0 failures.
- Asymptotic g(omega,t) >= 0 thresholds: omega < 0.1880 at t = 3/4 (N < 1.9380, not 1.94); 0.2078 at 0.8; 0.2365 at 0.875.
  min g over N < 11/6, t >= 3/4 is 0.315.

## Exactly what is proved for coset families
Let H = (a + C) intersect (V choose k), covering at level k + r, T = n - k - r >= 3k/4.
- **N < 11/6:** rho_par <= r + 1 (Theorem D), hence the Corollary 7 obstruction cannot occur (7 rho_par <= 7(r+1) <=
  12 delta k up to the stated small-k side condition). Three pairwise disjoint parity-correct Omega_i of weight <= r+1 exist
  (shrinking argument; min g after the worst shrink is 0.111; the shrink works for omega < 0.102 at t = 3/4, N < 1.852).
  A Fano-type good seven (so H not (7,2)) is **proved only under H2-H4'** of Theorem 9' (few classes in V',
  no excess singleton classes, one large class). For general C (many classes) it is **unproved**.
- **11/6 <= N <= 1.938:** rho_par <= r + 1 for a single Omega (Theorem D). Three disjoint small Omegas are proved only
  for N < 1.852 at t = 3/4 (up to about 1.91 at t = 0.8). Fano-type good seven: same conditional status as above.
  Existence of a Fano-type good seven suffices for any N, so the "all good sevens are Fano-type" fact is not needed
  here, but no unconditional statement is proved.
- **N > 1.938:** nothing proved beyond Lemma 8 (rho <= 2r + 1 when n >= 3k/2 + r + 1). Counting does not give dim C >= k + r.
  No good seven is proved for coset families.
