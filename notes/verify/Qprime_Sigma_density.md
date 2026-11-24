# Verification: Q' (CORE 37), reduction CP <= (Sigma) (CORE 38), density form of Theorem S (CORE 39.2)

Code: `compute/verify/qprime_sigma_density.py` (modes A, P, B, C, D), `tight_q.py`, `dens_more.py`, `finite_b.py`.
Everything is exact integer point counts (k points per unit mass, n = |V|, c = n-k, T = request cap); the
"seven" is built from the stated recipe and pair-coverage is checked by brute force on the explicit sets
(replies are taken minimal, which is WLOG by 1.1: adding points only helps her).

## Verdicts

| item | verdict |
|---|---|
| (1) Q' (set form of Theorem Q) | PASS |
| (1') "pool families miss Q' by base/2" | PASS |
| (2) reduction CP <= (Sigma), shapes (a), (c) | PASS |
| (2) shape (b), as written | PASS with GAP in the definition (see below) |
| (3) density form 39.2 | PASS (sharpness remark over-stated) |

## (1) Q'
- Algebra re-derived: 4c = s_1 + 2p + 3u_3 + 4u_4 and N = s_0+s_1+p+u_3+u_4 give W = u_3+2u_4+s_1 = 2N-4+2 sigma.
  Direct count: sum of the three loads c(m_r)+sigma+tau_r equals N + 2 sigma, so "<= 3t" is exactly sigma <= (3t-N)/2.
  Given c(m_r)+sigma <= t for each r, a tau-distribution (tau_r >= 0, sum = u_3+u_4, loads <= t) exists iff
  sum of slacks >= u_3+u_4 iff 2 sigma <= 3t-N. So the parenthetical "(tau exists iff first inequality)" is correct
  under the per-matching conditions (they are needed as hypotheses, which Q' states).
- Theorem Q's proof re-checked case by case (pair cell -> its diagonal point; |I|<=1 -> all three of 5,6,7;
  |I|>=3 -> any diagonal point; the two pair cells of one matching share a diagonal point because the quadrangle's
  three matchings correspond to the three points of the line 567). Correct.
- Code: identity W = 2n-4k+2 sigma asserted on every random quadruple (5400 quadruples, 9 parameter sets); tau-iff
  asserted; 876 quadruples satisfying the Q' hypotheses (including 19 within one unit of the sigma threshold,
  `tight_q.py`) were finished by the recipe: 0 failures.
- Remark (not an error): with four distinct-size-c sets and sigma = 0 and only pair cells, x_ab = x_cd is forced,
  so loads are even; at zero slack the hypothesis is sometimes arithmetically infeasible at finite k
  (n=15,k=8,T=6 gave no instance). Q' is not vacuous (hundreds of instances at n=15..22).

## (1') Pool families
- Pool family = Y (mass omega) plus a t-subset of V\Y. T-covering. Edges live on mass 1+t; 4 <= 2(1+t-sigma)+4 sigma
  gives sigma >= 1-t. Y points are in all four co-edges, so are not in sigma. Correct.
- 1-t - (3t-N)/2 = (2-5t+N)/2 = base/2 with base = omega-4 eps = N+2-5t. Correct (checked symbolically).
- Brute force over ALL quadruples (with repetition) of edges of the pool model, (k,T) = (4,3),(4,2),(5,4),(5,3):
  min sigma = k-T in every case, i.e. the bound is attained, so "by at least base/2, for every quadruple" is sharp.
- Second bullet: W = 2 omega  =>  2N-2-2t = 2N-4+2 sigma  =>  sigma = 1-t. Correct.

## (2) Reduction
Each shape yields a good seven in the window (family members as replies are supplied by T-covering):
- (a) = Q' (above). "Balanced matchings" is not defined in CORE 38; it must mean the three per-matching conditions
  c(m_r)+sigma <= t of Q'. Minor wording issue.
- (c) = Theorem T. Fano incidences re-checked (7 lines, all 21 pairs once; every co-type of a, b, d, e_i, g, kappa_4..6
  contains three lines through one point). 400-2000 random triples per parameter set (7 sets, g > 0 allowed, kappa split
  searched exhaustively): 1316 hypotheses-satisfying triples, 0 failures.
- (b) "three members forming a pencil with kernel in [N-2t, N-3/2]". Cited proof 35.1 only covers kernel EXACTLY N-3/2
  with petals of mass exactly 1/2 (fine; re-verified: masses, pairwise intersections, partition, loads 3/4).
  GAP (definition, not truth): read literally as a sunflower (pairwise intersections = kernel), three c-sets with
  union V force kernel = (3c-N)/2 = N-3/2, so the interval is a single point and 35.1 suffices. The interval
  [N-2t, N-3/2] is meaningful only for the reading "triple intersection kappa >= N-2t and K_1 u K_2 u K_3 = V";
  then kappa <= N-3/2 is automatic (sum |K_i| = 3c >= N+2 kappa), petals Q_i (partition of V\kappa, Q_i in K_i) are
  chosen by assignment, and the four requests are (half of each petal)x3 of mass (N-kappa)/2 <= t. I proved that
  statement and tested it (below); CORE 38 should state (b) in this form and cite the halving argument (Theorem C),
  not only 35.1. Union V is essential: a point outside K_1uK_2uK_3 has co-type inside {4,5,6,7}, a quadrangle, which
  contains no line.
- Code (mode B): random triples with union V and kappa >= n-2T, adversarial petal assignment: 0 coverage failures;
  0 violations of kappa <= (3c-n)/2.
- Finite-k only (minor): at kappa = n-2T exactly, equal halving fails when petal sizes have mixed parities
  (e.g. n=15,k=8,T=7, petals 5,3,6, kappa 1: loads must all equal T). Not a counterexample: `finite_b.py` (SAT) finds
  four requests of size <= T for every tested padding of such instances, using other splits. The reduction is
  first order, so this does not matter.
- No case missing: (Sigma) is a disjunction of hypotheses, each shown sufficient; nothing else is claimed. The
  reduction is one-way as stated. Window usage: none of Q', Theorem T, or the pencil finishing uses N; N matters only
  for non-vacuity (Q' non-vacuous needs N >= 4-3t, inside the window).

## (3) Density form 39.2
- Argument re-derived: the pencil-triple hypergraph on the class is vertex-transitive (group acts transitively on
  [pi], each member lies in a triple), hence regular; an independent set A has at most 2 vertices per edge, so
  |A| d <= 2 |E| = 2|X| d/3. Correct. A family with > 2/3 of the class contains a whole triple, which is finished
  by (b) with kappa = N-3/2.
- Code (mode D, `dens_more.py`; exact max independent set by MILP): classes (cells; pi) = (4,3;2,1), (6,5;2,3),
  (6,6;4,2), (5,5;3,3): hypergraph regular in all, max independent density 2/3, 2/3, 2/3, 3/5. Bound never exceeded.
- Minor error: "2/3 is sharp for this argument: all K in [pi] avoiding a fixed point has no triple". That family has
  density 1 - pi_j/v_j for a point in cell j, which equals 2/3 only if some cell has pi_j = v_j/3 (true in the first
  three tests, where 2/3 is attained; in (5,5;3,3) the true maximum is 3/5 while avoid-a-point gives only 2/5).
  So 2/3 is sharp only on profiles with a cell at the lower limit pi_j = v_j/3, not "sharp" in general.
- "Misses at least a third of every class it meets" is true (it holds for every class, met or not).
- Parity/size conditions: same as 39.4 (u odd cells; need 3 ceil((k+u)/4) <= T); not re-proved here, but
  the generic pencil finishing (mode B) covers the case where each point is assigned to some Q_i in K_i.

## Minor errors collected
1. CORE 38: (b)'s interval needs the "union V, triple intersection" definition and the Theorem C halving proof; 35.1
   only gives kappa = N-3/2.
2. CORE 38: "balanced matchings" undefined (= per-matching conditions of Q').
3. CORE 39.2: sharpness of 2/3 holds only with a tight cell pi_j = v_j/3.
4. Finite k: equal halving at kappa = n-2T can fail on parity; other splits work (first-order irrelevant).
