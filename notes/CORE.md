# CORE — the concentrated window in co-edge form (Erdős #644)

Scope: the one remaining gap (TWIN §16–§17, PETAL §9.4, REDTEAM §9): adversaries with no good spread
triple. Time box ~2 h. Code: `compute/core/check_core.py` (`py compute/core/check_core.py`, < 1 min).
Units: k = 1 where convenient, t = T/k = 3/4 + eps, N = |V|/k, c = N - 1 (co-edge mass),
omega = N - 1 - t (mass the adversary adds to a full request), delta = N - 7/4.
Tags: [proved by hand] / [computed exact] / [heuristic]. Nothing here is in Lean.

**Bottom line.** The gap is NOT closed. What is new:
1. A cleaner exact form of the concentrated case as a pair-covering problem for co-edges (§1), and
   a one-line slack count (§2) that explains every stall so far: a certificate built on q
   "free" replies and 7 - q fully requested ones has slack exactly (q - 3)(N - 7k/4) + (7 - q)·eps·k.
   Three-reply certificates (Theorem C, and Theorem T below) have slack 4·eps·k at every N, so
   their targets are points with O(eps) tolerance, while the adversary moves every overlap inside a
   window of width omega. That is the exact reason the anchored route cannot close the window.
2. Two static certificates, proved and checked: Theorem T (triangle: three replies that are NOT
   anchors, §3) with a closed form, and Theorem Q (four free replies, static finish) with the
   waste functional W (§4). Theorem T interpolates between the Fano triangle (N = 7k/4) and PETAL's
   point (1/4,1/4,1/4) (N = 3k - T); it is a closed form for TWIN's unformulated labelling (T).
3. Pool theorem (§5): an adversary whose additions always fall into a fixed pool Z,
   omega <= |Z| <= N - 3k/2, loses in seven requests at every N >= k + T, for T >= 3k/4 — by
   "forcing by exhaustion", the only mechanism I found that makes his additions useful.
4. The obstruction (§6) [first-order analysis, partly heuristic]: for 5T - 2k < N < 2k every
   winning seven needs adversarial additions on the lines of at least three replies (proved count);
   the first two replies are free, and in every later reply he can dump his omega on a class that
   is already determined. So the whole gap is: force (or find) a THIRD reply whose additions are
   useful. Discards help only through dilution (several disjoint dump targets) or exhaustion (a pool).

**Part II (appended below, §8–§11)** corrects item 4 and §6–§7: the dump dichotomy is not proved;
see the outcome paragraph there.

---------------------------------------------------------------------------------------------

## 1. Co-edge form [proved by hand]

Confined setting: all replies inside V, |V| = N, k + T <= N. For a reply B put K = V∖B (co-edge,
|K| = N - k = c). A request S (|S| <= T) is answered by a co-edge K ⊇ S; the adversary chooses
E = K∖S, of mass c - |S| >= omega. For co-edges K_1..K_7 and x in V let I_x = {i : x in K_i}.

**1.1** {x,y} misses B_i iff x, y in K_i. So the seven replies have no 2-cover iff the seven
co-edges cover all pairs of V (x = y included: every point lies in some K_i), i.e. iff the co-types
I_x are nonempty and pairwise intersecting. Adding points to a co-edge can only help her (this is
TWIN 13.2(i)/13.3 in complement form).

**1.2 Family form of the concentrated case.** By TWIN 16.2, with unboundedly many requests the
statement is: *a family 𝒞 of c-subsets of V in which every T-subset lies in a member ("T-covering")
contains seven members covering all pairs of V*, for k + T <= N < 3k - T. Proved for N <= 3T - k/2
(TWIN 16.A = Lean `TheoremA`).

**1.3 Fano certificate, two equivalent forms.** Label seven co-edges by the points of a Fano plane.
(i) for every line {a,b,c}: K_a ∪ K_b ∪ K_c = V;  (ii) V = ⋃_lines (K_a ∩ K_b ∩ K_c).
Each implies pair-covering. *Proof.* (i) says every I_x meets every line; a blocking set of the Fano
plane contains a line, so (i) ⟺ every I_x contains a line ⟺ (ii); two lines meet. ∎
(i) is TWIN 7.5 ("every reply-type is line-free"); (ii) says V is covered by seven classes V_ℓ and
K_i ⊇ L_i := ⋃_{ℓ ∋ i} V_ℓ: a weighted Fano blow-up whose seven "lines" L_i have mass <= c.
For N < 11k/6 every pair-covering seven is of this kind (quoted from ROADMAP §0.1, [computed] there).

## 2. The slack count [proved by hand]

**2.1 Waste identity.** For any seven co-edges, Σ_x (|I_x| - 3) = 7(N - 1) - 3N = 4N - 7 = 4·delta.
For N < 2 every co-type of a winning seven has |I_x| >= 3 (a co-type {i,j} needs K_i ∪ K_j = V, and
2c < N). So a winning seven on N < 2k carries total waste exactly 4·delta, whatever its structure.

**2.2 Useful additions.** In a winning seven on N < 2k choose a 3-set ℓ(x) ⊆ I_x for each x (the
line of x in the Fano case) and put L_i = {x : i in ℓ(x)} ⊆ K_i. Then Σ_i |L_i| = 3N and
|L_i ∩ S_i| <= t, so

    Σ_i |L_i ∖ S_i|  >=  3N - 7t  =  3·delta - 7·eps :

at least that much of the mass on the lines was added by the adversary. A reply to a full request
contributes at most omega = delta - eps. Hence **for N > 5T - 2k (delta > 5·eps) every winning
seven contains at least three replies in which the adversary's additions lie partly on that
reply's own line.** (5T - 2k is also where the pencil certificate dies for a different reason:
anchors at the Fano point need a kernel >= N - 2t, and S_3 ⊇ kernel ∪ (V∖(K_1∪K_2)) caps the kernel
at (t + N - 2)/2; these are compatible iff N <= 5t - 2.)

**2.3 Slack of a certificate with q free replies.** If q of the seven co-edges are used in full
(mass c each, whatever he added) and the other 7 - q only through their requests (mass t), the
count q(N - 1) + (7 - q)t >= 3N has slack

    (q - 3)(N - 7/4) + (7 - q)·eps .

q = 3: slack 4·eps at every N. So every "three replies + four non-adaptive requests" certificate is
a zero-slack design at t = 3/4. Direct check for anchors (union V; kernel κ, pair parts p, single
parts q in the notation of TWIN §13): p = 3 - N + κ, q = 2N - 3 - 2κ, so 2p + q = 3 identically,
against the 4t kills available.
q = 4: slack delta + 3·eps; q = 6: 3·delta + eps. More free replies give more slack, but §6 shows
the adversary spends omega of it in every free reply after the second.

## 3. Theorem T: triangle anchors [proved by hand; computed exact]

Three co-edges K_1, K_2, K_3 (any N; confined game on V). Cells:
a = K_1∩K_2∖K_3, b = K_1∩K_3∖K_2, d = K_2∩K_3∖K_1, e_i = points in K_i only, g = V∖(K_1∪K_2∪K_3),
κ = K_1∩K_2∩K_3.

**Theorem T.** Split κ = κ_4 ⊔ κ_5 ⊔ κ_6 arbitrarily. If

    |a| + |e_3| + |g| + |κ_4| <= T,  |b| + |e_2| + |g| + |κ_5| <= T,  |d| + |e_1| + |g| + |κ_6| <= T,
    |e_1| + |e_2| + |e_3| <= T,

then the four non-adaptive requests S_4 = a∪e_3∪g∪κ_4, S_5 = b∪e_2∪g∪κ_5, S_6 = d∪e_1∪g∪κ_6,
S_7 = e_1∪e_2∪e_3 give seven replies with no 2-cover, whatever the adversary answers.
*Proof.* a, b, d, e_1, e_2, e_3, g are the points of a Fano plane with lines
abe_1, ade_2, bde_3 (inside K_1, K_2, K_3), ae_3g, be_2g, de_1g, e_1e_2e_3 (inside K_4..K_7 because
requested). Every point of one of the seven cells lies in the three co-edges of its pencil; a point
of κ_4 lies in K_1, K_2, K_4, the pencil of a (similarly κ_5, κ_6 with b, d). So every co-type
contains a pencil; two pencils share a line; 1.1. ∎
Edge language: a = points only in B_3, e_3 = B_1∩B_2∖B_3, g = B_1∩B_2∩B_3, κ = points in no B_i; so
S_4 = (B_1∩B_2) ∪ (only B_3) etc., S_7 = points in exactly two of B_1, B_2, B_3. The three replies are
anchors only if g = ∅. (In the open game the theorem needs g = ∅ or confinement: a point outside V
together with a point of g could cover.)

**Closed form (κ = ∅).** With a, b, d now the masses of the three pairwise intersections of the
co-edges: |a| + |e_3| + |g| = 2a + 2k - N and Σ|e_i| = 3(N - k) - 2(a + b + d), so the condition is

    a, b, d <= (T + N - 2k)/2    and    a + b + d >= (3N - 3k - T)/2 ,

solvable iff T >= 3k/4, with a = b = d = N/2 - 5k/8 at T = 3k/4 and tolerance O(eps·k). In terms of
the replies (x_ij = |B_i∩B_j| = a_ij + 2k - N): B_1∪B_2∪B_3 = V, every x_ij <= (T + 2k - N)/2,
Σ x_ij >= (9k - 3N - T)/2.
- N = 7k/4: x_ij = k/2, triple intersection k/4: three lines of the Fano blow-up in general position.
- N = 2k: x_ij = 3k/8, triple intersection k/8.
- N = 3k - T: x_ij = T - k/2, triple intersection 0: PETAL's balanced anchors (1/4,1/4,1/4).
So the zero-slack three-reply certificates form two curves in N: the pencil (Theorem C, kernel
N - 2t; exists for all N but is unreachable for N > 5t - 2) and the triangle (Theorem T).
`check_core.py A`: 1581 random triples of co-edges on 8–16 points, requests as stated, replies padded
adversarially (kernel points first): all seven-tuples uncoverable by brute force. `D`: closed forms.

Why this does not close the window: the target is a point (a, b, d) with tolerance O(eps), and the
adversary places each |K_i∩K_j| anywhere in a window of width omega >> eps (he adds E inside K_i or
outside it at will). The same holds for Theorem C. This is 2.3 with q = 3.

## 4. Theorem Q: four free replies, static finish [proved by hand; computed exact]

Four co-edges K_1..K_4, cells by co-type I ⊆ [4]. s_0, s_1 = mass with |I| = 0, 1;
u_3, u_4 = mass with |I| = 3, 4; c(m) = mass of the two pair cells of the matching m.
**Theorem Q.** Distribute the cells with |I| >= 3 over the three matchings (masses τ_1+τ_2+τ_3 =
u_3+u_4). If c(m_r) + s_0 + s_1 + τ_r <= T for r = 1, 2, 3, three non-adaptive requests win.
*Proof.* Quadrangle 1234 with diagonal points 5, 6, 7; a co-type must be completed to contain a
line: a pair needs its diagonal point, |I| <= 1 needs 5, 6, 7 (the line 567), |I| >= 3 needs any one
of 5, 6, 7 (three points of a quadrangle span three lines, each through one diagonal point). ∎
**Load identity.** Σ_r loads = 4k - N + W,  W := u_3 + 2u_4 + s_1. So the certificate needs

    W  <=  N - 7k/4 + 3·eps·k  (= slack of 2.3 with q = 4),

plus balance of the three loads. (Same count as TWIN 16.4 in complement form; TWIN's adaptive
version does not charge τ.) Points outside all four co-edges (s_0; TWIN's n_4) cost nothing in W:
they are the seventh Fano class. `check_core.py B`: 1560 random quadruples, all uncoverable;
identity exact.
So with four free replies she may tolerate waste delta + 3·eps in total; the adversary's dumping (§6)
produces omega = delta - eps per reply after the second, i.e. 2·omega > delta + 3·eps as soon as
delta > 5·eps. One of K_3, K_4 must be (almost) waste-free.

## 5. Pool theorem: forcing by exhaustion [proved by hand; computed exact]

**Theorem P.** Confined game on V, k + T <= N, T >= 3k/4. Let Z ⊆ V be known to her,
omega <= |Z| <= N - 3k/2, and suppose the adversary follows the pool rule: K∖S ⊆ Z whenever
|Z∖S| >= c - |S|. Then she wins in seven requests without discard (for every N, in particular
throughout the window where TWIN 16.A and the (L)/(Q) strategies are unproved).
*Proof.* Choose w_o with max(|Z|, N - 2T) <= w_o <= N - 3k/2 (possible iff T >= 3k/4), a class
V_o ⊇ Z of mass w_o, and split the rest into six classes of mass (N - w_o)/6. Lines through o
have mass (N + 2w_o)/3 <= c, the other four (N - w_o)/2 <= T. For a line L ∋ o request
S = (L∖Z'') ∪ padding, Z'' ⊆ Z of mass omega, |S| = T, padding outside Z''; then Z∖S = Z'' has
exactly the mass he must add, so K = S ∪ Z'' ⊇ L. For the other four lines request L itself.
1.3(ii). ∎
`check_core.py C`: (k,T,N,|Z|) = (8,6,16,2), (8,6,16,4), (8,6,15,3), (12,9,24,4), (12,10,24,5),
(12,10,23,3), (16,13,30,4), (16,13,33,5), (20,16,40,6): 200 random pool adversaries each, all seven-
tuples uncoverable. (At T = 3k/4 exactly this is consistent with FRESH_C 14.1: the genuine
(7,2)-families there are not pool adversaries.)
Reading: the pool adversary is the cheapest way to waste — he wastes omega in each of the four
lines missing o and is forced to be useful in the three lines through o; total waste 4·omega
against the budget 4·delta of 2.1. The margin is 4·eps: a single pool is exactly as strong as the
complete family, in line with FRESH_C Cor. 3b and the "pool barrier" of STATUS_AND_PLAN.

## 6. Where the gap really is [first-order analysis; heuristic where tagged]

Regime 5T - 2k < N < 11k/6 (eps << delta): every certificate is a Fano blow-up (1.3) with classes
of mass in [k/4 - delta, k/4 + delta] [proved, given 1.3: from the seven line constraints
w(L) <= c and Σ w = N].
- Reply 1 is free (L_1 := K_1). Reply 2 is free: K_1∩K_2 becomes the class o, provided
  k/4 - delta <= |K_1∩K_2| <= k/4 + delta, which she can enforce [proved].
- From reply 3 on, some class of mass about k/4 is already determined and off the current line
  (o for a triangle labelling; K_1 △ K_2 for the third pencil line), and it cannot be requested
  without wasting it herself. He adds his omega there: a co-type {1,2,3} with 1,2,3 a triangle, or
  a point of K_1∖K_2 in the third pencil line — each one unit of waste (2.1). So in a seven-request
  play with fixed order he wastes 5·omega > 4·delta. [heuristic as a statement about all strategies;
  it is the first-order form of the 7-request thresholds of FRESH_C §10]
- By 2.2 she needs a third reply with useful additions: three co-edges that are exact lines of one
  blow-up, i.e. (triangle) pair intersections within O(eps) of N/2 - 5k/8 and triple intersection
  O(eps) — Theorem T — or, using Theorem Q's larger slack, only

      |K_1 ∩ K_2 ∩ K_3| <= about 4·eps·k,  no single cells, pair intersections in windows of width ~delta,

  followed by one dumped reply K_4 (waste omega = delta + 3·eps - 4·eps).
  In edge language: **three replies whose union misses at most ~4·eps·k points of V**, with pairwise
  intersections k/2 - O(delta). He prevents it for the triple he sees by omitting from the third
  reply omega points of V∖(B_1∪B_2).
- What a discard can do [heuristic]: (a) dilution — if she holds m pairs (K_i, K_j) with pairwise
  disjoint intersections, his omega additions meet one of them in at most omega/m; (b) exhaustion —
  if his dumps stay inside a set Z of mass <= N - 3k/2, Theorem P forces three useful replies.
  His counter to (a) is to re-use one dump set Y (so Y lies in every co-edge); then Y is a kernel
  and he is a pool adversary: (b). REDTEAM §11's verified winning lines (class (T) at 1.9k with one
  spare and rounds 7–8 binding; class (Q) at 2.0k with a 0.122 cell of reply-type 1234, i.e. s_0 > 0)
  are consistent with this picture; I did not turn (a)/(b) into a lemma.

## 7. Exact remaining statement, and what was not touched

**(CP)** For every eps > 0 and k >= k_0(eps), T = (3/4 + eps)k, k + T <= N < 3k - T: every T-covering
family of (N - k)-subsets of an N-set contains seven members covering all pairs. Open for
3T - k/2 < N < 3k - T. For N < 11k/6 it is equivalent to: seven members and a cover of V by seven
Fano classes with K_i ⊇ L_i. Necessary by 2.2: three of them carry useful additions.
**Suggested lemma (dump dichotomy), not proved.** For N in the window, within m(eps) requests either
(a) three replies have union >= N - 4·eps·k with pair intersections in the windows of §4, or
(b) there is Z, |Z| <= N - 3k/2, containing the additions of all replies to requests that leave
omega of Z free. (a) then still needs the balance step for K_4 (TWIN 16.6 with W in place of the
count); (b) is Theorem P.
Not touched: the far-reply half of the gap (dominant-pair spread triples; TWIN 17.3 ordering
problem; PROOFS §10 E10e: a far reply only forces overlaps > t - 1/3); N >= 11k/6, where non-Fano
endings occur (REDTEAM 11.3) and 1.3 is only sufficient; any exact game computation (none was run:
the informative sizes (10,8), (12,10) are beyond one worker in the time box).

Self-check: Theorems T, Q, P and 2.1–2.3 re-derived once after writing; T, Q, P and the identities
agree with brute force (`check_core.py`). §6 is analysis, not proof; "every winning seven for
N < 11k/6 is a Fano blow-up" is quoted from ROADMAP §0.1 (computed there, not re-checked here).

=============================================================================================
# Part II — the dump dichotomy (second time box)

Brief: prove "within m(eps) requests either (a) three replies with union >= N - 4·eps·k and pair
intersections in Theorem Q's windows, or (b) all dumps in a pool of size <= N - 3k/2"; cover the swap
adversary (TWIN §18, REDTEAM §12); re-check ROADMAP's 11k/6. Code: `compute/core/fano_floor.py`,
`compute/core/swap_check.py`.

**Outcome: the dichotomy is NOT proved, and as stated in §7 it is not the right statement.**
- Branch (a) was mis-stated (§8.2): once the fourth reply is dumped, Theorem Q's windows collapse
  to Theorem T's point; the correct requirement is a count of *useful* dump (§8.1).
- Proved: a reading lemma (§9.1: against a FIXED pair the third reply always carries waste omega,
  whichever labelling she chooses afterwards), the mode lemma (§9.2: pure "high" and pure "low"
  adversaries lose in seven requests; the rigid swap adversary is pure high at replies 2–3 and
  loses to pencil-first — agrees with REDTEAM §12), and a dilution lemma with its consequence
  "pile or pay" (§10).
- What is left is exactly the adversary the coordinator's caveat names: one whose mode at replies
  2–3 depends on her request (§9.3, "anti-plan"). §10 shows what he is forced to do against a
  portfolio (re-dump into a nested kernel) but I could not close either branch (§11).
- ROADMAP's 11k/6 re-computed: confirmed (§8.3).

## 8. Corrections and the exact accounting

### 8.1 Useful-dump profile [proved by hand, given 1.3 for N < 11k/6]

In a Fano certificate with classes w_v and lines L_i ⊆ K_i put u_i = (|L_i| - t)^+ (the part of line i
she could not request). Then w_v = (Σ_{i ∋ v} |L_i| - N)/2, so the class masses and the line masses
determine each other, and Σ_i (|L_i| - t) = 3N - 7t = 3·omega - 4·eps. A reply K_i = S_i ∪ D_i can be the
line i only if D_i ⊇ L_i∖S_i, i.e. at least u_i of its dump is on its line. Two replies are free
(u = omega each: L_1 = K_1, L_2 = K_2). Hence

    she wins with these seven  ⟹  Σ_{i >= 3} (useful dump of reply i)  >=  omega - 4·eps,

and the certificate has total slack (Σ_{i>=3} useful dump) - (omega - 4·eps). With exactly three
useful replies the slack is 4·eps and all class masses are forced: triangle a = b = d =
N/2 - 5k/8 + O(eps) (Theorem T) or pencil with kernel N - 3k/2 + O(eps) (Theorem C at the Fano
point). "Useful" includes landing in the right cell: a dump that is on the line but unbalances
the three classes of the line is useful only if a later line absorbs the imbalance, which again
needs useful dump there.

### 8.2 Correction to §4/§6/§7 [proved]

§6 said that with Theorem Q she needs only |K_1∩K_2∩K_3| <= 4·eps·k "with pair intersections in
windows of width ~delta". That is wrong when the fourth reply is dumped: then W = omega + (waste of
the first three), the slack of Theorem Q is 4·eps - (that waste), base loads are
2a + 2k - N etc., and the conditions are those of Theorem T (a, b, d within O(eps) of N/2 - 5k/8).
Windows of width ~delta exist only if the FOURTH reply is also (partly) useful. Branch (a) of the
"suggested lemma" in §7 must therefore read: *replies 3..7 carry useful dump >= omega - 4·eps in
total, in the right cells* (8.1). Three replies with a small common intersection are necessary for
the profile (omega, omega, omega, 0, 0, 0, 0) but not sufficient.

### 8.3 ROADMAP §2.2 re-checked [computed; float MILP, HiGHS]

`fano_floor.py`: co-types F ⊆ [7] with masses m_F, pairwise intersecting supports, every edge of
mass 1 (Σ_{F ∌ i} m_F = 1); minimise N = Σ m_F. Unrestricted optimum 7/4 (the seven lines, 1/4
each). With the constraint "for each of the 30 Fano planes, not all seven lines are co-types":
optimum **11/6** = 1.83333, attained by six lines (1/3, 1/3, 1/3, 1/6, 1/6, 1/6) and one 4-set
(1/3) — ROADMAP's example. So for N < 11k/6 all seven lines of one plane occur as co-types, hence
every co-type meets every line, hence contains a line: 1.3's "every winning seven is a Fano
blow-up" stands. Not an exact certificate (127 binaries, floating point); the value and the
optimal support agree with ROADMAP's independent run.

## 9. One pair, one third reply

Notation: free pair K_1, K_2; O = K_1∩K_2, A = K_1∖K_2, B = K_2∖K_1, g = V∖(K_1∪K_2). For a third
co-edge K_3 define
  W_tri = |K_1∩K_2∩K_3|  (1,2,3 labelled as three non-concurrent lines),
  W_pen = |K_3∩(A∪B)| + |O∖K_3|  (1,2,3 labelled as a pencil; needs g ⊆ K_3).

### 9.1 Reading lemma [proved by hand]

**Lemma.** In a Fano certificate containing K_1, K_2, K_3, the points counted by W_tri (resp. W_pen)
have co-type of size >= 4, so they consume that much of the waste 4N - 7k of 2.1. If
3·omega <= |O| <= c/2, then for EVERY request S_3 the adversary has a reply with
min(W_tri, W_pen) >= omega.
*Proof.* Waste: a co-type ⊇ {1,2,3} with 1,2,3 non-concurrent contains a pencil and a line outside
it. For the pencil labelling, a point of K_3∩A has 1, 3 in its co-type but not 2; the only pencil
containing two of the lines 1, 2, 3 is {1,2,3}; so its co-type contains a pencil plus one of 1, 3
outside it. Same for O∖K_3 (has 1, 2, lacks 3).
Reply: let s_O = |S_3∩O|. If s_O >= omega he dumps entirely into (A∪B)∖S_3 (it has mass
>= c + omega - 2|O| >= omega): W_tri >= s_O >= omega and W_pen >= omega. If s_O < omega he dumps entirely
into O∖S_3 (mass >= 2·omega): W_tri >= omega and W_pen >= |O| - s_O - omega >= omega. ∎
So no labelling chosen after the fact rescues the third reply against a fixed pair: she loses
omega of the 4·omega + 4·eps available, and by 8.1 must then find omega - 4·eps of useful dump in
replies 4..7. The lemma is about one pair; it says nothing when she holds several candidate pairs.

### 9.2 Mode lemma: pure adversaries lose [proved by hand; computed]

Call a reply *high* if its dump lies in the common intersection of the co-edges she relates it to
(points "unused" by the replies so far), *low* if it lies on points in the fewest co-edges.
**(H) High at replies 2 and 3 (this is the rigid swap adversary of TWIN 18.6 F1 / REDTEAM §12).**
She wins in seven requests, whatever he does from reply 4 on (swap included):
S_2 = o_2 ∪ P_2 with o_2 ⊆ K_1, |o_2| = N - 3k/2 - omega, P_2 ⊆ B_1, |P_2| = k/2. High dump: D_2 ⊆ K_1,
so |K_1∩K_2| = N - 3k/2 and B_1∩B_2 = B_1∖P_2 has k/2 points. S_3 = (K_1∩K_2 ∖ D_2) ∪ (B_1∩B_2),
|S_3| = T. High dump at reply 3 must be D_2 (the only unused unrequested points): B_3 = B_1 △ B_2.
The three replies are anchors with union of 3k/2 <= 2T points; Theorem C finishes. ∎
(This is "forcing by exhaustion" again: Theorem P with Z = the current unused set.)
`swap_check.py`: (k,T) = (20,16), (24,19), (40,31), every N with 3T - k/2 < N < 3k - T, 40 random
plays each, rule "omit unused at replies 2–3, take unused first and B_1-only next at reply 4":
no 2-cover in any play. REDTEAM §12's exact 8-request lines find the same mechanism (line-first,
B_1∩B_2 = k/2 sealed at request 3); seven requests suffice for the rigid rule.
**(L) Low at replies 2 and 3.** S_2 with exactly a* = N/2 - 5k/8 points of K_1: low dump stays
outside K_1, so |K_1∩K_2| = a*. S_3 with a* points of each of A, B, the rest in g, none in O: low
dump goes to g (mass |g| - |S_3∩g| = k/4 + delta/2 >= omega to spare). Then K_1∩K_2∩K_3 = ∅ and
a = b = d = a*: Theorem T finishes. ∎
**(K) High forever.** If every dump lies in the common intersection of all earlier co-edges
whenever she leaves it unrequested, then from the third reply on the dump is one fixed set Y,
|Y| = omega, K = S ∪ Y: on V∖Y he has no move, and the complete family on (k + T) points loses to
the Fano blow-up for T >= 3k/4.

### 9.3 What is left: the anti-plan adversary

By 9.1 the adversary who survives answers a triangle-type request (S_3 ∩ O = ∅) high and a
pencil-type request (S_3 ⊇ most of O) low; by 9.2 he must really switch. This is precisely the
coordinator's caveat ("rounds 2–3 omissions depend on her request"). Is a swap a dump into a
pool? At replies 2–3 yes (pool = unused set), and that is why the rigid version loses; the
dangerous version uses the pool only when she does not ask for it. He is neither branch of the
§7 dichotomy: his dumps are not confined to any set of mass <= N - 3k/2 (the low dumps range over
A∪B), and against a fixed pair no third reply is useful (9.1).

## 10. Portfolios: dilution, and "pile or pay" [proved by hand]

**Dilution lemma.** Let X_1, X_2, X_3 be co-edges, κ = X_1∩X_2∩X_3, and K = S ∪ D a co-edge with S
disjoint from X_a∩X_b for all a < b. Then

    min_{a<b} |K ∩ X_a ∩ X_b|  <=  |D∩κ| + (omega - |D∩κ|)/3 .

*Proof.* A point outside κ lies in at most one of the three pairwise intersections. ∎
**Pile or pay.** Fix 0 < ν < 1. If the triangle waste of K against every one of the three pairs is
at least ν·omega, then |D ∩ κ| >= (3ν - 1)·omega/2: he has re-dumped into the common intersection of
the portfolio. With ν = 1 - η: |D∩κ| >= (1 - 3η/2)·omega.
Consequences.
- If the portfolio is an exact triangle (κ = ∅) the next reply has triangle waste <= omega/3
  against some pair — but an exact triangle is already what she wants (circular).
- Starting from K_1, K_2 free and K_3 dumped high (Y_3 = D_3 ⊆ O), a request S_4 avoiding the three
  pairwise intersections (possible: the points in at most one of K_1, K_2, K_3 have mass about k)
  gives: either K_4 has waste < ν·omega against one pair (he "pays" (1-ν)·omega of useful dump), or
  Y_4 = D_4∩Y_3 has mass >= (3ν-1)·omega/2 and lies in four co-edges (he "piles").
- Iterating over triples that contain the newest reply produces nested sets Y_3 ⊇ Y_4 ⊇ ...,
  |Y_j| >= (1 - 3(j-3)η)·omega (the common intersection of a later triple exceeds the previous Y by at most 3η·omega/2), each lying in all co-edges used so far, as long as he never pays
  more than η·omega. In the limit η → 0 this is case (K) of 9.2.
So against a portfolio the anti-plan adversary's high answers are forced into ONE nested kernel;
he cannot spread them.

## 11. Why this does not yet close the gap

Two steps are missing; each is a precise statement.
**(M1) Cashing the "pile" branch.** After j replies there is Y with |Y| >= (1 - O(η))·omega inside
K_1, ..., K_j, and K_i = S_i ∪ Y ∪ (error O(η·omega)) for i >= 3. On V∖Y the replies i >= 3 are her own
requests, so she has (almost) the complete family there — but only for requests that were
triangle-type against the portfolio, and K_1∖Y, K_2∖Y are not hers. To finish she must make the
later S_i lines of one Fano blow-up of V∖Y through K_1∖Y and K_2∖Y while each S_i still avoids the
pairwise intersections of some earlier triple (so that the dilution lemma keeps applying). In a
Fano plane exactly one line avoids all three vertices of a triangle, so the portfolio must be
re-chosen at every step; I did not find an order of seven lines that keeps the lemma applicable
throughout, nor a proof that none exists. If he stops piling at some step, that step is "pay".
**(M2) Cashing the "pay" branch.** A reply that pays gives useful dump (1-ν)·omega against one pair,
at a place of his choosing among A, B, g (balance). By 8.1 she needs omega - 4·eps in total and in
the right cells; one payment of size η·omega is far from it, and I have no mechanism that makes him
pay repeatedly: after a payment the portfolio changes and he may pile into a different kernel.
The natural potential is Σ_j |Y_j|-deficits (each reply either extends the nested kernel or pays),
but the kernel can be abandoned at no cost to him when she changes the portfolio — this is the
swap, now in its request-dependent form.
**Exact remaining statement** (replaces §7's suggested lemma). For 3T - k/2 < N < 11k/6 and
T = (3/4 + eps)k: there is m(eps) such that against every adversary she obtains, within m(eps)
requests, seven replies and a Fano labelling with Σ_{i>=3} (useful dump of reply i) >= omega - 4·eps·k
in the cells required by 8.1. Known: false for any fixed pair and fixed order (9.1 plus 2.2);
true against pure-mode adversaries and pool adversaries (9.2, Theorem P); against a portfolio the
adversary must pile into one nested kernel or pay (§10).
**Single best next step.** Decide (M1) by a finite search: the first-order game is finite-
dimensional (masses of the Venn cells of the portfolio), and the pile branch with η = 0 is a
one-player problem: choose requests S_3, ..., S_m in V∖Y, each avoiding the pairwise intersections of
three earlier co-edges, with replies K_i = S_i ∪ Y, such that K_1, K_2 and five of the S_i ∪ Y form a
Fano cover. If that design exists (an LP over cell masses for each of the finitely many line
orders), "pile" is a win and only (M2) remains; if it does not, the request-dependent swap is a
genuine obstruction to every strategy of the "portfolio + triangle-type request" kind, and a
different request type (one that is triangle-type for one pair and pencil-type for another) is
needed. I did not run this search (time).
Not touched in this box either: the far-reply half (TWIN 17.3), N >= 11k/6.

Self-check (Part II): 9.1 re-derived with the room condition |(A∪B)∖S_3| >= c + omega - 2|O|; 9.2(H)
arithmetic checked symbolically and by `swap_check.py`; 9.2(L) uses |g| = 2k - N + a* and
|S_3∩g| = T - 2a*; dilution lemma is a one-line count. §10's iteration and all of §11 are
statements about what is forced, not a strategy with a proof.

=============================================================================================
# Part III — M1 decided, M2 analysed (third time box)

Code: `compute/core/m1_search.py`, `compute/core/balance_check.py`.
**Outcome.**
- **M1 (pile branch):** decided, in two versions. Strict version (every request a line of the
  target plane, justified by dilution against three earlier piled lines): INFEASIBLE for
  omega > 4·eps·k, with an explicit combinatorial obstruction (§12.1). Weak version (helper requests
  allowed): a design exists and is verified in exact rationals at t = 19/25 and t = 751/1000
  (§12.2) — but it needs |K_1∩K_2| = N - 3k/2 exactly, and, decisively, **the pile is not forced**
  at its critical request: the adversary has dumps that "pay" in the sense of §10 and give her
  nothing (§12.3, real sets). So "pile or pay" is a true inequality with no strategic content.
- **Why:** piling is good for HER, not for him (§13: a predictable dump is exact control; two piled
  replies after any reply give a Theorem T triangle). The adversary never needs to pile.
- **M2 ("pay"):** exact criterion (§14.1, proved and checked): after an exact pair, a triangle-type
  third reply closes with Theorem T iff all but eps·k of its dump lies outside K_1 ∪ K_2. So he
  spoils every three-useful-reply certificate by keeping 2·eps·k of every dump inside K_i ∪ K_j for
  the pairs in position — a spread dump does it for all pairs at once (§14.2). Dilution cannot
  prevent that. The dichotomy is therefore not rescued: neither branch is forced.
- What survives is §8.1's accounting and one new structural fact: *usefulness is predictability*
  (§13). The adversary that remains must be simultaneously spread and unpredictable in one real
  parameter per reply ("tilt"); a testable seed is given in §15. No counterexample is claimed:
  the seed defeats only certificates of profile (omega, omega, omega, 0, 0, 0, 0).

## 12. M1: the pile branch with the kernel fixed

Model. He answers K_3 = S_3 ∪ Y (S_3 triangle-type against K_1, K_2; Y ⊆ K_1∩K_2, |Y| = omega) and
piles (D = Y) on every later full request that is *justified*: disjoint from Y and from the
pairwise intersections of three earlier co-edges whose common intersection is exactly Y. All other
replies add nothing she can use. On V' = V∖Y (mass k + T, independent of N) piled co-edges are her
own T-sets, so she is in the complete family on k + T points: total slack 4·eps·k, every
certificate a Fano blow-up with all lines of mass T - O(eps·k). Y itself must end inside three
concurrent co-edges.

### 12.1 Strict version: infeasible; the obstruction [proved by hand; computed]

**Lemma (quadrilateral closure).** In the Fano plane the only line missing the three vertices of
a triangle is the line through the third points of its sides; the four lines so obtained (a
complete quadrilateral, six intersection points) are closed under this operation, and each of the
remaining three lines passes through a vertex of every triangle formed by three of the four.
*Proof.* Seven points: three vertices, three side-midpoints (collinear), one centre; the other three
lines are {vertex, opposite midpoint, centre}; a triple of the four lines has as vertices three of
the six non-centre points and the complementary three are the vertices involving the fourth line;
{v_ab, mid_c, centre} meets {v_ab, ...}, and for the triples containing the medial line it meets
mid_c. ∎
Consequence: starting from K_1, K_2, S_3, the justified lines are exactly these four. Y then has
co-type = a quadrangle, which contains no pencil; the three remaining lines are pencil-type
against some pair and are answered low. She must request Y herself in one of them:
that line has mass <= T - omega while the two given lines have mass T, and the LP over class masses is
feasible iff **omega <= 4·eps·k** (i.e. N <= 5T - 2k; nothing beyond the known range).
`m1_search.py (a)`: closure size 4 and "Y in no pencil" for all 168 ordered starts; LP feasible at
omega = 4·eps - 10⁻⁴ and infeasible at 4·eps + 10⁻³ for t = 0.76 and t = 0.751 [float LP].

### 12.2 Weak version: a design exists [computed; exact rational verification]

Allow helper requests (any three classes, mass exactly T, justified the same way, later discarded).
Shortest sequence found (classes 0..6, lines 012, 034, 056, 135, 146, 236, 245):
K_1 = 012, K_2 = 034, S_3 = 135 (triangle, vertices 0, 1, 3), helper H = 246 (misses 0, 1, 3), then
the third line through v_12, 056, is justified by the triple (012, 135, 246) (pairwise
intersections {1}, {2}, ∅). If he piles there, Y lies in K_1, K_2 and that reply — a pencil — and the
remaining lines 146, 236, 245 need no help. Eight requests.
Exact solutions: t = 19/25: classes (6/25, 13/50, 13/50, 13/50, 13/50, 6/25, 6/25);
t = 751/1000: (249, 251, 251, 251, 251, 249, 249)/1000; all constraints verified in Fractions.
The class v_12 is forced to mass T - k/2 in both LPs: the design exists only if |K_1∩K_2| =
N - 3k/2 exactly (the pencil kernel). N does not enter otherwise, so this holds for every N in the
window. Real-set check at (k,T,N) = (100,76,190): with the pile at 056 the seven co-edges cover all
pairs.

### 12.3 The pile is not forced [computed on real sets; reason proved in §13–§14]

Same instance, the decisive request S = 056 against the triple A = 012 ∪ Y, B = 135 ∪ Y, C = 246 ∪ Y.
For each dump the table gives the amount by which Theorem T fails (max load - T, best split of the
common part) for the three pairs with K = S ∪ D as third co-edge:

| dump D (omega = 14 points) | pair AB | AC | BC |
|---|---|---|---|
| inside class 1 = A∩B | 5 | 14 | 38 |
| inside class 2 = A∩C | 14 | 5 | 38 |
| inside class 3 (in B only) | 14 | 14 | 38 |
| inside class 4 (in C only) | 14 | 14 | 38 |

A dump inside class 3 or 4 meets no pairwise intersection at all ("pays" omega against every pair
in the sense of the dilution lemma), does not contain Y, and no reading closes. So after such a
reply she has neither the pencil for Y nor a triangle: the M1 design is a design, not a strategy.
This is the obstruction asked for. It is NOT an adversary's winning certificate for the game: it
kills the pile branch and every plan whose only free replies are K_1, K_2 and one more.

## 13. Usefulness is predictability [proved by hand]

**Exact-control lemma.** Let K be any co-edge and suppose that for two later full requests S', S''
she knows the dumps in advance (e.g. D' = D'' = Y for a known Y, Y∩K = ∅). Then she wins in six
requests after K: choose S', S'' with |S'∩K| = |S''∩K| = a*, |S'∩S''| = a* - |Y|, S'∩S''∩K = ∅ and
T - 2a* + (something fixed) points outside, so that (K, S' ∪ Y, S'' ∪ Y) has pairwise intersections
a* = N/2 - 5k/8 and empty common intersection; Theorem T finishes with four non-adaptive requests.
*Proof.* All three pairwise intersections and the triple intersection are determined by her
choices once D', D'' are known; the sizes fit because |S'| = |S''| = T and 3a* <= c + (c - a*)
(room inside and outside K). ∎
So: a reply is "free" exactly when its dump is known before the request is made. The first reply
is free because nothing depends on it; the second because one class absorbs any dump; from the
third on a dump is useful only if predicted. This explains at once why (i) every scripted
adversary of FRESH_C/REDTEAM loses (proportional, rigid swap, pure modes: all predictable — she
pre-compensates the class sizes), (ii) piling loses (§9.2 (K)), (iii) the dilution lemma has no
force: it restricts where an unpredictable dump can be simultaneously "inside" several pair
intersections, but he needs no such thing.

## 14. M2: what a "payment" would have to be

### 14.1 Balance lemma [proved by hand; computed exact]

Let |K_1∩K_2| = a* (exact pair), g = V∖(K_1∪K_2), and S_3 the triangle-type request with a* points in
each of K_1∖K_2, K_2∖K_1 and T - 2a* points of g. For the reply K_3 = S_3 ∪ D write
d_O, d_A, d_B, d_g for the masses of D in K_1∩K_2, K_1∖K_2, K_2∖K_1, g. Then Theorem T applies to
(K_1, K_2, K_3) iff

    d_g  >=  omega - eps·k + |d_A - d_B|      (in particular  |D ∩ (K_1∪K_2)| <= eps·k).

*Proof.* Cells: a = a* - d_O, κ = d_O, b = a* + d_A, d = a* + d_B, e_1 = c - 2a* - d_A,
e_2 = c - 2a* - d_B, e_3 = T - 2a* + d_g, g' = |g| - (T - 2a*) - d_g. Loads: a + e_3 + g' + κ_4 =
3k/4 - d_O + κ_4 (so all of κ goes to round 4); b + e_2 + g' = T + (omega - eps·k) - d_g + (d_A - d_B);
d + e_1 + g' = the same with A, B exchanged; e_1 + e_2 + e_3 = T - (N - 7k/4) - d_A - d_B + d_g <= T. ∎
`balance_check.py`, (k,T,N) = (100,76,189), omega = 13, eps·k = 1: dumps (O,A,B,g) = (0,0,0,13) and
(1,0,0,12) close; (0,1,0,12), (2,0,0,11), (0,1,1,11), (0,6,7,0), (13,0,0,0), (0,13,0,0) do not
(excess 1, 1, 1, 13, 12, 25).
Other triangle-type requests are no better: with a* - x points in each private part she needs
2x + d_g >= omega - eps·k and d_A + d_B >= 4x - omega - eps·k with |d_A - d_B| <= O(eps·k); every request
has a spoiling dump (all of D in K_1∩K_2), which is 9.1.
In reply language: the third reply must omit, from the offered set, only points of B_1∩B_2.

### 14.2 The spoiler, and why dilution does not stop it [proved]

To spoil the triangle for a pair he needs only 2·eps·k of the dump inside K_i ∪ K_j. For m pairs in
position this costs at most 2·eps·k·m of dump if he treats them separately, and nothing extra if
the dump is spread: a dump proportional on V∖S puts a constant fraction of omega (about 0.7 in the 14.1 position) inside every K_i ∪ K_j. So for
omega >> eps·k no portfolio of pairs yields a closing triangle against a spread dump. For a pencil-type
request the same holds with K_i △ K_j in place of K_i ∪ K_j.
A *known* spread dump is harmless (§13): she shifts her requests by the known amounts. So the
adversary must be spread and unpredictable. One real parameter suffices: by 14.1 her tolerance in
d_A - d_B (or in d_g) is eps·k, his freedom is omega.
**Hence M2 fails as a forcing statement:** against the request-dependent adversary a single reply
never "pays" in a usable way, with or without a portfolio. Any proof must use certificates in
which the useful dump of 8.1 is spread over several replies with total slack >> eps·k, i.e. at
least four replies whose dumps she can absorb whatever their tilt; with three it is impossible.

## 15. Where this leaves the gap

**Seed adversary to test exactly (not a counterexample claim).** "Tilted spread": to each full
request S reply with the dump D = proportional dump on V∖S, modified by moving omega/2 of it either
INTO or OUT OF the set of points lying in at least two earlier replies' co-edges (two modes), the
mode chosen by the adversary. It is spread (spoils Theorems C, T, P and every exact triangle by
14.1–14.2) and has one unpredictable bit per reply. It is a two-branch menu, so the exact engines of
FRESH_C/REDTEAM can search it with the requester free: sizes (k,T,N) = (25,19,45..47), (50,38,90..95),
m = 8, 9. If the requester wins, the winning lines show how four or more replies absorb a tilt
(the mechanism a proof needs). If she loses for all m the engine can reach, the menu is a serious
candidate for the family test of 1.2.
**Exact remaining statement** (unchanged from §11, now with the reason it is hard): for
3T - k/2 < N < 11k/6 she must reach seven replies whose useful dump in replies 3..7 totals
>= omega - 4·eps·k in the cells fixed by 8.1; a dump is useful only if its location was known up to
the slack when the request was made (§13); against a fixed pair or any portfolio of pairs the
third reply is never useful (9.1, 14.1–14.2).
**A different route worth one look** [heuristic; literature not checked here]. In the family form
the "unpredictable" adversary is a fixed map, and T-covering forces |𝒞| >= C(N,c)/C(N-T, c-T), a
fraction exp(-omega·ln(e/omega)·k(1+o(1))) of all c-sets. For omega below an absolute constant this
exceeds the Frankl–Rödl forbidden-intersection threshold (1-γ)^N, so 𝒞 contains pairs with
|K∩K'| equal to any prescribed value such as a*·k or N - 3k/2: the window dodging at reply 2 is
impossible for a family. A version for the full Venn diagram of three members (pairwise a*, common
part <= eps·k) would give Theorem T directly for N <= (7/4 + δ_0)k; the obstacle is that the common
part must be O(eps·k), so the constant δ_0 may degrade with eps — this needs checking against the
quantitative forms (Keevash–Long) before any claim.
Not touched: far replies (TWIN 17.3), N >= 11k/6.

Self-check (Part III): 12.1 lemma re-derived from the seven-point picture and confirmed by
enumeration; 12.2 numbers are exact Fractions, the feasibility range of v_12 is from a float LP;
12.3 and 14.1 tables are brute-force on real sets; 13's sizes: |S'| = a* + (a* - omega) + rest with
S'∩S'' = a* - omega >= 0 outside K, and the parts outside K fit: omega + 2(T - a*) - (a* - omega) = N/2 - k/8 <= k for N <= 9k/4. §14.2's "at least four replies" is a
consequence of 2.3/8.1 (slack with three useful replies is 4·eps), not of a separate proof.

=============================================================================================
# Part IV — Barrier 2: the window 11k/6 <= N < 3k - T (fourth time box)

Code: `compute/core/spectrum.py` (patterns), `slackq.py` (slack by number of fully used replies),
`anchor_design.py` (static value of anchor triples). Units k = 1; tables at t = 3/4.
**Outcome: CP is NOT proved on this range, and the obstruction is the same one as below 11k/6.**
- Patterns (§16): the first genuinely non-Fano minimal pattern appears at N = 15/8, not 11/6; the
  11/6 pattern is still a Fano blow-up (one class carries an extra incidence). K4 and the
  2-(6,3,2) design both have minimal ground set exactly 2k. Exact rational values per pattern;
  the ordering and completeness rest on a float MILP, and the enumeration is complete only up to
  N = 17/9.
- Count (§17): non-Fano patterns need MORE incidences than Fano ones. Two fully used replies never
  suffice (proved, all N, T < 4k/5); with three the slack is exactly 4·eps·k and with four exactly
  (N - 7k/4) + 3·eps·k through the whole window (proved for N < 2k, computed for 2k <= N <= 9k/4).
  Non-Fano patterns improve the slack only for certificates with at least five fully used replies
  (from N ≈ 2.2k) or six (from N = 2k, where six co-edges alone can cover all pairs).
- Anchors (§17.3): on the grid 1/16 the only anchor shape with p > 3/4 and static value <= 0.76 is
  the Fano point (1/2,1/2,1/2); the next is (5,4,4)/16 at 0.777. So in the window three-reply
  certificates are still Theorem C (kernel N - 3k/2) and Theorem T, both zero-slack points.
- Mechanism of REDTEAM §11.3's non-Fano endings (§18): six fully used replies. That is available
  against a predictable adversary (§13) and only against one; it is not a new forcing mechanism.

## 16. Which patterns exist between 7k/4 and 9k/4

Model: co-types F ⊆ [7] with masses m_F, supports pairwise intersecting, every edge of mass 1
(Σ_{F ∌ i} m_F = 1); N = Σ m_F. `spectrum.py enum`: repeatedly minimise N by MILP, then exclude every
support containing an S_7-image of the support found; for each support the minimum is recomputed
exactly (vertex enumeration in Fractions). [exact per support; order/completeness: float MILP]

| N | co-type sizes | co-types and masses (rounds 1..7) | inside the up-set of a Fano plane? |
|---|---|---|---|
| 7/4 | 3⁷ | 125 134 167 236 247 357 456, 1/4 each | yes (the plane) |
| 11/6 | 3⁶ 4 | 126:1/3 134:1/3 157:1/6 247:1/6 367:1/6 456:1/3 2357:1/3 | yes (2357 ⊃ the seventh line 235) |
| 15/8 | 3⁵ 4 | 123:1/4 167:1/8 236:1/4 257:3/8 347:3/8 1456:1/2 | **no** |
| 15/8 | 3⁵ 4² | 136:1/4 157:1/8 256:3/8 345:3/8 467:1/4 1237:1/4 1247:1/4 | yes |
| 17/9 | 3⁶ 4 | 124:2/9 126:1/9 147:2/9 156:1/3 346:1/3 467:1/9 2357:5/9 | **no** |
| 17/9 | 3⁶ 4 | 124:1/3 125:1/9 156:1/9 167:1/3 236:1/3 256:1/9 3457:5/9 | **no** |
| 2 (not reached by the loop; checked directly) | K4: four classes, six co-edges = pairs of classes, seventh free | yes |
| 2 (checked directly) | 2-(6,3,2): ten blocks on six co-edges, seventh free | **no** |

The loop was stopped after 17/9 (each new pattern adds up to 5040 cuts; about a minute per step).
Reading.
- ROADMAP §2.2's "next shape at 11k/6" is confirmed, but it is not a non-Fano shape: every co-type
  contains a line of one plane. A co-type containing no line can be added to it with small mass
  (the MILP with "some lineless co-type allowed" also returns 11/6), so non-Fano *supports* exist
  for every N > 11/6; non-Fano *minimal* patterns start at **15/8**.
- In the 15/8 pattern the 4-set 1456 is a genuine core (no 3-subset of it meets all five triples)
  and carries mass 1/2; needed incidences 49/8 against 3N = 45/8.
- So §1.3 stands as stated (N < 11k/6), and for 11k/6 <= N < 15k/8 every minimal pattern is still
  Fano-supported.

## 17. The count across the window

### 17.1 Cores, 2-cores, and "two never suffice" [proved by hand]

Fix a pair-covering seven and for each point a minimal core A_x ⊆ I_x (the cores pairwise
intersect). ℓ_i = mass of points with i in the core; ℓ_i <= |K_i| = N - k, and a reply used only
through its request has ℓ_i <= T.
**Lemma.** (i) N < 2k: every core has size >= 3. (ii) A 2-core {i,j} forces K_i ∪ K_j = V
(B_i ∩ B_j = ∅), its points lie in K_i∩K_j, of mass N - 2k; the 2-cores form a star (a triangle of
2-cores needs N >= 3k); and ℓ_i + ℓ_j >= N + (mass of that 2-core).
**Theorem (two free replies never suffice).** Let T < 4k/5 and N > 5T - 2k. In every pair-covering
seven at least three co-edges have ℓ_i > T.
*Proof.* Suppose only ℓ_1, ℓ_2 exceed T. If there is no 2-core, Σℓ >= 3N gives 2(N-k) + 5T >= 3N.
A 2-core {i,j} needs ℓ_i + ℓ_j >= N, impossible with T + (N-k) or 2T unless {i,j} = {1,2}; then
its mass is at most N - 2k and Σℓ >= 3N - (N - 2k), so 2(N-k) + 5T >= 2N + 2k, i.e. T >= 4k/5. ∎
This extends 2.2 to all N and all patterns.

### 17.2 Slack by number of fully used replies [computed, float MILP; equals the count for N < 2k]

`slackq.py`: maximise s subject to: intersecting support, Σm = N, q co-edges of mass <= N - 1,
7 - q co-edges of mass <= 3/4 - s. In brackets the Fano count (q-3)(N - 7/4)/(7-q).

| N | q = 2 | q = 3 | q = 4 | q = 5 | q = 6 |
|---|---|---|---|---|---|
| 11/6 | -0.0167 | 0 | 0.0278 | 0.0833 | 0.25 |
| 1.9 | -0.03 | 0 | 0.05 | 0.15 | 0.45 |
| 2.0 | -0.05 | 0 | 0.0833 | 0.25 | 0.75 (= t: seventh reply not needed) |
| 2.1 | -0.07 | 0 | 0.1167 | 0.35 | 0.75 |
| 2.2 | -0.09 | 0 | 0.15 | **0.50** (0.45) | 0.75 |
| 2.25 | -0.10 | 0 | 0.1667 | **0.75** (0.50) | 0.75 |
| 2.3 | -0.11 | 0 | **0.2167** (0.1833) | 0.75 | 0.75 |
| 2.5 | -0.15 | **0.05** (0) | 0.75 | 0.75 | 0.75 |

So throughout 11k/6 <= N <= 9k/4: with q <= 4 the best pattern is a Fano blow-up and the slack is the
Fano count; in particular three fully used replies leave exactly 4·eps·k. Non-Fano patterns pay off
only with five or six fully used replies. (Three replies start to have real slack somewhere
between 2.3k and 2.5k — outside this window, in the range of Theorem D.)

### 17.3 Static value of anchor triples [computed, float MILP, grid 1/16]

`anchor_design.py`: three co-edges covering V, shape (p_12, p_13, p_23) = masses of the B_a∩B_b,
q_c = 1 - p_ac - p_bc; four non-adaptive requests; all kill-types allowed (no Fano assumption);
value D = least maximal load. It depends only on the shape; D <= t is sufficient for a win, and
exact when the union has at most k + T points. In the window p >= 3k - N > 3k/4.
Window shapes by value: (8,8,8)/16: 0.7500; (5,4,4): 0.7768; (8,8,7), (9,7,7): 0.7812;
(5,5,5): 0.7875; (5,5,4): 0.7917; (6,5,5): 0.8000; every other shape with p > 3/4 is above 0.80.
So at t = 3/4 + eps the anchored static region inside the window is the O(eps)-neighbourhood of the
Fano point (kernel N - 3k/2, unreachable for N > 5T - 2k by 2.2) plus the O(eps)-neighbourhood of
(1/4,1/4,1/4) at the top end N = 3k - T. No non-Fano anchor design fills the gap.
By-product for the spread side (p <= 3/4; cells that are exactly empty are treated as empty, so
shapes with zeros are optimistic, cf. PETAL K(iii)): D <= 3/4 for 40 shapes of the grid, including
(8,0,0), (7,0,0), (6,4,0), (5,4,0), (4,4,4), (4,4,0), (4,3,3), (3,3,3); dominant-pair shapes with a
second positive cell are above 3/4 from p_12 = 7/16 on ((7,1,0): 0.771, (8,1,0): 0.833).

## 18. Mechanism of the non-Fano endings, and the obstruction

**What REDTEAM §11.3 shows.** The lines at 2.1k–2.2k keep six replies and pay D at the last
request; D has mass 0.63 at budget 0.759. In the count of 17.2 that is q = 6: all six kept replies
are used in full. With q = 6 the ideal seventh request has mass (6k - 3N)^+ for Fano-type patterns
and 0 from N = 2k on (K4 or 2-(6,3,2): six co-edges cover all pairs), so there is room t for
waste; the non-Fano shape (three of the four triples of the quadrangle empty, the fourth heavy and
paid last) is simply the cheapest way to place the waste that the proportional rule produces. It
is available because that adversary is predictable (§13): every one of his dumps is "useful".
**Why this is not a mechanism against a real adversary.** By 17.1 she needs at least three replies
with core load above T, by 17.2 exactly three leave slack 4·eps·k and four leave N - 7k/4 + 3·eps·k,
while each unpredictable dump can waste omega = N - k - T: with replies 1, 2 free and every later
dump wasted, six fully used replies cost 4·omega > 3(N - 7k/4) + eps·k of slack as soon as
N > 5T - 2k — the same inequality as in Part I, now for all patterns (for N < 2k proved; for
2k <= N <= 9k/4 from the computed table). The balance lemma 14.1, the reading lemma 9.1 and the
spoiler 14.2 use only two co-edges and Theorem T / Theorem C, which by 17.3 remain the only
three-reply certificates here. So Barrier 2 is Barrier 1 with a larger omega: the adversary to beat
is spread and unpredictable in one parameter per reply; the non-Fano patterns enlarge the set of
endings once four or more replies are useful, not the set of ways to make a reply useful.
**What is different in this window (for whoever continues).**
- From N = 2k, a certificate needs no seventh reply at all if six are useful; from N ≈ 2.2k, five
  useful replies beat the Fano count. A proof that makes replies useful (Barrier 1) therefore gets
  cheaper here, not harder: with four useful replies the slack is N - 7k/4 >= k/12.
- Kernels move left: if he piles a set Y into every reply, the game is the game on N - |Y| points
  with the same k, T (§9.2 (K)); so a proof for all N' < N handles every piling adversary at N.
- Theorem P needs a pool of at most N - 3k/2 points, and omega <= N - 3k/2 always; Theorem D needs
  three replies with union >= 10k/3 - T, which a confined adversary on N < 3k - T never gives.
  Neither borders the window from inside: both ends (5T - 2k and 3k - T) are zero-slack points of
  three-reply certificates.

## 19. Exact remaining statement for Barrier 2

For T = (3/4 + eps)k and 5T - 2k < N < 3k - T (both barriers together): every T-covering family of
(N-k)-subsets of an N-set contains seven members covering all pairs. Necessary (17.1): three
members whose cores exceed T. Sufficient with slack: four members forming a waste-free quadrangle
(Theorem Q) or, from N = 2k, six members covering all pairs. Unproved in every case: the existence
of a third (and fourth) member in exact position against a request-dependent adversary.
**Next step.** The same as for Barrier 1 — the tilted-spread test — run also at N = 2.1k, 2.2k,
where the requester's extra endings (q = 5, 6) are available: if she beats the two-mode menu
there but not at 1.85k–1.9k, the proof should be organised around "many useful replies, non-Fano
ending" for N >= 2k and the window splits at 2k; if the outcome is the same on both sides, the two
barriers are one statement. Also worth doing exactly: finish the pattern enumeration between 17/9
and 9/4 with a dual certificate (finitely many dual vectors y, each excluding a set of co-types,
plus a SAT check that no intersecting family avoids all excluded sets) to replace the float MILP.
Not done in this box: that certificate; the enumeration beyond 17/9; any game computation.

Self-check (Part IV): table of §16 — pairwise intersections and all seven co-edge masses of the
15/8 pattern verified by hand (each co-edge 7/8); exact values from Fractions. 17.1 re-derived;
the 2-core bound uses |K_i∩K_j| = N - 2k when K_i ∪ K_j = V. 17.2 and 17.3 are float MILPs (HiGHS);
the q <= 4 columns agree with the hand count to four decimals.

=============================================================================================
# Part V — Barrier D+E: what the 1.8k strategy tree is, and why it does not extend (fifth time box)

Code: `compute/core/tree_read.py` (`py tree_read.py nodes | leaf BITS`), `tree_leaves.py` (all 64 leaves),
`fixlab.py` (`py fixlab.py t N...`, fixed-labelling MILP, < 1 min). Input: REDTEAM §14's tree
`compute/redteam/logs/adaptive_tree_full_T0.76_N1.8.json`. Types below are reply-types (set of replies
B_i containing the point), as in REDTEAM; co-type = complement.
**Outcome: CP is NOT proved in the window. No adversary win either.**
- §20 [computed]: the tree is Theorem T (triangle at replies 1–3, the four lines of §3 afterwards) with a
  flexible finish; reply 5 is a dummy at all 64 leaves; the Fano labelling is fixed by round 4.
- §21 [proved]: N = 1.8k at t = 0.76 is exactly N = 5T - 2k, where omega = 4·eps·k. The tree wins because
  a fixed labelling has slack 4·eps·k = omega there. It says nothing about the interior of the window.
- §22 [proved + computed]: an exact potential form of the game for a fixed labelling, and the
  **fixed-labelling theorem**: if the Fano labelling of the seven kept replies is determined by her
  requests (no discard), the "W-dumper" beats her whenever omega > 4·eps·k, for all 30 labellings.
- §23: candidate type-relative strategy, what is proved for it, and the exact point where it breaks
  (a covering condition on "absorbable sets" that fails for every portfolio of three co-edges).
- §24: exact remaining statement and next step.

## 20. Structure of the 1.8k tree [computed; float re-simulation of the exactly verified tree]

All 64 leaves: discard = reply 5; kept six 1,2,3,4,6,7 plus the eighth reply; the seven classes are
(kept reply-types) 134, 246, 237, 167 and, inside D, 1236, 1247, 3467 — masses 0.19–0.26 each.
Branch OU (bits of replies 2,3) uses 136, 246, 237, 147 | 1234, 1267, 3467 instead. Both are Fano blow-ups of class (T).
Rules, in type-relative form (cells of §3 after three replies: d, b, a = points in B_1, B_2, B_3 only;
e_3, e_2, e_1 = types 12, 13, 23; g = type 123; κ = points in no reply):
- R2. Request s of the unused points and T - s of B_1, with s chosen so that |K_1∩K_2| lands in
  [a* - small, a* + omega/2] for both bits (a* = N/2 - 5k/8 = 0.275; tree: s = 0.258, result 0.269 / 0.290).
- R3. Triangle-type request: nothing of K_1∩K_2, about half of each of d ∪ e_2-to-be, b ∪ e_1-to-be, and half of
  B_1∩B_2 (0.26, 0.26, 0.24). After reply 3 all seven cells are 0.22–0.28 and κ = 0.005 (bit O) or 0.026 (bit U).
- R4. One complete line of Theorem T: d ∪ e_1 ∪ g (branches UU, UO, OO; plus <= 0.02 of e_3, a, κ), or
  e_1 ∪ e_2 ∪ e_3 (branch OU). Which line goes first is the only place the labelling depends on the bits.
- R5. Dummy (reply 5 is never kept; the value does not depend on its bit).
- R6, R7, D. The remaining three lines of Theorem T, each requested as "all points of these three cells,
  refined by the replies since", slivers (points his dump kept out of an earlier reply) added as budget allows.
So the describable strategy is: **Theorem T, lines requested in an order chosen after reply 3, class
membership of dumped points re-decided at the end.** Static Theorem T alone does not suffice at the nodes:
node UU fails by 0.001 (loads 0.752, 0.744, 0.759, 0.744 plus κ = 0.026 against 4 x 0.76), node UO by 0.014
(loads 0.774 and 0.765). The difference is absorbed by *flexible points*: a point of class b that his
reply-4 dump put into K_4 has co-type {1,3,4} and may be finished by L_b or by L_e (pencil of b or of e_1);
similarly e_3-points in K_4 need L_a and one of L_e, L_b. κ-points that he dumps into a later line
through a vertex are discharged for free ("pile pays").
Consistent with REDTEAM §16 (coordinator's note): the tree's absolute masses are meaningless away from
tilt fraction 1/2; only the rules above are. I did not re-encode or re-test them (another agent's job, §17 there).

## 21. Why it works at 1.8k and not beyond [proved by hand; numbers computed]

**21.1 Six-plus-one identity.** For six kept co-edges let D = {x : I_x ∩ I_y = ∅ for some y} and
W6 := Σ_{x ∉ D} (|I_x| - 3) + Σ_{x ∈ D} (|I_x| - 2). Then |D| = 3N - 6(N-k) + W6, so the ending "six kept
replies, then request D" wins iff W6 <= 3(N - 7k/4) + eps·k = 3·omega + 4·eps·k. (Count Σ|I_x| = 6(N-k).)
**21.2** In a class-(T) ending the dumps of the four kept replies 3, 4, 6, 7 are the only source of W6
(replies 1, 2 are lines by definition). If all four are wasted, W6 = 4·omega > 3·omega + 4·eps·k iff
omega > 4·eps·k iff **N > 5T - 2k**. At t = 0.76 that is N > 1.80k: the tree sits exactly on the boundary.
From the exact margins: W6 = 0.160 - margin lies in 0.127–0.154, against 0.164 if the four dumps
(0.041 each at budget 0.759) were all wasted. The tilted spread wastes 78–94 % of them; 100 % would win.
**21.3 Consequence.** The 1.8k win is the statement "Theorem T with a third reply that wastes at most
~0.65·omega" at the one N where even a fully wasted third reply costs only the whole slack. It is not
evidence for the interior of the window. At N = 1.85k, bit U at reply 3 alone gives κ >= omega/2 =
0.045 > 4·eps·k = 0.04, so no class-(T) plan with reply 3 kept survives that bit [proved count]; this
matches the other agent's failure to build a tree at 1.85k (`adaptive_drv*_N1.85_m8.log`, "constructed": false).

## 22. The game for a fixed labelling: exact potential, and a theorem

Setting: seven replies in time order 1..7, a Fano labelling λ (which triples of replies are pencils).
For a point x with current co-type I and time τ call a pencil P *completable* if P ∩ [τ] ⊆ I, and put
e(x) = |I| - max over completable P of |I ∩ P|  (= ∞ if none).
**22.1 Lemma [proved].** e is non-decreasing in time for every x; at the end e(x) = |I_x| - 3 if I_x
contains a pencil and ∞ otherwise. Hence she wins with labelling λ iff Σ_x e(x) <= 4N - 7k at the end,
and then equality holds (2.1). The increment at step j depends only on x's own history:
c_in = 1 unless a completable pencil through j attains the max; c_out = (drop of the max when pencils
through j become non-completable). *Proof.* Adding j raises |I| by 1 and the max by at most 1; excluding
x from K_j only removes pencils from the max. ∎
Check against §9: step 3, triangle labelling: cost = |K_1∩K_2∩K_3| = W_tri; pencil labelling: cost =
|O∖K_3| now, and K_3∩(A∪B) has e = 1 from the next step on — W_pen. Step 4 through the vertex a (pencils
124, 135, 236, 347, 167, 257, 456): b, d, e_1, e_2 have c_in = 1; a∖κ, e_3, g must be requested (c_out >= 1);
κ is neutral — "pile pays".
**22.2 W-dumper.** W_j := {x : c_in(x) = 1 at step j}. Adversary rule: put the dump on W_j ∖ S_j first.
Then the cost of step j is at least min(omega, |W_j|), her own requests inside W_j included.
**22.3 Fixed-labelling theorem [principle proved by hand; the bound computed, float MILP].** For every one
of the 30 labellings, every final configuration (masses on co-types containing a pencil, every co-edge
of mass N - k) that satisfies |K_j ∩ W_j| >= min(omega, |W_j|) for j = 3..7 exists iff omega <= 4·eps·k.
`fixlab.py`: max of s such that the conditions hold with omega + s in place of omega is exactly
(4·eps·k - omega)/5 for all 30 planes at (t, N) = (0.76; 1.79, 1.8, 1.82, 1.85, 1.9, 1.95, 2.0) and
(0.751; 1.76, 1.8, 1.9); the alternative "all of W_j inside K_j" never helps. So:
*if her seven replies are kept in order and their labelling is a function of what she has requested,
the W-dumper wins for every N > 5T - 2k (Fano-type certificates; that is all certificates for N < 11k/6).*
This is the rigorous form of §6's heuristic "5·omega > 4·delta". The 1.8k tree is of this kind (labelling
fixed by round 4), which is why it lives at omega = 4·eps·k.
**22.4 Why requests reveal the labelling [proved count].** Under a labelling the points with c_out >= 1 at
step j ("needy") are the line L_j, mass about 3k/4; for two labellings that differ at step j the needy
sets differ by about k/2, and a request serving one costs about k/2 under the other, more than the whole
budget 4N - 7k <= k/2 for N <= 15k/8. So within one kept seven she cannot keep two labellings alive past
the request. The only freedom left is which replies are kept (discards).

## 23. Candidate general strategy, and where the proof breaks

**Strategy Σ (type-relative).** (1) Any K_1. (2) Request a* of K_1 and T - a* of B_1. (3) Triangle-type
request against a pair in hand: nothing of K_i∩K_j, a* of each private part, T - 2a* of the rest.
(4) If the reply satisfies 14.1 (all but eps·k of the dump outside K_i∪K_j), finish with Theorem T, lines in
any order, κ split by 22.1 (κ is neutral for a line through a vertex). (5) Otherwise keep the reply in the
portfolio and repeat (3) against other pairs.
What is proved for Σ: it wins against every adversary whose dump at some reply satisfies 14.1 for some
pair in position (Theorem T); against pool adversaries (Theorem P) and pure modes (9.2). Nothing else.
**Where it breaks — the covering condition.** For a request S and a reading R (a set of earlier replies
to be kept, with labelling) let U^R(S) be the set of unrequested points on which a dump costs nothing
under R. The useful part of a dump D is at most max_R |D ∩ U^R(S)|, and by 8.1 she needs useful dump
>= omega - 4·eps·k in total over the kept replies 3..7, plus whatever slack balance consumes.
- [proved] For three co-edges X_1, X_2, X_3 and a request that is triangle-type for all three pairs, the
  points lying in at least two of them have mass >= (3(N-k) - N)/2 = N - 3k/2 > omega, are all unrequested,
  and a dump there is in X_a∩X_b for one pair (waste, 9.1) and in a private part for the other two
  (fails 14.1 by its full mass). So U^R = points in at most one X_a, and he never needs to touch it.
  This is 12.3 and 14.2 as one statement: no portfolio of third-line readings covers V∖S.
- [proved, from 22.1, for clean blow-ups] From step 4 on, under a reading in which S is a line, U^R(S) is the
  unrequested part of that line plus the neutral points: mass about omega out of k + omega unrequested.
  Readings with disjoint U^R give him a dump with max_R |D∩U^R| about omega·omega/(k + omega); readings with a
  common U^R are avoided altogether.
- [heuristic] Flexible points (§20) relax balance, not waste, and he can deny them: after a line through d,
  a dump on class b gives the alternatives L_b or L_e, useless whenever L_e is the heavier line.
So Σ, and every strategy whose kept replies are "lines against a portfolio", gets useful dump o(omega)
per reply against a spread, request-dependent dump. The missing lemma is exactly:
**(COVER)** *there are m, a request rule and a family of readings such that for every adversary one
consistent reading R has Σ over its kept replies of |D_j ∩ U^R(S_j)| >= omega - 4·eps·k + (balance cost).*
Dead, with reasons: fixed labelling without discard (22.3); third-line portfolios (above); pile-or-pay (§12–14).

## 24. Exact remaining statement and next step

Unchanged in content from §19, now in potential form: for 5T - 2k < N < 3k - T find m and a requester
strategy such that for every adversary some seven of the m replies and some labelling λ have
Σ_x e_λ(x) <= 4N - 7k. Known necessary: the kept seven or their labelling must depend on his dumps
(22.3), i.e. discards are essential; a single kept seven cannot hedge between labellings (22.4).
Not known, in either direction: whether discards can make a dump useful beyond o(omega) (COVER).
**Next step.** Decide COVER for two stages exactly. By 22.1 the cost under each reading is linear in the
type masses, so "she requests S_3, he dumps, she requests S_4 (free to discard reply 3), he dumps; value =
min over readings of the cost" is a finite max-min over at most 16 types and a few dozen readings. If
the value stays >= 2·omega - o(omega), the same structure repeats at every later stage and the bounded-m game
is lost at first order; CP must then be attacked as a family statement (the forbidden-intersection route
of §15). If it drops to (2 - c)·omega with c > 0 independent of eps, that request pair is the mechanism.
Not done: that computation; any test of the type-relative rules of §20; non-Fano certificates for
N >= 11k/6 in 22.3 (the MILP allows only co-types containing a pencil).

Self-check (Part V): §20 from a float replay of the exactly verified tree (64/64 leaves, discard 5);
21.1 is a count; 22.1 re-derived and checked against W_tri, W_pen and the step-4 table by hand; 22.3 is a
relaxation in her favour (it ignores the T-budget of her requests and where exactly inside W_j he dumps), so
infeasibility is on the safe side, but it is floating point, not a certificate. The "about k/2" in 22.4
and the omega·omega/(k + omega) in §23 are first-order counts, not optimised bounds.

=============================================================================================
# Part VI — the two-stage game (replies 3 and 4, discard allowed): no drop below 2·omega (sixth time box)

Code (all in `compute/core`, logs in `compute/core/logs`): `twostage.py` (the game, search), `twostage_cert.py`
(MILP lower bound with LP-dual cuts), `twostage_menu.py` (which of his dumps are needed), `twostage_test.py`
(optimiser check against a predictable opponent). Units k = 1.
**Outcome.** At every point tested the value of the two-stage game is exactly the baseline: replies 3 and 4
together give her **nothing** (cost 2.00·omega; the question of §24 is answered "it does not drop").
Status of that sentence: his side holds with a small explicit menu of dumps (a subset of his legal replies);
her side is a heuristic search, validated, plus a MILP certificate for the triangle-type reply-3 request at
five of the six points. It is not certified for all reply-3 requests at once (that MILP did not close).
No request pair to extract. No adversary win for the real game is claimed (§28).

## 25. The game and its value [definitions; inequalities proved by hand]

Position: the co-type masses of the replies so far. After replies 1, 2: O = K_1∩K_2 (mass o), A, B (N-k-o each),
g (2k-N+o). Reply 3: she requests S_3 (mass T over the 4 types), he adds D_3 (mass omega on unrequested points);
reply 4 the same over the 8 types. A *reading* R is a set of at least two of the replies with a Fano
labelling (which triples are pencils; 19 readings for four replies). For a reading put
    need_R = min Σ_f u_f : every point's final co-type contains a pencil, each of the 7 - |R| future lines has
             mass <= T + u_f, 0 <= u_f <= omega                       (an LP in the type masses).
- need_R <= 0 is an outright win: the future lines can be requested as they stand (as in Theorems T, Q).
- need_R is optimistic for her: it assumes every later reply adds up to omega exactly where she wants it.
- [proved] need_R >= (3 - |R|)·omega - 4·eps·k + W_R, W_R = total off-line mass of the kept co-edges (count of 8.1:
  Σ over the seven lines of (|L_i| - T) = 3·omega - 4·eps·k, a kept line has |L_i| <= T + omega - waste_i).
  So a pair has need >= base := omega - 4·eps·k, with equality for the right o (o = 0.305, 0.33, 0.38, 0.43 at
  N = 1.85, 1.9, 2.0, 2.1); a reading with r extra replies is no better than base iff those replies waste r·omega
  in the balance-inclusive sense. "Cost of replies 3, 4 in units of omega" = 2 - (base - value)/omega.
- Value: V = min_{S_3} max_{D_3} min_{S_4} max_{D_4} min_R need_R; "discard" is the min over R (any kept set).
- [proved, 9.1 in this form] One stage: for 3·omega <= o <= (N-k)/2 the value after reply 3 is >= base.
Caveat: only Fano-type certificates (co-types containing a pencil). That is every certificate for N < 11k/6;
for N >= 11k/6 it is every certificate that 17.2 found optimal with at most four fully used replies
[float MILP there], not a proved restriction. Of the points below only N = 1.82k is inside the proved range.

## 26. Results

**26.1 Search [computed, float LPs; her side heuristic].** His menu at each reply: the proportional dump, all of
omega on one type (spill by co-degree), and half-half on two types (1 + 8 + 28 = 37 dumps at reply 4; quarter
splits and thirds on three types added for the final check of her best request). Her side: 27–51 reply-3 requests per row (triangle family nothing-of-O with a* - j·omega/8 in each
private part, pencil-type, mixed, random), and for each of his reply-3 dumps a reply-4 optimiser (LP-guided
line requests for every reading, unions of whole types, compass search from 7 starts). 4–6 million LPs, 5–10 min per row.

| t | N | o | omega | base | need of the pair | value after reply 4 | cost of replies 3, 4 |
|---|---|---|---|---|---|---|---|
| 0.76 | 1.82 | 0.29 | 0.06 | 0.02 | 0.02 | 0.0200 | 2.00·omega |
| 0.76 | 1.85 | 0.305 | 0.09 | 0.05 | 0.05 | 0.0500 | 2.00·omega |
| 0.76 | 1.90 | 0.33 | 0.14 | 0.10 | 0.10 | 0.1000 | 2.00·omega |
| 0.76 | 2.00 | 0.38 | 0.24 | 0.20 | 0.20 | 0.2000 | 2.00·omega |
| 0.76 | 2.10 | 0.43 | 0.34 | 0.30 | 0.30 | 0.3000 | 2.00·omega |
| 0.755 | 1.90 | 0.3275 | 0.145 | 0.125 | 0.125 | 0.1250 | 2.00·omega |
| 0.76 | 1.90 | 0.26 (pair too small) | 0.14 | 0.10 | 0.24 | 0.1000 | 2.00·omega |
| 0.76 | 1.90 | 0.40 (pencil kernel) | 0.14 | 0.10 | 0.12 | 0.1150 | 2.11·omega |

The value equals base to 1e-13 in the first seven rows: not "close to", equal. With an unbalanced pair she
repairs the pair (row 7) and gains nothing beyond it. For every reply-3 request tried he had a
reply-3 dump after which no reply-4 request found brought any reading below base against the menu.
**26.2 Optimiser check [computed].** Against the proportional dump at both replies (predictable, §13) the
same search reaches need 0.0000 at N = 1.9 (after reply 3 already 0.0019): `twostage_test.py`. So the search does
find gains when they exist; and "proportional" alone is not his answer.
**26.3 Which dumps he needs [computed, N = 1.9].** `twostage_menu.py`, reply-4 menu restricted to
(a) proportional only: value 0.0017 (he loses the stage); (b) one-type dumps only: value = base;
(c) one-type dumps on types lying in at least two of K_1, K_2, K_3 only: value = base.
So the reply-4 spoiler is always "all of omega on one cell of co-degree >= 2 among the earlier replies", which
cell depending on her request; at reply 3 it is 9.1's rule (O if she leaves omega of it, else the private parts) or,
for some requests, the proportional dump.
**26.4 Certificate [computed: float MILP (HiGHS, status Optimal), cuts valid by weak duality].**
`twostage_cert.py`: his menu cut down to piecewise-linear options (proportional; all on J; all of J then J2), her
S_4 for every reply-3 option as continuous variables, each need_R replaced by LP-dual lower bounds (valid for
every dual vector, so the MILP optimum is a lower bound for her true optimum against the menu, hence for V).
With S_3 = the triangle-type request (nothing of O, a* of each private part, the rest of g):
MILP optimum = base at (t, N) = (0.76; 1.82, 1.85, 1.90, 2.00) and (0.755; 1.90) — 15–90 s each.
Not certified: (i) all S_3 simultaneously — MILP lower bound still 0 after 2 x 380 s at N = 1.82 and 1.90;
(ii) N = 2.10 (its S_3 is not of that form; MILP bound 0.213 against 0.300 at the same point: an unresolved
slack in my encoding of dump availability, which can only favour her). The earlier runs with that slack
that reported base are unaffected for the same reason.

## 27. Reading

- The fork of §24 is decided on the "no mechanism" side: there is no pair of requests (S_3, S_4) that makes
  him pay anything, discards included. The numbers are also sharper than §23's o(omega): the saving is 0.
- Type-relative form of his two-stage rule, as far as the runs determine it: *answer a request by putting the
  whole dump on one cell of points already lying in two or more kept co-edges and not requested; choose the cell
  so that no reading through the new reply beats the best reading without it.* The existence of such a cell at
  every position is the statement
  **(SPOIL)** for every position and every request there is a dump after which every reading containing the new
  reply has need >= the least need of a reading not containing it.
  Proved for reply 3 under 9.1's hypothesis 3·omega <= o <= (N-k)/2 (computed outside it); computed for reply 4 (§26); open beyond. It is false for menus that are fixed in
  advance (pool, pure high, pure low, proportional: Theorem P, 9.2, 26.2) — the cell must depend on the request.
- [heuristic] If SPOIL holds at every position, the first-order game with Fano certificates is an adversary
  win for every number of requests as soon as omega > 4·eps·k: need never falls below base > 0.
- This is NOT a counterexample to CP and not evidence against it. The spoiler at reply 4 is chosen knowing
  K_1, K_2, K_3. In the family form (1.2) the reply to S_4 is one fixed set, and she may meet it before, after or
  without K_3: the same K(S_4) has to spoil against every triple she can assemble. The game gives him the last
  word at every step; a family has no last word.

## 28. Exact remaining statement and next step

Remaining statement: §24's, with one clause added — a proof must use that the reply to a request does not
depend on the history (family form), or certificates outside the Fano type for N >= 11k/6; the adaptive game
with Fano readings shows no gain through four replies.
**Next step (one computation, same code).** The consistent two-stage game: she holds K_1, K_2 and asks S_3,
S_3' and S_4; he answers each request once (D_4 may not depend on which of K_3, K_3' she keeps). 16 types
before reply 4, readings through K_3 or K_3'. If the value is still base, also allow two requests at stage 4.
A drop there is the mechanism (and is exactly the dilution idea of §10 with balance-inclusive accounting);
no drop for every finite portfolio would show that even consistency does not help at first order and would
leave only the density route of §15.
Not done: that computation; SPOIL at reply 5; an exact (rational) version of the 26.4 certificates; the
all-S_3 certificate; N = 2.1 certificate; non-Fano readings.

Self-check (Part VI): need LP checked on known cases (Theorem T position: need 0; dump into O, A or A∪B at a
balanced pair: need = base; pair need as a function of o reproduces the count 3N - 7T). LP duals reproduce the
LP values on 117 random positions before use as cuts. Two encoding errors in the certificate MILP were found
and fixed during the runs (dump options droppable on both sides of a threshold; readings with a dead type
given a finite bound) — both made her stronger, so bounds reported as equal to base were already valid.
All LP/MILP work is floating point (HiGHS); nothing is an exact rational certificate.

=============================================================================================
# Part VII — "consistency": what it is, what it is not, and one step deeper (seventh time box)

Code: `compute/core/deep.py` (five replies), logs `compute/core/logs/deep_*.log`.
**Outcome.** (1) There is no separate "consistent game". The exploration game in which every reply is kept
and any seven may be used is *exactly* the family statement, cut off after m requests (29.2, proved). So Part VI
already was the consistent game at depth 2, and the last bullet of §27 and the "next step" of §28 were wrong in
suggesting that a family constrains him more than that game does. (2) One step deeper (K_3, K_3', K_4 all kept,
he answers each request once): no drop found, value = base at all four points — three replies cost 3·omega.
[float; her side heuristic; not certified]. (3) None of the earlier adversary wins relies on inconsistent
answers; all of them rely on a restriction on her (§31).

## 29. The model [proved by hand]

**29.1 Deterministic replies are WLOG.** Let H be k-uniform on V with τ(H) > T and property (7,2). In co-edge
form: every T-set lies in a co-edge of H, and no seven co-edges cover all pairs. Choose for every T-set S one
co-edge F(S) ⊇ S of H. The image of F is a subfamily of H, still T-covering, still (7,2). So a counterexample
exists iff a reply MAP F exists whose image has no seven members covering all pairs.
**29.2 Proposition.** Let G_m be the game: m rounds; she names a T-set (depending on everything seen), he names a
co-edge containing it (depending on everything seen); she wins iff some seven of the m replies cover all pairs.
Then for fixed (k, T, N):  CP holds  ⟺  she wins G_m for m = C(N,T)  ⟺  she wins G_m for some m.
*Proof.* If CP holds she asks every T-set once, in any order; the replies form a T-covering family, which has a
good seven. If she wins some G_m and H is T-covering, let him answer from H; her seven lie in H. ∎
Consequences.
- An adversary strategy that survives every m gives a family (the replies along "ask everything"). History-
  dependent answers are therefore legitimate: along one play with distinct requests a history-dependent adversary
  and a fixed map F cannot be told apart, and repeating a request can only add members.
- "Branches" of her strategy tree under DIFFERENT answers belong to different families; edges from two such
  branches never coexist. What coexists is everything she asks in one play — extra requests, i.e. depth.
  So "her seven may come from different branches" is correct only as "she may ask more and keep everything",
  which is G_m with larger m. (This corrects the premise of the task as posed to me, and my own §27–§28.)
- Valid one-sided relaxations: (a) truncating to depth m handicaps HER — her win at any depth proves the first-
  order statement, his holding at depth m proves nothing beyond m; (b) a non-adaptive portfolio (all requests
  fixed in advance) handicaps her further. There is no computable relaxation in which his holding is conclusive
  short of all depths.
- The first-order (mass) model and the Fano restriction are as in §25; complete only for N < 11k/6.

## 30. Depth 3 [computed, float; her side heuristic at two of three levels]

Game: after K_1, K_2 she asks S_3, then S_3' (knowing K_3), then S_4 (knowing K_3, K_3'); he answers each once;
value = min over all readings among the five replies (70 readings: 10 pairs, 20 triples, 25 quadruples, 15
quintuples). This is the game I called "consistent two-stage" in §28.
Tested slice: S_3 = the triangle-type request (nothing of O, a* of each private part, rest of g); his D_3 = all of
omega on O; her S_3' over 16 candidates (LP-optimal future lines of every reading among K_1, K_2, K_3, and
unions of whole cells by co-degree); his D_3' from the piecewise-linear menu, at most four tried; her S_4 over
16 cells by candidate lines of all 19 readings plus compass search; his D_4 from a numeric priority-fill menu
(proportional; all on one cell with spill by co-degree; half-half on two cells of co-degree >= 2).

| t | N | o | omega | base | value found after three replies | cost of the three replies |
|---|---|---|---|---|---|---|
| 0.76 | 1.82 | 0.29 | 0.06 | 0.02 | 0.0200 | 3.00·omega |
| 0.76 | 1.85 | 0.305 | 0.09 | 0.05 | 0.0500 | 3.00·omega |
| 0.76 | 1.90 | 0.33 | 0.14 | 0.10 | 0.1000 | 3.00·omega |
| 0.755 | 1.90 | 0.3275 | 0.145 | 0.125 | 0.1250 | 3.00·omega |

(N = 1.82k is the only point with N < 11k/6 = 1.833k; 1.85k is just above it.) 3–4 minutes each.
In all 64 (S_3', position) cases he had a second dump after which neither the four-reply position nor any last
request found went below base; in 57 of them the dump that sufficed starts on a cell of co-degree >= 2, in 28 on
K_1∩K_2∩K_3 (the pile again). The menu order favoured those cells, so this shows sufficiency, not necessity.
**Not certified.** The exact last-level MILP (`deep.last_level`, same construction as 26.4) did not close: against
the piecewise-linear menu she parks the free mass of the two highest cells exactly at omega, where the two-cell
fill stops being available, and "gains" 0.03–0.09; the true adversary answers with that fill (or a three-cell
one just beyond the threshold), which gave 0.100 = base at her point in the instrumented run. So the linear menu
is too weak at depth 3, and the depth-3 numbers rest on the heuristic search alone. Weak points: one S_3, one D_3,
16 second requests.

## 31. Do the earlier adversary wins rely on inconsistent answers? No — on restrictions of her.

- **(10,8), m = 8, 9, 10 (FAST Part 3).** In 393 of 410 terminal positions the arena has 18 = k + T points, where
  the reply to an 8-set is its complement: a function of the request, as consistent as possible. The family behind
  it is the complete K_18^(10), which is not (7,2) (seven 8-sets cover all pairs of 18 points — FAST's own side
  check). So that win is an artefact of what the requester of that engine may do (anchored certificates, J kept
  replies), not of inconsistency and not a family obstruction. [read from FAST; not re-run; the 17 terminals with
  19–20 points not examined.]
- **Fixed-labelling W-dumper (22.3).** History- and labelling-dependent, which 29.2 allows. Its win is entirely
  the restriction "one seven, labelling determined by her requests, no discard". No claim without it.
- **Part VI and §30.** History-aware, legitimate; evidence for depths 2 and 3 only.
- General rule: an adversary win at bounded depth is never evidence of a family. Only a strategy for all m is.

## 32. Where this leaves the statement

By 29.2 the fork is now clean. Either
(a) SPOIL (§27) fails at some depth — then at that position she has a request against which every dump leaves a
    reading below base; or
(b) SPOIL holds at every position — then the first-order statement itself fails for 5T - 2k < N < 11k/6 (need never
    drops below base > 0), and CP can hold only through effects outside the first-order model (integrality; or,
    for N >= 11k/6, certificates I excluded). I have evidence for (b) only up to depth 3, and none for (a).
[heuristic] What (b) would need is an invariant. The runs suggest "there is always a cell of points lying in at
least two kept co-edges, with unrequested mass >= omega, whose filling keeps every reading at base"; the known wins
against fixed rules (pool, pure high) are exactly the cases where she exhausts that cell. I did not find the invariant.
**Next step.** A falsification test of SPOIL that needs no game search: sample positions with 5 and 6 replies
produced by his own rule, and for each solve the one-step problem "her best request against all his priority
fills" (one level, so the search of §26 applies and the numbers are reliable). A single position with value < base
settles (a) and gives the request rule. If several hundred positions give none, take SPOIL as the working
conjecture and move the proof effort to its invariant, and to whether first-order failure is compatible with CP.
Not done: that test; certification of §30; other S_3 or D_3 at depth 3; N in (5T - 2k, 11k/6) other than 1.82k.

Self-check (Part VII): 29.1–29.2 are two-line arguments, re-read once; they use only finiteness of V. §30's
engine is §26's with five replies (same LP, 70 readings); the depth-2 positions inside it reproduce base. The
statement about the MILP's failure is from one instrumented run (N = 1.9).

## 33. HANDOVER (self-contained)

**(1) Statement.** Units k = 1 (masses are fractions of k; "first order" = k → ∞ with masses fixed). t = T/k = 3/4 + eps,
V a ground set of mass N, c = N - 1, omega = N - 1 - t, delta = N - 7/4. A *co-edge* is the complement in V of an
edge: a set of mass c. A family 𝒞 of co-edges is *T-covering* if every set of mass t lies in a member
(⟺ τ(H) > T for the edge family H confined to V).
**(CP)** For 5t - 2 < N < 3 - t: every T-covering 𝒞 has seven members K_1..K_7 covering all pairs of V, i.e. the
co-types I_x = {i : x ∈ K_i} are nonempty and pairwise intersecting (1.1). For N < 11/6 this is equivalent to: a
labelling of the seven by the lines of a Fano plane in which every I_x contains a pencil (three concurrent lines)
(1.3, 8.3 [float MILP]). Game form, equivalent for every finite k (29.2): she names sets of mass t, he answers
with a co-edge containing each, all replies are kept, she wins when seven of them cover all pairs. Each reply is
S ∪ D, D the *dump*, mass omega (when |S| = t). Proved outside the window: N <= 3t - 1/2 (TWIN 16.A) and, by a count,
omega <= 4·eps is the regime where a fixed plan suffices (21.2); N >= 3 - t is PETAL's side.

**(2) Proved tools** (by hand unless tagged).
- Slack count (2.1–2.3, 8.1, 17.1): Σ_x (|I_x| - 3) = 4·delta for any seven co-edges; lines L_i ⊆ K_i of a certificate
  satisfy Σ(|L_i| - t) = 3·omega - 4·eps, so the dumps must supply that much on-line mass; two replies are free, hence
  the others must supply omega - 4·eps =: base. Two fully used replies never suffice; three leave slack 4·eps.
- Theorem T (§3): three co-edges with pair intersections a, b, d <= (t + N - 2)/2, a + b + d >= (3N - 3 - t)/2 and empty
  triple intersection are finished by four fixed requests. Zero-slack point a = b = d = N/2 - 5/8.
- Theorem Q (§4): four co-edges forming a quadrangle are finished by three fixed requests iff W := u_3 + 2u_4 + s_1
  <= delta + 3·eps and the three matching loads are <= t.
- Pool theorem P (§5): if his dumps stay in a known set Z, omega <= |Z| <= N - 3/2, she wins in seven requests.
- Reading lemma 9.1 / balance 14.1: against a fixed pair the third reply can always be made to waste omega; a triangle
  closes iff all but eps of the dump lies outside K_1 ∪ K_2. Mode lemma 9.2: pure high, pure low, pure pile lose.
- Potential form (22.1): for a fixed labelling, e(x) = |I_x| - max over completable pencils of |I_x ∩ P| is monotone,
  and she wins iff Σ_x e(x) <= 4·delta at the end.
- Fixed-labelling theorem (22.3, bound by float MILP over all 30 labellings): if the seven are kept in order and the
  labelling follows from her requests, the W-dumper wins whenever omega > 4·eps.
- need_R (§25): LP giving the on-line dump still required if she keeps the set R; need_R >= (3 - |R|)·omega - 4·eps + waste.

**(3) Computed** (float LP/MILP, Fano-type certificates only; complete for N < 11/6).
- Tilted spread (half proportional, one free bit per reply): beaten by an exact tree at t = 0.76, N = 1.80 only, which
  is N = 5t - 2 (REDTEAM §14; CORE §20–21). Every fixed bit schedule is beaten for N = 1.78..2.2 (REDTEAM §13.2).
- Depth 2 (replies 3, 4, any kept set): value = base exactly at t = 0.76, N = 1.82, 1.85, 1.9, 2.0, 2.1 and t = 0.755,
  N = 1.9; MILP-certified for the triangle-type third request at all but N = 2.1 (§26).
- Depth 3: value = base at N = 1.82, 1.85, 1.9 (t = 0.76) and 1.9 (t = 0.755); heuristic, narrow slice (§30).
- His sufficient rule so far: the whole dump on one unrequested cell of points lying in >= 2 kept co-edges (26.3).
  Conjecture SPOIL (§27): such a dump exists at every position. If true for all depths, the first-order statement fails.

**(4) A non-game route [heuristic; nothing below is proved].** Work with the reply map F(S) = S ∪ D(S) and ask what
D must look like, rather than how to beat it. Three structural facts are already forced on a (7,2) family:
(i) D(S) is never "predictable": if D(S) ⊆ Z for a fixed Z of mass <= N - 3/2 on enough requests, Theorem P wins;
(ii) for every pair of members (K, K') and every S that is triangle-type for it, D(S) must put >= omega - O(eps) of
its mass inside K ∪ K' in the balance-inclusive sense (else Theorem T closes; 14.1);
(iii) exact triangles (Theorem T's point) must not occur among members at all.
The stability statement to aim for: *a T-covering family with no good seven is, up to O(eps) mass, a pool family —
there is Y with |Y| ≈ omega contained in almost every member* (the complete family on V∖Y is the model, and it is beaten
exactly when t > 3/4). This is the analogue, on this side, of a "few arenas" structure theorem.
**First lemma to try (kernel lemma).** Fix members K_1, K_2 with |K_1∩K_2| = o in the pair window. For every
triangle-type S (S ∩ K_1 ∩ K_2 = ∅, a* of each private part) (ii) forces |D(S) ∩ (K_1 ∪ K_2)| >= omega - eps, and 9.1's
count splits this into a part in O = K_1∩K_2 and a part in the private parts. Claim to prove or refute: *the sets
D(S) ∩ O, over all such S, have a common core of mass >= (1 - o(1))·omega·λ, where λ is the average fraction of the
dump landing in O.* Method: two triangle-type requests S, S' with S ∪ S' avoiding the private-part mass that D(S), D(S')
used give a quadruple (K_1, K_2, F(S), F(S')); if D(S) ∩ D(S') ∩ O is small, Theorem Q's waste W = u_3 + 2u_4 + s_1 drops
below delta + 3·eps and she wins — so large pairwise overlap of the O-parts is forced, and a Δ-system / Kleitman-type
step turns pairwise overlap into a common core. Then (i) finishes when λ is near 1; the residual case (dumps mostly in
the private parts) is the pencil reading and should be treated symmetrically with the kernel N - 3/2.
Cheap numerical pre-check: in `twostage.py` positions, compute need for the reading (K_1, K_2, K_3, K_3') with two
triangle-type requests and D_3, D_3' ⊆ O disjoint versus nested; the lemma predicts need < base for disjoint.

=============================================================================================
# Part VIII — the kernel lemma tested; what a structural proof can and cannot use (eighth time box)

Code: `compute/core8/` — `lpx.py` (LP helper on highspy; pulp 4.x changed its API), `kernel_precheck.py`, `tri_class.py`,
`pool_class.py`, `scale_rule.py`, `sym_check.py`. All LPs float (HiGHS) unless tagged exact. Units k = 1.
**Outcome. CP is NOT proved. The kernel lemma of §33(4) is dead as a route** — not because a T-covering family
without a core was built (that would disprove CP), but because (a) its method is false at the first step, (b) what the
zero-slack certificates really force on the triangle-type class is satisfied by coreless rules, and (c) even a
perfect core on that class is worth exactly nothing. New and proved: Theorem S (no family that is symmetric under
any fixed finite partition is a counterexample), the pencil-through-one-member lemma, the triple-overlap bound, and a
set form of Theorem Q (Q'). CP is reduced one-way to a four-member extremal statement (Σ, §38), which is open.

## 34. The pre-check of §33 [computed float; exact for each reading]

Method. For a fixed reading R the need LP of §25 has right-hand sides linear in her request variables, so
"min over all her requests of need_R" is ONE joint LP; the minimum over the readings is then exact for the model
(no search on her side). Position: pair K_1, K_2 with the balanced o of §26; requests avoid O; dumps lie in O.

**34.1 Two triangle-type requests, as the lemma states them** (a* of A, a* of B, t - 2a* of g, nothing of O; mutual
position free), dumps D, D' ⊆ O with |D ∩ D'| = θ. `kernel_precheck.py t N o sym`:

| t, N, o | base | θ = 0 (disjoint) | ω/4 | ω/2 | 3ω/4 | ω (nested) |
|---|---|---|---|---|---|---|
| 0.76, 1.90, 0.33 | 0.100 | 0.100 | 0.100 | 0.100 | 0.100 | 0.100 |
| 0.76, 1.85, 0.305 | 0.050 | 0.050 | 0.050 | 0.050 | 0.050 | 0.050 |
| 0.76, 1.82, 0.29 | 0.020 | 0.020 | 0.020 | 0.020 | 0.020 | 0.020 |

**The prediction "need < base for disjoint dumps" is false:** need = base for every overlap; the best reading is
the bare pair. Reason [proved by hand]: in the quadruple (K_1, K_2, K_3, K_4) the points of D∖D', D'∖D, D∩D' have
co-types 123, 124, 1234, so u_3 + 2u_4 gets |D| + |D'| = 2ω from O **whatever the overlap**. Theorem Q's W does not
see the overlap at all. The first step of the lemma's method ("small overlap ⟹ W drops") is wrong.

**34.2 The same with the request shape free** (only S ∩ O = ∅), `kernel_precheck.py t N o`: value 0 at θ = 0 AND at
θ = ω at all three points; in between 0.030 (N = 1.9, θ = ω/2), 0.005 (N = 1.85), 0 (N = 1.82). Here she knows θ when she
chooses the shapes (max over θ of min over requests), so these are lower bounds for a rule that picks θ after seeing
S'. Both extremes are wins, and neither uses K_2: disjoint dumps give a Theorem-T triangle (K_1, K_3, K_4) with
|S ∩ A| = a* - ω; nested dumps give a pencil (35.1). Shape dependence, q = 2, she chooses the overlaps (`tri_class.py`,
a* - shift in each private part): N = 1.9: need 0.100, 0.100, 0.060, 0.013, 0.020 at shift 0, ω/4, ω/2, 3ω/4, ω;
N = 1.85: 0.050, 0.050, 0.027, 0, 0. So everything depends on the SHAPE of the request, which is exactly the parameter
the anti-plan adversary (9.3) switches on.

**34.3 Three or more triangle-type requests, dumps in O, she chooses all overlaps** (`tri_class.py`, q = 3, 4):
need 0 at all three points, by a Theorem-T triangle among the three class members, K_1 and K_2 discarded. With all
pairwise overlaps forced >= θ the value is 0 up to θ = 0.5ω (N = 1.9) / 0.7ω (N = 1.85) and reaches base at 0.9ω / ω;
with a common core of mass >= θ forced it is 0 up to 0.2ω / 0.4ω and reaches base at 0.9ω / ω. So the lemma's
*conclusion* (large overlap) does appear in the optimistic need model, but through triples and Theorem T, not through
pairs and Theorem Q — and "need < base" is not a contradiction for a family; only need = 0 is (next section).

## 35. What is forced, what is not

**35.1 Pencil through one member [proved by hand; = Theorem C in family form].** Let K be a member, B = V∖K (mass 1),
B = P ⊔ P' with |P| = |P'| = 1/2, A_0 ⊆ K with |A_0| = t - 1/2, Y ⊆ K∖A_0 with |Y| = ω. If A_0 ∪ P ∪ Y and A_0 ∪ P' ∪ Y
are members, she wins: the three members pairwise meet in κ = A_0 ∪ Y, |κ| = N - 3/2, their petals K∖κ, P, P' have
mass 1/2 and partition V∖κ; halve each petal, the four transversal lines have mass 3/4 <= t; 1.3(ii). ∎
So two requests of that shape with THE SAME dump inside K are fatal for him. A common core is not something he is
forced into and she must then exploit: it is something he must avoid on this shape.

**35.2 Triple-overlap bound [proved by hand].** In Theorem T the four loads sum to 3N - 3c + |κ| = 3 + |κ|, so the
certificate needs |K_1 ∩ K_2 ∩ K_3| <= 4·eps (and then balance). Hence in a (7,2) family: any three members whose
pairwise intersections are within eps/2 of a* have common part > 4·eps or fail balance. For three requests avoiding a
set O with dumps inside O this reads: s_ij + θ_ij = a* for all pairs and S_1∩S_2∩S_3 = ∅ ⟹ |D_1∩D_2∩D_3| > 4·eps (★).
This is everything the zero-slack certificates say about the class.

**35.3 (★) does not give a core [proved by hand; threshold confirmed by LP].** Let O' ⊆ O, ω < |O'| < 3ω/2 - 2·eps, and
let the dumps of the class be arbitrary ω-subsets of O'. Any three of them share >= 3ω - 2|O'| > 4·eps, so no triangle
exists among class members; with K_1 (or K_2) a triangle needs |K_1∩K_3| = a* + ω > a* + eps/2 and a pencil needs
a* + ω = N - 3/2, i.e. ω = eps. The dumps have no common core at all and pairwise overlaps as low as 2ω - |O'| ≈ ω/2.
`pool_class.py` (she picks any ω-subsets of O' for q = 3, 4, 5 strictly triangle-type requests; |O'| = σω):
no static certificate (need > 0) for σ = 1.2 at N = 1.9 (need = base) and 1.85 (need 0.014); static win at N = 1.82,
where 1.2ω > 3ω/2 - 2·eps = 1.167ω — the hand threshold. So the kernel lemma's statement cannot be derived from
certificates among K_1, K_2 and replies to triangle-type requests. (This is a rule on one class of requests, not a
family; no counterexample to CP is claimed.)

**35.4 A perfect core on the class is worth nothing [computed float].** σ = 1 (every triangle-type request gets the
same Y ⊆ O): for q = 3, 4, 5 and all readings among K_1, K_2 and the q replies, need = base exactly at N = 1.82, 1.85,
1.9, and the static LP (no future dump) is infeasible. To use Y she needs requests of ANOTHER shape (35.1: t - 1/2 in
K_1, 1/2 outside; `pool_class.py ... free`: need 0), or requests meeting O (Theorem P: S ⊇ Z∖Z''). About those the
lemma is silent, and no certificate links the two classes with first-order slack: the links are 35.1 and Theorem T,
both of tolerance O(eps). **Transfer gap:** "core on triangle-type requests" ⇏ "pool rule on the requests P needs".
The anti-plan adversary is by definition shape-dependent, so this is not a technicality: it is the adversary.

**35.5 Coreless but regular rules die [computed float].** `scale_rule.py`: D(S) = ψ(S) for a measure-scaling map
ψ: V∖O → O' (so D(S)∩D(S') = ψ(S∩S'), never disjoint, never nested, no core). q = 2: need 0.011 < base; q = 3, 4: need 0
at N = 1.9 (triangle among three class members; she pre-compensates). §13 again: predictable ⟹ free.

**Verdict on the route.** Dead: "kernel lemma ⟹ pool ⟹ Theorem P". (i) The two-request step is false (34.1).
(ii) The correct three-request statement is (★), which coreless small-pool rules satisfy (35.3). (iii) A core on one
shape class does not transfer (35.4). What survives: pool-like behaviour on a *shape* is refuted directly by 35.1 or
Theorem T, so a (7,2) family must have, on every shape class and relative to every pair of members, dumps that are
neither (nearly) equal where 35.1 applies nor (nearly) triple-disjoint where (★) applies. These are measure-zero
conditions on a map and can be dodged (for 35.1 the bad pairs form a perfect matching on requests). A structural
proof therefore needs a certificate with first-order slack, i.e. at least four members used in full (2.3).

## 36. Theorem S: symmetric families lose [proved by hand; computed exact on small cases]

**Theorem S.** Let V = V_1 ⊔ ... ⊔ V_m (masses v_j, m fixed) and let 𝒞 be a T-covering family of co-edges that is
invariant under all mass-preserving bijections of V fixing every V_j (i.e. membership depends only on the profile
(|K∩V_j|)_j). Then for t >= 3/4 and 3/2 <= N <= 9/4 (first order) 𝒞 contains a good seven.
*Proof.* v/3 has mass N/3 <= t, so there is a profile s with v/3 <= s <= v, |s| = t, and by T-covering a member K with
profile π >= s >= v/3. Put κ_j = (3π_j - v_j)/2 >= 0 and split each V_j into a part of mass κ_j and three parts of mass
(v_j - π_j)/2 >= 0 (total v_j). Let κ be the union of the first parts and P_1, P_2, P_3 the unions of the others:
|κ| = (3c - N)/2 = N - 3/2, |P_i| = 1/2, and κ ∪ P_i has profile π, so all three are members. They form a pencil with
kernel κ; finish as in 35.1. ∎
`sym_check.py` [computed exact, brute force over every choice of the four later replies inside the family]:
(k,T,N) = (4,3,8), partitions (5,3), (5,3), (4,4), (3,3,2) with profile sets {31,13}, {31,22,13}, {22,40,04},
{112,310,130,211,121,220}: 3, 375, 27, 375 reply choices, 0 failures. (At finite k the proof needs 3π_j - v_j even.)
Consequences.
- No counterexample to CP is a profile family of a fixed partition, for any bounded number of classes: the pool
  family (m = 2, classes Y and V∖Y), every "pool with switch" or anti-plan rule frozen to the four cells of ONE pair
  with exchangeable choices inside the cells, every threshold family. This is the rigorous form of §13 for families,
  and it holds across the whole window with one certificate.
- A (7,2) family must therefore break exchangeability inside every cell of every finite partition: the identity of
  the dumped points, not their profile, has to depend on the request. The first-order game of §25–§30 models him
  by profiles only relative to cells created by the play; Theorem S says a first-order description relative to a
  FIXED partition with exchangeable cells is never enough for him.
- The certificate is the zero-slack pencil; in a symmetric family all seven lines can be members (slack 4·delta), so a
  robust version (families close to symmetric) is plausible but not proved here [heuristic].

## 37. Theorem Q in set form (Q') [proved by hand]

For four co-edges put σ = s_0 + s_1 = mass of the points lying in at most one of them (in at least three of the four
edges). From 4c = s_1 + 2p + 3u_3 + 4u_4 and N = s_0 + s_1 + p + u_3 + u_4:  W = u_3 + 2u_4 + s_1 = 2N - 4 + 2σ. Hence
**Q'.** Four members with σ <= (3t - N)/2 and, for each of the three matchings, (pair-only mass of the matching) + σ <= t,
are finished by three fixed requests. (The τ-distribution of Theorem Q exists iff the first inequality holds.)
- Any four members of the pool family have σ >= 1 - t (edges live on mass 1 + t: 4 <= 2(1 + t - σ) + 4σ), and
  1 - t - (3t - N)/2 = (ω - 4·eps)/2 = base/2. So Q' fails for the pool family by at least base/2, for every quadruple.
- A quadruple in which replies 3 and 4 are fully wasted (W = 2ω) has σ = 1 - t as well: at the level of four members
  the anti-plan adversary and the pool family are indistinguishable; "value = base at depth 2" (§26) is σ = 1 - t.

## 38. Exact remaining gap, and the next step

**Reduction (one-way) [proved: Q', 35.1, Theorem T].** CP in the window follows from
**(Σ)** every T-covering family contains (a) four members with σ <= (3t - N)/2 and balanced matchings, or (b) three
members forming a pencil with kernel in [N - 2t, N - 3/2], or (c) three members satisfying Theorem T.
(Σ) is open; it is true for symmetric families (Theorem S, via (b)) and for pool-rule adversaries (Theorem P).
It is not known to be equivalent to CP: a good seven may need five or more members used in full.
**What is known about (Σ) [computed float, depth 2 only]:** against the adaptive adversary every quadruple reachable
in two further requests has σ >= 1 - t (= the pool value), i.e. misses (a) by base/2 (§26 read through §37).
**The gap, stated without a game.** Call σ*(𝒞) the least σ over balanced quadruples of members. Pool families have
σ* = 1 - t and are beaten only by (b), with margin O(eps). (Σ) asks for: σ*(𝒞) > (3t - N)/2 ⟹ (b) or (c). Nothing in
Parts I–VIII proves any implication of this kind for a family that is not exchangeable; the kernel lemma was the
candidate and is dead (§35).
**Dead routes (this part).** Kernel lemma via two requests and Theorem Q (34.1); core from triple exclusions (35.3);
transfer of a core between request shapes (35.4); any counterexample search among fixed-partition profile families
(Theorem S — relevant to SPOIL: a first-order counterexample cannot be stationary and exchangeable).
**Next step.** Prove or refute the robust form of Theorem S, which is the first statement that would reach beyond
exchangeable families with first-order slack: *if for some partition into boundedly many cells the profile of D(S)
is a function φ of the profile of S (the points inside the cells chosen adversarially), she wins.* For continuous φ
the natural proof is exhaustion by a fixed point (choose s with s + φ(s) = v on the support of φ(s), so the dump is
forced as a set and the reply is free; seven free replies have slack 4·delta) [heuristic]; the anti-plan rule is the
discontinuous case (switch at |S∩O| = ω), where exhaustion fails by a count (the low cell A∪B cannot be filled to
within ω by a request of mass t). So the single test case is: **the anti-plan rule frozen to the four cells of one
pair, in-cell choices adversarial** — a finite-dimensional first-order game in which he has no freedom of profile at
all. A win for her there is the mechanism (Σ) needs; a win for him is a stationary first-order adversary and should
be handed to the SPOIL side.
Not done: that test; any proof of (Σ); exact (rational) versions of the LPs of §34–§35; N >= 11/6 uses Fano-type
readings only (as in §25).

Self-check (Part VIII): 34.1's invariance is a three-line count and agrees with the LP at 15 points; the joint LP
reproduces base for the bare pair and 0 at the Theorem-T and pencil positions (hand constructions 35.1, 34.2). 35.2's
load sum re-derived from 3c = 2(a+b+d) + Σe + 3κ. 35.3's threshold 3ω/2 - 2·eps is matched by the LP on both sides
(σ = 1.2: no certificate at N = 1.85, 1.9; certificate at N = 1.82). Theorem S: the profile arithmetic checked by hand and
by brute force on four families; it uses only T-covering for the one profile s >= v/3 and for the four transversal
requests. Q' checked against the load identity of §4. Everything in §34–§35 is first-order and float; none of it is
a statement about a complete family except Theorem S, 35.1, 35.2 and Q'.

## 39. Regularity / compactness reduction to Theorem S: rejected; what replaces it

Brief: approximate an arbitrary T-covering family by a profile family of a bounded partition, keeping T-covering and
"no good seven" up to the slack, then apply Theorem S. Code: `compute/core8/sym_plus_check.py`.
**Outcome. The reduction is dead, for a reason that can be stated exactly (39.1–39.3). (Σ) is not advanced for
general families.** Positive by-products, both proved: Theorem S holds at finite k for partitions with up to
4·eps·k/3 - 4 cells of arbitrary sizes, single points included (S+, 39.4), and in density form (39.2). So the least
non-exchangeable feature of a counterexample is quantified: linearly many cells (39.5).

**39.1 Which property survives [proved by hand].** Fix a partition P. There are two profile families attached to 𝒞:
the upper closure 𝒞^P (all co-edges having the profile of some member) and the lower kernel 𝒞_P (the profile classes
contained in 𝒞).  𝒞_P ⊆ 𝒞 ⊆ 𝒞^P.
- T-covering is monotone up: it survives in 𝒞^P exactly, and is lost in 𝒞_P (which is empty in general).
- "No good seven" is monotone down: it survives in 𝒞_P, and is lost in 𝒞^P — always, by Theorem S: 𝒞^P is symmetric and
  T-covering, hence has a good seven, for EVERY 𝒞 and every P (for the trivial partition 𝒞^P is the complete family).
So the approximation that keeps T-covering never keeps (7,2), by a theorem, not by accident; and the error term is
explicit: the pencil triples (K, K', K'') of one profile class with K in 𝒞 and K', K'' not both in 𝒞. A reduction would
need 𝒞 to fill almost all of each profile class it meets. 39.2 shows the opposite is forced.

**39.2 Density form of Theorem S [proved by hand].** Let π be a profile with π >= v/3 (and the parity/size conditions of
39.4). The pencil triples inside the class [π] form a 3-uniform hypergraph on which ∏ Sym(V_j) acts transitively on
vertices, so every member of [π] lies in the same number of triples; a subfamily containing no whole triple has at
most 2/3 of [π]. Hence: **if 𝒞 is T-covering and contains more than 2/3 of one profile class [π] with π >= v/3, for
any partition as in 39.4, it has a good seven.** Consequently a (7,2) family misses at least a third of every such
class it meets, for every such partition: it is never close to exchangeable, in any metric in which "close" means
density above 2/3 on classes. (2/3 is sharp for this argument: "all K in [π] avoiding a fixed point" has no triple.)
What T-covering gives from below is only |𝒞| >= C(n,T)/C(c,T), i.e. overall density exp(-γk), γ = (N - t)·h(ω/(N - t))
(nats; 0.42 at N = 1.9, t = 0.76 against 0.39 for the number of T-subsets of a member). Graph/hypergraph regularity
controls nothing at density exp(-γk), and the only families that are dense on the classes they meet are those living
on extreme profiles (pool: the whole of Y), which is the exchangeable case again. [density remark: heuristic as a
no-go; the 2/3 bound is the proved part]

**39.3 What compactness really gives [proved by hand, first order].** For a sequence of families let 𝒯_q be the closed
set of Venn-diagram mass vectors (2^q cells) of q-tuples of members. The system (𝒯_q) is closed under sub-tuples and
permutations, and T-covering is exactly the extension property: for μ in 𝒯_q and every request profile s on its cells
(mass t) some μ' in 𝒯_{q+1} projects to μ with the new member >= s on every cell. Conversely the set of positions
reachable under a first-order adversary strategy, closed under sub-tuples, is such a system. So the compactness limit
of a family is an adversary strategy of the first-order game G_∞ of 29.2/§25, and nothing smaller: the limit object
is infinite-dimensional (cells refine with q). Profile families are precisely the systems generated by one fixed
finite partition. Compactness therefore returns the game, not Theorem S; there is no intermediate "bounded
partition up to o(1)" stage, because the cells that matter to a member are those cut out by the other members of the
tuple, and their number is unbounded in q (already 2^7 for one seven).

**39.4 Theorem S+ (finite k, many cells, points allowed) [proved by hand; construction computed exact].**
Let |V| = n, V = V_1 ⊔ ... ⊔ V_m with arbitrary sizes v_j >= 1, 𝒞 a T-covering family of (n - k)-sets invariant under
∏ Sym(V_j). If n/3 + m <= T and m <= 4(T - 3k/4)/3 - 4, then 𝒞 has seven members covering all pairs.
*Proof.* Request ⌈v_j/3⌉ points of each cell (padded to T); a member K ⊇ S has profile π with 3π_j >= v_j. Put
κ_j = ⌊(3π_j - v_j)/2⌋, p_j = π_j - κ_j; u = number of cells with 3π_j - v_j odd. In V_j take a set of κ_j points and three
sets of p_j points covering the rest, disjoint if the cell is even, the first two sharing exactly one point y_j if it is
odd (3p_j + κ_j = v_j or v_j + 1). The unions K_i = κ ∪ P_i have profile π, so all three are members. Classes: V_o = κ;
Q_1 = P_1, Q_2 = P_2 minus the points y_j, Q_3 = P_3 (sizes (k+u)/2, (k-u)/2, (k+u)/2); split each Q_i into a_i, b_i.
L_i = κ ∪ Q_i ⊆ K_i, and the four transversals can be made of size <= 3⌈(k+u)/4⌉ <= T. Every point is in a class, its
co-type contains the pencil of the class (y_j is also in K_2, harmless); 1.3. ∎
`sym_plus_check.py` [computed exact]: (k,T,n; cells; π) = (8,7,16; 9,7; 4,4), (8,7,16; 9,6,1; 4,3,1),
(12,10,23; 11,7,4,1; 4,4,2,1), (16,13,30; 10,9,7,3,1; 4,4,3,2,1): profiles of K_1, K_2, K_3 equal π, largest transversal
<= T, all pairs covered by the unpadded seven.
So: junta-type families (membership a function of the profile on a bounded partition AND of the trace on up to
about 4·eps·k/3 named points), ordered tie-breaks on boundedly many points, and partitions into o(k) cells are all
excluded. The window parameters do not enter beyond n/3 + m <= T.

**39.5 The minimal non-exchangeable feature [proved: lower bound; heuristic: what attains it].** Call the partition
complexity of 𝒞 the least m such that 𝒞 is invariant under ∏ Sym(V_j) for some partition into m cells. By S+ a
counterexample has complexity > 4·eps·k/3 - 4, i.e. linear in k for fixed eps, and by 39.2 it misses a third of every
qualifying profile class at every lower complexity. The cheapest structures of linear complexity are (i) dependence
on Θ(k) individual points (a point-wise tie-breaking order: the "first ω points of a request-dependent cell") and
(ii) pair-relative rules, where the cells are cut out by other members (the anti-plan rule of 9.3). (i) alone with a
FIXED order is a nested pool and loses to Theorem P; so the feature a counterexample needs is (ii): **cells that
depend on the request through other members of the family**, equivalently a limit system (39.3) that is not finitely
generated. That is the object the SPOIL side is trying to build; S+ says nothing simpler can work.

**39.6 Status of (Σ).** Unchanged for general families. What this section adds: (Σ) holds, via branch (b), for all
families of partition complexity <= 4·eps·k/3 - 4 and for all families exceeding density 2/3 on one qualifying class.
The route "regularity ⟹ Theorem S" is dead because the property that must be transported (no good seven) is the
one destroyed by symmetrisation, and density exp(-γk) leaves no room for an approximate version.
**Exact gap.** Families of linear partition complexity, equivalently non-finitely-generated limit systems; for them no
certificate with first-order slack is known to be forced (§38).
**Next step [heuristic].** Raise the complexity bound from eps·k to c·k with c independent of eps: use, instead of the
zero-slack pencil, a seven in which all lines are members of one orbit (slack 4·delta, 2.3 with q = 7), so that the
parity/boundary loss per cell is paid from delta rather than from eps. If S+ then holds for m <= c(N)·k cells, a
counterexample must have complexity above c(N)·k, and the SPOIL constructions can be tested against that bound
directly (count the cells their rule distinguishes).

Self-check (§39): 39.1 is monotonicity plus Theorem S. 39.2: transitivity of ∏ Sym(V_j) on [π] and on the triples of the
39.4 construction; averaging gives 2/3. 39.4: sizes re-derived (|κ| = (3c - n - u)/2 with c = n - k, |Q_1| = (k+u)/2), bound
u <= m; four instances checked by machine, including singleton cells. 39.3 is a restatement of 29.2 in the limit and
uses first-order masses only. The entropy numbers in 39.2 are hand arithmetic.

## 45. (structural side; §40–§44 are reserved for the SPOIL agent) Can the cell bound of S+ reach c(N)·k, and does it touch SPOIL?

Brief: raise the S+ bound from about 4·eps·k/3 cells to c(N)·k using a seven of members with slack 4·delta; compare with
the partition complexity of SPOIL-type adversaries. Code: `compute/core8/sym_plus2_check.py`.
**Outcome. Not achieved, and it would not matter.** (1) The bound improves only to 4·eps·k - 12 cells, and that is
optimal for the pencil certificate (45.1). (2) A bound c(N)·k with c independent of eps cannot come from slack: the
premise "an all-members seven has slack 4·delta" is false for symmetric families in general — the pool family is
symmetric and every good seven in it has slack exactly 4·eps·k (45.2). (3) No cell bound short of m = n beats a
SPOIL-type rule: such a rule creates new cells at every reply and passes any bound c·k at depth log2(c·k) (45.4).
What S+ does exclude is stated exactly in 45.3. **SPOIL is not killed as a disproof route by this line.**

**45.1 S+ with rotating overlaps [proved by hand; construction computed exact].** In 39.4 let the shared point y_j of
the r-th odd cell lie in petals r and r+1 (mod 3) and be assigned to line r. Then |Q_i| = k/2 + u/6 up to rounding, the
transversals have size <= 3k/4 + u/4 + 3, and the theorem holds for **m <= 4(T - 3k/4) - 12 = 4·eps·k - 12** cells
(with n/3 + m <= T). Optimal for this certificate: each odd cell forces one point of co-type size 4 (one wasted
incidence), and a certificate with three members used in full has exactly 4·eps·k spare incidences (2.3).
`sym_plus2_check.py`: (k,T,n; cells; π; u) = (16,14,31; 9,9,9,4; 4,4,4,3; 4), (16,14,34; 7,7,7,5,5,3; 4,4,4,2,2,2; 6),
(20,17,38; 5⁷,3; 2⁶,3,3; 6): transversals 14, 14, 17 <= T, all pairs covered; at (16,13,31), u = 4 the largest
transversal is 14 > T (the additive constant is real).

**45.2 Why slack 4·delta is not available [proved by hand].**
(a) *One orbit.* Seven sets of one profile π form a Fano-type good seven iff in every cell the v_j points can be given
pencils with every line used at most π_j times; this needs π_j >= μ(v_j), μ(v) = least possible maximum number of
chosen points on a line, 3v/7 <= μ(v) <= 3v/7 + 2 (μ = 1, 2, 2, 2, 3, 3, 3 for v = 1..7). No parity condition, and the slack
is 4·delta. But she cannot force such a member: she would have to request μ(v_j) points of every cell, total
>= 3n/7 > T throughout the window (N > 7t/3 ⟺ delta > 7·eps/3), and he leaves the unrequested cells below 3v_j/7.
(b) *Several orbits.* For members with profiles π^1..π^q and 7 - q requested lines the condition is cell-wise: class
sizes w^j in Z^7, Σ_p w^j_p = v_j, line sums <= π^i_j for the member lines, Σ_j (line sum) <= T for the requested ones
(sufficient; exact for N < 11/6). A real solution with 6 spare points per line and cell rounds to an integer one. So:
*a first-order certificate whose member lines all have slack η·k survives m <= η·k/6 cells* (conditional S++).
(c) *The condition of (b) cannot hold uniformly.* The pool family (all co-edges containing Y, |Y| = ω) is symmetric
under every partition refining {Y, V∖Y}; all seven members of any good seven contain Y, so Y alone consumes 4ω of the
4·delta of 2.1 and the total slack is 4·eps·k, for every certificate type. Hence no argument "symmetric ⟹ certificate
with slack independent of eps" exists; a c(N)·k bound, if true, needs a dichotomy (pool-like part exact, rest with
slack) — which is (Σ) again, restricted to symmetric families of linear complexity. Not proved; no counterexample
either: for cell size b the question is a finite profile game (he chooses π >= s in his profile set, she places the
sets), open for 1 << b << 1/eps.

**45.3 What S+ excludes on the SPOIL side [proved by hand, from S+ and 39.2].**
*Stabilisation lemma.* Suppose that from some position with q kept co-edges on, the set of his replies is closed under
permutations inside the 2^q Venn cells (profile rule, in-cell points exchangeable). If 2^q <= 4·eps·k - 12 and
n/3 + 2^q <= T, she wins using replies made after that position only. More generally, if more than 2/3 of the sets
with the profile of one such reply (to a request taking a third of every cell) are replies, she wins.
So a SPOIL-type rule can never become stationary with exchangeable cells: either (α) every reply keeps cutting the
cells that later dumps depend on, without bound in the depth, or (β) the points chosen inside a cell are tied to an
order or to the request. The first-order model of §25–§30 is of type (α) by construction (a dump on part of a cell
splits it, and the next rule refers to the pieces).

**45.4 Comparison of complexities; the precise statement about SPOIL.**
- SPOIL rule (26.3, §27): "whole dump on one unrequested cell of points lying in >= 2 kept co-edges". After d replies
  it distinguishes up to 2^d cells, so the family generated by a play of depth d has partition complexity up to 2^d,
  and exceeds any bound c·k at d = log2(c·k) (about 9 replies for eps·k = 100). The evidence for SPOIL is at depth 2–3;
  S+ with any linear bound says nothing there, and nothing later.
- A bound that kills SPOIL by complexity alone would have to be m = n (cells = points), which is CP.
- Therefore: **Theorem S / S+ do not kill SPOIL. They kill exactly the stationary exchangeable adversaries** (39.4,
  45.3), in particular any attempt to turn a bounded-depth SPOIL invariant into a family by freezing the cells and
  letting the in-cell choice be arbitrary.
- The simplest object left on his side is of type (β) with bounded cells: a stationary profile rule on the cells of
  boundedly many members with a FIXED order of the points inside each cell (dump = first unrequested points of the
  chosen cell: one nested pool per cell, switched by the request). Complexity n; not covered by S+ (not exchangeable)
  nor by Theorem P (several pools, shape-dependent switch). This is the frozen anti-plan rule already handed to the
  SPOIL agent; nothing here decides it.

**45.5 Status.** (Σ) unchanged for general families. Proved in this section: S+ for m <= 4·eps·k - 12 cells (sharp for
the pencil); the one-orbit criterion μ and why it cannot be forced; the rounding lemma; the stabilisation lemma.
**Dead:** "all-members seven ⟹ c(N)·k" (pool family, 45.2c); "complexity bound ⟹ SPOIL dead" (45.4).
**Exact gap.** (i) Symmetric families with cells of bounded size b, 1 << b << 1/eps (a finite profile game);
(ii) non-exchangeable families: nested pools per cell with a shape-dependent switch, and history-refining rules.
**Next step.** Decide (ii) in its smallest instance by hand, because it is a family and no game is needed: cells
O, A, B, g of one pair, each with a fixed order; dump = first ω unrequested points of O if |S∩O| < ω, else first
unrequested points of A∪B. Every member then contains an initial segment of O or of A∪B, so the members are the
co-edges K with K∩O ⊇ I_O(K) or K∩(A∪B) ⊇ I_AB(K) for explicit initial segments; a good seven is a Fano blow-up whose
seven lines each contain the initial segment their own shape demands. That is one LP in the class masses per
assignment of shapes to lines (2^7 cases), exact in rationals. Feasible ⟹ this adversary is dead and the mechanism
(mixing high-shape and low-shape lines in one seven) is a candidate proof of (Σ)(a); infeasible ⟹ it is a stationary
first-order counterexample candidate and belongs to §40+.

Self-check (§45): 45.1 sizes: Σ|Q_i| = 3k/2 + u/2, transversal total = 2Σ|Q_i| = 3k + u <= 4T ⟺ u <= 4·eps·k; machine check on
four instances (one deliberately failing by rounding). 45.2(a): μ values from the Fano plane (two points share a line;
a quadrangle has no three collinear; five points always contain three collinear). 45.2(c) is the waste identity 2.1.
45.3 is S+ applied to the replies after the position; it needs the reply SET to be orbit-closed, not the reply map to be
equivariant (an equivariant map has D(S) a union of whole remainders V_j∖S). 45.4's depth count is 2^d against c·k.

## 46. (structural side) The ordered frozen anti-plan family: it has a good seven — dead as a disproof candidate

Code: `compute/core8/frozen_antiplan.py` (128 shape assignments, float LP), `frozen_antiplan2.py` (`scan t`: parameter
scan; `finite`: integer design by MILP, then the adversary's actual rule on real sets and brute-force pair cover).
**Outcome. Not a counterexample.** For every parameter choice in the window the family contains a good seven, by
Theorem P applied to ONE of its two pools [proved by hand]; confirmed by LP on a scan and by twelve finite instances
with the real rule [computed exact for the final check]. The winning assignment is "the three pencil lines of one
shape"; the shapes of the other four lines are irrelevant.

**46.1 The family.** Cells O (mass o), U = A ∪ B (mass 2(c - o)), g, each with a fixed order; O1, U1 = the first ω points
of O, U. Rule: if |S ∩ O| < ω the dump is the first ω unrequested points of O, otherwise the first ω unrequested points of
U (the scan keeps o >= 2ω, |U| >= 2ω, |g| >= 0, which makes the rule well defined on the requests used).
Members as sets [proved by hand]: shape H: K ⊇ O1 and |K ∩ O| < 2ω; shape L: K ⊇ U1 and |K ∩ O| >= ω. (K = S ∪ D with D
the first ω unrequested points of the cell ⟺ D lies in the largest initial segment of the cell inside K.) A line lies in
an H-member iff |L ∩ O2| < ω and |L ∪ O1| <= c; in an L-member iff |L ∪ U1| + (ω - |L ∩ O|)^+ <= c. Every line of mass <= t
lies in a member of one of the two shapes (T-covering).

**46.2 Good seven [proved by hand].** Pencil with kernel class V_o of mass N - 3/2, six classes of mass 1/4.
- *L-pencil* (ω <= t - 1/2, i.e. N <= 2t + 1/2): V_o ⊇ U1 ∪ (ω points of O) — room: 2ω <= N - 3/2 = ω + t - 1/2. For a pencil line
  L request S = L∖U1 (mass c - ω = t); |S ∩ O| >= ω, so the dump is the first ω unrequested points of U, which is U1;
  the reply is L.
- *H-pencil* (o < 4ω): V_o ⊇ O1, and O∖O1 spread evenly over the three pencil lines outside V_o, so each has
  (o - ω)/3 < ω of it. Request S = L∖O1; |S ∩ O| < ω, the dump is O1; the reply is L.
- One of the two always applies: if ω > t - 1/2 and o >= 4ω then o > 1 + 4·eps > c - ω, contradicting |U| >= 2ω.
The four transversal lines have mass 3/4 <= t; request them, any reply; 1.3(ii). ∎
So the switch does not help him: each branch of the rule is a pool rule on its own shape class, and Theorem P needs
only three requests of ONE shape — the other four requests are short and their replies are irrelevant.

**46.3 LP scan [computed float].** `frozen_antiplan2.py scan 0.76`: N = 1.81, 1.84, ..., 2.11, o on a grid of step 0.04 with
o >= 2ω (104 points): at every point at least 8 of the 128 shape assignments are feasible; all-H or all-L is feasible at
every point; "pencil L, rest H" (LLLHHHH) at 83 of them, consistent with 46.2 once the (irrelevant)
shape constraints on the transversals are taken into account. At the positions of §26: N = 1.82, o = 0.29: 64/128
(all-L yes, all-H no, since o > 3ω); N = 1.85, o = 0.305: 127/128; N = 1.9, o = 0.33: 128/128.

**46.4 Finite k, actual rule [computed exact: integer design by MILP, then the rule applied verbatim to real sets and
all pairs checked].** (k,T,n,o) = (40,31,74,12), (40,31,76,13), (40,31,80,20), (100,76,182,29), (100,76,185,31),
(100,76,190,33), (100,76,190,40), (100,76,200,50), (100,76,210,70), (100,76,220,90), (200,151,370,60), (200,151,390,80):
assignment LLLHHHH in all twelve; every line lies inside the actual reply to its request; the seven actual replies
cover all pairs. (The MILP only proposes the classes; the verdict is the brute-force check on the replies.)

**46.5 What it means.**
- Type (β) of 45.3 with a FIXED order is dead: a fixed order inside a cell makes the cell a nested pool, and a
  shape-dependent switch between finitely many nested pools loses to Theorem P on one shape class. The proof uses
  nothing about the pair (K_1, K_2) and extends verbatim to any rule "dump = first ω unrequested points of a cell
  chosen by the profile of S" as soon as one cell Z_1 (first ω points) can be put into a kernel class together with
  whatever the selection of that cell demands of the request (here: ω points of O, or fewer than ω of O per line).
  [proved for two cells as above; the general statement is the same argument, not written out]
- The real anti-plan adversary of 9.3 differs exactly here: on a pencil-type request his low dump is not an initial
  segment of A ∪ B but depends on which points of A ∪ B the request contains, so the three pencil lines cannot be given
  one pool. The surviving object is therefore: in-cell choice tied to the REQUEST (not to an order), or cells refined
  by the play — (α) of 45.3. Stationary + exchangeable (Theorem S/S+) and stationary + ordered (this section) are both dead.
- For (Σ): the winning certificate is again branch (b) (zero-slack pencil), not a four-member certificate; no
  first-order-slack mechanism was found.
**Exact gap.** Unchanged: (Σ) for families whose in-cell choice depends on the request.
**Next step.** The same finite test for the least request-dependent in-cell rule: dump = the ω unrequested points of
the chosen cell that come first in an order determined by the request's trace on a SECOND cell (two orders, one bit).
It is still a family with an explicit member description (two pools per cell, selected by the bit), so the check is
again a union of pool designs: 2^3 choices of bit for the pencil lines. If every such bit pattern is beaten by a
pencil with a split kernel, iterate (b bits); the first b at which no pencil exists is where a four-member
certificate becomes necessary, and that instance is the right test case for (Σ)(a).

Self-check (§46): member description re-derived from the rule (maximal initial segment); L-pencil sizes: kernel
N - 3/2 >= 2ω ⟺ ω <= t - 1/2; requests have mass c - ω = t exactly; H-pencil needs strict inequality (o - ω)/3 < ω, which the
integer designs enforce as <= ω - 1. Case exhaustion uses |U| = 2(c - o) >= 2ω. The LP's shape constraints on transversal
lines are stronger than necessary (a line of mass <= t needs none), so LP-infeasible assignments are not claims.
Finite instances: n up to 390, exhaustive pair check on the seven replies produced by the rule itself.

## 47. (structural side) Theorem W: class-selected greedy rules — the theorem behind §46, and what escapes it

Brief: one theorem for adversaries whose reply depends on the request through B bits of its traces plus fixed in-cell
orders, conjectured bound M·2^B <= c·eps·k. Code: `compute/core8/window_thm.py`.
**Outcome.** The right bound has neither M nor 2^B nor eps in it. What matters is the mass of the set the selector
*looks at*: **if the class of a request is decided by its trace on a window of at most T - k/2 points, he loses in
seven requests, for any number of cells, classes and orders** (47.2; exact at finite k; 1200 random adversaries and the
twelve instances of 46.4 checked on real sets). Pigeonholing is not needed: she requests the whole window, which
fixes the class, and applies Theorem P to that class. Thresholds and profile selectors are covered by the same frame
criterion (47.3–47.4). The escape is stated exactly in 47.5.

**47.1 The class of adversaries.** A *greedy rule* consists of a selector σ: requests → classes (any set of classes) and,
for each class r, a priority order ≺_r on V (any linear order). Reply: S ∪ (the first n - k - T points of V∖S in ≺_r), r = σ(S).
Cells with in-cell orders are the special case "the points of the cell chosen by r first, in the cell's order"; rules that
take prescribed amounts d_j(r) from several ordered cells have the same property used below and are included.
Every member of class r contains an initial segment of ≺_r∖S, so these are exactly the "nested pools switched by the
request" of 45.4(β) and §46.

**47.2 Theorem W [proved by hand; exact for 4 | k, T >= 3k/4, n >= k + T].**
*Frame criterion.* Suppose there are a class r, a set Z of n - k - T points and a pencil frame (κ; P_1, P_2, P_3)
(|κ| = n - 3k/2, |P_i| = k/2, a partition of V) with Z ⊆ κ such that for S_i = (κ ∪ P_i)∖Z:
 (i) σ(S_i) = r for i = 1, 2, 3, and (ii) Z precedes every point of V∖(S_i ∪ Z) = P_j ∪ P_l in ≺_r.
Then the replies to S_1, S_2, S_3 are the three pencil lines and four requests of 3k/4 points finish (1.3(ii)). ∎
*Window theorem.* If σ(S) depends only on S ∩ W for a fixed W with |W| <= T - k/2, the criterion holds: let r = σ of any
request containing W, Z = the first n - k - T points of V∖W in ≺_r, κ ⊇ W ∪ Z (room: |W| + |Z| <= n - 3k/2), petals arbitrary.
Every S_i contains W, so (i); everything outside W ∪ Z comes after Z, so (ii). ∎
Corollaries.
- *Juntas:* a selector that reads B individual points loses for **B <= T - k/2 = (1/4 + eps)·k**, with 2^B classes if he
  likes and a different order for each. No eps in the threshold, no dependence on the number of cells.
- *B bits, each a function of the trace on a set of at most w points:* loses for B·w <= T - k/2.
- *Thresholds (the rule of §46):* if "σ(S) = r whenever |S ∩ E| >= θ" and ≺_r starts outside E, put x = min(θ, T - k/2)
  points of E into κ and θ - x into each petal: holds iff |E| >= 3θ - 2x. For §46 (E = O, θ = ω): o >= 3ω - 2·min(ω, T - k/2) —
  true in all twelve instances. Downward thresholds ("|S ∩ E| < θ", the H-class of §46) are certified by a frame with
  fewer than θ points of E∖Z on each line: (|E| - |E ∩ Z|)/3 < θ.
`window_thm.py` [computed exact; the rule applied verbatim, all pairs checked]: (a) (k,T,n) = (40,31,74), (40,31,80),
(100,76,185), (100,76,190), (100,76,210); window of B = 1, 3, ⌊(T - k/2)/2⌋, T - k/2 random points; an arbitrary (random)
table {0,1}^B → R classes, R = 2, 8, 64; an independent random order for each class; 20 adversaries per cell of this
grid: 1200/1200 pencil replies exact, 1200/1200 good sevens (B = T - k/2 is tight for the construction: κ = W ∪ Z exactly at
n = 76). (b) the twelve instances of 46.4 by the threshold formula, no MILP: 12/12.

**47.3 Why the coordinator's bound M·2^B <= c·eps·k is not the right shape.** The number of classes costs nothing: one
frame serves one class and she chooses which. The number of cells costs nothing: an order is an order. eps does not
enter because the kernel has room N - 3/2 - ω = t - 1/2 at first order, whatever eps is. eps·k appears only when the
frame cannot be exact (S+ parity, 39.4/45.1), i.e. for exchangeable cells, where there is no order to exhaust.

**47.4 Profile selectors [proved at first order; finite-k rounding not done].** Let σ be an arbitrary function of the
profile of S on a partition (V_j), R classes, Z_r = the first ω points of ≺_r, z^r its profile. A frame for class r in which
the three requests have a common profile s exists iff s lies in 𝒮_r = {(v - z^r)/3 + 2κ/3 : 0 <= κ <= v - z^r, |κ| = N - 3/2 - ω}
(per cell: kernel part κ_j, three equal petal parts). If the 𝒮_r have a common point s, then σ(s) is one of the r and that
class has a frame, so she wins. A common point exists whenever Σ_j (v_j - (3/2)·max_r z^r_j)^+ >= N - 3/2 - 3ω/2; e.g. for cells
of mass >= 3ω/2 as soon as (R - 1)·ω <= 1. At finite k the profiles must agree exactly, which a parity-sensitive selector
can prevent; the repair costs O(1) points of the 4·eps·k slack per cell, as in S+. [first-order statement proved;
the finite version is where eps·k enters again]

**47.5 What an adversary must do to escape [proved: necessity for greedy rules; heuristic: which rules do it].**
For a greedy rule to survive the pencil, for EVERY class r and every frame (κ; P_1, P_2, P_3) whose kernel contains the
head Z of ≺_r relative to the requests, at least one of the three requests (κ ∪ P_i)∖Z must be sent to another class. The
three requests coincide on κ∖Z (mass t - 1/2) and differ only by which petal (mass 1/2) they contain. Hence:
1. the selector must depend on more than T - k/2 points *essentially*: no set of at most T - k/2 requested points may
   determine the class (else 47.2);
2. it must not be decided by monotone thresholds or by the profile on a partition with cells large against ω (47.2
   thresholds, 47.4), up to O(eps·k) parity effects;
3. so it must separate petals: among any three requests sharing a (t - 1/2)-kernel and carrying complementary halves of
   the rest, it must tell at least one apart from the class whose head lies in that kernel. That is a selector that
   reads the IDENTITY of a positive fraction (> 1/4 + eps of k) of the requested points and is balanced on every large
   subcube — hash-like on linearly many points; or
4. he gives up greediness: the dumped points are not an initial segment of an order fixed by the class, i.e. the in-cell
   choice itself depends on the request (the genuine anti-plan dump of 9.3), or the cells are cut by earlier replies
   ((α) of 45.3).
A rule of type 3 is still a family with an explicit description, but it is no longer "bounded information": it is a
colouring of requests in which every pencil frame around every class head is non-monochromatic. Whether such a
colouring can also avoid the triangle frames of Theorem T and the four-member frames of Q' is (Σ) for greedy rules.
**Dead:** every greedy rule with a window of at most T - k/2 points; threshold and (first-order) profile selectors.
**Exact gap.** (Σ) for (i) greedy rules with hash-like selectors on more than (1/4 + eps)·k points, (ii) non-greedy rules.
**Next step.** For (i) the pencil is the wrong certificate (one bad request kills it) and the natural one is the count:
a selector with R classes puts a fraction >= 1/R of the requests of any frame family into one class, and the frames
around a fixed kernel form a symmetric design in the petals; the density form of Theorem S (39.2: more than 2/3 of
an orbit ⟹ a pencil) applies verbatim to the class-r requests over a fixed kernel. So: *if for some class r and
some kernel κ ⊇ head of ≺_r more than 2/3 of the halves P of V∖κ have σ((κ ∪ P)∖Z) = r, she wins* — a selector must
keep every class below density 2/3 on every such family [proved, same averaging]. Sharpening 2/3 (complementary
halves P, P' of the same K∖κ must not both be class r for any third member: an intersecting-type condition on the
class-r halves) is the concrete extremal problem that decides (i).

Self-check (§47): frame criterion: reply to S_i = S_i ∪ (first ω unrequested in ≺_r) = S_i ∪ Z = κ ∪ P_i by (ii), class by (i); sizes
|S_i| = n - 3k/2 + k/2 - (n - k - T) = T. Window theorem needs only |W| + |Z| <= |κ|, i.e. |W| <= T - k/2. Threshold arithmetic: each line
holds x + (θ - x) = θ points of E, using x + 3(θ - x) of them. Machine check uses the rule itself, including classes never seen
before (lazy random table), so (i) is tested, not assumed. 47.4: κ^r = c + z^r/2 gives a common s; first order only.
The 2/3 statement in "Next step" is 39.2's averaging on the orbit of halves under Sym(V∖κ); it is tagged proved for that
reason only, and has not been machine-checked.

=============================================================================================
# Part IX — SPOIL tested (disproof side; §40–§44)

Code (all in `compute/core`, logs in `compute/core/logs`): `spoil.py` (engine: any number of kept replies, every
reading of 2..7 replies, 83 concurrency patterns), `spoil_hunt.py` (her search for a request with no spoiling dump),
`spoil_exact.py` (exact rational certificate "no dump spoils"), `spoil_two.py`, `two_check*.py` (two levels),
`spoil_struct.py`, `tri_test.py` (multi-pair design), `spoil_frozen.py` (stationary rule, superseded by §46),
`onebit.py` (one-bit rule, finite k, exact). Units k = 1, t = 0.76 throughout the float work.
**Verdict.** (1) SPOIL as written in §27 ("every position, every request") is FALSE: exact counterexample with three
kept replies (§40). It is false only at positions he need not enter, so this does not contradict §26/§30.
(2) The meaningful form — *he has a strategy that keeps every need >= base for ever* — is undecided. Up to four
kept replies nothing breaks it; at five kept replies there is one sampled two-request break of the one-step rule
(§41). Evidence now leans against it, weakly. (3) No construction. Nothing here is a counterexample to CP or
evidence that f(k,7) > 3k/4 + o(k). (4) "SPOIL at all depths ⟹ disproof" (task statement, §27, §32(b)) is not an
implication (§43).

## 40. Literal SPOIL fails at three kept replies [computed exact]

Position (t, N) = (19/25, 19/10), omega = 7/50, base = 1/10; cells by co-type:
    K1∩K2∖K3 = 33/100, K1∩K3∖K2 = 57/100, K2∩K3∖K1 = 33/100, K2 only = 24/100, outside = 43/100
(K3 contains all of K1∖K2; |K_i| = 9/10). Existing readings: pairs 0.100, 0.440, 0.100 (>= base proved, §25), both
triples infeasible [float]. Request S = 212/1000 of "K2 only", 62/1000 of K1∩K2, 274/1000 of K1∩K3, 212/1000 of outside.
**Claim [computed exact].** For EVERY dump D some reading containing the new reply has need <= 199/2000 < base.
Certificate (`spoil_exact.py positions/p3a.json`): the dump polytope (5 free cells) is cut into 5 boxes; on each box
one triangle reading ((2,3,4) on four boxes, (1,2,4) on one) has an explicit feasible LP point with objective
<= 199/2000 at every vertex of the box, feasibility and objective recomputed in Fractions; need_R is convex in D, so
the bound holds on the box. Float: his best is 0.072 (gain 0.2·omega) [menu + 4000 random fills].
Frequency [computed float]: along self-play in which he answers with a RANDOM spoiling dump, her local search
(objective: number of spoiling dumps in his menu) found a request with no spoiler — menu, rich menu and 3000 random
priority fills — at 12 of 41 positions with 3 or 4 kept replies (N = 1.9). So SPOIL is a statement about a
strategy, not about positions: most spoiling dumps are blunders one request later.
Corrected statement **(SPOIL\*)**: he has a strategy under which min over readings of need stays >= base at every depth.

## 41. Two levels along one-step-robust play [computed float; both sides sampled]

`spoil_two.py`: he answers with a *robust* spoiler = a menu spoiler after which her search (20 candidates, three
120-step hunts, confirmation against the rich menu and 1500 random fills) finds no request without spoiler; menu
tried in order of co-degree. A request all of whose menu spoilers are non-robust is a two-request break.
18 runs (N = 1.82, 1.85, 1.9; six seeds; 45 min each, 24 cores):

| kept replies | requests tested | two-request breaks | first spoiler tried was robust |
|---|---|---|---|
| 2 | 180 | 0 | 177 |
| 3 | 180 | 0 | 173 |
| 4 | 40 | 0 | most (6 of the first 10 logged) |
| 5 | few (one run got there) | 1 | — |

Rows 2–3 agree with §26/§30: the highest-co-degree spoiler is almost always the right one, and where it is not
another is. **The hit** (`positions/p5_level2.json`; N = 1.9, five kept replies, all existing needs >= base): one
request S for which, of 2364 + 107 dumps sampled (rich menu, random fills, mixtures around the spoilers), 11 spoil —
all with >= 60% of the dump on the cell "K1, K2, K3 and no other" — and after each of the 11 she has a second request
with no spoiler found (one of them needed a 600-step hunt). Status: candidate. Not exact (his side is sampled at
both levels; a spoiler outside the sample at either level would void it); the position was reached against a
one-step-robust opponent, so it shows only that one-step robustness is not an invariant. A two-step-robust opponent
was not built (cost: about 1 h per request at five replies). Gain not measured.
Reading: the depth-2 and depth-3 "value = base" results do not extend unchanged to depth 5–6 for the rule the
earlier runs suggested ("whole dump on one unrequested cell of co-degree >= 2", 26.3); whether a better rule exists is
exactly SPOIL\*.

## 42. Dead routes [computed float]

- **Multi-pair triangle exhaustion.** Idea: q disjoint balanced pairs, S triangle-type for all of them, unrequested
  mass inside all q unions K_i∪K_j below omega, so every dump leaks >= (omega - f)/q outside some union. LP designs exist
  (`spoil_struct.py`, N = 1.96, q = 3, f = 0.15 < omega = 0.20) but he holds (his best 0.175–0.185 > base 0.16). Reason
  (`tri_test.py`): for a triangle-type request need = 2·(dump mass inside K_i∪K_j) - 2·eps, so a gain needs more than
  omega/2 + eps of the dump outside ONE union; q >= 2 pairs cannot force that. Dead.
- **One-level sampling as a test of SPOIL\*.** §32's "next step" (one-level solves at sampled positions) cannot decide
  it: literal breaks are frequent after non-robust dumps (§40) and absent after robust ones. Only game depth counts.
- **Frozen anti-plan, exchangeable in-cell version**: her greedy line wins in 5, 6, 7 replies at N = 1.82, 1.85, 1.9
  by exhausting O (he is forced onto a cell with exactly omega free) [one line each; his in-cell choices best-response
  from a menu]. Superseded by Theorems S/S+ and §46; not pursued.

## 43. What SPOIL\* would and would not give [proved by hand where stated]

- [proved, 29.2] A first-order strategy that survives m requests for every fixed m is a statement for k >= k_0(m):
  after m replies there are up to 2^m cells, and the mass model needs every cell >> 1. A family needs him to survive
  C(N,T) requests at ONE k. So SPOIL\* at all depths ⟹ "no bounded-depth first-order proof of CP", not ⟹ f(k,7) >=
  (3/4 + c)k. A disproof needs an explicit family.
- Theorems S/S+ (§36, §45) and §46 exclude stationary rules, exchangeable or ordered; §44 excludes the first
  request-dependent one. A SPOIL\* strategy must refine cells without bound or tie the dumped points to the request.
  The engine's adversary is of the first kind (cells created by the play), which is why it is not covered.
- (b) of the task: no T-covering family without a good seven was found or attempted beyond §44; every explicit
  family examined in Parts VIII–IX has one. The known constructions (complete family on k + T points) stop at 3k/4;
  nothing here beats them by any margin.

## 44. The one-bit rule: it has a good seven [computed exact at finite k; reason by hand, sketch]

Rule (`onebit.py`): cells O, U = A ∪ B, g = gL ∪ gR, each ordered. If |S∩O| < omega: dump = first omega unrequested
points of O, in forward order if |S∩A| >= |S∩B|, else backward. Otherwise dump = first omega unrequested points of U,
forward if |S∩gL| >= |S∩gR|, else backward. Four pools O^1, O^0, U^1, U^0 (needs o >= 2·omega, c - o >= omega).
Test as in 46.4: three pencil lines of ONE shape X ∈ {H1, H0, L1, L0} with the pool of X in the kernel class, four
transversal lines of mass <= T; integer design by MILP, then the rule applied verbatim to real sets and all pairs
checked by brute force.
Result: 89 instances — (k,T) = (40,31), (100,76), (200,151), n/k from 1.81 to 2.14, o on a grid — a good seven in every
one; L1 and L0 pencils work in all 89, H1/H0 in 55. (A 90th listed instance, (100,76,220,90), has c - o < omega: the
rule is not defined there; not a failure.)
Reason [by hand, sketch]: the bit is read on a cell disjoint from the pool, and she chooses the lines, so she gives
the three pencil lines the same bit (equal traces on the bit cell); the rule then acts on them as the single pool
rule of 46.2. The same works for any b bits read off profiles of cells she can split evenly among three lines.
Dead as a disproof candidate. The general bounded-bit statement is the proof side's §47.

**Exact remaining statement (this side).** SPOIL\*: existence of a first-order adversary strategy keeping need >= base
at every depth. Known: holds to depth 2 (§26, partly certified) and on sampled lines to depth 3–4 (§30, §41);
one sampled two-request break at five kept replies against the one-step rule (§41).
**Next step.** Make §41's hit exact or kill it: (i) rationalise `positions/p5_level2.json`; (ii) outer level: box
subdivision of the dump polytope as in `spoil_exact.py`, with "she has a second request with an exact no-spoiler
certificate" as the leaf test on the spoiler region (it is small: >= 60% of the dump on one cell); (iii) then ask
whether he could have avoided the position: rerun `spoil_two.py` with two-step-robust dumps at kept replies 3 and 4.
If the hit survives (i)–(iii), SPOIL\* is dead at depth 6 and the first-order game has a requester gain to extract.
Not done: any of that; exactness of §41; N >= 11/6 uses Fano readings only; old triple readings in §40 are float.

Self-check (Part IX): engine reproduces base for the balanced pair at the three N, 0 for D in g and 2w - 2·eps for the
triangle request (`tri_test.py`), and §26's "spoiler exists" at depth 2 (360 requests). `spoil_exact.py` asserts
masses (|K_i| = c, |S| = t) in Fractions and never trusts a float objective. The surviving spoiler of the first
fine scan in §41 was re-attacked with four seeds and broken four times. `onebit.py`'s verdict is the brute-force
pair check on replies produced by the rule itself; the MILP only proposes classes.

## 48. (structural side; INTERIM — stopped by the coordinator, handed to the pseudorandom-side agent) Hash-like selectors

Code: `compute/core8/sunflower_ramsey.py` (SAT, python-sat). Status of every item is tagged; nothing here is finished.

**48.1 The 2/3 of §47 cannot be sharpened for one class over one kernel [proved by hand, quoting Kleitman 1968].**
Over a fixed kernel the class-r halves are a family of k/2-subsets of a 3k/2-set with no three pairwise disjoint
members; Kleitman's theorem (the n = sk case of the Erdős matching problem) gives the maximum C(3k/2 - 1, k/2) = 2/3 of
all halves, attained by "all halves avoiding one point". That extremal selector is a one-point junta and dies by
Theorem W once the kernel is moved onto the point. So the right object is not a density over one kernel but the
hypergraph over ALL kernels:
**ℋ(k,T):** vertices = T-subsets of a ground set G, |G| = k + T (= V minus the head of one class); edges = perfect
sunflowers (three T-sets with one common pairwise intersection of T - k/2 points and union G). A selector avoids every
pencil frame of that head iff the requests it sends to that class form an independent set of ℋ.

**48.2 ℋ is not 2-colourable in the cases tested [computed exact, SAT, UNSAT = proof for that size].**
(k,T) = (4,3): 35 vertices, 105 edges, not 2-colourable, 3-colourable. (k,T) = (8,6): 3003 vertices, 525 525 edges, not
2-colourable (2 s). Running when stopped, NO result: 3-colourability at (8,6); 2-colourability at (8,7) and (4,2).
For one fixed kernel the hypergraph is the Kneser hypergraph KG³(3k/2, k/2), chromatic number 2 (Alon–Frankl–Lovász);
the extra edges from moving the kernel are what push it to 3.
Meaning, if it holds for all (k,T) [conjecture, not proved]: every 2-colouring of the T-subsets of G has a
monochromatic perfect sunflower.

**48.3 What 48.2 does NOT yet give [exact open step].** A greedy rule with classes a, b has two different grounds,
G_a = V∖Z_a and G_b = V∖Z_b. Non-2-colourability of ℋ on G_a yields a monochromatic sunflower covering G_a; if it is
all-a she wins, but if it is all-b it is not a b-frame (its three replies are S_i plus the ≺_b-first unrequested
points, which lie in the other petals or in Z_a), unless the orders are compatible (initial segments I_a, I_b with
|I_a ∩ I_b| >= ω and |I_a ∪ I_b| <= n - 3k/2, in which case one hole set serves both classes and she wins outright
[proved by hand: request (I_a ∪ I_b)∖Z, then the first ω unrequested points are Z in both orders]).
**Open step:** a two-ground version — for every 2-colouring of the T-subsets of V there is an all-a perfect sunflower of
V∖Z_a or an all-b perfect sunflower of V∖Z_b (heads taken relative to the requested gaps, as in 47.2). Smallest test:
SAT at (k,T,n) = (8,6,16) with ≺_b the reverse of ≺_a (about 10⁶ clauses; not run). For R classes one needs χ(ℋ) > R,
and already χ(ℋ(4,3)) = 3: **three classes may escape every pencil**; then Theorem T and Q' frames must be added.

**48.4 Parity selectors [proved by hand].** For a selector that is a function of the parity vector (|S ∩ E_j| mod 2)_j:
in an exact frame of class r the three parity vectors sum to v + z^r (mod 2); if neither colour class may contain such
a triple, both have exactly half the cube and are the two cosets of one hyperplane (a set of more than half of F_2^m has
A + A = F_2^m; equality case Kneser), so the selector is the parity of |S ∩ E| for ONE set E; one requested junk point
per pencil line (slack 3 points, available once eps·k >= 3) flips it. Parity-type selectors therefore lose.

**48.5 Non-greedy rules: not started.** Only the observation that every member of a greedy rule contains the head of
its class relative to its request, so "re-greedifying" a request-dependent in-cell choice by a fixed order replaces
each member S ∪ D(S) by S ∪ (first points), which is a different family: T-covering is kept (replies are redefined, not
removed), but "no good seven" is not known to transfer in either direction. No reduction and no obstruction proved.

Self-check (§48): 48.1 is a citation, not re-proved. 48.2: UNSAT results from Cadical with one symmetry-breaking unit
clause (colour of one vertex), which is sound; edge counts match C(g, q) x (3k/2)!/((k/2)!³·3!). 48.4's additive step
uses |A| > 2^(m-1) ⟹ A + A = F_2^m (pigeonhole) and the structure of sets of size exactly 2^(m-1) with A + A ≠ F_2^m;
written from memory, not machine-checked. The "three classes may escape" sentence is an inference from one tiny case.

=============================================================================================
# Part X — structure vs randomness: junta and spread approximation (§50–§54; others use §55+)

Brief: can an arbitrary T-covering family be split into a junta-like core (killed by S/S+/W/P) plus a spread
remainder (handed to the pseudorandom side)? Code: `compute/spread/spread_params.py` (exponent table, < 1 s),
`compute/spread/kz_request.py` (Kupavskii–Zakharov procedure on the request measure, exact Fractions, 2 s).
Window: 3t - 1/2 < N < 3 - t (LEDGER: 21.2 has a gap).
**Outcome.**
(1) Junta approximation in measure is dead in both normalisations, and the cited theorems do not apply to the
confined setting at all (§51).
(2) The standard spread lemmas are vacuous here. A family of (N-1)k-sets on Nk points is at most N/(N-1) <= 2.28-spread,
and the lemmas need spreadness above 32, or above log k (§52).
(3) The only notion with content is spreadness *relative to the complete family* (KZ "homogeneity"). Run on the request
measure, the KZ procedure gives a decomposition that always exists (Prop. 53.1, proved). It is not a reduction:
- its structured output is a selector over pool heads, which is exactly the open object of §47.5/§48, and the
  decomposition carries no information about the selector (53.3);
- its spread output is not "random": profile structure and greedy rules with more than e^{0.025k} classes pass as
  spread (53.4);
- for N >= N*(t) (2.157 at t = 0.76) no useful τ exists (53.2).
The spread condition it outputs is stated in §54 for the pseudorandom side. **No reduction of CP is obtained.**

## 50. What was read, what was recalled

- Kupavskii–Zakharov, *Spread approximations for forbidden intersections problems*, arXiv:2203.13379v3. Read in the
  HTML version (the PDF text extraction lost the symbols). Read:
  - the definitions of r-spread (μ({F : X ⊂ F}) <= r^{-|X|}) and of (r, q)-spread;
  - Theorem 4, the spread lemma (ALWZ as sharpened by Tao): Pr[W contains a member] >= 1 - (5/log₂(rδ))^m·|μ| for W
    an (mδ)-random set;
  - Theorem 8: hypotheses n > 2¹²τk·log₂(2k), n >= 2qτk and q >= t; remainder |ℱ'| <= τ^{-q-1}·C(n,k);
  - the definitions of τ-homogeneous and (𝒜, τ)-homogeneous;
  - Observation 5 (τ-homogeneous ⟹ n/(τk)-spread), Observation 7, and Lemma 10 (the procedure; remainder <= τ^{-q-1}|𝒜|).

  All the main results need k <= n/(C log n), or k polynomially smaller than n. [literature, checked]
- Keller–Lifshitz, *The junta method for hypergraphs and the Erdős–Chvátal simplex conjecture*, arXiv:1707.02643
  (Adv. Math. 392, 2021). Read the first half (ar5iv HTML). Theorem 1.2: for a fixed ℋ and C < k < n/C there is an
  ℋ⁺-free j-junta 𝒥 with |ℱ∖𝒥| <= max(e^{-k/C}, Ck/n)·|𝒥|. ℋ⁺ is the expansion (each edge padded with distinct new
  vertices); "d-expanded" means the expansion of a d-uniform multi-hypergraph. [literature, checked]
- Dinur–Friedgut (CPC 2009), only as quoted in Keller–Lifshitz Lemma 2.8: if k/n <= p/2 and μ_p(ℱ↑) <= 1 - ζ, then ℱ is
  (s, (k/n)^r)-capturable. [literature, checked as cited; original not read]
- Not read; recalled only:
  - Alweiss–Lovett–Wu–Zhang (used only through KZ's Theorem 4);
  - Frankston–Kahn–Narayanan–Park (p_c <= K·q_f·log ℓ for ℓ-bounded families);
  - Park–Pham;
  - Keevash–Lifshitz–Long–Minzer (global hypercontractivity).

## 51. (1) Junta approximation in measure: dead

**51.1 The cited theorems do not apply [proved by hand].**
- *No expansions fit.* In the confined setting |V| = n = Nk < 2.24k. Two edges of an expansion ℋ⁺ of a fixed ℋ share at
  most |V(ℋ)| = O(1) vertices. So an ℋ⁺ with m edges needs at least m(k - O(1)) vertices, and m <= N + o(1) < 3. No
  expansion with three or more edges fits in V. The same holds in co-edge form: m(c - O(1)) <= n gives
  m <= N/(N-1) + o(1) < 3. So every family on V is ℋ⁺-free for every ℋ with at least three edges.
- *The forbidden configuration is not an expansion.* "No good seven" (no seven members covering all pairs) is not
  ℋ⁺-freeness for any fixed ℋ: a Fano blow-up has no private vertices at all.
- *The ranges do not match.* Keller–Lifshitz needs k < n/C, and here k/n = 1/N > 0.44. Dinur–Friedgut's error
  (k/n)^r is a constant here (k/n and c/n are both near 1/2), not o(1).

**51.2 Both normalisations fail [proved by hand].**
(a) *Absolute error* (relative to |𝒥|, C(n,k) or C(n-1,k-1)). A T-covering family can have density e^{-γk}, with
γ = ln C(n-T, ω)/k = (N-t)·h(ω/(N-t)) running from 0.135 to 0.92 across the window ([computed float], table 53.2).
Every nonempty dense junta meets the error bound, so the bound says nothing about 𝒞.
(b) *Relative error* (|𝒞 Δ 𝒥| <= ε|𝒞|). This fails for spread families. A nonempty j-junta of c-sets has density
>= e^{-O(j)}. A family of density e^{-Θ(k)} that no j-coordinate pattern concentrates therefore has |𝒥∖𝒞| >> |𝒞| for
every j-junta 𝒥 ⊇ (1-ε)𝒞, when j = o(k). Example: the fully random reply family (each request gets an independent
uniform dump). Its request measure is uniform on 𝒜 (53.1(c)), and its member density is C(n,T)/C(n,c) = e^{-Θ(k)},
because c is closer to n/2 than T is whenever N > 1 + t.

§39 already killed *exact* profile approximation; approximation in measure is dead too. The obstruction is the
density e^{-γk}, as the brief feared. On top of that, the confined geometry leaves no room for the configurations the
junta method needs.

## 52. (2) Spread lemmas: vacuous in this regime

**52.1 The ALWZ/Tao lemma [proved by hand].** For ℱ ⊆ C(V, c), Σ_x |ℱ(x)| = c|ℱ|, so some point has
|ℱ(x)| >= (c/n)|ℱ|. Hence no family of co-edges is more than n/c-spread, and no edge family is more than
n/k-spread. Here n/c = N/(N-1) ∈ (1.81, 2.28), and n/k < 0.57. KZ's Theorem 4 bound 1 - (5/log₂(rδ))^m·|μ| is
positive only if rδ > 32, and δ <= 1 (W is (mδ)-random with m >= 1), so it would need r > 32.
**Dead for every family in the window, at every k.**

**52.2 FKNP [recalled + proved by hand].** FKNP gives p_c <= K·q_f·log ℓ, with ℓ = k or c here (linear in k). Taking
the fractional cover g = 1 on the edges themselves gives q_f >= (2|H|)^{-1/ℓ} >= 2^{-N-o(1)}, a constant. So the
bound exceeds 1 for large k. Dead.

**52.3 What survives.** Only spreadness *relative to the complete family* has content: KZ's (𝒜, τ)-homogeneity. As
plain spreadness it is useless: Observation 5 converts it to n/(τc)-spreadness, which is below 2.28/τ. KZ use
homogeneity only to feed Theorem 4 (52.1). I know of no sampling lemma for homogeneous families at uniformity about
n/2 and density e^{-γk}. The nearest tool is global hypercontractivity (KLLM). [recalled; not checked whether it
reaches density e^{-γk} with γ of order 1]

## 53. The relative decomposition: it exists, and why it is not a reduction

**Setup.** Fix a reply choice F: C(V,T) → 𝒞 with F(S) ⊇ S. Let ν be the push-forward of the uniform measure on
requests (the *request measure*). Then ν(K) <= M := C(c,T)/C(n,T) for every K, and |𝒜|·M = C(n-T, ω) = e^{γk + o(k)},
where 𝒜 = C(V, c). For a head B (|B| = b) write 𝒜(B) for the co-edges containing B.

**53.1 Proposition (KZ Lemma 10 in the request measure) [proved by hand; KZ's proof with |·| replaced by ν].**
For every τ > 1 and q <= c there are disjoint request classes R_1, ..., R_m, R_rem and heads B_1, ..., B_m with
|B_i| <= q such that:
 (i) F(S) ⊇ S ∪ B_i for S ∈ R_i;
 (ii) each piece is homogeneous relative to its head: if ν_i is the law of F(S) for S uniform in R_i, then
  ν_i(K ⊇ B_i ∪ X) <= τ^{|X|}·|𝒜(B_i ∪ X)|/|𝒜(B_i)| for every X;
 (iii) ν(R_rem) <= τ^{-q-1}·|𝒜|·M = τ^{-q-1}·e^{γk+o(k)}.
*Proof.* Start with ν^1 = ν. At step i let B_i be an inclusion-maximal set with
ν^i(K ⊇ B_i) >= τ^{|B_i|}·(|𝒜(B_i)|/|𝒜|)·ν^i(total). The set ∅ qualifies, so B_i exists. Stop if |B_i| > q.
Otherwise let R_i be the remaining requests whose reply contains B_i, remove them, and continue.
(ii): if some X violated (ii), then B_i ∪ X would qualify at step i, against maximality (KZ Obs. 7).
(iii): at the stopping step, ν^m(total) <= τ^{-|B_m|}·(|𝒜|/|𝒜(B_m)|)·ν^m(K ⊇ B_m) <= τ^{-q-1}·|𝒜|·M, because
ν^m(K ⊇ B_m) <= |𝒜(B_m)|·M. ∎
Examples [proved by hand]:
 (a) the pool family: one piece, with head B_1 ⊇ Y;
 (b) a greedy rule with a bounded number of classes: each class head Z_r is selected once ν(R_r) >= τ^ω·|𝒜(Z_r)|/|𝒜|
  (53.3);
 (c) the fully random reply family: S ∪ D is a uniform c-set, so ν is uniform on 𝒜 and 1-homogeneous; one piece,
  B = ∅.
Exact check (`kz_request.py`, (n,k,T) = (12,5,4), τ = 9/5, which lies between τ_0 = 1.776 and τ_pool = 1.846 of 53.2):
- pool rule: heads {0,1,2,8,9,10}, {0,1,2,8}, {0,1,2}, all containing the pool;
- three-class greedy rules: one headless piece, the same for a 2-point junta selector and for a random hash selector.
Homogeneity (ii) and the bound (iii) are asserted in Fractions. [computed exact; sanity sizes, outside the window]

**53.2 Parameters: the heads are linear, and for large N no τ is useful [computed float; exact log-binomials at
k = 4000 agree with the entropy forms to 0.001].** Two thresholds decide whether the decomposition has content:
- τ_0 = e^{γ/c}. A member carrying the maximal request mass M passes the selection test at X = K iff τ <= τ_0
  (M >= τ^c/|𝒜| ⟺ τ^c <= e^{γk}). Below τ_0, a minimal family decomposes into single members: the trivial
  decomposition.
- τ_pool = (|𝒜|/|𝒜(Y)|)^{1/ω}, with |Y| = ω. The pool family's head Y is selected iff τ <= τ_pool.

So the useful range is τ_0 < τ < τ_pool. There, (iii) needs q >= γk/ln τ ∈ (γk/ln τ_pool, ck).

| N (t = 0.76) | ω | n/c | γ | τ_0 | τ_pool | q range γ/ln τ_pool .. c | T/k - 1/2 | ρ_hom(τ_m) | Φ/2 |
|---|---|---|---|---|---|---|---|---|---|
| 1.79 | 0.03 | 2.27 | 0.135 | 1.19 | 2.29 | 0.16 .. 0.79 | 0.26 | 0.010 | 1.19 |
| 1.85 | 0.09 | 2.18 | 0.310 | 1.44 | 2.24 | 0.38 .. 0.85 | 0.26 | 0.020 | 1.19 |
| 1.90 | 0.14 | 2.11 | 0.424 | 1.60 | 2.21 | 0.54 .. 0.90 | 0.26 | 0.022 | 1.19 |
| 2.00 | 0.24 | 2.00 | 0.608 | 1.84 | 2.14 | 0.80 .. 1.00 | 0.26 | 0.018 | 1.19 |
| 2.10 | 0.34 | 1.91 | 0.758 | 1.99 | 2.08 | 1.03 .. 1.10 | 0.26 | 0.008 | 1.19 |
| 2.20 | 0.44 | 1.83 | 0.885 | 2.09 | 2.03 | empty | 0.26 | — | 1.19 |

(τ_m = (τ_0·τ_pool)^{1/2}; ρ_hom and Φ are defined in 53.4(b).)
The useful range is empty for N >= N*(t): N* = 2.1475, 2.1519, 2.1574, 2.1685 at t = 0.751, 0.755, 0.76, 0.77. At
t = 0.8 the range is nonempty across the whole window. Conclusions:
(α) The heads are linear: q > 0.16k everywhere, and q exceeds W's window T - k/2 for N >= 1.82. The "junta core" is a
core of (0.4–1.0)k named points, not a junta.
(β) For N >= N*(t), every choice of τ either decomposes minimal families into single members or hides the pool head.
The decomposition degenerates there.

**53.3 The structured output is the open selector problem [proved by hand].** Call a piece *full* when its head is a
full pool: |B_i ∖ S| = ω for S ∈ R_i, so F(S) = S ∪ B_i. On the union of the full pieces the family is a greedy rule
(§47.1) with selector σ(S) = i and heads B_i. Z_r is selected whenever ν(R_r) >= τ^ω·|𝒜(Z_r)|/|𝒜|, since
ν(K ⊇ Z_r) >= ν(R_r), whatever σ does inside the classes. So a junta selector (window <= T - k/2, dead by Theorem W)
and a hash-like selector with the same class masses (open: §47.5(i), §48) both produce the heads Z_r. The exact run
in 53.1 is an instance at small size. What Theorem W uses, that one class contains the three requests of a frame, is
a property of σ on frames, and homogeneity statements about the laws ν_i cannot see it. Whether a hash selector
separates every frame is the colouring problem ℋ(k,T) of §48, and the decomposition adds nothing to it.
**The structured side of the decomposition is (Σ) for greedy rules with arbitrary selectors and heads up to q, i.e.
the open problem itself.** Dead as a reduction.

**53.4 The spread output is not random.**
(a) *Profile structure passes [proved by hand for X inside one cell; heuristic for mixed X].* Homogeneity tests only
principal up-sets 𝒞(X), the same restrictions that globalness uses. A symmetric profile family whose cell densities
π_j/v_j are within a factor τ of c/n passes the test (for X inside one cell, by the hypergeometric product bound).
Theorem S kills such families, but their hash-like in-cell variants (§46.5, 47.5(4)) pass the test too.
(b) *Numerous pool heads pass [selection threshold computed float; pencil count a first-moment heuristic].* Take a
greedy rule with R = e^{ρk} classes, random heads of mass ω and a random selector. Class r has ν-mass about e^{-ρk},
so its head is selected iff ρ <= ρ_hom := -ω·ln τ - ln(|𝒜(Z)|/|𝒜|)/k, which is <= 0.022 at τ = τ_m (table). The
expected number of pencil frames whose three requests fall in one class is e^{(Φ - 2ρ)k}. Here
Φ = (1+t)·h((t - 1/2)/(1+t)) + (3/2)·ln 3 = 2.385 is the log-count of frames around a head. That number is
exponentially large for ρ < Φ/2 = 1.19; for comparison, the number of requests is e^{(1.22..1.43)k}. This is a
first moment only, with no second moment. So for 0.022 < ρ < 1.19 the family is "spread" at every useful τ, yet the
certificate that should beat it is the head-based pencil of Theorem W/P. **The pseudorandom side cannot assume
that spread pieces have no pool heads.**
(c) *Pieces are partial [proved by hand].* A piece answers only its own requests R_i, so it is not T-covering, and
there can be exponentially many pieces (as in (b)). A good seven may need requests from several pieces, which is
again §48.

## 54. The exact decomposition statement, its obstruction, and what goes to the pseudorandom side

**(DEC) [proved: Prop. 53.1].** Every reply map of every T-covering family splits the requests into classes R_i with
heads B_i (|B_i| <= q, for any q >= (γ + η)k/ln τ), plus a remainder of request mass <= e^{-ηk + o(k)}. Each class
satisfies H_τ below.
**Needed for a reduction (not proved; blocked):**
 (DEC-S) every family made of full pieces (pool heads) under an arbitrary selector has a good seven. This is (Σ) for
  hash-like greedy rules, §47.5(i)/§48. (DEC) gives no extra information on the selector (53.3).
 (DEC-R) every family whose pieces satisfy H_τ has a good seven, using members from several pieces if needed.
 (DEC-mix) the two combine: one good seven built from structured and spread pieces together.
Obstructions: 53.3 for (DEC-S); 53.4(b–c) for (DEC-R). For N >= N*(t) no useful τ exists, so (DEC) is trivial there
(53.2β).
**Condition H_τ, stated precisely for the pseudorandom side.** A class R ⊆ C(V,T) with head B (|B| = b, possibly ∅) is
*τ-homogeneous* if F(S) ⊇ B for all S ∈ R and, for S uniform in R and every X ⊆ V∖B,
  Pr[X ⊆ F(S)] <= τ^{|X|}·C(n-b-|X|, c-b-|X|)/C(n-b, c-b),
with τ_0 = e^{γ/c} < τ < τ_pool. This range is nonempty only for N < N*(t).
What H_τ does NOT give (all shown above):
- T-covering of the piece, or any lower bound on |R|: pieces can have request mass e^{-ρk};
- absence of pool heads when the classes are numerous (53.4b);
- absence of profile or threshold structure (53.4a);
- any sampling or spread lemma (52.1).
H_τ is strictly weaker than "random". A theorem proved under H_τ alone must handle 53.4(a) and (b) as special cases.
**Dead (this part):**
- junta approximation in measure, in both normalisations (51.2);
- Keller–Lifshitz and Dinur–Friedgut in the confined setting (51.1);
- the ALWZ/Tao spread lemma, and FKNP (52.1–52.2);
- spread approximation as a reduction of CP to S/S+/W plus a spread remainder (53.3);
- any decomposition with sublinear heads (53.2α).
**Exact gap.** Unchanged: (Σ) for hash-like selectors and for non-greedy rules. (DEC) only restates it as "a selector
over at most e^{O(k)} pool-headed classes with homogeneous links".
**Next step [heuristic].** The only quantitative lever found is 53.4(b): a uniformly random selector loses by the
first moment unless it has e^{1.19k} classes, nearly one class per request. A second-moment (Janson) version for
selectors that are merely *balanced on pencil frames* would turn the §48 colouring problem into a counting
statement. That belongs with the hash-selector work, not with spread approximation.

Self-check (Part X):
- 51.1 is vertex counting (m·(k - O(1)) <= n). 52.1 is averaging plus Theorem 4's bound at δ <= 1.
- 53.1 follows KZ Lemma 10 line by line. The only change is ν(K ⊇ B) <= |𝒜(B)|·M, which uses |F^{-1}(K)| <= C(c,T).
  It was asserted exactly on three families.
- 53.2's thresholds come from the selection test at X = K and X = Y. They were evaluated by `spread_params.py` with
  exact log-binomials; the entropy forms agree to 0.001.
- 53.4(b): Φ is the frame count of §47.2 (kernel ⊇ head, three halves), checked by log-binomial at k = 4000 (2.381
  against 2.385). The first moment is not a proof.
- KZ, KL and DF statements are quoted from the HTML texts as read (DF only through KL's Lemma 2.8). ALWZ beyond KZ's
  Theorem 4, FKNP, Park–Pham and KLLM are from memory.

## 60. Five-reply candidate of §41: stronger dumps do not save him; the break is not exact [verdict: UNDECIDED, survives in float]

**Run.** (a) `p5_strong.py` (his dump is hill-climbed at the inner level, 150 outer dumps near cell 123, 10 workers): 17 outer
spoilers reached the test, 16 "broken" (her S2 held against the climb), 1 "ROBUST" (outer dump index 80,
{123: 0.13128, 12345: 0.00872}; three S2 each answered by a climbed dump). (b) `p5_verify.py` re-attacked that one dump:
12 seeds x 15 min, break1 (300 iters, 30 candidates) then climb. (c) `spoil_three.py` (two-step-robust dumps at 3 kept
replies, one request tested per row). (d) `spoil_exact_p5.py` (new): exact check of the outer dump. Processes were killed at
the 15-20 min mark.

| item | result | tag |
|---|---|---|
| p5_strong, outer spoilers tested | 17: 16 broken, 1 robust (idx 80) | float |
| p5_verify on idx 80: S2 found / answered by climb / not answered | 43 / 18 / 25 (8 more attempts found no S2) | float |
| seeds with at least one unanswered S2 | 12 of 12; best climbed need among them 0.0835 to 0.099999 vs base 0.1 | float |
| spoil_three, N = 1.9, 3 kept replies (4 seeds) | 5 rows, every one robust2 (one request, one robust1 spoiler, robust2) | float |
| spoil_three, N = 1.82 and 1.85 | 1 row each (robust2); other seeds cut by the time limit, incomplete | float |
| exact check, 5-reply position, S as stored, D = {123: 131/1000, 12345: 9/1000} (also a = 7/50) | all 180 readings with the new reply and all 70 old readings have need >= 1/10 = base (min exactly 1/10, tight on reading (1,2,3,6) pattern 0; next 0.103) | exact |

Exact part: position and S are rational (denominators 4300), asserted in Fractions (|S| = 19/25, each co-edge 9/10); for each reading
the bound sum y mu - t sum z + omega sum min(0, 1 - z) with rationalised z and y = min over columns is dual feasible, so it is a
rigorous lower bound; z came from HiGHS. 159 of the 180 new-reply readings (52 of 70 old) are LP-infeasible, which is
only established in float. So dump 80's family (cells 123 and 12345 only, a up to 7/50) is an exact spoiler of the stored S.

**Reading.** The stronger dump does not avoid the position: the one ROBUST verdict of the first pass was three lucky
S2 draws; with 12 independent seeds every one finds a request on which his climb fails (25 of 43), though some climbs end within
1.5e-6 of base, so those need not be genuine. The candidate break therefore survives both attacks I made. It is NOT
exact: his side is a menu plus hill-climb at both levels, and her second request is only certified by his failure to
climb. An exact break would need the box subdivision of §40 on the 6-reply dump polytope (about 20 cells) for one S2; not done.
Three-level (robust2) runs at 3 kept replies find no break, so the position was not avoided by two-step care at depth 3;
the two-step-robust test at kept replies 4 was not run.

**Verdict: UNDECIDED. Candidate break not killed (float evidence for it), not exact. §43/§44's "next step" (i)-(ii) is half
done: the outer level of one spoiler is exact, the inner level is not.**
Files: `compute/core/p5_verify.py`, `spoil_exact_p5.py`, `logs/p5_verify_80_*.log`, `logs/p5_strong_*.log`, `logs/three_*.log`.

=============================================================================================
# Part (§75–§79) — flag algebras / type-space relaxations on the compactness limit

Code: `compute/flag/` — `fano.py` (need LP, members labelled by Fano points), `pair_steer.py`, `robust3.py` (level-3
robust LP), `scan3.py`; logs `compute/flag/logs_scan3_*.txt`. Run with `py -3.14` (scipy is missing from the default 3.15).
No SDP solver is installed (cvxpy, SCS, CVXOPT all absent); none was installed, and 76.1 shows none is needed.
**Outcome. CP is NOT proved and no counterexample candidate is produced. The flag-algebra method is DEAD here, for
proved reasons:** (i) the semidefinite (Cauchy–Schwarz) part is vacuous on this limit object (76.1); (ii) neither the
hypothesis (T-covering) nor the conclusion (a good seven) is a density statement — good sevens have density → 0 even
in families that satisfy CP (76.2); (iii) the only sound relaxation hierarchy on the type space is the bounded-depth
first-order game (76.3), which Parts VI–IX already compute. Two corrections to §39.3: "no good seven" does not pass
to the limit (75.2); a transfer lemma with t' < t is what makes a first-order win a certificate (75.3). Computed: the
lowest levels of the hierarchy stop exactly at the window's lower edge N = 3t − 1/2 (77.1 proved by hand, 77.2 float).
(Compatible with Part XI §83, which kills LP relaxations of the hitting-set side; this part kills the density side.)

## 75. The limit object as a type space

**75.1 Definition.** Parameters (t, N), c = N − 1, ω = N − 1 − t. A *q-type* is μ ∈ R_{>=0}^{P([q])} with
Σ_I μ_I = N and Σ_{I ∋ i} μ_I = c for each i (μ_I = mass of points of co-type I; equivalently N times the law of the
co-type of a random point — this is the only "density of a q-point Venn configuration" there is). A *type system*
𝒯 = (𝒯_q)_{q>=1}: nonempty closed sets of q-types with
- (C) closure under permuting members and under marginals (forgetting a member);
- (E) extension: for μ ∈ 𝒯_q and every request s with 0 <= s <= μ, Σ s = t, some μ' ∈ 𝒯_{q+1} has marginal μ on [q] and
  μ'_{I ∪ {q+1}} >= s_I for every I (the new member contains s);
- (A) avoidance: no type in 𝒯_q (q >= 7) has a 7-marginal supported on nonempty, pairwise intersecting co-types.
Check against §39.3 [proved by hand]: (C) and (E) are §39.3's closure and extension property, and they pass to
Hausdorff limits of the finite-k systems 𝒯_q^{(k)} (for (E): approximate s by an integral request at level k, take the
reply, pass to a convergent subsequence; μ' >= s is a closed condition). Systems with (C), (E) are exactly the position
sets of first-order adversary strategies, as §39.3 says. (A) is where §39.3 needs correcting.

**75.2 (A) does not pass to the limit [proved by hand].** Goodness of a 7-type is the closed condition b(μ) = 0
(b = mass on bad cells), so "no good seven" is open, and limits of bad types can be good. It happens for the extremal
family itself. Let 𝒞_k = all (n − k)-subsets of an n-set, n = ⌈7k/4⌉ − 1, T = n − k (T-covering: τ(K_n^(k)) = n − k + 1).
No good seven at finite k: seven c-sets (c = n − k) covering all pairs put every point in >= 3 of them (a point in <= 2
sees at most 2(c − 1) < n − 1 others, as n > 2c − 1), so 7c >= 3n, i.e. n >= 7k/4 — false. But the limit (t, N) = (3/4, 7/4)
of 𝒞_k contains every type with the right marginals (all are realised up to rounding), among them the Fano blow-up
(seven classes of mass 1/4, lines of mass 3/4 = c), which is good. **So the limit of a (7,2) family can contain good
sevens: "limit object = a winning adversary strategy" is false as stated.** What survives is (C) + (E), plus 75.3.

**75.3 Transfer lemma [proved by hand].** Suppose that for some m, some t' < t and all N' in a neighbourhood U of N she
has a strategy winning G_∞(t', N') within m requests against every system with (C), (E) (= every first-order
adversary). Then for all large k, every T-covering family of c-sets with T >= tk, |V| = N'k, N' ∈ U, has a good seven.
*Proof.* At finite k a position IS an exact cell vector (divided by k). Her strategy gives a profile s of mass t'; she
requests ⌈s_I k⌉ points of each cell I (possible: cells are integral and s <= μ) and pads to T; rounding costs at most
2^m points <= (t − t')k once k >= 2^m/(t − t'). Each reply has mass c and contains a set of profile >= s, so the play is a
legal play of G_∞(t', N') on exact positions, and her leaf condition (a good seven) is checked on the real sets. ∎
Nothing holds in the other direction: an adversary surviving every finite depth is not a family (§43).
Consequence: **the correct limit-level form of CP is "she wins G_∞ at finite depth on a neighbourhood of (t', N),
t' < t"**, not "every type system violates (A)" (false at t = 3/4 by 75.2, so not the right object just above 3/4 either).

**75.4 What carries a measure [proved by hand].** Point side: given a q-tuple, r random points have independent
co-types (law μ/N each): points carry no relations among themselves, and every set of r <= T points lies in a member, so
r-point traces of 𝒞 are complete. Member side: no measure at all — 𝒯_q is a set; (E) is a ∀∃ statement on it, (A) a ∀
statement on 𝒯_7, and the alternation of (E) is unbounded.

## 76. The flag-algebra relaxation, and why it is empty

**76.1 Positivity is vacuous [proved by hand].** Razborov's constraints are ⟦(Σ a_i F_i)^2⟧_σ >= 0 for σ-flags F_i
over a type σ. Here σ is a tuple of members, and a flag can only add points (adding members is not a sampling
operation: there is no measure on members). Point flags multiply independently, p(F_i F_j) = μ_{I_i} μ_{I_j} / N^2, so
every Gram matrix is rank one and PSD for every μ — no constraint beyond μ >= 0. And every μ >= 0 with the marginals is
realisable (atomless limit; at finite k up to rounding). So the level-q "flag algebra" is the polytope of q-types; there
is no SDP to solve.
**76.2 No density formulation of CP [proved by hand].** Let 𝒞 be the complete family (all c-sets) on V, N >= 7/4:
T-covering, and it HAS good sevens (the Fano blow-up needs 3N <= 7c, i.e. N >= 7/4). Under the uniform (the only
Sym(V)-invariant) measure a random 7-tuple has co-type masses concentrated at N p^{|I|}(1 − p)^{7−|I|}, p = c/N, so
μ_∅ ≈ N(1 − p)^7 > 0 and the tuple is bad with probability 1 − e^{−Ω(k)}. Hence the density of good sevens tends to 0 in a
family satisfying CP: every flag inequality "d(good) >= λ > 0" is false there, and "d(good) >= 0" is empty. (Part XI §83's
second item is the finite-k form: a full-support measure sees a good seven with positive, but here e^{−Ω(k)}, probability;
the limit loses it.) T-covering is not a density condition either: by 39.2 a T-covering family can have density e^{−γk}
in every class. A flag-algebra certificate is a ∀-statement linear in densities (alternation depth 1); CP is ∀∃∀∃…
(iterated (E)) followed by ∃ (a good seven). No density functional sees it.
**76.3 The sound hierarchy is the game [proved by hand].** Level-m relaxation 𝓡_m(t, N): systems (𝒯_q)_{q<=m} with (C),
(E) for q < m and (A) for q <= m. 𝓡_m is feasible iff he survives m requests in G_∞(t, N) (positions reachable under his
strategy form such a system; conversely a system is a strategy: answer with any extension type). 𝓡_{m+1} feasible ⇒ 𝓡_m
feasible. By 75.3, infeasibility of 𝓡_m on a neighbourhood of (t', N), t' < t, certifies CP at (t, N). This is §29.2(a)
in type language; "flag algebra at level q" adds only 76.1, i.e. nothing.
**76.4 Trivial levels.** 𝓡_m is feasible for every t when m <= 6 (no seven exists; the complete family gives (E)).

## 77. The hierarchy solved at its lowest levels

**77.1 Level 7 through a steered pair [proved by hand; `pair_steer.py` agrees in float].** Label K_1, K_2 by Fano points
0, 1 (all pairs are equivalent); the position is o = |K_1 ∩ K_2|; cells O = o, A = B = c − o, g = 2 − N + o. Let Z be the
set of o for which the five future lines can all be requested as they stand (pair need = 0, §25).
*Claim.* Z = [N − 2t, 3t − 2]; so Z ≠ ∅ iff N <= 5t − 2 (base <= 0), and |Z| = 5t − 2 − N = −base.
*Necessity.* Every line other than {0,1,2} meets the four future points {3,4,5,6} twice, and only points of O can sit on
{0,1,2}; so 2(N − o) <= Σ_{j=3..6} |L_j| <= 4t gives o >= N − 2t. Let y = mass of O not on {0,1,2}. Every class of g sits on a
line through 2 (the lines avoiding 0 and 1 are {2,3,6}, {2,4,5}), so t >= |L_2| >= (o − y) + g, i.e. y >= 2o + 2 − N − t. Counting
future incidences (O on {0,1,2}: 1; other points of O, and A, B: >= 2; g: 3) gives 5t >= Σ_{j=2..6} |L_j| >= N + 2 + y.
Together o <= 3t − 2.
*Sufficiency.* O: o − y on {0,1,2}, y/4 on each of {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}; A in halves on {0,3,4}, {0,5,6}; B in halves
on {1,3,5}, {1,4,6}; g in halves on {2,3,6}, {2,4,5}. Then |L_2| = 2o + 2 − N − y and |L_3| = … = |L_6| = (y + N − o)/2, and some
y ∈ [0, o] makes both <= t iff N − 2t <= o <= 3t − 2. ∎ (LP: Z = [0.27, 0.28] at (0.76, 1.79), [0.31, 0.34] at (0.78, 1.87),
[0.35, 0.40] at (0.8, 1.95), grids 0.0025–0.01.)
*Steering.* After S_2 with |S_2 ∩ K_1| = x, the unrequested mass outside K_1 is 1 − t + x >= 1 − t > ω (as N < 2), so his
dump puts any d ∈ [0, min(ω, c − x)] into K_1 and o = x + d is his choice in an interval of length min(ω, c − x); c ∉ Z.
Hence the steered pair wins (2 + 5 = 7 requests) iff |Z| >= ω, i.e. **N <= 3t − 1/2: exactly TWIN 16.A's line**. This level
sees nothing of the window. His extremal answer: o at the end of [x, x + ω] outside Z.

**77.2 Three adaptive replies, then a static finish [computed float; her S_3 class restricted].** `robust3.py`: for a
pair position o, look for S_3 (profile on O, A, B, g) such that EVERY dump leaves some reading — pairs {1,2}, {1,3}, {2,3},
or the triple labelled collinear or as a triangle (ordered triples of each kind are equivalent under GL(3,2)) — with all
future lines <= t (7 or 8 requests in all). Restriction: each cell is either exhausted by S_3 or keeps >= ω unrequested;
then the dump polytope has vertices ω·e_j, and one LP (S_3 shared, one class assignment per vertex) decides a
single-reading win; per-vertex mixed readings are accepted only after a grid check of the dump simplex (286 points).
Exhausting cells is included (the pool mechanism); partial exhaustion (0 < unrequested < ω) is not.

| (t, N) | ω | 2ε / 4ε | Z | o scanned | S_3 found |
|---|---|---|---|---|---|
| 0.76, 1.79 | 0.03 | 0.02 / 0.04 | [0.27, 0.28] | [0, 0.79] step 0.026; [0.25, 0.30] step 0.0025 | only for o ∈ Z (pair reading) |
| 0.78, 1.87 | 0.09 | 0.06 / 0.12 | [0.31, 0.34] | [0.25, 0.40] step 0.01 | only for o ∈ Z |
| 0.80, 1.95 | 0.15 | 0.10 / 0.20 | [0.35, 0.40] | [0.30, 0.46] step 0.01 | only for o ∈ Z |

All three points lie in the lower strip 3t − 1/2 < N <= 5t − 2. Within this class the third reply never repairs a pair
that he steered out of Z, so this level's threshold is again N = 3t − 1/2. This matches 9.1 (the third reply can be made
to waste ω against the pair) where 9.1's hypothesis 3ω <= o holds (only the first point).
**77.3 Deeper levels [repo results, not re-run].** At t = 0.76 the exact tilted-spread tree (REDTEAM §14, CORE §20–21)
wins at N = 1.80 = 5t − 2, so 𝓡_m is infeasible there at that tree's depth; nothing in between is known, and 21.2 (the
claim that the whole strip N <= 5t − 2 is closed) is a GAP (LEDGER). For N > 5t − 2 (base > 0) the float searches of §26,
§30, §41, §60 found 𝓡_m feasible at every depth reached (up to five or six kept replies), with one unresolved candidate break.
**Extreme t.** For every N in the window, every level computed here is feasible for all t < (N + 1/2)/3, i.e. on the whole
window; infeasibility appears only on and below the line N = 3t − 1/2 (levels 7–8), plus the single exact point
(0.76, 1.80) at greater depth. No t > 3/4 gives a certificate inside the window.

## 78. Extremal structure read off; counterexample candidates

- Level 7: the steerer (77.1) — the pair carries one number, o, and he puts it outside Z. Level 8: the same plus a third
  dump that keeps every reading of {K_1, K_2, K_3} positive (in the LP the failing vertices are dumps into O and into the
  private part the request left open, as in 9.1). These are bounded-depth first-order strategies; by §43 they are not
  families, and none is proposed as one. [computed float for level 8; heuristic as a description]
- An all-levels feasible system is not finitely generated [proved]: finitely generated systems are profile families
  (39.3), and those have a good seven (Theorem S). So the "extremal limit object" of this method, if it exists, is exactly
  the non-finitely-generated system SPOIL\* asks for; the relaxation gives no finite description of it.

## 79. Verdict, dead routes, next step

**Dead.** (a) Flag algebras / SDP in Razborov's or Lidický–Pfender's sense: no measure on members, rank-one positivity
on points (76.1). (b) Any density formulation of CP (76.2). (c) "Level-q relaxation with positivity" as something beyond
the game: it is the bounded-depth game (76.3). (d) Pair-steered and pair-plus-one-reply levels inside the window: they
stop at N = 3t − 1/2 (77.1 proved; 77.2 float).
**Corrected.** §39.3: the limit of a (7,2) family satisfies (C), (E) but not (A) (75.2); the certificate direction is the
transfer lemma 75.3 (t' < t, finite depth).
**Status of CP.** Unchanged: open on 3t − 1/2 < N < 3 − t. Inside it, the lower strip N <= 5t − 2 (base <= 0) is where
finite levels can still win by static finishes (they do at (0.76, 1.80)); above 5t − 2 every static finish needs on-line
dump mass from a non-free reply (§25), and the question is SPOIL\*.
**Next step [heuristic].** If the hierarchy is pushed, push it where it can terminate: the strip 3t − 1/2 < N <= 5t − 2.
Rationalise the REDTEAM §14 tree as a function of (t, N) and test it with `robust3`-style vertex LPs at 3–4 adaptive levels,
aiming at "she wins 𝓡_m for all N <= 5t − 2". That would close the 21.2 GAP and move the open window to (5t − 2, 3 − t).
Not done: that; exact (rational) versions of 77.2; partial-exhaustion requests in 77.2; levels beyond 8.

Self-check (§75–§79): 75.2's count is the standard "every point in >= 3 blocks" bound, checked against n = 7k/4 (Fano
blow-up exact). 75.3 uses only that finite-k positions are exact and that requesting more points is legal in G_∞(t').
76.1: the point flags of a fixed tuple are i.i.d. by definition of the limit; 76.2: the concentration is the LLN for seven
independent uniform c-subsets. 77.1: both inequalities re-derived from the incidence table of the seven lines; the LP
matches the endpoints N − 2t, 3t − 2 at three points and gives need 0 at the Theorem-T point a = N/2 − 5/8 for the
triangle labelling at (0.76, 1.79). 77.2 is float (HiGHS via scipy) with the class restriction stated; its "no S_3"
verdicts are not proofs even within the class. Everything is first order.

=============================================================================================
# Part XI — fractional relaxation and rounding (§80–§84)

Brief: replace τ by τ*, settle the fractional question by LP duality, bound τ/τ*, combine. Code:
`compute/core10/frac_gap.py`, `compute/core10/sat_rand.py`; logs `compute/core10/logs/frac_gap.log`, `sat_rand.log`.
Families of k-sets ("edges") with the (7,2)-property: every 7 members have a 2-point transversal.
**Outcome. The route is dead, for a structural reason. For (7,2)-families τ* is always o(k), in fact O(k^{1/3}), and it is
O(1) in the core window, so the relaxation forgets the whole question. The gap τ/τ* is Θ(k) on exactly the families that
matter, and "rounding" is the original problem with nothing removed (§82–§83).**

## 80. The fractional problem, and its answer [proved by hand]

Define f*(k,7) = sup τ*(H) over (7,2)-families of k-sets, and f*_frac(k,7) the same sup over families in which every 7
members have τ* <= 2. This is a weaker hypothesis, since τ* <= τ.
**80.1 Theorem F.** For every family of k-sets with at least 7 members in which every 7 members have τ* <= 2 (in
particular every (7,2)-family), τ*(H) <= (35k)^{1/3}. Hence f*(k,7) <= f*_frac(k,7) <= (35k)^{1/3} = o(k).
*Proof (dual with 7-member weightings).* By LP duality τ* = ν* = max Σ w_F over w >= 0 with Σ_{F∋x} w_F <= 1 for all x.
Take an optimal w, put W = Σ w_F, and draw 7 members i.i.d. from w/W. Put p_x = P(sample ∋ x) = (Σ_{F∋x} w_F)/W. Then
p_x <= 1/W and Σ_x p_x = Σ_F w_F|F|/W = k. The sampled multiset uses at most 7 distinct members, and these lie in some
7 members, so it has a fractional cover of total 2 (τ* is monotone, and repeats do not change τ*). If every point lay
in at most 3 of the 7 slots, weight 1/3 on every slot would be a fractional matching of value 7/3 > 2. So almost surely
some point lies in >= 4 slots, and 1 <= Σ_x C(7,4) p_x^4 <= 35 (max p)^3 Σ p_x <= 35k/W^3. ∎
**80.2 Lower bound and the extremal example [proved by hand, exact at finite k].** Let H be all k-subsets of [n] with
n < 7k/4 (so also n < 2k). Then H is a (7,2)-family. Seven co-edges (size c = n - k) covering all pairs would need every
point in >= 3 of them: a point in at most 2 co-edges K_i, K_j needs K_i ∪ K_j = V, which is impossible since 2c < n.
That forces 7c >= 3n, i.e. n >= 7k/4. Here τ = n - k + 1 ≈ 3k/4 and τ* = n/k < 7/4 (uniform weight 1/k; the matching
side follows by symmetry). So f*(k,7) ∈ [7/4 - o(1), (35k)^{1/3}]. The exact order of f* is open and does not matter
(§82). The 3k/4 example itself has τ* < 7/4.
**80.3 Answer to (1).** f*(k,7) = (3/4 + o(1))k is FALSE: f*(k,7) = O(k^{1/3}). The fractional analogue is not a
weakening of the question but a different, easy question. τ* cannot see the constant 3/4.
**80.4 Confined setting [proved by hand].** If all edges lie in V with |V| = Nk, then τ* <= N (weight 1/k per point).
In the core window 3t - 1/2 < N < 3 - t this gives τ* < 9/4, while τ > T = tk. So the dual (7-member weighting) of
80.1 is vacuous there: W is already bounded by N long before the sampling bound bites.

## 81. The integrality gap [proved by hand; literature as tagged]

**81.1** For any (7,2)-family with τ >= εk: τ/τ* >= εk/(35k)^{1/3} = Ω(k^{2/3}) [80.1]. In the core window,
τ/τ* > tk/N > tk/(3 - t) ≈ 0.33k [80.4]. For the pool family (all k-subsets of k + T points, pool Y unused) τ = T + 1
and τ* = 1 + t, so the gap is about tk/(1 + t) ≈ 0.43k. For the complete family of 80.2 the gap is about 3k/7.
**So the gap is never 1 + o(1) on any family relevant to the question; it is linear in k.** The brief's premise
"gap = 1 + o(1) in the window" is false.
**81.2 ν <= 2 [proved by hand].** Three pairwise disjoint members cannot be hit by 2 points, so a (7,2)-family with at
least 7 members has ν <= 2. Füredi-type bounds τ* <= (k - 1 + 1/ν)ν [literature, from memory; not re-checked] then give
only τ* = O(k), which is weaker than 80.1.
**81.3 Ding–Seymour–Winkler** (Combinatorica 14 (1994) 23–34) [literature: bibliographic data checked; the statement is
from memory and a secondary citation, not checked against the paper]. They bound τ by a function of ν and λ only,
independent of k (λ = the largest set of points every two of which are separated by an edge meeting the set in exactly
those two points). With ν <= 2 and τ ≈ 3k/4, this forces λ → ∞ with k. It says nothing about the constant. Dead for
this question.
**81.4 (p,q)/Alon–Kleitman shape [literature, checked at abstract level only: Alon–Kalai–Matoušek–Meshulam, Adv. Appl.
Math. 29 (2002) 79–101, an abstract (p,q) theorem from a fractional Helly property].** The (7,2)-property implies the
(7,4) property "some 4 of every 7 share a point", which is what 80.1 uses; this IS the fractional-Helly step. The second
Alon–Kleitman step is ε-nets: τ <= C·d·τ*·log τ*, with d the VC dimension (Haussler–Welzl [literature, from memory]).
Given the ε-net theorem this yields τ = O(d·k^{1/3}·log k) in general and τ = O(d) in the window [proved by hand].
Since d <= k always, the bound is non-trivial only for d = o(k^{2/3}/log k), and it gives at best τ = O(k) bounds with
unspecified constants. It can show "small VC dimension ⟹ τ = o(k)" but never the constant 3/4. This is consistent with
S+ (§39.4): in the window a family with τ > T must have VC dimension linear in k [heuristic as stated; the ε-net
constant is not computed]. Dead for the constant.

## 82. Combining: which half is the difficulty [proved by hand]

The hoped-for chain τ <= (gap)·τ* <= (1 + o(1))·(3/4 + o(1))k fails at both links, but asymmetrically:
- the fractional link is TRUE in a much stronger form (τ* = O(k^{1/3})) and costs nothing;
- the gap link is false as stated (81.1): it has to carry a factor Θ(k), not 1 + o(1).
So the whole difficulty is the rounding half, in the exact form
**(R)** for every (7,2)-family H of k-sets, τ(H) <= (3/4 + o(1))k, where τ*(H) <= (35k)^{1/3} is free (and τ* <= N if
H is confined).
In the confined window (|V| = Nk, 3t - 1/2 < N < 3 - t), (R) says word for word that CP has no counterexample (§33(1)).
The hypothesis τ* <= N holds automatically for every family on V, so (R) adds nothing to CP there. The relaxation
removes no case: rounding = CP.

## 83. Why no LP relaxation of this kind can help [first two items proved; third heuristic]

- The hypothesis of CP (T-covering, τ > T = tk) has no fractional counterpart in the window: τ* > T is impossible
  (τ* <= N < 9/4 < tk for k >= 3). The relaxed hypothesis is empty. [proved by hand]
- The "7-member dual weighting" with the full (7,2) event, P_μ(seven i.i.d. members are 2-coverable) = 1 for every
  distribution μ on H, is equivalent to the (7,2)-property itself: P < 1 iff some bad seven exists, since a full-support
  μ samples it with positive probability. So the distributional form of the dual is exact, not a relaxation.
  [proved by hand]
- Between these two extremes the natural lifts are hierarchies (Sherali–Adams/Lasserre) of the hitting-set LP. For the
  complete k-uniform family on n points the gap (n - k + 1)k/n is a pure symmetry gap, and certifying τ > T should need
  lifts of degree comparable to T, i.e. about linear in k rounds [heuristic; not checked against the literature]. Any
  fractional object that sees the constant 3/4 must look at 7-tuples of members jointly. That is the Fano/pencil
  certificate machinery of §1–§5, not τ*.

## 84. Numerics [computed exact: τ* by rational primal/dual certificates, τ by ILP (HiGHS)]

`py compute/core10/frac_gap.py` (< 2 min) and `py compute/core10/sat_rand.py`. τ* is exact: a rational fractional
cover and a rational fractional matching with equal totals are checked in Fractions.

| family | k | T | n | members | τ* | τ | τ/τ* | n/k |
|---|---|---|---|---|---|---|---|---|
| fam_8_6_15_rev (core9, co-edges → edges) | 8 | 6 | 15 | 2352 | 13/7 | 7 | 3.77 | 1.875 |
| SAT rand R=3 seed 1 (decide_family.build) | 8 | 6 | 15 | 2348 | 15/8 | 7 | 3.73 | 1.875 |
| pool on k + T = 7 points | 4 | 3 | 8 | 35 | 7/4 | 4 | 2.29 | 2.000 |
| pool | 6 | 5 | 13 | 462 | 11/6 | 6 | 3.27 | 2.167 |
| pool | 8 | 6 | 17 | 3003 | 7/4 | 7 | 4.00 | 2.125 |
| pool | 8 | 7 | 18 | 6435 | 15/8 | 8 | 4.27 | 2.250 |
| pool | 10 | 8 | 22 | 43758 | 9/5 | 9 | 5.00 | 2.200 |
| complete on n < 7k/4 (80.2) | 8 | 5 | 13 | 1287 | 13/8 | 6 | 3.69 | 1.625 |
| complete on n < 7k/4 (80.2) | 12 | 8 | 20 | 125970 | 5/3 | 9 | 5.40 | 1.667 |

At (8,6,15) the SAT instance of decide_family.build is unsatisfiable for R=2 seeds 1–2 and for R=3 seeds 2–3, so those
give no family. Readings: every family has τ* in [1.62, 1.88]. For pool families τ* = (k + T)/k exactly and for complete
families τ* = n/k; the core9 family is the only one below its uniform weight (13/7 < n/k = 15/8). Meanwhile τ = T + 1,
roughly 3k/4, and the gap grows linearly in k (2.3 → 5.4 as k goes 4 → 12), as 81.1 predicts. The (7,2)-status of the
core9 and SAT families is not decided here (cover_ilp: best cover 8, bound 7). It does not matter: either way τ* is
O(1) for every family on 15 points.

Self-check (§80–§84). 80.1: Σ p_x = k uses uniformity; p_x <= 1/W is the matching constraint; the 7/3 matching uses
only that each point is in <= 3 slots. 80.2: the counts 2c < n and 7c < 3n are exact at finite k. 81.1 is arithmetic on
80.1 and 80.4. The literature items in 81.2–81.4 are tagged with what was checked: bibliography and abstracts only, and
DSW's exact bound and the ε-net constants were not checked against the papers. The §84 numbers are from the logs.
**Dead routes (this part):** fractional relaxation by τ* (80.3, 82); integrality-gap bounds of DSW/Füredi/ε-net type
for the constant (81.2–81.4); any LP relaxation of the T-covering hypothesis in the window (83).

=============================================================================================
# Part XII — hypergraph containers plus supersaturation (§85–§89)

Code: `compute/core11/`. `container_scales.py` computes codegree exponents at the sparse scale for all four shape
hypergraphs. `pool_pencils.py` is alongside; the §86.2 bisection was a one-liner whose output is `logs/hand_boundary.log`; logs are in
`compute/core11/logs/`. All exponents are first order (nats per k, k → ∞, subexponential factors dropped). Units k = 1,
notation of §33.

**Outcome. The route is DEAD, for two independent reasons.**
(i) Logical (§87). The host is complete and T-covering is upward closed. So the supersaturation statement that
containers would need already implies CP without containers, and a container carries no information about I beyond
its independence.
(ii) Numerical, and it bites first (§86). Work at the scale of the families in question: fingerprint τ <= p, where p is
the density of the sparsest T-covering family, and container edge density ε <= p^r, the edge density of the random
threshold family. At that scale the Saxton–Thomason codegree condition fails:
- for the good-seven 7-graph and the Q' 4-graph, in essentially the whole window;
- for pencils and triangles, outside a bottom strip ω ≲ 0.09.
The first obstruction is the 2-codegree (j = 2). It is shape-free, so no choice of shape repairs it (§86.2).

## 85. Set-up [definitions; literature checked against the papers]

- X is the set of all co-edges (c-subsets of V, |V| = Nk), and log|X| = N h(1/N). Sym(V) acts transitively on X and
  preserves every shape hypergraph below, so every vertex has the same degree d and the same maximum j-codegree Δ_j.
  [proved by hand]
- The shape hypergraphs are:
  - G_7, the good sevens (Fano-type; complete for N < 11/6, §1.3);
  - by (Σ) (§38, corrected in LEDGER): G_pen, the 3-sets with union V and triple intersection >= N - 2t;
  - G_tri, the Theorem-T triangles;
  - G_Q, the Q' quadruples.
  A counterexample to CP is a T-covering family I ⊆ X that is independent in G_7. If (Σ) is used, it is also
  independent in the other three.
- **Saxton–Thomason** [literature, checked: Invent. Math. 201 (2015), arXiv 1204.6595; Def. 3.2, Thm 3.4, Cor. 3.6,
  Remark 3.5 read in the arXiv PDF]. Let G be an r-graph on n vertices with average degree d. Put
  d^{(j)}(v) = max{d(σ) : v ∈ σ, |σ| = j}, define δ_j by δ_j τ^{j-1} n d = Σ_v d^{(j)}(v), and put
  δ(G,τ) = 2^{C(r,2)-1} Σ_{j=2}^r 2^{-C(j-1,2)} δ_j.
  Cor. 3.6: suppose 0 < ε, τ < 1/2 and δ(G,τ) <= ε/12r!. Then there are containers C(T), where T is a tuple of
  s <= c log(1/ε) sets of size <= cτn, such that:
  - every independent set lies inside one container;
  - e(G[C]) <= ε e(G) for every container;
  - log|𝒞| <= c log(1/ε) n τ log(1/τ), with c(r) = 800 r!^3 r.
  Remark 3.5 says that the construction "makes essentially no use of the independence" of I.
- **Balogh–Morris–Samotij** [literature, partly checked: JAMS 28 (2015), arXiv 1204.6530; only pp. 4–9 read]. Their
  container theorem plays the same role. Every application read there is either a sparse random host or a counting
  question: Turán and stability in G(n,p), counting H-free graphs, KŁR. Their Thm 2.2 was not among the pages read, so
  BMS is used here only through ST.
- The host is vertex-transitive, so δ_j = Δ_j / (τ^{j-1} d) exactly. Per k, the ST condition reads
      L_j := log(d/Δ_j) >= (j - 1)·log(1/τ) + log(1/ε)        (2 <= j <= r).                           (85.1)

## 86. The codegree check at the relevant scale (step (2), done first)

**86.1 The scale [proved by hand].** Let p := e^{-γk} with γ = (N - t) h(ω/(N - t)). Then p is the least density of a
T-covering family, namely 1/C(n - T, c - T). The random family of density p·Ck has two properties:
- it is T-covering w.h.p., by a union bound over the <= 2^{Nk} T-sets;
- it has <= 3·(pCk)^r e(G) edges with probability >= 2/3, by Markov.
Hence:
(a) any supersaturation of the form "T-covering ⟹ more than ε e(G) edges" is FALSE unless log(1/ε) >= rγ;
(b) containers say something about families of density about p only if τ <= p. Otherwise the fingerprint may be all
    of I, and the count log|𝒞| exceeds the number of such families.
So the meaningful regime is τ <= p and ε <= p^r. In that regime (85.1) becomes L_j >= (r + j - 1)γ for all j.

**86.2 A shape-free obstruction at j = 2 [proved by hand].** For any r-graph on X,
Σ_{K' ≠ K} codeg(K,K') = (r - 1)d. So Δ_2 >= (r - 1)d/|X|, and therefore L_2 <= log|X|. With τ <= p and ε <= p^r,
condition (85.1) at j = 2 then requires
      log|X| >= (r + 1)γ,   i.e.   N h(1/N) >= (r + 1)(N - t) h(ω/(N - t)).
[computed float, `logs/hand_boundary.log`] Over t ∈ [0.7501, 0.78] this holds only in a bottom strip:
- r = 3: ω < 0.093–0.095;
- r = 4: ω < 0.067–0.069;
- r = 7: ω < 0.035–0.060. At t = 0.78 it fails for r = 7 on the whole window.
The window has ω up to 3 - 2t - 1 (ω = 0.50 at its top for t = 0.75). So above ω ≈ 0.095, no shape hypergraph with
r >= 3 can carry containers at the family scale, whatever the shape. The reason is that the families are too dense in
X for r + 1 powers of p to fit: |X| is only e^{1.2–1.5k}, while p is e^{-0.2k} to e^{-0.95k}.

**86.3 Shape by shape [computed float; `logs/container_scales.log`].** Let eps* = min_j [L_j - (j - 1)γ]. This is the
best log(1/ε) available at τ = p, and it must be >= rγ. How sharp each entry is:
- For sevens, triangles and Q', L_j uses the typical j-codegree of the max-entropy shape. That is a lower bound for
  Δ_j, so eps* there is an upper bound, and a failure (✗) is a proof of failure at first order.
- For pencils, Δ_2 is a true maximum over positions (on a grid).

| t | N | γ | sevens: eps* / 7γ | pencils: eps* / 3γ | triangles: eps* / 3γ | Q': eps* / 4γ |
|---|---|---|---|---|---|---|
| 0.7501 | 1.800 | 0.202 | <= 1.01 / 1.41 ✗ | 0.82 / 0.60 ✓ | none (infeasible) | <= 1.01 / 0.81 ✓? |
| 0.7501 | 1.900 | 0.446 | <= 0.85 / 3.12 ✗ | 0.42 / 1.34 ✗ | none | <= 0.82 / 1.78 ✗ |
| 0.7501 | 2.100 | 0.773 | <= 0.66 / 5.41 ✗ | -0.09 / 2.32 ✗ | none | <= 0.62 / 3.09 ✗ |
| 0.76 | 1.826 | 0.248 | <= 0.99 / 1.73 ✗ | 0.93 / 0.74 ✓ | <= 0.99 / 0.74 ✓? | <= 0.97 / 0.99 ✗ |
| 0.76 | 1.918 | 0.461 | <= 0.85 / 3.23 ✗ | 0.58 / 1.38 ✗ | <= 0.83 / 1.38 ✗ | <= 0.83 / 1.85 ✗ |
| 0.76 | 2.010 | 0.626 | <= 0.75 / 4.38 ✗ | 0.33 / 1.88 ✗ | <= 0.72 / 1.88 ✗ | <= 0.72 / 2.50 ✗ |
| 0.78 | 1.878 | 0.330 | <= 0.95 / 2.31 ✗ | 0.95 / 0.99 ✗ | <= 0.96 / 0.99 ✗ | <= 0.94 / 1.32 ✗ |

✓? means the necessary check passes; the sufficient check with the true Δ_j was not done.
- For the good-seven graph the binding term is always j = 2 (L_2 ≈ 1.2–1.5 against 8γ), so its failure is the one of
  §86.2.
- At t = 0.7501, Theorem-T triangles do not exist in the symmetric max-entropy form, because their tolerance is O(ε)
  (§3). So G_tri is exponentially thin there.
- The full grid (t = 0.7501, 0.76, 0.78, five N each) is in the log. Every N in the upper four-fifths of the window
  fails for all four shapes.

**86.4 Is the random family the right benchmark? [computed float, `logs/pool_pencils.log`]** The pool family (a
Theorem-S family) has pencil density e^{-0.04k} to e^{-0.69k}, far above the random family's e^{-3γk}. So the random
threshold family is the sparsest-in-pencils T-covering family known, and §86.1(a) is the operative bound. Only its
role as an upper bound on the minimum is used; that it is the minimiser is [heuristic].

**Verdict on step (2).** At the family scale the codegree conditions hold only in a bottom strip of the window:
ω ≲ 0.09 for pencils (and possibly triangles), and nowhere for good sevens or Q' above ω ≈ 0.07. The bulk of the window
is out of reach of containers by §86.2, independently of shape. That bulk is also where every earlier method stalls.

## 87. Why containers are idle here even where the codegrees work [proved by hand]

**87.1** T-covering is upward closed, and every container C contains I. So if I is a counterexample, every container
of I is T-covering. Hence step (3), "each container has τ <= T", is not really a statement about containers. All that
is known about which C arise is: C contains an independent set, e(G[C]) <= ε e(G), and C is determined by a
fingerprint T ⊆ I. So the statement one must prove is
   (Sup_ε)  every T-covering family C ⊆ X has e(G[C]) > ε e(G).
Applied to C = I, where e(G[I]) = 0 <= ε e(G), it gives CP at once. So any container proof contains a container-free
proof of CP. And (Sup_ε) is strictly stronger than CP: it is CP with a quantitative count.

**87.2** The fingerprint adds nothing. C(T) is the set of K whose degree into the link of T is small, and for K ∈ I
that degree is 0 by independence. ST's own remark (§85), that the construction does not use independence, says the
same.

**87.3 What containers are for, and why none of it applies.** Containers transfer a dense extremal or supersaturation
theorem to (a) sparse random hosts, (b) counting independent sets, or (c) list colouring. CP has a complete host, asks
for existence rather than a number, and the dense statement that would have to be transferred is CP itself.
The symmetry-counting variant also fails, by size. Its idea: a counterexample has n!/|Aut| images, all lying in
containers. But log n! = O(k log k), while a container holding a family of density p has at least e^{(log|X| - γ)k}
members, which is e^{0.6k} to e^{1.1k}. [proved by hand: compare the exponents in the logs]

**87.4 The stability version does not help either.** Consider "T-covering with <= e^{-ηk} p^r e(G) shapes ⟹ close to
structured". The counterexample I itself lies in its hypothesis class. So this is the robust Theorem S of §38 applied
directly to I, with or without containers, and §39 showed that regularity-type approximation does not deliver it.

**87.5 The other side of the colouring.** T-covering can be encoded too: X∖𝒞 is independent in the star hypergraph
{St(S) = {K ⊇ S} : |S| = T}, whose uniformity is M = C(n - T, c - T) = e^{γk}.
- Containers for it need c(M) = 800 M!^3 M (§85), which is doubly exponential in k.
- The condition τ >= d^{-1/(M-1)} forces τ = 1 - o(1).
Dead. [proved by hand from the checked statement]

## 88. Step (3): structured containers [proved by hand]

Not reached, because there are no containers to classify (§86, §87). Even granting them, S, S+ and W would not apply:
- they are statements about families that are exactly profile-invariant (S, and S+ with <= 4εk - 12 cells) or that
  follow exact greedy-window rules (W);
- a container is a superset of I with few shapes, and nothing makes it profile-invariant;
- its own shape count (> 0 in general) says nothing about I.
Using S, S+ or W on containers would need their robust versions. That is the open problem of §38, and passing to a
superset does not make it easier.

## 89. Exact remaining statement, dead routes, self-check

**Dead (this part).** Hypergraph containers plus supersaturation for CP, in every form tried: G_7, G_pen, G_tri, G_Q,
their union, the star hypergraph, the stability version and the symmetry-counting version.

**First obstruction, exactly (§86.2).** For an r-uniform shape hypergraph on X, containers at the family scale need
log|X| >= (r + 1)γ. This fails once ω > 0.095 (r = 3), ω > 0.069 (r = 4), or ω > 0.035–0.06 (r = 7).
**Behind it (§87.1).** Even where the numbers pass, the supersaturation (Sup_ε) that containers need implies CP
directly.

**What survives.** Only the observation of report §5(a), stated correctly: a counterexample must have e^{-Ω(k)} times
the random number of every (Σ)-shape. That is a first-moment fact about random families, not a mechanism. A proof
must still produce a shape in an arbitrary T-covering family, which is (Σ) itself.

**Bottom strip.** For ω ≲ 0.09 (pencils), §86 does not exclude the container condition, but §87 applies there too.
That strip lies near 3t - 1/2 < N <= 5t - 2, where the fixed-plan method of §21.2 nearly works (LEDGER: GAP).
Repairing §21.2 there is a better use of effort than containers.

**Self-check.**
- §86.1: the density 1/C(n - T, c - T) follows from the double count C(n,T)C(n-T,c-T) = C(n,c)C(c,T), and γ
  reproduces `core9/exponents.py`.
- §86.2: one averaging line; the bisection is in `logs/hand_boundary.log`.
- §86.3: for sevens, log e(G) - 7γ reproduces the G7 - 7γ column of `core9/logs/exponents.log` (3.006, 2.643, 2.430
  at t = 0.7501, N = 1.80, 1.90, 2.00).
- The ST statement was read from the arXiv PDF (Def. 3.2, Thm 3.4, Cor. 3.6, Remark 3.5, §3.5).
- Typical-codegree margins are upper bounds only, and the ✓? entries were not confirmed with true maxima.
- Nothing in this part has been checked by an independent verifier.
