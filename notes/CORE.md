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
