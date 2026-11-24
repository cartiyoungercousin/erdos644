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
