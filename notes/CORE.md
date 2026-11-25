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

=============================================================================================
# Part X-b — hash-like greedy rules: finite-k exact checks, random selectors, the pseudorandom condition (§55–§59)

Code: `compute/core9/`. The first agent on this part wrote `two_ground_sat.py`, `hash_check.py`, `escape_check.py` and
`exponents.py` and ran them, but was cut off before writing notes. Its logs are kept as they were. This part reconstructs
what it intended (the docstrings name §55, 55.1, 55.2, §56, 56.3, §57), re-runs what was needed, and finishes what it could.
New files: `pencil_exact.py`, `hash_replay.py`, `decide_family.py`, `cover_ilp.py`, `seven_dfs.js`, `random_selector.py`.
Finite-k conventions are those of §47: (k, T, n), ω = n - k - T, kernel n - 3k/2, petals ("halves") k/2. A *greedy rule*
(47.1) has classes c with linear orders ≺_c, and the reply to S is S ∪ head_c(S), where head_c(S) is the first ω points
of V∖S in ≺_c and c = σ(S).

**Verdicts first.**
- **The (8,6,15) family** (`esc_8_6_15.log`: "pencil-free family of 2352 members, local search found NO good seven"):
  **not relevant to CP, and the good-seven question there is UNDECIDED.** (k,T) = (8,6) has t = 3/4 exactly
  (ε = 0). It lies in no core window: 5t - 2 < N < 3 - t needs t < 5/6, and at k = 8 no T gives 3/4 < t < 5/6. The family
  is T-covering, so τ = 7 exactly [computed exact + proved by hand, 55.5]. Whether it has a good seven (pair-cover
  number 7 or 8) was not settled by four exact methods within budget (55.5). If it has none, it gives f(8,7) >= 7. That
  equals 3k/4 + 1 and FKW's ⌈7k/8⌉ = 7, so it would only fix the small value f(8,7) = 7 and could not beat any known
  bound. Small-k rounding.
- **The 7 failures of `hash_check.log` (798/805)** are all search failures [computed exact]. All seven are `junta+` rules
  (the min-junta on T - k/2 + 1 points, one point more than Theorem W allows). For each one an exact SAT search
  (`pencil_exact.py`) finds a perfect pencil. That pencil is checked on the rule verbatim and completed to a good seven by
  four transversal requests, with all pairs checked: 7/7. Corrected total: **805/805 good sevens**. Why the random search
  missed them is explained in 56.2.

## 55. The two-ground pencil question, exact at k = 8 [statements proved by hand; tables computed exact by SAT]

**55.1 Parent criterion [proved by hand].** For a greedy rule, a co-edge K is a member iff for some class c there is an
ω-set Z ⊆ J_c(K) with σ(K∖Z) = c. Here J_c(K) is the longest initial segment of ≺_c contained in K.
*Proof.* The reply to S = K∖Z in class c is S ∪ (the first ω points of Z ∪ (V∖K) in ≺_c). This equals K iff every
point of Z precedes every point of V∖K, i.e. iff Z ⊆ J_c(K). ∎
(This generalises 47.2(ii); it is the membership test that `hash_check.py` and `pencil_exact.py` use.)

**55.2 Pencil completion [proved: 1.3(ii), Theorem C].** If 4 | k, T >= 3k/4 and three members κ ∪ P_1, κ ∪ P_2, κ ∪ P_3
form a perfect pencil (|κ| = n - 3k/2, the P_i are disjoint halves), then the four requests "one half (k/4 points) of each
petal, in the patterns 000, 011, 101, 110, padded to T points" finish a good seven, whatever the replies are.

**55.3 The question.** §48.3 asked for a *two-ground* version of ℋ(k,T)'s non-2-colourability: every selector of a greedy
rule with two classes leaves a monochromatic head pencil. `two_ground_sat.py` decides exactly whether, for given orders,
*some* selector makes the family free of perfect pencils of *any* kind. Variables: the class of every T-set. Membership
is implied by selection (55.1). One clause per reachable frame forbids all three of its lines. SAT means a
pencil-free selector exists (an escape); UNSAT means every selector leaves a pencil. "rev" means ≺_b is the reverse of
≺_a. "rand s" means random orders from seed s. "shift" means cyclic shifts by n/R.

| (k,T,n) | ω | R = 2 | R = 3 |
|---|---|---|---|
| (8,6,15) | 1 | rev: **escape**; rand 1, 2, 3: none | rand 1: **escape**; shift: none |
| (8,6,16) | 2 | rev, rand 1, rand 2: none | rand 1, shift: none |
| (8,6,17) | 3 | rev: **escape**; rand 1, rand 2: none | rand 1: **escape**; shift: **escape** |
| (8,7,16) | 1 | rev: **escape**; rand 1, rand 2: none | rand 1, shift: none |
| (8,7,17) | 2 | rev: none | — |

[computed exact; CaDiCaL 1.5.3 via python-sat. The R = 2 rev/rand-1 and R = 3 rand-1/shift entries at (8,6,16), plus
(8,6,15) rand 1, (8,6,17) rev, (8,7,16) rev and (8,7,17) rev, are the first agent's runs. The rest were run in this
part. Logs: `logs/tg_*.log`.]
Reading:
- **The two-ground pencil step of 48.3 is false as a finite statement** [computed exact]: pencil-free selectors exist at
  (8,6,15), (8,6,17) and (8,7,16) with reversed orders. Reversed orders are the natural worst case: the two heads lie
  at opposite ends, so no request can serve both. **Dead:** "every 2-class greedy rule has a pencil" as a lemma to prove.
- 48.3 inferred from χ(ℋ(4,3)) = 3 that "three classes may escape every pencil". That inference is not supported where
  it was tested: random 3-class rules have no escape at (8,6,15) shift, (8,6,16) and (8,7,16). Three-class escapes exist
  at (8,6,15) rand 1 and at (8,6,17). Whether a selector escapes depends on the orders more than on R.
- With random orders and two classes there was no escape in any of the nine tested runs.

**55.4 Do the escapes have good sevens? (`escape_check.py`) [computed exact where marked].** Each round solves the SAT
of 55.3, builds the family from the rule verbatim, and searches it for a good seven. A good seven that is found is
forbidden by a clause over its seven members, and the solve is repeated. UNSAT therefore means: every selector for these
orders produces a pencil or one of the forbidden sevens, so every selector has a good seven [exact].
| case | result |
|---|---|
| (8,6,17) R=2 rev | UNSAT after 36 forbidden sevens (CaDiCaL); re-run with Glucose 4: UNSAT after 26 [exact] |
| (8,7,16) R=2 rev | UNSAT after 2 forbidden sevens (both solvers) [exact]. CaDiCaL's "c found falsified original clause" in the first run is its root-level UNSAT message; Glucose agrees |
| (8,6,17) R=3 rand 0 ("shift" in escape_check means rand seed 0) | UNSAT at round 0: no pencil-free selector [exact] |
| (8,6,17) R=3 rand 1 | 300/300 rounds, each pencil-free family had a good seven; not exhausted [computed exact per round] |
| (8,6,15) R=3 rand 1 | round 0: pencil-free family of 2348 members, local search found no good seven (not decided) |
| (8,6,15) R=2 rev | round 0: pencil-free family of 2352 members; see 55.5 |

**55.5 The (8,6,15) family, decided.** `decide_family.py` rebuilds the round-0 SAT instance in the same clause order.
CaDiCaL is deterministic, so this gives the same model. It extracts the family, written to `logs/fam_8_6_15_rev.txt`,
2352 members of size 7. It re-checks from the family alone [computed exact]: every 6-set of V lies in a member
(T-covering, i.e. τ(H) >= 7 for the 8-uniform complements), the family contains no perfect pencil, and the class
counts are 2485/2520. The selector is balanced against the obvious statistics: conditioned on (first gap, last gap) of
V∖S, the two classes are near 50/50 in every cell. It is a hash-like solution, not a threshold.
Good seven: by the Schönheim bound, covering the pairs of 15 points needs >= 7 sets of size 7, so a good seven is a
minimum covering. Each point then lies in >= 3 of the seven, and Σ(r_x - 3) = 4.
τ: any 7-set that is not a member meets every edge (an edge V∖K misses X only if X ⊆ K, i.e. X = K), so τ <= 7.
T-covering gives τ >= 7. Hence **τ = 7 exactly** [proved by hand; the T-covering check is computed exact]. The "ILP gap
{7, 8}" is the pair-cover number, not τ.
| method | result |
|---|---|
| local search (`escape_check.py`) | no good seven found (not a proof) |
| CaDiCaL, ≤ 7 members + r_x >= 3 (`decide_family.py`) | no answer in 4 h; killed |
| HiGHS MILP, min cover (`cover_ilp.py`, 3000 s) | primal 8, dual 7: undecided |
| CaDiCaL split into "r_x = 3" for x = 0..4 (`seven_split.py`) | no answer in 3.5 h; killed |
| triple-DFS (`seven_dfs.js`) and co-type DFS (`seven_cotype.js`) | too slow; killed. `seven_cotype.js` counts all 30 Fano planes at (7,3) exactly, as a check |
| configuration enumeration (`seven_config2.py`): co-type configurations up to S_7, then embedding by exact Venn counts | stage (a) done: 604 supports in 129 s. Stage (b,c), the multiplicities, did not finish in the 20-min budget and was killed. The method passes the (7,3) Fano control. **UNDECIDED** |
Facts used (all [proved by hand]): every point of a good seven has r_x >= 3 and Σ(r_x - 3) = 4. So at least 11 points
have r_x = 3, and every r_x = 3 point sees its three members cover V. There are 604 intersecting supports of triples on
[7] up to S_7 [computed exact, `seven_config2.py`]. A parallel agent reports that this family has no Q′ quadruples, no
(b) pencil triples and 12.8M triples at defect 1 [their computation, not re-run]. That does not decide it, because (Σ)
is only sufficient.
**What it means.** Nothing for CP (ε = 0, outside every window). If the cover number is 8, then f(8,7) = 7, the FKW upper
bound, matching 3k/4 + 1. **Dead as a counterexample route:** small-k families at t = 3/4.

## 56. Greedy rules at finite k with hash-like and structured selectors (`hash_check.py`) [computed exact per instance]

**56.1 Setup.** Sizes (k,T,n) = (40,31,74), (40,31,76), (40,31,80), (40,31,88), (100,76,180), (100,76,190), (100,76,210).
Selectors (R classes):
- `hash`: a blake2 hash of S mod R, i.e. an independent uniform class per request; R = 2, 8, 64.
- `linear`: (Σ a_x + b mod p) mod R, pairwise independent; R = 2, 8.
- `parity`: parity vector on random half-sets; R = 2, 8.
- `early` / `late`: the class whose head ends earliest / latest in its own order (anti-plan thresholds); R = 2, 4.
- `early^hash`: `early` shifted by a hash.
- `junta+`: the min-junta on T - k/2 + 1 points; R = T - k/2 + 2.
- `midhash`: a hash of the request outside the two kernel-length prefixes, flipped by an anti-plan bit.
Orders are random, plus "rev" for R = 2. Five rules per cell, 805 in all.
Her search uses the rule only through replies. It picks a class r, a kernel containing a prefix of ≺_r, and random
petals. For each line it tries holes Z inside J_c(K) for random classes c (55.1). With three member lines it applies
55.2. Coverage of all pairs is checked by brute force on the actual replies. A success is therefore an exact
certificate; a failure means only that the search found nothing.

**56.2 Result: 805/805 after the exact pass.** The first run gave 798/805 (`logs/hash_check.log`). `hash_replay.py`
replays the same RNG stream, reproduces exactly 798/805, and saves the 7 failing rules. All are `junta+`, with R = 13
(k = 40, n = 80, 80, 88) and R = 28 (k = 100, n = 190, 210, 210, 210). `pencil_exact.py` encodes "a labelling of V into
kernel/petals with the right sizes such that each line satisfies one of the explicit membership options of the
min-junta" as SAT. The options are exact consequences of 55.1:
- class c < w: W_{<c} ⊆ K, and either W_c ∉ K with ω non-W_{<c} points of ≺_c before W_c in K, or W_c ∈ Z ⊆ J_c(K);
- class w: W ⊆ K.
All 7 instances are SAT. The pencil is re-verified on the rule verbatim (each line is the reply to a request inside it)
and completed by 55.2. All pairs are covered in 7/7 [computed exact, `logs/pencil_exact.log`].
*Why the search failed* [read off the SAT solutions]:
- the pencils mix classes, e.g. lines via classes (0A, 21A, 0A), (11A, 4B, 12B), (3B, 3B, 8A), but the search builds
  the kernel around one class's prefix and draws the petals at random, so a second class's head lands in the right line
  only by chance;
- option B needs W_c ∈ Z and W_{<c} ∩ Z = ∅, which a uniformly random hole set rarely satisfies.
So `junta+` is not an escape from Theorem W at window T - k/2 + 1. Theorem W's frame (one class, kernel ⊇ W ∪ Z) fails
there by one point, but mixed-class frames exist.
Per-kind medians (frames tried, queries) are in the log. `hash` with R = 64 is the most expensive: median 39 frames and
about 2500 queries at k = 40.

## 57. Random selectors: first-order exponents, and a proof that uniformly random selectors lose

**57.1 Exponents (`exponents.py`, `logs/exponents.log`) [computed float; heuristic as statements about families].**
Nats per k, t = 0.76, across the window:
- γ = (N - t)·h(ω/(N - t)): 0.10 to 0.93;
- the expected number of pencils in a binomial family at the covering threshold, F_tot - 3γ: +2.13 down to +0.27;
- the same in the random-dump model (one uniform dump per request), F_tot + 3p: +2.41 to +2.75;
- Fano-type good sevens at the threshold, G7 - 7γ: +3.38 to +2.20.
These are all positive. So, at first moment, random families of either kind have exponentially many pencils and good
sevens. The shadow exponent at level 3N/7 is negative. (F_tot = N·h(3/(2N)) + (3/2)ln 3 counts all perfect pencil
frames, not only those around a head.) These are first moments only.

**57.2 Theorem R (uniformly random selectors over arbitrary heads lose) [proved by hand; Chebyshev].**
Setting:
- classes r = 1..R, each with a *head* B_r of size exactly ω, arbitrary (equal heads, overlapping heads and greedy
  prefixes are all allowed);
- every request S disjoint from B_r that is sent to class r gets the reply S ∪ B_r (true for full pool pieces, 53.3,
  and for greedy rules with B_r = the first ω points of ≺_r);
- the selector σ is random with P(σ(S) = r) = 1/R for every S disjoint from B_r, independent across requests (the
  replies to other requests are arbitrary).
A *head pencil* for r is a frame (κ ⊇ B_r; P_1, P_2, P_3) whose three requests S_i = (κ ∪ P_i)∖B_r all have σ = r.
Let
- F = C(k+T, T)·C(T, k/2)·C(k, k/2)/6, the number of frames around one head (perfect sunflowers on V∖B_r, |V∖B_r| = k + T);
- D = C(T, k/2)·C(k, k/2)/2, the number of frames through one request.
Then
  **P(no head pencil for any class) <= R²/F + 9/C(k+T, T).**
With 55.2 this gives a good seven (4 | k, T >= 3k/4).
*Proof.* Let X = Σ_r Σ_frames 1[A_{r,F}], where A_{r,F} is the event that all three requests of F are class r. Then
E X = R·F·R^{-3} = F/R². For the variance, take two events A_{r,F} and A_{r',F'} with (r,F) ≠ (r',F'):
- if F and F' share no request, the events are independent;
- if they share a request and r ≠ r', the events are disjoint, so the covariance is negative;
- two distinct frames share at most one request, since two requests S_1, S_2 of a frame determine κ∖B = S_1 ∩ S_2 and
  P_3. So in the remaining case (same class, one shared request) P(both) = R^{-5}.
The number of ordered pairs of distinct frames sharing a request is at most F·3D. Hence
  Var X <= E X + R·3FD·R^{-5}
and, by Chebyshev,
  P(X = 0) <= Var X/(E X)² <= R²/F + 3D/F,
with 3D/F = 9/C(k+T,T). ∎
Remarks.
- The proof uses only 6-wise independence: within a frame (3 requests), within two frames sharing a request (5) and
  within two disjoint frames (6). So **a selector drawn from any 6-wise independent family with uniform marginals
  loses with probability >= 1 - R²/F - 9/C(k+T,T)** [proved, same proof]. The `linear` selectors of §56 are only
  pairwise independent and are not covered. They lost in the computation anyway.
- *Non-uniform marginals* (e.g. σ uniform on the admissible classes {r : S ∩ B_r = ∅}): with p_{S,r} := P(σ(S) = r),
  the same computation gives P(X = 0) <= (1 + 3D)/E X with E X >= F/R². The bound is used as
  P(A ∧ A') <= P(A) when they share a request. So the threshold becomes R² < F/(3D) [proved].
- *Heads larger than ω* (full pieces with |B_r| = b, ω <= b <= n - 3k/2, F(S) = S ∪ B_r when |B_r∖S| = ω): the frames
  are (Z ⊆ B_r, |Z| = ω; κ ⊇ B_r), with
    F_b = C(b, ω)·C(k+T-(b-ω), T-k/2-(b-ω))·(3k/2)!/((k/2)!³·3!),
    D_b = C(T-(b-ω), k/2)·C(k, k/2)/2.
  The same proof gives P <= R²/F_b + 3D_b/F_b. **For b > n - 3k/2 no head pencil exists at all**: three lines that all
  contain B_r would meet in more than n - 3k/2 points. 53.2 allows heads up to q, and q exceeds n - 3k/2 for most of
  the window. Such heads are outside Theorem R and outside every pencil argument.
Numbers [computed exact, log-binomials; `random_selector.py`, `logs/random_selector.log`]: the threshold R < F^{1/2},
written as R < e^{ρk}, has
- ρ = 0.823 at k = 8, 1.105 at k = 40, 1.145 at k = 100, 1.178 at k = 400, 1.1906 at k = 4000;
- at first order Φ/2 with Φ = (1+t)h(t/(1+t)) + t·h(1/(2t)) + ln 2: 1.183 at t = 0.75, 1.1925 at t = 0.76, 1.229 at t = 0.8;
- for non-uniform marginals, (Φ - d)/2 = (1+t)h(t/(1+t))/2 = 0.60, with d = t·h(1/(2t)) + ln 2.
Φ does not depend on N: the frames around a head live on V∖B_r, which has k + T points for every N.
Sanity simulation, (8,6,16), random heads, independent uniform σ, 5 samples per R; the observed counts match F/R²
[computed exact per sample]:
| R | head pencils found | F/R² |
|---|---|---|
| 16 | 1913–2142 | 2053 |
| 64 | 120–163 | 128 |
| 256 | 4–10 | 8 |
| 1024 | 0–2 (2 of 5 samples had none) | 0.5 |
**This makes 53.4(b)'s first-moment heuristic rigorous, with the same exponent Φ/2 = 1.19**: a uniformly random selector
over pool heads of size ω loses with high probability unless it has e^{(1.19 - o(1))k} classes. The number of requests
is e^{(1.22..1.43)k}, so a surviving random selector needs nearly a class per request.

## 58. Deterministic selectors: the kernel-density theorem, what an escape must look like, three classes

**58.1 Theorem H (kernel density) [proved by hand; the averaging of 39.2].** Let 𝒞 be T-covering, 4 | k, T >= 3k/4, and
let κ ⊆ V with |κ| = n - 3k/2. If more than 2/3 of the C(3k/2, k/2) lines κ ∪ P (P a half of V∖κ) are members, then 𝒞
has a good seven.
*Proof.* The partitions of V∖κ into three halves form a 3-uniform hypergraph on the halves. Every half lies in exactly
d = C(k, k/2)/2 of them, so there are (number of halves)·d/3 of them. If none has all three lines in 𝒞, each contains
a half whose line is a non-member. Counting gives (number of halves)·d/3 <= (non-member halves)·d. A pencil therefore
exists, and 55.2 finishes. ∎ (2/3 is sharp over one kernel, 48.1.)
**For greedy rules (star hitting).** Let J ⊆ κ be an initial segment of ≺_c with |J| >= ω. If σ((κ ∪ P)∖Z) = c for some
ω-set Z ⊆ J, then κ ∪ P is a member (55.1). So it suffices that more than 2/3 of the halves P are *c-hit*: c occurs
among the σ-values on the star {(κ ∪ P)∖Z : Z ∈ C(J, ω)}. Two special cases:
- Theorem W is the case where every star contains one request of class r (the one containing W).
- An independent uniform σ: take κ = J = the first n - 3k/2 points of ≺_c. A star has C(n - 3k/2, ω) requests and
  P(not hit) = (1 - 1/R)^{C(n-3k/2, ω)}, so Markov gives a good seven with probability >= 1 - 3e^{-C(n-3k/2,ω)/R}
  [proved]. This is weaker than Theorem R in R (first-order exponent (N - 3/2)h(ω/(N - 3/2)) <= 0.52 against 1.19).
  But its hypothesis is deterministic and local: one class, one kernel, density 2/3.

**58.2 What an escape must do [proved: necessity; the names are descriptive].** A selector survives Theorem H only if
**for every kernel κ, at least a third of the lines over κ are non-members**. For a greedy rule, a non-member line
K = κ ∪ P must satisfy, for every class c, σ(K∖Z) ≠ c for every ω-set Z ⊆ J_c(K). So for every c, at least a third of
the stars around every c-prefix kernel must avoid c entirely. Since each star has C(|J|, ω) = e^{Θ(k)} requests,
avoiding c on it is a strong correlation between σ(S) and the position of S's holes relative to ≺_c. This is the
anti-plan principle ("send S away from the class whose head S leaves open") made quantitative. A selector that is
balanced on stars, meaning that each class c has density bounded below on more than 2/3 of the stars of some c-prefix
kernel, loses. `early`, `late`, `early^hash` and `midhash` are anti-plan attempts, and every one of them lost (§56). The
SAT escapes of 55.3 are such correlations at k = 8, where a star has only C(n - 12, ω) <= 10 requests.
With pool heads, the analogous necessary condition says that for every r, at least a third of the head frames around
B_r have a request not in class r, for every kernel. By Theorem R this holds for no selector with uniform 6-wise
independent randomness and R < e^{1.19k} classes.

**58.3 Two-ground step: status.** As a statement about all selectors it is false at k = 8 (55.3). It is not needed:
- with any pseudorandom structure, Theorem R and 58.1 give a one-class pencil and never use a second ground;
- for deterministic two-class rules the exact computations go further than the pencil: every pencil-free selector at
  (8,6,17) rev and (8,7,16) rev has a good seven (55.4). (8,6,15) rev: see 55.5.
**Dead:** the two-ground sunflower step (48.3) as a universal lemma. **Open:** its first-order form, i.e. whether escapes
need ω = O(1) (all three exact escapes have ω <= 3 and stars of at most 10 requests).

**58.4 Three classes, and Theorem T / Q′ frames.** Exact, k = 8 (55.3–55.4):
- (8,6,17) R = 3 rand 0: no pencil-free selector;
- (8,6,17) R = 3 rand 1: 300 successive pencil-free selectors, each with a good seven (not exhausted);
- (8,6,15) R = 3 rand 1: one pencil-free family, undecided.
Every good seven found in 55.4 is a certificate of any shape (pencil + 4, Theorem T + 4, Q′ + 3, or other), so those runs
already contain the T/Q′ frames. The density analogue of 58.1 holds for them: within an orbit of triples (or
quadruples) of a fixed Theorem-T (or Q′) shape under the stabiliser of a frame partition, a family with no whole
frame misses at least 1/3 (or 1/4) of the orbit [proved, same averaging]. These thresholds are no better than the
pencil's. I found no argument in which T/Q′ frames beat an escape that the pencil cannot. **Not done:** a SAT run that
forbids pencils, Theorem-T frames and Q′ frames simultaneously and asks for a selector avoiding all three (the
natural next exact test of "(Σ) for 3-class greedy rules"). escape_check's forbidden-seven loop is the stronger test,
and it was run.

## 59. The pseudorandomness condition, stated to join with §54

**59.1 Statement.** Let 𝒞 be T-covering, 4 | k, T >= 3k/4. Take any piece R_i of §54's (DEC) that is full (53.3: F(S)
= S ∪ B_i on R_i) with ω <= |B_i| =: b <= n - 3k/2. Let 𝔉_i be its head frames: pairs (Z ⊆ B_i, |Z| = ω;
κ ⊇ B_i, |κ| = n - 3k/2) with three disjoint halves of V∖κ, the requests being (κ ∪ P_j)∖Z.
**(PR_i) some head frame of B_i has all three of its requests in R_i.**
(PR_i) for one i gives a good seven [proved: 55.2]. Each of the following implies (PR_i) [proved]:
- **(PR-density)** for some (Z, κ), more than 2/3 of the halves P have (κ ∪ P)∖Z ∈ R_i (Theorem H; deterministic).
- **(PR-random)** the assignment of requests to pieces is drawn from a 6-wise independent law, all heads have size b,
  and P(S ∈ R_i) >= 1/R for every request of every 𝔉_i. Then some (PR_i) fails with probability at most
  (1 + 3D_b)·R²/F_b. If the marginals are exactly 1/R, the bound improves to R²/F_b + 3D_b/F_b, i.e. the condition is
  R < e^{(Φ_b/2 - o(1))k} with Φ_ω = Φ (Theorem R).
**Joined with (DEC):** CP holds for every T-covering family whose (DEC) has a full piece with head size in
[ω, n - 3k/2] satisfying (PR-density), and with high probability for every family whose selector over such pieces is
6-wise independent with fewer than e^{(Φ_b/2 - o(1))k} pieces [proved, given 53.1].

**59.2 What is left, exactly.**
(i) *Deterministic hash-like selectors.* These are selectors with no randomness to exploit that keep, for every piece,
at least a third of every kernel's head frames out of the piece (58.2). The question is whether such a selector can also
be T-covering and avoid every other certificate. Exact data say "yes, against the pencil" at k = 8 for some orders, and
"no, against all certificates" in every case decided so far (55.4; (8,6,15): 55.5).
(ii) *Large heads* b > n - 3k/2. No head pencil exists. Certificates must combine pieces, which is §54's (DEC-mix).
(iii) *The remainder of (DEC)* and non-greedy rules (48.5), untouched here.
**Dead (this part):**
- the 7 `hash_check` failures as escapes (they are search failures);
- the two-ground pencil step as a universal statement (55.3);
- the inference "three classes escape every pencil" from χ(ℋ(4,3)) = 3 (55.3);
- deterministic spectral counting of pencils at density 1/R. The Kneser-type frame hypergraph over a kernel has second
  eigenvalue ratio 1/2 (the Kneser graph K(3h, h) has λ_1/λ_0 = -1/2). Discrepancy bounds therefore cannot reach the
  densities e^{-Θ(k)} of 53.4(b) [proved: eigenvalue of the Kneser graph; as a no-go, heuristic].
**Next step.** Run the exact SAT of 58.4 with pencils, T-frames and Q′-frames all forbidden at (8,6,16)–(8,6,17), R = 2, 3.
Prove or refute "escapes need ω = O(1)": a first-order version of 58.2's star condition with |J| - ω linear.

Self-check (Part XI):
- 55.1 is the definition of the reply read backwards.
- Theorem R: the covariance cases were checked by hand. Two frames sharing two requests coincide, since S_1 ∩ S_2 is the
  kernel and the complement of S_1 ∪ S_2 is the third petal. The count E X = F/R² matches the simulation within
  sampling error at four values of R. F = 525 525 at (8,6) agrees with 48.2's edge count.
- Theorem H: the double count assumes that every half lies in the same number of partitions; it does, by Sym(V∖κ).
- The 56.2 SAT options were derived from 55.1 for the min-junta. Each SAT pencil is re-verified against the rule's own
  replies, so an encoding error could only lose pencils, not invent them.
- 55.5: only τ is settled; the good-seven question is recorded as undecided unless the configuration run finished (table).
- Not machine-checked: the 6-wise independence remark, the non-uniform and large-head variants (same proof, bounds by
  hand), and the T/Q′ averaging in 58.4.

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

=============================================================================================
# Part XIII — the bottom strip 3t − 1/2 < N <= 5t − 2 (§90–§94)

Brief: close the strip ω <= 4ε (the 21.2 GAP, LEDGER V4), or show it is as hard as the rest of the window.
Code: `compute/strip/pair_window.py` (exact MILP plus a brute-force pair check), `compute/strip/density_rate.py`.
Logs are in `compute/strip/logs/`. Units k = 1 unless finite k is stated.
**Outcome.** For ε <= ε_0 (an absolute constant from Frankl–Rödl) and k >= k_0(ε), CP holds for every N with
n <= 5T − 2k (k even) or n <= 5T − 2k − 2 (k odd). At first order that is every ω <= 4ε: the WHOLE strip. The ratio
ω/ε = 4 is the largest this certificate can reach.
This is not a game strategy. It is a family statement: a density theorem forces two members whose intersection lies in
the 77.1 window Z, and Z's five static lines finish the seven. No steering lemma, no adaptivity, no deficit bound.
The route is the conditional ROADMAP L4 / NEW_PATHS 13.3 / CORE §11-end one. New here:
- the FR statement checked against a source;
- uniformity in α handled by padding;
- an exact finite-k certificate, with a hand proof of the parity rule.
ε_0 is ineffective (it comes from FR's δ). Small ε is all Erdős #644 needs. No independent verifier has checked this
part yet.

## 90. The certificate: one pair in Z [proved by hand (re-derived from 77.1); computed exact]

**Lemma 90.1 (= 77.1).** Let K, K' be members of a T-covering family 𝒞 of c-subsets of V, |V| = N, with
o := |K ∩ K'| ∈ Z := [N − 2t, 3t − 2]. Then 𝒞 has a good seven.
*Proof.* Label K, K' by the Fano points 0, 1, with lines {012, 034, 056, 135, 146, 236, 245}. Place the classes:
- O = K ∩ K': o − y points on line 012, and y/4 on each of 034, 056, 135, 146;
- A = K ∖ K': in halves on 034, 056;
- B = K' ∖ K: in halves on 135, 146;
- G = V ∖ (K ∪ K'), of mass 2 − N + o: in halves on 236, 245.

Each point's line meets {0, 1} only inside its co-type so far. For j = 2..6 let L_j be the union of the classes on lines
through j. Then |L_2| = 2o + 2 − N − y and |L_3| = … = |L_6| = (y + N − o)/2. Some y ∈ [0, o] makes all five <= t iff
N − 2t <= o <= 3t − 2. By T-covering each L_j lies in a member K_j. Every co-type then contains a line (monotonicity,
1.1), and two lines meet. ∎ Z ≠ ∅ iff N <= 5t − 2 iff ω <= 4ε, and |Z| = 4ε − ω.

**90.2 Finite k, parity rule [proved by hand].** Put y = 0.
- *k even, o := n − 2T.* Then |A| = |B| = 2T − k and |G| = 2k − 2T are all even. Split each in exact halves:
  |L_3| = … = |L_6| = (n − o)/2 = T, and |L_2| = 2o + 2k − n = n − 4T + 2k <= T iff n <= 5T − 2k.
- *k odd, o := n − 2T + 1.* Then |A| = |B| = 2T − k − 1 are even and |G| = 2k − 2T + 1 is odd. Put the extra G point on
  line 236: |L_3| = |L_6| = T and |L_4| = |L_5| = T − 1. Also |L_2| = n − 4T + 2k + 2 <= T iff n <= 5T − 2k − 2.

Nonnegativity of the cells is clear in the strip. So for n in the strip there is an explicit integer ℓ(n, k, T) for
which any two members meeting in exactly ℓ points give a good seven.

**90.3 [computed exact].** `pair_window.py k T n` solves the exact integer assignment (every cell to every compatible
line; HiGHS MILP) for each o. For each feasible o it builds the seven real sets and pads every L_j to n − k points
(random, low-line-first and greedy orders). Every pair is then checked by brute force.
- Sweep `logs/sweep.log`: k ∈ {24, 32, 40, 48, 60}, T = 3k/4 + e (e = 1, 2, 3), every n from ⌈3T − k/2⌉ to 5T − 2k.
  That is 75 triples. Z_k is nonempty at every one and always contains n − 2T. Paddings: 0 failures. Extra points
  (40, 31, 72–76) and (100, 78, 185–191): 0 failures in 30 or 12 paddings per o.
- Odd k (41, 32 | 33 | 34; 61, 47 | 49): Z_k = ∅ exactly at n ∈ {5T − 2k − 1, 5T − 2k}, and nonempty with
  min Z_k = n − 2T below that. This matches 90.2: the rounding loss is real, and it is at most 2 points.

## 91. Density forces the pair [proved by hand, citing Frankl–Rödl]

**Theorem FR** (Frankl–Rödl 1987; statement read in Keevash–Long, TAMS 369 (2017) 1147–1162, Thm 1.1). Let
α, η ∈ (0, 1) with η <= α/2, k' = ⌊α n'⌋, and ℓ ∈ [max(0, 2k' − n') + η n', k' − η n']. Then every
𝒜 ⊆ C([n'], k') with |A ∩ B| ≠ ℓ for all A, B ∈ 𝒜 has |𝒜| <= (1 − δ)^{n'} C(n', k'), where δ = δ(α, η) > 0.
**Theorem 91.1 (strip).** There is an absolute ε_0 > 0 with the following property. Let 0 < ε <= ε_0, k >= k_0(ε),
T = (3/4 + ε)k, and 7k/4 <= n <= 5T − 2k (minus 2 if k is odd). Then every T-covering family 𝒞 of (n − k)-subsets of
an n-set has a good seven.
*Proof.*
1. **Size.** Each member contains C(n − k, T) T-sets. So |𝒞| >= C(n, T)/C(n − k, T) = C(n, n − k)/C(n − T, ωk).
2. **Fix α.** FR's δ depends on α, and n/(n − k) moves with N. Add m := ⌈7(n − k)/3⌉ − n isolated points.
   - m >= 0 iff n >= 7k/4, and m ≈ (4δ/3)k, writing δ = N − 7/4 for the excess (not FR's δ).
   - The members are now (n − k)-subsets of an (n + m)-set, with n − k = ⌊(3/7)(n + m)⌋.
   - No intersection changes.
   - Their density in C(n + m, n − k) is at least 1/[C(n − T, ωk) · C(n + m, n − k)/C(n, n − k)] =: e^{−r(n + m)}.
   - r = O(ω ln(e/ω) + δ) = O(ε ln(1/ε)), because ω <= 4ε and δ <= 5ε.
3. **Apply FR** with α = 3/7, η = 1/14 and ℓ the integer of 90.2 (≈ k/4).
   - Since 2k' − n' < 0, the range is [η n', k' − η n'] ≈ [k/8, 5k/8], which contains ℓ with room for small ε.
     `density_rate.py` reports "FR range ok" at every tested point.
   - Choose ε_0 so that r < −ln(1 − δ(3/7, 1/14)) throughout the strip.
   - Then 𝒞 is not ℓ-avoiding: two members meet in exactly ℓ points.
4. **Finish** by Lemma 90.1 at finite k (90.2). ∎

Rates r [computed: exact integer binomials, logs in float] (`logs/density_rate.log`). At ω/ε = 3.9 and
ε = 0.04, 0.02, 0.01, 0.005, 0.002, 0.001: r = 0.279, 0.180, 0.109, 0.064, 0.030, 0.0165. So r → 0 like ε ln(1/ε),
while FR's δ is fixed. ε_0 is whatever FR's (unknown, small) δ allows.

**Range.** The argument needs only ω <= 4ε (so that ℓ exists) and N >= 7/4. It also covers N <= 3t − 1/2, which
re-proves 16.A's range independently for small ε. It stops at N = 5t − 2 exactly: above that Z = ∅, and a single pair
carries no certificate.

## 92. Why the game routes failed here, and what that means [proved by hand where stated]

**The strip is NOT as hard as the rest of the window, but only in the family form.**
- In the 7-request game her own request makes the pair. He steers o through a window of width ω > |Z| = 4ε − ω (77.1).
  One adaptive reply plus a static finish does not help (77.2, float).
- In the family form she does not build the pair. 𝒞 has density at least e^{−rn}, and FR then guarantees a pair with
  o exactly ℓ.
- Steering is a statement about one reply. Avoiding ℓ is a statement about all pairs, and it costs density the family
  does not have.
- CP is the family statement (§7, TWIN 16.2), so this is legitimate. The transfer lemma 75.3 is not needed.

**Adaptive triangle: dead** [proved by hand for symmetric private-part splits b_s = d_s; consistent with 77.2].
Choose S_3 after seeing o, then finish statically. Take the worst dump vertices: ω into a private part, ω into g, or
ω into O. They leave the o-window [1/4 − ε + 5ω/2, 1/4 + ε + ω/2], which is nonempty only for ω <= ε. That lies
inside 16.A's range.

**Deficit bound: does not rescue 21.2.** "Each reply has only ω of free mass" does not save the fixed-labelling count.
- The W-dumper spends exactly ω per reply (22.3). His total is 5ω against her budget of 4ω + 4ε.
- Steering at reply 2 is free for him: both choices cost 0 in the potential (22.1).
- At ω = 4ε there is zero slack, so any steering defeats the count.
- **21.2 stays a GAP as written.** Its conclusion now holds for ε <= ε_0, by Theorem 91.1 (a different proof).

**Q′ quadruples** were not needed and not pursued.

## 93. Self-check

- I re-derived 90.1's two load formulas from the incidence table. I also re-derived the necessity half of 77.1:
  o >= N − 2t from 2(N − o) <= 4t, and o <= 3t − 2 from the y-count.
- The parity rule 90.2 was derived by hand before it was observed in the MILP. It explains exactly the odd-k empty
  windows.
- The FR statement was read from the Keevash–Long PDF (Thm 1.1: η <= α/2; ℓ ∈ [max(0, 2k − n) + ηn, k − ηn]).
  NOTES.md (R2) had quoted it from a survey only.
- `density_rate.py` asserts the floor identity n − k = ⌊3(n + m)/7⌋ and m >= 0 at every tested point.

## 94. Status, dead routes, what remains

**Status.** For ε <= ε_0 and k >= k_0(ε), the strip 3t − 1/2 < N <= 5t − 2 is closed (finite k: 90.2's bound). Tags:
proved by hand, modulo the cited FR theorem; finite-k certificate exact.
- LEDGER should move "window lower end" from GAP to HAND (the new proof of §91, not 21.2), pending a verifier.
- **The open core window becomes 5t − 2 < N < 3 − t** (for small ε). The top 2 points at odd k are absorbed by the
  next case or by monotonicity in T.

**Dead.**
- The adaptive triangle with a static finish (§92).
- The fixed-plan count of 21.2 as a proof (§92).
- The game form as a route through the strip: unnecessary.

**Does density go further? [heuristic; = NEW_PATHS 13.3(ii)]** Probably not.
- Above 5t − 2 every certificate needs three members with a degenerate Venn cell (triple part <= 4ε, 35.2).
- Forcing a cell of relative size γ costs density of about e^{−γ ln(1/γ) k}.
- The guaranteed density is e^{−ω ln(e/ω) k} with ω > 4ε. That is the same order, with the constants on the wrong side.
- A multi-set FR (in the spirit of Keevash–Long's vector versions) at that scale is the only density continuation, and
  it is not expected to work.

**For the verifier.**
- (a) Uniformity of FR's δ, handled by padding to α = 3/7.
- (b) 90.2's two parity cases, including the nonnegativity of all cells at the strip's lower end.
- (c) Whether "small ε suffices" is acceptable for the global argument. It is for f(k,7) <= (3/4 + ε)k, which is
  monotone in ε.
- (d) That CP's family form is the right target (TWIN 16.2).

=============================================================================================
# Part XIV — how far up the window can density go? (§95–§99)

Brief: can a forbidden-configuration (density) theorem do in 5t − 2 < N < 3 − t (ε → 0: 1.75 < N < 2.25) what
Frankl–Rödl did in the strip (§91; verified in notes/verify/bottom_strip.md)?
Code: `compute/strip/window_density.py` (MILP for static certificates on scipy/HiGHS, rate tables, Frankl–Wilson
rates). Logs: `compute/strip/logs/{threshold_check, rate_table, fw_rate, fw_eps0, thresh_*}.log`. Units: k = 1.
**Outcome.**
- (Σ) has one shape with first-order slack: the Q′ quadruple (a). The pencil (b) and the Theorem-T triangle (c) are
  boundary patterns with tolerance O(ε) (§95).
- **Density alone cannot work anywhere above the strip.** Theorem 96.1 is proved by hand. Take one point outside
  every member and a core of mass (δ + 3ε)/2 inside every member. That kills every static certificate of every
  order r <= 7, and the family has density e^{−ρk} with ρ <= 0.17·γ as ε → 0 (ρ <= 0.28·γ for ε <= 0.05). The same
  construction inside a link kills every link-density argument.
- Requiring every point to be covered (all small links dense) does not rescue the route above N ≈ 1.77 (§98.3,
  computed float). Below that, only a sliver of width about 0.02 in N is not refuted by the families tested, and
  no theorem is known there.
- Bonus (§98.1): in the strip, Frankl–Wilson gives an EXPLICIT rate. So ε_0 ≈ 0.0088 is effective, except on a
  vanishing top sliver.

## 95. Which (Σ)-shapes are prescribed-pattern configurations [proved by hand]

**Pattern.** A pattern of r members is a Venn vector v = (v_I)_{I ⊆ [r]}, where v_I is the mass of points whose
co-type among K_1..K_r is exactly I. It satisfies Σ_I v_I = N and Σ_{I ∋ i} v_I = c.

**Open.** Call a pattern class *open* if its certifying set has nonempty interior in that affine slice. Only open
targets fit FR / Keevash–Long-type theorems. Those need every cell bounded away from 0 and a tolerance that does not
depend on ε.

- **(a) The Q′ quadruple is open.** Put s_0 = v_∅, s_1 = Σ_{|I|=1} v_I, σ = s_0 + s_1, and v_ij for the pair cells.
  The certifying set is
      σ <= (3t − N)/2,   v_12 + v_34 + σ <= t,   v_13 + v_24 + σ <= t,   v_14 + v_23 + σ <= t
  (the matchings condition is the reading confirmed by the verifier, Qprime_Sigma_density.md (2)).
  - Its total slack is δ + 3ε > 0, by the §4 identity W = 2N − 4 + 2σ <= δ + 3ε. So the set is open for N > 7/4.
  - Example at N = 2: σ = 0 and all six pair cells equal to 1/3. Each matching load is 2/3 < t.
- **(b) The pencil is not open.** The verifier's reading is triple cell κ >= N − 2t and K_1 ∪ K_2 ∪ K_3 = V.
  - Union V means v_∅ = 0, so the pattern lies on a face of the simplex.
  - Union V also forces κ <= N − 3/2. So κ lies in [N − 2t, N − 3/2], an interval of width 2ε.
- **(c) Theorem T is not open.** It needs κ <= 4ε (35.2), which is a face up to O(ε), with the pair cells within O(ε)
  of a* = N/2 − 5/8.
- **In general (2.3),** a certificate that uses q members in full and 7 − q requests has slack (q − 3)δ + (7 − q)ε.
  - Only q >= 4 gives an open pattern.
  - q = 2 is open only in the strip (the window Z of §90).
  - q = 3 is always a boundary pattern.

## 96. Density alone fails above the strip [proved by hand; MILP-confirmed, computed float]

**Static r-certificate.** This is r members K_1..K_r together with 7 − r requests L_j with |L_j| <= t, such that the
minimal co-types J_x = {i <= r : x ∈ K_i} ∪ {j > r : x ∈ L_j} are nonempty and pairwise intersecting.
- By 1.1 and monotonicity, any T-covering family containing K_1..K_r then has a good seven.
- §90 (r = 2), (Σ)(a)–(c) (r = 4, 3, 3) and a good seven among members (r = 7) are all instances.

**Density-only argument.** This is a theorem of the form "density >= e^{−ρ'k} forces some static certificate",
applied with ρ' = γ.

**Theorem 96.1.** Suppose δ > 5ε (above the strip) and N < 3 − t. Let x_0 ∈ V, and let Y ⊆ V ∖ {x_0} have mass
y > (δ + 3ε)/2. Then G = {K ∈ C(V, c) : x_0 ∉ K, Y ⊆ K} contains no static r-certificate, for any r.

*Proof.*
1. **Every co-type has size >= 3, also for N >= 2.**
   - J_{x_0} ⊆ {r+1, …, 7}, because x_0 lies in no member.
   - Every other co-type meets J_{x_0}, so no co-type lies inside [r].
   - A co-type {i, j} with i <= r < j would need c + t >= N. A co-type {j, j'} of two requests would need 2t >= N.
     Both fail because t < 1. Singletons fail too.
2. **Waste budget.** Σ_x |J_x| <= rc + (7 − r)t. Hence Σ_x (|J_x| − 3) <= S_r := (r − 3)δ + (7 − r)ε (2.3).
3. **Case analysis on r.**
   - r <= 2: S_r < 0 because δ > 5ε. Impossible.
   - r >= 5: J_{x_0} would need size >= 3 inside at most two requests. Impossible.
   - r = 3: J_{x_0} ⊆ {4, 5, 6, 7}. A Y-point's co-type contains {1, 2, 3} and meets J_{x_0}, so it has size >= 4.
     The waste is then >= y > 4ε = S_3.
   - r = 4: J_{x_0} = {5, 6, 7}. A Y-point's co-type contains [4] and one of 5, 6, 7, so it has size >= 5.
     The waste is then >= 2y > δ + 3ε = S_4. ∎

**Remarks.**
- At finite k, x_0 is a single point and the proof is unchanged, since step 1 is pointwise.
- The r = 4 case is Q′'s W-count again: u_4 >= y gives W >= 2y.
- The threshold is sharp. The MILP finds a 4-certificate at y = (δ + 3ε)/2 − 0.004, and none of any order at
  y = (δ + 3ε)/2 + 0.004. Tested at N = 1.78, 1.85, 1.95, 2.0, 2.1, 2.2, 2.24 with t = 0.7521, x_0 replaced by a cell
  of mass 0.005 (`logs/threshold_check.log`).

**Density of G.**
- |G|/C(n, c) = (1 − c/n) · C(n − 1 − y, c − y)/C(n − 1, c).
- So ρ = N h(c/N) − (N − y) h((c − y)/(N − y)) + o(1).
- Values at y = (δ + 3ε)/2, from 40 points per ε across 5t − 2 < N < 3 − t [computed float, `logs/rate_table.log`]:

| ε | ρ/γ at low end | ρ/γ at N ≈ 2 | ρ/γ at top | max ρ/γ |
|---|---|---|---|---|
| 0.0001 | 0.081 | 0.145 | 0.167 | 0.167 |
| 0.001 | 0.102 | 0.148 | 0.168 | 0.168 |
| 0.01 | 0.183 | 0.169 | 0.180 | 0.183 |
| 0.05 | 0.275 | 0.262 | 0.241 | 0.275 |

- At N = 2, as ε → 0: ρ = 0.091 against γ = 0.626.
- Near the bottom (δ ↓ 5ε), ρ ≈ 4ε ln(N/c) ≈ 3.4ε while γ ≈ 4ε ln(e/4ε). So the ratio → 0 as ε → 0 [heuristic
  asymptotics; the table is the computed statement].

**Corollary 96.2.** Fix N with 5t − 2 < N < 3 − t and ε <= 0.05 (tested range). Then the statement "every family of
c-sets of density >= e^{−γk} contains a static certificate" is false. G is a counterexample with exponential room:
ρ <= 0.28·γ.
- So no forbidden-pattern rate, explicit or ineffective, can reach γ for (Σ)(a), (b), (c), or for any other static
  certificate.
- **Dead route.**

**Links.** T-covering gives the same γ in every link 𝒞_A = {K ∈ 𝒞 : A ⊆ K}: the ground becomes N − a, the sets
c − a, the requests t − a, and ω and N − t are unchanged.
- A link-density argument finds a certificate whose members all contain A.
- Put G_A = {K ⊇ A ∪ Y' : x_0 ∉ K} with x_0 ∉ A. Theorem 96.1 applies verbatim with Y = A ∪ Y'.
- Inside the link, the cost is that of Y' alone. It is zero once |A| > (δ + 3ε)/2.
- **Dead**, for every A.

## 97. Literature: forbidden vector / pattern intersection theorems

Tags: [literature, checked] means I read the statements quoted, in the PDF or the ar5iv text. "Abstract only" and
"recalled" mean exactly that.

- **Keevash–Long, "Frankl–Rödl type theorems for codes and permutations"** (TAMS 369 (2017); arXiv 1402.6294).
  PDF read: Thm 1, Lemmas 10–11, Thm 12, Cor 13, Thms 2, 3, 6, and the §2 proof. [literature, checked]
  - Pairs only.
  - FR (Thm 1) is reproved from Frankl–Wilson (Thm 12). The proof uses Baker–Harman three-prime splitting (Thm 14)
    and dependent random choice (Lemmas 10–11).
  - So δ(α, η) is effective in principle, but no value is given. The authors say the new proof "does not seem to
    improve on the bounds" of FR.
  - Thm 6 forbids weak k-petal sunflowers in [q]^n (all pairwise agreements of EQUAL size), with δ(k) not explicit.
    This is a pattern on pairwise sizes, not a Venn pattern.
- **Keevash–Long, "Forbidden vector-valued intersections"** (PLMS 121 (2020); arXiv 1706.03740). ar5iv read: Thm 1.1,
  the Thm 1.9 dichotomy, Thms 1.13–1.14, §6 Thms 6.2–6.4, Lemma 8.1. [literature, checked]
  - The intersections are vector-weighted, but always of PAIRS.
  - The multi-family statement (Thm 6.2, |S| <= C) is reduced to |S| = 2 by Lemma 8.1.
  - All constants come from hierarchies n^{−1} ≪ δ ≪ ε, so they are ineffective.
  - There is no prescribed Venn pattern for r >= 3 sets.
- **Frankl–Rödl, "Forbidden intersections"** (TAMS 300 (1987)). Abstract only (AMS page), plus the statement as
  given in KL.
  - Pairs, with ineffective δ.
  - Weak Δ-systems of size r (pairwise intersections all equal) are forbidden at density (2 − ε_r)^n, with ε_r
    ineffective.
- **Ellis–Keller–Lifshitz** (arXiv 1604.06135). Abstract only.
  - Forbids |A ∩ B| = t − 1 for FIXED t, with o(n) <= k <= n/2 − o(n).
  - The forbidden intersection is constant, not linear, so this is not our regime.
- **Frankl–Füredi 1985; Keevash–Mubayi–Wilson 2006 (no singleton intersection).** Recalled, not read.
  - Exact results for fixed k or a fixed intersection value. Neither linear nor about r-tuples.
- **Frankl–Wilson** (statement as KL Thm 12, read). [literature, checked]
  - If k − l is a prime power and 2l + 1 <= k, an l-avoiding family of k-sets has |𝒜| <= C(n, k − l − 1).
  - **Explicit**, but pairs only. Used in §98.1.

**Summary.** In what I read, no theorem gives density <= e^{−δn} for families avoiding a prescribed Venn pattern of
r >= 3 sets in the linear regime, explicit or not. Corollary 96.2 makes this moot above the strip: no such theorem,
however strong, could be applied there.

## 98. The quantitative question

**98.1 Explicit ε_0 in the strip [proved by hand from FW; computed float].**
- **Setting.** §90's ℓ = o = n − 2T has c − ℓ = 2T − k =: p. Also 2ℓ + 1 <= c, because N < 4t − 1.
- **FW bound.** If p is a prime power, FW gives density <= C(n, p − 1)/C(n, c) = e^{−δ_FW k}, where
  δ_FW = N[h(c/N) − h((2t − 1)/N)] (≈ 0.149 at N = 7/4).
- **Comparison.** T-covering gives density >= e^{−γk}. So the pair exists once γ < δ_FW on the whole strip
  3t − 1/2 <= N <= 5t − 2, and the worst point is the top.
- **Value.** Bisection gives **ε_0^{FW} = 0.00881** (`logs/fw_eps0.log`). The table in `logs/fw_rate.log` has
  margin +0.123 at ε = 0.001 and −0.015 at ε = 0.01.
- **Primality.**
  - ℓ may be any integer of Z_k (§90, width (4ε − ω)k), so p ranges over an interval of that length.
  - That interval contains a prime once (4ε − ω)k >= k^{0.525} (Baker–Harman–Pintz, effective for large k).
  - This needs every o inside Z_k to be certifying at finite k, not only n − 2T. §90.3's MILP solved each feasible o,
    but I did not re-check parity for every o [heuristic for that step].
  - The top sliver, 4ε − ω < k^{−0.475}, stays with the verified ineffective FR argument.
- **Net.** §91 becomes effective, with ε_0 ≈ 0.0088, on all of the strip except a vanishing sliver.

**98.2 Above the strip, no static pattern has an explicit δ > γ (§96).** The obstruction costs ρ <= 0.17γ as ε → 0.
It does not depend on γ(2) ≈ 0.63 being large: even at the bottom of the window, ρ/γ ≈ 0.08.

**98.3 What T-covering adds beyond density, and whether that rescues the route.**
- **Where G fails.** G violates T-covering in exactly one way: the t-sets through x_0 are not covered. So any proof
  must use members through every point.
- **The hypothesis that remains.** In density language this is local density (LD_a): every link 𝒞_A with |A| <= a
  has density >= e^{−γk}.
  - At a = t this is T-covering itself, since the link density at a t-set is exactly 1/C(N − t, ω). There is
    nothing left to relax.
  - For small a > 0, LD_a is a new hypothesis, and no forbidden-configuration theorem in the literature uses it.
- **Families with every point covered** (MILP over all orders r = 3..7; `logs/thresh_*.log`; t = 0.7501, requests
  tested at mass t + 0.002) [computed float]:
  - Core families {K ⊇ Y} need y > N − 3/2 (the pencil threshold, confirmed by the MILP). Their ρ is below γ only for
    N > 1.842 (crossover: ρ = 0.314 against γ = 0.310 at N = 1.84).
  - Threshold families {|K ∩ W| >= θ} are much better. They satisfy LD_a for a < c − θ ≈ 0.36. Best found, over an
    8-point grid in w:

| N | γ | best ρ | (w, θ) | ρ/γ |
|---|---|---|---|---|
| 1.755 | 0.031 | 0.105 | (0.58, 0.390) | 3.38 |
| 1.765 | 0.078 | 0.102 | (0.58, 0.392) | 1.31 |
| 1.770 | 0.098 | 0.102 | (0.58, 0.393) | 1.04 |
| 1.780 | 0.135 | 0.099 | (0.59, 0.395) | 0.73 |
| 1.800 | 0.201 | 0.094 | (0.59, 0.399) | 0.47 |
| 1.850 | 0.335 | 0.101 | (1.52, 0.809) | 0.30 |
| 1.900 | 0.445 | 0.091 | (1.56, 0.848) | 0.20 |
| 2.000 | 0.625 | 0.075 | (1.65, 0.926) | 0.12 |
| 2.100 | 0.772 | 0.050 | (2.00, 1.093) | 0.06 |
| 2.200 | 0.898 | 0.021 | (2.10, 1.176) | 0.02 |

- **Reading of the table.**
  - The "every point covered" refinement is also dead for N >~ 1.771, where these families have ρ < γ.
  - On 5t − 2 < N < ~1.771 (ω up to about 0.02), these families do NOT refute it. Their ρ stays near 0.10 while
    γ → 0.
  - That sliver is the only place left where a local-density / forbidden-pattern argument could in principle
    exceed γ. It would need a new theorem: forbid a static certificate (necessarily a q >= 4 one, by §95, unless
    ω <= 4ε) in families with all small links dense. I know no such theorem [heuristic].
  - The grid gives only an upper bound on the best ρ. A finer search can only move 1.771 down.
- **Traces on a sub-ground W [heuristic].** A trace pattern fixes no co-type outside W, and the x_0 trick can be
  placed outside W. Dead for the same reason as §96.

## 99. Status, dead routes, what remains; self-check

**Status.**
- **(1)** Q′ is the only (Σ)-shape that is an open prescribed pattern. Its certifying set is that of §95(a), with
  slack δ + 3ε. The pencil and Theorem T are O(ε) boundary patterns.
- **(2)** No theorem I checked handles r >= 3 Venn patterns in the linear regime. All the pair theorems are
  ineffective except Frankl–Wilson.
- **(3)** Density-only arguments, global or in a link, are dead throughout 5t − 2 < N < 3 − t. This is proved by
  hand, with room ρ <= 0.28γ for ε <= 0.05.
  - Adding "every point covered" (small-link density) is dead above N ≈ 1.771 [computed float].
  - Below that it is open, and only as an unproved new kind of theorem.
- **Bonus.** The strip's ε_0 is effective, about 0.0088, up to a vanishing sliver.

**Dead.**
- Density ⟹ static certificate, at any N above the strip, for any r and any (Σ)-shape.
- The same argument inside any link.
- Trace versions [heuristic].
- A vector-FR / Keevash–Long continuation (moot by 96.2).
- Point-covered density for N >~ 1.771 [computed float].

**What remains.** Arguments that use the coverage of every t-set, i.e. T-covering proper and not a density
consequence of it. The narrow open density question is the sliver 5t − 2 < N < 1.771: does LD_a (a ≈ 0.3) plus
density e^{−γk} force a Q′-type or other q >= 4 certificate?

**Not covered.** Adaptive finishes, where a pattern is followed by requests chosen after seeing replies. Corollary
96.2 concerns static finishes only. Adaptive finishes bring the game back, and §77 / §92 found the one-adaptive levels
stop at 3t − 1/2 [heuristic for the whole class].

**Self-check.**
- I re-derived steps 1–3 of 96.1. S_r = rc + (7 − r)t − 3N = (r − 3)δ + (7 − r)ε was checked by hand.
- The MILP may take the co-type family WLOG to be a maximal intersecting upset: it holds exactly one of J and
  [7] ∖ J, and it is upward closed. It reproduces three earlier results:
  - §90's strip pair (r = 2 feasible at N = 1.7505), and its absence at N = 1.8;
  - the pencil threshold y* = N − 3/2 at N = 1.8, 2.0 and 2.2;
  - the hand threshold (δ + 3ε)/2 at seven values of N.
- The FW conditions (prime power, 2ℓ + 1 <= c) were checked against KL's statement of Thm 12.
- ρ is computed from first-order entropies, and the x_0 factor (1 − c/n) is polynomial.
- Not independently verified.

=============================================================================================
# Part XV — adaptive density: links, traces, dependent random choice (§100–§104)

Brief: a request S forces a member K ⊇ S, so every link 𝒞_S (|S| <= t) is nonempty and inherits covering. Use requests
or DRC to pass to a sub-configuration that is dense AND covering (which 96.1's family is not), then run the §90 pair
step or FR / Keevash–Long inside it; or chain such steps to a Q′ quadruple or a pencil.
Code: `compute/links/link_check.py` (`exact`: sympy identities; `milp`: static certificates of the pool family inside
links, via `compute/strip/window_density.cert`). Logs: `compute/links/logs/{exact,milp}.log`. Units k = 1.
**Outcome. Dead, for every operation tried, with one exact invariant.**
- Links move (N, t) by (−s, −s). They keep ω and γ and lower ε by s, so they move AWAY from all three closed regions
  (strip, crowded, petal side). For s > ε the reduced statement is false: the pool family is a counterexample (§100).
- Every static certificate, wherever its members come from, pays its waste from S_q(N, t) − 4|S| in V. Here q is the
  number of members used in full and S is the set lying in all seven. Selecting members (links, traces, DRC, density)
  cannot change S_q. Only adaptivity, i.e. replies used in full, raises q (§102).
- The pool family is T-covering and dense, inherits covering in every link, and has no Q′ quadruple and no pair
  certificate above the strip. Its only certificates are pencils, a boundary pattern. So a covering-plus-density
  argument, adaptive or not, needs a separate pencil branch. That is §33(4)'s stability statement again (§103).

## 100. What links inherit, in units [proved by hand; identities computed exact]

**100.1 Inheritance.** Let |S| = s <= t and 𝒞_S = {K ∖ S : K ∈ 𝒞, K ⊇ S}, a family of (c − s)-subsets of V' = V ∖ S.
- (a) 𝒞_S is (T − s)-covering on V': a (t − s)-set R ⊆ V' gives the t-set R ∪ S, which lies in some K ∈ 𝒞, and
  K ⊇ S. In edge form this is vertex deletion, H − S, with τ(H − S) >= τ(H) − s.
- (b) The conclusion transfers both ways. Seven members of 𝒞_S cover all pairs of V' iff the seven K ⊇ S cover all
  pairs of V, since a point of S has co-type [7].
- (c) Nothing more is guaranteed. The link of a link is a link, and every link of the pool family P_Y is again a
  core family, which has no good seven once s > ε (100.3).

**100.2 Parameters.** The edge size is unchanged: (N − s) − (c − s) = 1, so the unit k = 1 survives and nothing gets
renormalised. With the identities from `exact.log`:
  N′ = N − s,  t′ = t − s,  c′ = c − s,  ω′ = ω,  ε′ = ε − s,  δ′ = δ − s,  N′ − t′ = N − t.
- **Strip margin** 5t′ − 2 − N′ = (5t − 2 − N) − 4s. The link moves away from the strip by 4s.
- **Crowded margin** 3t′ − 1/2 − N′ = (3t − 1/2 − N) − 2s. It moves away from TWIN 16.A's region.
- **Petal margin** N′ + t′ − 3 = (N + t − 3) − 2s. It moves away from PETAL's side too.
- **ω′/ε′ = ω/(ε − s)**, which only increases, and t′ < 3/4 once s > ε.
- **Density.** The T-covering bound 1/C(N − t, ω) is the same in every link, so γ = (1 + ω) h(ω/(1 + ω)) is
  invariant, while the ground shrinks. That is §96's remark; the density per ground point gets worse.

So **no link lands in a closed region** if (N, t) is not already in one [proved by hand]. Composing links gives a
single link (S ∪ S′), so chains of links do no better.

**100.3 For s > ε the reduced problem is false [proved by hand; MILP-confirmed, computed float].** The pool family
P_Y = {K ∈ C(V, c) : K ⊇ Y}, |Y| = ω, is T-covering. For S ∩ Y = ∅ its link is the pool family of V′ with the same
core. Any seven members of the link waste 4ω on Y, and the slack identity gives a total of 4δ′ = 4(δ − s). So the link
has no good seven once ω > δ − s, i.e. s > ε (`exact.log`: 4ω − 4δ′ = 4(s − ε)).
- In words: 𝒞_S is dense, (T − s)-covering, and contains no good seven. That is exactly the object the plan needed not
  to exist. The rôle of 96.1's family is taken over, inside a link, by the pool family, with covering intact.
- MILP (`milp.log`, t = 0.76, ε = 0.01, N ∈ {1.80, 1.85, 1.90, 2.00, 2.10}, s/ε ∈ {0, .5, .9, 1.1, 1.5, 3}): the pool
  family in the link has static certificates (orders r = 3..7) for s <= 0.9ε and none of any order for s >= 1.1ε, at
  every N. The bare link has no r = 2 certificate except at s = 0, N = 1.80 = 5t − 2 (the boundary control).
- For s < ε the link is a CP instance that is strictly worse in every margin (100.2). **Links: dead.**

## 101. Dependent random choice and dense links [proved by hand]

**101.1 Averaging.** C(N, s)·C(N − s, c − s) = C(N, c)·C(c, s), so the average over all s-sets S of the density of 𝒞_S
in C(V′, c − s) equals the density of 𝒞. DRC can find links denser than average, but it cannot change the parameters
of 100.2. A dense link is still an instance at (N − s, t − s).

**101.2 Where dense links come from.** In P_Y the link at S ⊆ Y is P_{Y∖S} on V ∖ S. At S = Y it is the complete
family of t-sets on a ground of mass 1 + t, with density 1, and it has a good seven: a Fano blow-up, since
1 + t >= 7/4. The links that contain certificates are the ones inside a core. They contain them because of their
structure (completeness), not because of the (T − s)-covering they inherit: at s = ω > ε that covering is satisfied
by counterexamples (100.3). So DRC is a way of finding cores. It is not a density bootstrap.

**101.3 Pair step inside a link: dead.** A §90 pair found in 𝒞_S, finished by five link requests, is a static
certificate in V with q = 2, all of whose seven sets contain S. By 102.1 it needs ω + 4s <= 4ε, so it never exists
above the strip, whatever S is and however the pair is found (FR, Keevash–Long, Frankl–Wilson, DRC).

## 102. The invariant; traces, exclusions, padding [proved by hand; identities computed exact]

**Theorem 102.1 (slack invariant).** Take a static certificate in V: members K_1..K_q used in full and lines
L_{q+1}..L_7 with |L_j| <= t, whose co-types J_x are nonempty and pairwise intersecting. Let S be the set of points
lying in all seven. If every |J_x| >= 3, then
  Σ_x (|J_x| − 3) + 4|S| <= S_q(N, t) := qc + (7 − q)t − 3N = (q − 3)δ + (7 − q)ε,
where the sum counts only waste, outside S.
- *Proof.* Σ_x |J_x| <= qc + (7 − q)t, and the points of S each contribute 7 − 3 = 4. ∎
- **The hypothesis |J_x| >= 3 holds for q = 2 when t < 2/√5.** A co-type of size <= 2 needs two of the seven sets to
  cover V. Two lines, or a line and a member, cannot (2t < N, t + c < N). Two members can only if N >= 2, and then
  A = K_1 ∖ K_2 and B = K_2 ∖ K_1 have mass 1 each. Every A×B pair must then lie in one of five lines, but
  Σ_j |L_j ∩ A||L_j ∩ B| <= 5t²/4 < 1. So for q = 2 a certificate exists only if ω + 4|S| <= 4ε.
- **Corollary.** S_q depends on (N, t, q) only. An operation that only chooses which members of 𝒞 to use (a link, a
  trace, DRC, a density theorem) cannot add slack. It can only fix S (cost 4|S|) or fix q.
- The link identity S_q(N − s, t − s) = S_q(N, t) − 4s (`exact.log`) is the same statement read inside the link.

**102.2 Traces on W ⊂ V (u = N − |W|, t fixed).** The trace {K ∩ W} is T-covering on W. Its sets have mass >= |W| − 1,
so in W the instance is (N − u, t) with ω_W = ω − u and ε unchanged. That is the favourable direction, and for
u >= ω − 4ε it reaches the strip.
- The gain is fake. The trace instance's budget is S_q(W, t) = S_q(N, t) + (3 − q)u (`exact.log`): for q = 2 it gains u
  exactly because the points of U = V ∖ W no longer have to be paid for.
- A good seven for W leaves the pairs through U uncovered. Any lift to V is a certificate in V, so it is bounded by
  102.1 with the original S_2 = 4ε − ω < 0. **Traces: dead.** This upgrades 98.3's trace remark from heuristic to
  proved, for q = 2. For q >= 3, a trace certificate is just a V-certificate with constraints added.

**102.3 Exclusions (requests "contain S, avoid X").** These cannot be forced. In P_Y no member avoids a point of Y,
so {K ∈ 𝒞 : K ∩ X = ∅} can be empty with X a single point. In edge form this is the contraction H_X (edges ⊇ X),
which inherits no transversal bound. **Dead.** Padding with points that lie in no member moves (N, t) by (+m, 0) and
raises ω; it is only a device for fixing FR's α (§91). Blow-ups do not change the units.

**102.4 Table of moves (k = 1).**

| operation | (ΔN, Δt) | ω | ε | budget in V | conclusion transfers |
|---|---|---|---|---|---|
| link at S | (−s, −s) | = | −s | S_q − 4s | yes |
| trace on W | (−u, 0) | −u (apparent) | = | S_q (apparent: S_q + (3 − q)u) | no; lifting restores S_q |
| exclusion | not forceable | | | | |
| padding | (+m, 0) | +m | = | (not a CP instance) | — |

The only first-order direction that lowers ω/ε, (−1, 0), is not realised by any operation that keeps the conclusion.

## 103. Chains to Q′ or a pencil; what an adaptive-density argument would have to do

**103.1 Q′ cannot be forced by covering plus density [proved by hand; = the verified pool-family miss, V3].**
Every quadruple of P_Y has σ >= 1 − t. The Y points lie in all four members, and in V ∖ Y (mass 1 + t) the four
t-parts have total mass 4t, so the mass of points in at least two parts is at most 2t. But
(1 − t) − (3t − N)/2 = (ω − 4ε)/2 > 0 above the strip (`exact.log`). P_Y is T-covering, has density e^{−γk}, and every
quadruple of members, however it was reached, is a quadruple of P_Y. So **no chain of requests, links and density
steps produces a Q′ quadruple from T-covering alone**, at any N > 5t − 2.

**103.2 The pencil is the only certificate of P_Y, and it is a boundary pattern.**
- In the 100.3 MILP at s = 0, certificates of orders 3..7 exist and order 2 does not; by 103.1 none of them is Q′.
- Inside a link the pencil's window is κ ∈ [N − 2t + 2s, N − 3/2]. Its width is 2(ε − s), so links narrow it.
- A forbidden-pattern theorem needs a tolerance independent of ε (§95), so no density step finds it.

**103.3 Hybrids [heuristic].** a adaptive replies used in full, plus a density pair, plus static requests, have
q = a + 2. For a >= 2 the budget S_q is positive (δ + 3ε at q = 4), and §96.1 does not apply when replies are taken
through the excluded point x_0. So this combination is not killed by any count above. It is killed on P_Y by 103.1
(no Q′ among any four members, replies included), and P_Y is beaten only by a pencil. So any such argument must be a
dichotomy:
- near-pool ⟹ a pencil, by structure;
- far from pool ⟹ an open q >= 4 pattern, by a relative (vector-valued) Frankl–Rödl theorem.

The first half is the stability statement of §33(4). The second would need density e^{−γk} with γ not small
(γ(2) ≈ 0.63), far above any known Frankl–Rödl / Keevash–Long threshold [heuristic; the KL constants are
ineffective, §97]. So adaptive density reduces to the open problem. It is not a new route.

## 104. Status, dead routes, what remains; self-check

**Status.**
- (1) Links inherit exactly (T − s)-covering on V ∖ S, with k fixed. In units: (N − s, t − s, ω, ε − s), with γ fixed.
  Every closed-region margin drops (strip by 4s, crowded by 2s, petal by 2s). For s > ε the reduced claim is false
  (pool family).
- (2) No operation that keeps the conclusion lowers ω/ε. Traces lower it only apparently, and lifting restores the
  V-budget exactly. Exclusions cannot be forced.
- (3) No reduction lands in a closed region. **The blocking invariant is Theorem 102.1:** a static certificate pays
  its waste plus 4·|common part| out of S_q(N, t) = (q − 3)δ + (7 − q)ε, which no member-selection changes. For the
  pair route (q = 2) the condition is ω + 4|S| <= 4ε. For Q′ the pool family blocks it outright (103.1).

**Dead (add to LEDGER).**
- Link / DRC reduction to the strip or the crowded region.
- The §90 pair step or FR / KL inside any link.
- Traces (q = 2 proved; q >= 3 adds nothing).
- Exclusion requests.
- Chains of links to Q′ from covering plus density.

**What remains.** The same as before: a pencil branch for near-pool families (the §33(4) stability statement), combined
with an open-pattern branch elsewhere. Hybrids (103.3) are its only density-flavoured form.

**Self-check.**
- S_q, the link shift −4s, the trace shift (3 − q)u, the three margin changes and the pool σ identity were all
  checked symbolically (`exact.log`).
- The q = 2 hypothesis |J_x| >= 3 was re-derived. The case N >= 2 uses the bipartite bound 5t²/4 < 1, valid for
  t < 0.894.
- 100.3 rests on the slack identity (VERIFIED W2) and is matched by the MILP on both sides of s = ε at five N.
- The MILP is float and Fano-free (all maximal intersecting co-type families). It also reproduces the strip boundary
  at N = 5t − 2.
- Not independently verified.

=============================================================================================
# Part XVI — the entropy method (Gilmer style) for CP (§70–§74)

Brief: for any T-covering family in the window, build a law on 7-tuples (adaptive or correlated) and use entropy
inequalities to show some tuple covers all pairs, i.e. has pairwise-intersecting co-types I_x. Window: 3t - 1/2 < N < 3 - t.
Code: `compute/entropy/` — `entropy_tables.py` (first-order exponents, < 1 s), `fam_certs.py` (exact certificate census on
a finite family, a few minutes), `witness_pair.py` (the coordinator's witness-pair test, seconds). Logs: `compute/entropy/logs/`.
Test families at (k,T,n) = (8,6,15) in `compute/entropy/logs/fam_8_6_15_{pool,randdump_s1,sevenfree}.txt`, plus core9's
`fam_8_6_15_rev.txt`.
**Outcome. CP is NOT proved, and the entropy method is DEAD as a route, in every form I could set up.**
(1) The Gilmer shape needs an upper bound on entropy from "no good seven" and a lower bound from T-covering. It fails at every
point of the window: an explicit 7-free family is larger than the smallest T-covering family (§71.1).
(2) Independent samples (Gilmer, AHS, Chase–Lovett) see only typical tuples. Those leave a constant fraction of the pair mass
uncovered for every law (§71.2).
(3) Correlated, family-dependent laws (Sawin-type) need a correlation inequality on frames (supersaturation of pencils).
It fails exactly on the core9 hash-like family: 0 pencils against a density-product prediction of 128 301 (§72).
A random-dump family matches its prediction (459 702 against 465 265). The core9 family also has no Q′ quadruple, so all of
(Σ) fails on it at finite size with ε = 0 (new). Q′ is absent in every test family at ε = 0.
(4) The exact obstruction (§73) is that every minimal certificate is a cyclic containment constraint on ≥ 3 dumps. Entropy
inequalities give joint lower bounds only along acyclic orders, or through density. Density statements are false here,
and the cyclic statement is the Ramsey/colouring problem of §48.
(5) The witness-pair entropy idea (coordinator) is the first moment over pairs (§73.4). It is dead with uniform or iid laws:
E[#uncovered pairs] is 22 to 31 on all four test families, including ones that do have good sevens. With an adapted law
it is circular.

## 70. Formulation

**70.1 What the method is [literature, checked against the arXiv abstracts].**
- Gilmer, arXiv:2211.09055: if A, B are i.i.d. with Pr[i ∈ A] < 0.01 for all i and H(A) > 0, then H(A ∪ B) > H(A).
  With A uniform on a union-closed 𝓕, A ∪ B ∈ 𝓕 gives H(A ∪ B) <= log|𝓕| = H(A), a contradiction, so some element lies in
  >= 1% of the sets.
- Alweiss–Huang–Sellke (2211.11731), Chase–Lovett (2211.11689) and Sawin (2211.11504) each reach (3 - √5)/2 ≈ 0.38.
  Sawin's abstract also sketches an addition that gives a constant strictly larger, and disproves a conjecture of Gilmer
  that would have implied Frankl. That the "addition" uses correlated A, B is recalled, not checked.

The three ingredients are:
- (S) a law, uniform on the family;
- (U) an upper bound, from closure: the output of an operation stays in the support;
- (L) a lower bound, from the hypothesis, through a per-coordinate inequality.

**70.2 Dictionary for CP [proved by hand].**
- The only "closure" is the lift S ↦ F(S) ∈ 𝒞, F(S) ⊇ S. It is many-to-one, so for every request law ρ,
  H(F_*ρ) >= H(ρ) - E log|F^{-1}(F(S))| >= H(ρ) - log C(c, t)k. With ρ uniform this is Φk, where
  Φ := N h(t/N) - c h(t/c) is the counting bound on |𝒞|.
- The hypothesis "no good seven" is a 7-ary forbidden configuration. It can only give an UPPER bound of ex-type:
  H(F_*ρ) <= Λk for families with no good seven.
- So the Gilmer shape is **(I1)**: Λ < sup_ρ [H(ρ) - E log|fibre|]/k. This would give CP with no structure at all.

**70.3 The cleanest statement that implies CP [proved by hand: it is 2.2 read as an event].** For a law ν on 7-tuples of
requests (adapted to F, which she knows), let K_i = F(S_i) and D_i = K_i ∖ S_i.
**(E)** Pr_ν[ there are lines L_i ⊆ K_i with pairwise-intersecting co-types and Σ_i |D_i ∩ (L_i ∖ S_i)| >= 3N - 7t ] > 0.
- (E) ⟺ CP for N < 11/6 (Fano readings complete, §1.3), and (E) ⟹ CP everywhere.
- (E) with "> 0" is CP itself (cf. 83, second item). The content of an entropy proof is an INEQUALITY that yields the positive
  probability. Three candidates:
  - (I1) entropy/size (Gilmer shape, 70.2);
  - (I2) average inequalities over independent copies (AHS/CL);
  - (I3) a correlation inequality for a family-dependent correlated law (Sawin-type correlation; Sidorenko / Kopparty–Rossman
    sequential sampling).
- Since two replies are free (2.3), the event in (E) needs useful landing >= base = ω - 4ε in the dumps of replies 3–7.
- Each of those landings is a containment D_i ⊆ (target) up to O(ε): a large-deviation event for each reply separately.

## 71. (I1) and (I2) are dead

**71.1 Proposition E0 [proved by hand; numbers computed float on a grid].** Let W ⊆ V with |W| = 7/4 - η, Y' = V ∖ W, and
𝒫' = {Y' ∪ A : A ⊆ W, |A| = 3/4 - η}. Then:
- (i) 𝒫' has no good seven. Y' lies in every member, so a good seven would cover all pairs of W by seven (3/4 - η)-sets.
  That is impossible on fewer than 7k/4 points (80.2).
- (ii) 𝒫' contains a member ⊇ S for every t-set S with |S ∩ Y'| >= ε + η.
- (iii) log|𝒫'| → Λ0 k with Λ0 = log C(7/4, 3/4) = 1.1951.

Hence any bound Λ derived from "no good seven" has Λ >= Λ0, while T-covering guarantees only Φ. `entropy_tables.py`:
E0 = Λ0 - Φ > 0 at all 44 grid points (t = 0.7501, 0.76, 0.78, 0.80; N across the window). It is smallest at the lower
corner (+0.0016 at t = 0.7501, N = 3t - 1/2; +0.073 at t = 0.76) and largest at the top (+0.60). **(I1) is dead in the
whole window.** It is tight only as t → 3/4 at N → 3t - 1/2, which is the 21.2 gap region.

**Blindness to typical requests.** The requests that 𝒫' fails to cover (|S ∩ Y'| < ε) have uniform probability e^{-rk},
r = log C(N,t) - log C(δ,ε) - Λ0. The rate r ranges from 0.0006 (lower corner, t = 0.76) to 0.24 (t = 0.7501, N = 2.25).
So a working law must have relative entropy >= rk to the uniform request law, for each such Y'. It must be built from the
family, as in Gilmer, and it must avoid the common part of earlier members.

Finite check [computed exact, k = 8]: 𝒫' at (8,6,15) (|Y'| = 2) has 1287 members, which is more than
C(15,6)/C(7,6) = 715. It covers 3289 of the 5005 six-sets (65.7%) and has no good seven (80.2). It contains 75 075 (b)-triples.
This shows that (b) is a three-member condition PLUS the covering of four transversal requests, and 𝒫' fails the latter.

**71.2 Independent copies see only bad tuples [proved by hand: Jensen].** Let μ be any law on c-sets and K_1..K_7 i.i.d. ~ μ.
Put q(x,y) = μ(K ∋ x, y). Then E_{x,y} q = E|K|²/N² = (c/N)², so the expected uncovered (ordered) pair mass is
E_{x,y}(1 - q)^7 >= (1 - (c/N)²)^7. This is 0.075 to 0.24 across the window (table column iid).
- So an average/entropy inequality over independent copies controls tuples that miss a constant fraction of the pairs.
- A good seven is an event of probability e^{-Θ(k)} under such laws, and averages do not see it.
- This kills (I2) as a route. It does not say that i.i.d. sampling never hits a good seven: it does, if CP holds and μ has
  full support.

The correlation the law must create, as total correlation per point of a Fano-type co-type law with marginals c/N, is
TCmin = 0.90 to 2.83 nats; i.i.d. gives 0. [computed float; Fano-type co-types only]

## 72. (I3) tested: pencil supersaturation on finite families [computed exact]

The simplest correlation inequality that would give (Σ)(b) is "positive correlation of members along pencil frames":
#(b)-triples >= κ · (density)³ · #frames for some κ > 0. This is Harris/Sidorenko-type, and it is what a sequential entropy
count gives for acyclic patterns. `fam_certs.py` at (k,T,n) = (8,6,15), with t = 3/4 exactly, ε = 0, n - 2T = n - 3k/2 = 3:

| family | members | T-covering | (b)-triples | (b) defect 1 | Q′ splits σ <= 1 / with matchings OK | max point freq | H(reply) / log|𝒞| |
|---|---|---|---|---|---|---|---|
| core9 `fam_8_6_15_rev` (2-class hash-like selector) | 2352 | yes | **0** | 12 816 580 | 39 608 394 / **0** | 0.640 | 7.616 / 7.763 |
| pool (|Y| = ω = 1) | 3003 | yes | 525 525 | 42 882 840 | 0 / 0 | 1.000 | 7.871 / 8.007 |
| random dump, seed 1 | 3599 | yes | 459 702 | 45 233 747 | 171 507 483 / **0** | 0.476 | 7.735 / 8.188 |
| 𝒫′ (7-free; §71.1) | 1287 | no (1716 missed) | 75 075 | 4 864 860 | 0 / 0 | 1.000 | 7.113 / 7.160 |

- Perfect-pencil frames: C(15,3)·12!/(4!³·3!) = 2 627 625.
- Density-product prediction for the core9 family: 2 627 625 · (2352/6435)³ = 128 301. Under the random-dump model it is
  2 627 625 · (1 - (8/9)^7)³ = 465 265.
- (b) defect := uncovered points + max(0, 3 - triple meet). "Q′ splits" counts (pair, pair) splits of quadruples with
  σ <= (3T - n)/2. Q′ also needs every matching's pair-only mass + σ <= T.

Readings:
- **The correlation inequality fails totally on the core9 family**: 0 pencils against 128 301 predicted, although 12.8 M
  triples miss (b) by one point.
- The family is entropy-uniform: its reply entropy is within 0.15 nats of log|𝒞|, and its point frequencies are 0.44–0.64,
  around c/n = 0.467. So the Gilmer-type conclusion "a frequent element / a pool exists" also fails on it (max 0.64 against
  1.0 for the pool).
- The random-dump family has 459 702 pencils against the prediction 465 265 (ratio 0.99). So the first moment is accurate for a
  random map, and the core9 deficit (0 of 128 301) comes from the selector's structure, not from the size.
- **New: all of (Σ) fails on the core9 family.** No (b); no Q′ (39.6 M quadruples reach σ = 1, none passes the matching
  loads; Q′ is absent in ALL four families, including random dumps with 171.5 M σ = 1 quadruples, so at ε = 0 Q′ has no room
  and only (b) distinguishes the families); (c) is vacuous at this size, since Theorem T needs pair meets <= (T + n - 2k)/2 = 2.5 and sum
  >= (3n - 3k - T)/2 = 7.5, and three meets of at most 2 cannot sum to 8 [proved by hand].
  This is at ε = 0 and finite k. It is not a first-order counterexample to (Σ), but it says (Σ) has no room at t = 3/4.
  CP for this family, if true, needs at least five members used in full. Its good-seven status is still open
  (core9 cover_ilp: best 8, bound 7).
- The pool family has many (b)-triples and no Q′, as §37 predicts (σ >= 1 - t = 2 points).

## 73. The proof attempt, and the exact obstruction

**73.1 Attempt (sequential entropy count for (b)) [proved by hand].** Give the three requests a common kernel κ0 of mass N - 2t.
Then |K_1 ∩ K_2 ∩ K_3| >= N - 2t holds from the requests alone. Union = V then needs the holes
H = V ∖ (κ0 ∪ S_1 ∪ S_2 ∪ S_3) (petals disjoint, |H| = 2t - 3(3t - N) = 3N - 7t = 3ω - 4ε) to satisfy D_1 ∪ D_2 ∪ D_3 ⊇ H.
So the three dumps must be pairwise disjoint up to 4ε, and inside H up to 4ε, i.e. K_i ∩ K_j ≈ κ0 for all pairs.
This is a TRIANGLE in the compatibility graph G_{κ0} on requests (S ~ S′ iff F(S) ∩ F(S′) ⊆ κ0 up to O(ε)). A chain-rule
count samples S_1, then S_2 ~ S_1, then S_3 adjacent to both, and gives a lower bound only for the path S_1 ~ S_2 ~ S_3.
The closing edge S_3 ~ S_1 is the cyclic constraint. Triangles are not Sidorenko: a dense graph can be triangle-free.
Here the analogue is realised: the core9 family is T-covering with 12.8 M near-triangles and 0 triangles (§72).

**73.2 The obstruction, stated exactly.** For each minimal certificate (pencil (b), Theorem-T triangle, Q′ quadruple), the
success event for reply i is a containment of D(S_i) in a set fixed by the OTHER requests and dumps (73.1; 2.2; 35.2).
The dependency graph among the >= 3 non-free replies is cyclic. Entropy inequalities give lower bounds on joint
probabilities in only two ways, and neither is available:
- (a) along an acyclic elimination order. In game form the last reply's target is known before its dump and he avoids it
  (reading lemma 9.1; depth values = base, §26, §30).
- (b) through density. Density statements are false here: 𝒫′ has density e^{(Λ0 - N h(c/N))k}, above the least density
  e^{(Φ - N h(c/N))k} of a T-covering family (margin E0, §71.1), and it has no good seven.
What is left is the statement "every reply map has a frame whose three (or more) dumps are mutually compatible". That is the
monochromatic-edge problem of §48 (hypergraph ℋ, two grounds), a Ramsey-type statement with e^{Θ(k)} colours. Entropy enters
it only as the first moment: pdump = +2.37 to +2.80 (a uniformly random reply map has e^{2.4k} pencils). That is a heuristic
about random maps, not an inequality for arbitrary F.

**73.3 Dependent random choice [heuristic].** Choose S_3 first, condition on D(S_3), then sample S_1, S_2 among requests
compatible with it. The compatible set is a subfamily of requests on which F is arbitrary: T-covering does not restrict to
it, so the conditioned problem is the original one on fewer requests. Dependent random choice yields many common
neighbours (density); the frame needs one exact compatible triple. No gain found.

**73.4 Witness-pair entropy (coordinator's idea) [proved by hand; computed exact at k = 8].** Give each bad seven a witness
pair {x,y} that no member covers, so all seven avoid 𝒦_xy = {K ⊇ {x,y}}. Then
H(seven | bad) <= log #pairs + max_xy H(seven | all avoid 𝒦_xy). This is the union bound
Pr_ν[bad] <= Σ_xy Pr_ν[no K_i ∈ 𝒦_xy] up to the log #pairs term, i.e. the first moment of the number of uncovered pairs.
- At first order, log #pairs = O(log k). So the inequality asks that every pair be uncovered with probability
  e^{-ω(log k)} under ν.
- Link covering gives an ABSOLUTE bound |𝒦_xy| >= C(n-2,T-2)/C(c-2,T-2) = e^{Φk + O(1)}, not a fraction of |𝒞|.
  Relative to a minimal family it is a fraction of about (c/N)², which is exactly the constant of 71.2. It is a one-member
  statement and does not see how the seven are correlated.
- `witness_pair.py`, ν = 7 i.i.d. uniform members: E[#uncovered pairs] = 23.4 (core9), 26.4 (pool), 22.2 (random dump),
  31.2 (𝒫′), against the needed < 1. The entropy form fails by 3.4–3.8 nats in each case.
  Minimum link fractions are 0.17, 0.16, 0.19, 0.13, against (c/n)² = 0.218, and the links are 3–5 times the codegree bound 143.
- It fails on the pool, which does have good sevens. So with i.i.d. or uniform laws the inequality is false where CP is true.
- With a ν adapted to F it holds iff ν puts mass on good sevens (ν conditioned on good has zero uncovered pairs), which is
  circular. It also fails for every constructive design on random-dump families: lines of mass 3N/7 > t need dumps, so the
  per-pair failure probability is a constant.
- **Verdict: dead as stated.** Viable only with a law that already concentrates on good sevens, i.e. it reduces to (E) / CP.

## 74. Verdict, dead routes, next step

**Verdict.** The entropy method does not decide CP. Every form reduces either to a false density/entropy statement
(71.1, 73.2b), to an average that sees only bad tuples (71.2, 73.4), or to the cyclic Ramsey statement of §48 (73.1–73.2).
**Dead (this part):**
- entropy/size bounds of Gilmer shape (I1), in the whole window, with margin E0 > 0 (71.1);
- independent-copy average inequalities (I2) (71.2);
- pencil supersaturation by a correlation inequality, refuted exactly on the core9 family (72);
- witness-pair entropy / union bound over pairs (73.4);
- any argument that uses only requests meeting a fixed (δ + η)-set in >= ε + η (71.1).
**New facts:**
- E0 (71.1);
- the Jensen floor (1 - (c/N)²)^7 (71.2);
- the core9 family is T-covering, entropy-uniform, and has no (b), no Q′ and vacuous (c) at (8,6,15) (72).
**Next step [heuristic].** The only place entropy could still enter is a second-moment (Janson) bound for frames under maps
that are "balanced" in a sense that EXCLUDES 2-class hash-like selectors such as the core9 family. Theorem W does not reach
that family, so the balance hypothesis would itself need a structural proof. Before any proof attempt, decide the core9
family's good-seven status: an exact five-member certificate search is enough, since (Σ) fails there.

Self-check (Part XVI, §70–§74):
- E0 uses only 80.2 and the count of 𝒫′. Φ and Λ0 are closed-form log-binomials (entropy_tables.py); r assumes
  ε < tδ/N (true except at the lower endpoint, where r = 0 is printed).
- 71.2 is one application of Jensen to x ↦ (1 - x)^7.
- §72 counts are exact enumerations. The (b) check is "union = V and triple meet >= n - 2T", as corrected in LEDGER. The Q′
  check uses σ = points in <= 1 member, and the pair-only mass per matching. Members are read verbatim from the files, and
  T-covering is re-checked on each.
- 73.1's hole count is |V ∖ κ0| - 3(t - |κ0|) with |κ0| = N - 2t.
- The literature statements are from the four arXiv abstracts, fetched and read. Sawin's correlated-sampling detail is recalled.
- The fam_8_6_15 "perfect pencils 0" of core9 is reproduced independently as "(b)-triples 0".

=============================================================================================
# Part XVII — covering-design stability (§105–§109)

Brief: a T-covering family is a covering design C(n, c, T) (c-sets covering every T-set). Ask (1) whether having no
(Σ)-shape forces the design to be much larger than the Schönheim minimum, and whether random greedy or nibble designs
contain (Σ)-shapes; (2) whether a stability theorem "configuration-free design ⟹ structured" exists or can be proved,
using anti-Pasch Steiner triple systems as the model case; (3) a proof route or counterexample evidence.
Code: `compute/cover/` — `shape_exponents.py` (first-order counts), `parity_cost.py` (algebraic avoidance),
`build_designs.py` (small designs), `census.sh` with `certs_lean.py` (copy of `compute/entropy/fam_certs.py` without the
defect census) and `compute/core9/seven_dfs.js` / `seven_cotype.js` (exhaustive good-seven search). Logs:
`compute/cover/logs/`. Units k = 1.
**Outcome. No proof route, and no counterexample evidence.**
- Size is the wrong axis. The property is monotone, so a counterexample can be taken inclusion-minimal. The pool
  family is inclusion-minimal and exponentially larger than the Schönheim minimum. Dead (§105).
- Random and near-minimum designs are *supercritical* for Q′, Theorem T and the Fano seven. Each member lies in
  e^{(0.6 to 2.1)k} of each shape. Pasch in a Steiner triple system is *critical* (O(1) per block). So the
  random/nibble/conflict-free route that builds anti-Pasch and high-girth systems has nothing to work with (§106).
- The algebraic anti-Pasch mechanism (AG(d,3): a forced linear relation that fails in the wrong characteristic) does
  transplant: every (Σ)-shape and every good seven satisfies a mod-2 or mod-3 sum identity (107.1). But the code
  redundancy needed to block the identity is 2 to 3.4 times the covering budget γ for Q′, Theorem T and good sevens.
  For pencils it is far below γ (§107). So this gives no counterexample.
- No stability theorem of the required kind exists in the literature I checked. The classical analogue of (Σ) is a
  Brown–Erdős–Sós-type statement ("a supercritical configuration is unavoidable"), and that is open even for triple
  systems beyond (6,3) (§108).

## 105. Covering designs; size is the wrong axis

**105.1 Dictionary [proved by hand].**
- 𝒞 is T-covering ⟺ 𝒞 is a covering design C(n, c, T) ⟺ the edges V∖K form a Turán (n, n − T, k)-system.
- The counting (Schönheim) bound is |𝒞| >= C(n, T)/C(c, T), of exponent Φ = N h(t/N) − c h(t/c) (= N h(c/N) − γ).
- The threshold random family (density e^{−γk}·poly) meets it to first order. So Rödl-type asymptotic optimality is
  automatic at exponential scale: near-designs are not needed, and nibble and random are the same at this resolution.
- "Has a good seven" is monotone increasing in 𝒞. So if 𝒞 is a counterexample, so is every T-covering subfamily, in
  particular an inclusion-minimal one, in which every member K has a *private* T-set (one covered by K alone).

**105.2 The structured candidates are inclusion-minimal and far above the minimum [proved by hand; exponents computed
float].**
- The pool family 𝒫_Y = {K ⊇ Y}, |Y| = ω, is inclusion-minimal: K∖Y is a T-set lying in no other member.
- Its size has exponent (N − ω) h(t/(N − ω)). The excess over Φ is +0.14 (bottom of the window) to +0.58 (top)
  at t = 0.7501, and +0.21..+0.58 at t = 0.76 (`logs/shape_exponents.log`, column Pool−Phi).
- It has no Q′ quadruple (σ >= 1 − t, §37) and loses only to the pencil.
**105.3 Verdict on question (1).**
- A size-stability theorem ("|𝒞| <= e^{ηk}·Schönheim ⟹ good seven") would exclude only near-minimum counterexamples.
- The open families (hash-like selectors, request-dependent dumps, §47.5) are not near-minimum. Nothing forces a
  counterexample to be: inclusion-minimality is free (105.1), and near-minimum size is not inherited.
- The classical analogue says the same: Steiner systems are exactly minimum coverings, yet AG(d,3) is Pasch-free (107.2).
  "Minimum ⟹ configuration" already fails for triple systems.
- **Dead:** size / near-optimality as a route to CP or (Σ).

## 106. Random designs are supercritical [computed float; finite instances computed exact]

**106.1 Counts.**
- For a shape on r members with certifying polytope P (Venn masses), let Hmax = max_{v∈P} N·H(v/N). The number of
  ordered r-tuples of c-sets with pattern in P is then e^{k·Hmax + o(k)}.
- In the threshold random design, the shape count per member is e^{kD} with D = Hmax − rγ − Φ.
- `shape_exponents.py` maximizes entropy over the polytopes of §95(a) (Q′), (b) (pencil: union V, triple >= N − 2t),
  (c) (Theorem T, triple = 0), and the Fano upset (symmetric maximum entropy; a lower bound for "some good seven").
  SLSQP, 6 starts.

| t | N range | D_Q′ | D_pencil | D_tri | D_Fano7 |
|---|---|---|---|---|---|
| 0.7501 | 1.79 → 2.21 | +1.93 → +0.79 | +0.87 → −0.30 | +1.90 → +0.59 | +2.00 → +1.54 |
| 0.76 | 1.84 → 2.20 | +1.91 → +0.91 | +0.88 → −0.08 | +1.74 → +0.65 | +2.03 → +1.61 |
| 0.78 | 1.93 → 2.19 | +1.86 → +1.15 | +0.86 → +0.24 | +1.49 → +0.75 | +2.10 → +1.76 |

- (§57.1 already has the total Fano count, G7 − 7γ > 0, from core9 `exponents.py`. The
  per-member normalisation above is new.)
- In a random or nibble covering design, every member lies in exponentially many Q′ quadruples, Theorem-T
  triangles and good sevens, throughout the window.
- The pencil is the exception. It is a boundary pattern (§95), so near the top it is *subcritical*: fewer pencils than
  members. This matches §36–§47, where the pencil killed only structured families.
- Existence (count ≫ 1) needs only Hmax − rγ > 0. That holds with more room still [heuristic: second moment not
  written].

**106.2 Q′ is a blown-up Pasch [proved by hand].**
- At its centre (N = 2, σ = 0, six pair cells of mass 1/3), Q′ is four members in which every point lies in exactly
  two, and every two members meet in their own cell.
- That is the Pasch configuration (4 blocks, 6 points, each point on 2 blocks), blown up.
- In an STS(n), the expected number of Pasch configurations is n^6·n^{−4} = Θ(n^2) = Θ(#blocks): per block D = 0,
  which is *critical*.
- Here D_Q′ >= +0.79.
- That is the decisive quantitative difference. The tools that build anti-Pasch and high-girth systems by random
  processes only work at or below criticality: Bohman–Warnke's triangle removal, Glock–Kühn–Lo–Osthus, Kwan–Sah–
  Sawhney–Simkin, and the conflict-free matching theorems of Glock–Joos–Kim–Kühn–Lichev and Delcourt–Postle.
  Their conflict hypergraphs must have degrees about d^{j−1}. Here each member is in e^{Dk} conflicts against
  e^{0} allowed. [literature, checked: abstracts / statements of the conditions; heuristic: the comparison]

**106.3 Small exact census** (k, T) = (8, 6), i.e. ε = 0. The window 5T − 2k < n < 3k − T gives n = 15, 16, 17. The
smallest window instance with ε > 0 is (16, 13, 34), where C(34, 13) ≈ 9·10^8 T-sets make an exhaustive good-seven
search out of reach. `logs/census.log`, designs `logs/d_8_6_*`, `logs/c1_8_6_*`:
| n | design | members | (b) pencils | (a) σ-small quads / with matchings OK | good seven |
|---|---|---|---|---|---|
| 15 | random greedy | 1091 | 13412 | 1455594 / 0 | yes |
| 15 | greedy, inclusion-minimal | 1085 | 13201 | 1423938 / 0 | yes |
| 15 | nibble (random extension) | 1535 | 35604 | 5692266 / 0 | yes (its minimal subfamily has one; monotone) |
| 15 | nibble, inclusion-minimal | 1285 | 20961 | 2794716 / 0 | yes |
| 16 | random greedy (= its minimal) | 569 | 896 | 0 | yes |
| 16 | nibble, inclusion-minimal | 732 | 1915 | 0 | yes |
| 16 | zero-sum mod 16 (107.3) | 809 | 5578 | 0 | yes |
| 16 | binary code, r = 3, 1_V ∉ L (two builds, same code) | 1615 | **0** | 0 | yes |
| 17 | random greedy (= its minimal) | 358 | 110 | 0 | yes |
| 17 | nibble, inclusion-minimal | 480 | 263 | 0 | yes |
| 17 | zero-sum mod 17 | 1430 | 7492 | 0 | yes |
| 17 | binary code, r = 4, 1_V ∉ L (two builds, same code) | 1535 | **0** | 0 | yes |

Counting bound C(n,T)/C(c,T): 715 (n = 15), 286 (n = 16), 148 (n = 17);
greedy is within a factor 1.5–2.4 of it. Every design has a good seven; no design has a Q′ quadruple meeting all three
matching conditions at ε = 0.
- (b) is the exact count of triples with union V and triple meet >= n − 2T.
- (a) is fam_certs' Q′ count, restricted to the multiplicity-2-plus-one-empty-point patterns. It is a lower bound,
  not a full count.
- "good seven" is the exhaustive search: `seven_dfs.js` for n <= 16, `seven_cotype.js` for n = 17.
- At ε = 0, Q′ has slack only δ + 3ε = n − 7k/4 points (1, 2, 3), so (a) is rare there. That is not evidence about
  ε > 0.

## 107. The anti-Pasch mechanism, transplanted

**107.1 Sum identities [proved by hand; finite-k forms in brackets].** Write 1_K for the indicator vector.
- *Good seven, N < 2* [2(c − 1) < n − 1].
  - Every co-type has |I_x| >= 3.
  - Σ_i 1_{K_i} ≡ 1_V + 1_E (mod 2), where E = {x : |I_x| even}.
  - |E| <= Σ_x (|I_x| − 3) = 4δ [7c − 3n].
- *Pencil (b)* (union V, κ_3 := |K_1∩K_2∩K_3| >= N − 2t).
  - Σ 1_{K_i} ≡ 1_V + 1_{P_2} (mod 2), where P_2 is the set of points in exactly two members.
  - 3c = N + |P_2| + 2κ_3 gives |P_2| <= 4t − 3 = 4ε [4T − 3k].
- *Q′ (a)*.
  - 2·1_V − Σ 1_{K_i} (mod 3) is supported on the points of co-type size 0, 1, 3, 4.
  - From the §37 identities, u_3 + 2u_4 = 2N − 4 + 2s_0 + s_1. So the weight is
    <= 2N − 4 + 3σ <= B_Q := (9t + N − 8)/2.
- *Theorem T (c)* (triple cell empty). Σ 1_{K_i} ≡ 1_{singles} (mod 2). This is a vector of weight
  3c − 2(a + b + d) ∈ [3 − 3t, t].

So for a linear code L (over F_2 or F_3), the family 𝒞_L = {K ∈ C(V, c) : 1_K ∈ L} has:
- no good seven if d(1_V, L) > 4δ;
- no pencil if d(1_V, L) > 4ε;
- no Q′ if d_3(2·1_V, L) > B_Q (ternary L);
- no Theorem-T triangle if L has no codeword of weight in [3 − 3t, t].
(For the first three: a sum of codewords is a codeword. For the fourth: so is Σ1_{K_i}.)

**107.2 The classical case [proved by hand].**
- AG(d,3) is anti-Pasch. Take lines abc, ade, bdf, cef (x + y + z = 0 on lines). Then
  (a+b+c) + (a+d+e) − (b+d+f) − (c+e+f) = 2a − 2f = 0, which forces a = f in characteristic 3.
- In PG(d,2), every two meeting lines lie in a Fano plane, which contains Pasch configurations.
- In our setting the same parity phenomenon reappears: exact Pasch blow-ups have Σ1_K = 2·1_V, a relation that lives
  mod 2 or mod 3, exactly as in 107.1.

**107.3 Sum-hash families are profile families [proved by hand].**
- 𝒞 = {K : Σ_{x∈K} g(x) ∈ A} with g: V → G, an abelian group, is the zero-sum analogue of AG(d,3).
- Its membership depends only on the profile (|K ∩ g^{−1}(h)|)_h.
- So for bounded |G| it loses by Theorem S. With up to 4εk − 12 fibres it loses by S+ (finite k).
- Linear codes with r checks are profile families on 2^r column classes. T-covering needs r ≈ γk/ln 2 bits, which is
  far beyond S+. This is the hash-like case of §47.5(i).

**107.4 Cost of the identities [computed float; covering budget heuristic].**
- A random-like code of redundancy R nats per k has its coset leaders, and its least codeword weights, where the
  ball volume reaches e^{Rk}.
- T-covering a code family needs R <= γ + o(1) [heuristic: the number of weight-c codewords must reach e^{Φk};
  rigorous only is d(v, L) <= r bits = covering radius <= redundancy].
- `parity_cost.py` (columns = ball exponents, to compare with γ):

| t | N | γ | good seven N h(4δ/N) | pencil N h(4ε/N) | Q′ (ternary) | triangle N h(t/N) |
|---|---|---|---|---|---|---|
| 0.7501 | 1.775 | 0.119 | 0.390 | 0.004 | 0.927 | 1.209 |
| 0.7501 | 1.900 | 0.446 | 1.186 | 0.004 | 1.096 | 1.275 |
| 0.7501 | 2.000 | 0.625 | 1.386 | 0.004 | 1.226 | 1.323 |
| 0.76 | 1.820 | 0.231 | 0.781 | 0.192 | 1.090 | 1.225 |
| 0.76 | 2.000 | 0.609 | 1.386 | 0.196 | 1.319 | 1.323 |
| 0.78 | 1.910 | 0.403 | 1.218 | 0.448 | 1.382 | 1.270 |
| 0.78 | 2.000 | 0.576 | 1.386 | 0.454 | 1.489 | 1.323 |

- Good seven: cost/γ = 2.2 to 3.4 everywhere tested (N < 2). Q′ and triangle: cost/γ >= 1.96.
- Pencil: cost ≪ γ for ε ≪ ω.
- Reading [heuristic]:
  - Linear codes can kill (b) cheaply. So (Σ) must lean on (a) or (c) for near-random families, which is consistent
    with 106.1.
  - Linear codes cannot kill good sevens (nor Q′, nor T) within the covering budget. The anti-Pasch construction
    does not transfer to a counterexample.
- Exact check at ε = 0 (where 4εk = 0, so the pencil identity is exact): codes with 1_V ∉ L
  (`build_designs.py ... code1`, r = 3, 4; the n = 15 sum/code families with r = 1 were built but not censused) have **zero (b)-triples, as 107.1 predicts**, and still a good seven
  (106.3). That is because 7c − 3n = 8 or 12 > d(1_V, L).

## 108. Literature: configuration-free designs, stability

- **Anti-Pasch STS.** Exist for all v ≡ 1, 3 (mod 6) except 7 and 13 (Grannell–Griggs–Whitehead, JCD 8 (2000)
  300–309; Brouwer for v ≡ 3 (mod 6)). Anti-Pasch optimal coverings and packings with triples: Demirkale–Donovan–
  Grannell and coauthors. Constructions are algebraic or recursive (AG(d,3), auxiliary quasigroup designs).
  [literature, checked: abstracts and survey statements]
- **High girth.** Kwan–Sah–Sawhney–Simkin, Annals 200 (2024) 1059–1156 (arXiv 2201.04554): STS of girth → ∞.
  Glock–Kühn–Lo–Osthus (Combinatorica 2020): approximate version. Bohman–Warnke (JLMS 2019): high-girth partial STS by
  triangle removal. [literature, checked: abstract/statement]
- **Conflict-free hypergraph matchings.** Glock–Joos–Kim–Kühn–Lichev (arXiv 2205.05564; SODA 2023) and Delcourt–Postle
  (arXiv 2204.08981): near-perfect matchings avoiding conflicts under (d, ℓ, ε)-boundedness of the conflict
  hypergraph. Joos–Mubayi–Smith extend this to coverings. [literature, checked: abstract-level statements; exact
  degree thresholds not read]
  - All of these are fixed-uniformity and need the conflicts to be at most critical.
- **Supercritical configurations are forced by removal-type lemmas.** Ruzsa–Szemerédi: every STS contains a (6,3)
  configuration. The general Brown–Erdős–Sós (j + 3, j) problem is open. There are approximate and limit results
  (Glock et al. (6,4); Delcourt–Postle on the limit; group versions). [recalled, not read]
  - These proofs are regularity-based and need polynomial density. Our families have density e^{−γk}, where §96 already
    shows density alone is useless.
- **"Configuration-free ⟹ structured" for designs.** I found no stability theorem of that form, for Steiner systems
  or coverings, in any regime.
  - Anti-Pasch systems are not close to any single structure: algebraic, recursive and random-absorption
    constructions all exist.
  - So in the classical case such a stability statement is **false**, for the critical configuration.
  - For supercritical ones it is the BES problem.
- **Answer to (2).** The anti-Pasch analogy does not suggest counterexamples. Pasch is critical and exact; Q′ is
  supercritical (106.1) and open (§95). It suggests instead that (Σ) is a BES-type supersaturation statement in an
  exponentially sparse regime. No such theorem exists, and the regularity proofs of the classical cases do not apply.
  Proving "configuration-free ⟹ profile/ordered/window-selected" would in particular prove an exponential-scale BES
  statement. **Dead as a route with current tools** [heuristic for "would prove", proved for "no such theorem found"
  only in the sense of the search above].

## 109. Status, dead routes, what remains; self-check

**Status.**
- No proof of CP or (Σ), and no counterexample.
- New and proved by hand:
  - the dictionary and minimality reduction (105.1);
  - pool = inclusion-minimal and super-minimum (105.2);
  - Q′ centre = blown-up Pasch (106.2);
  - the four sum identities 107.1, with the code families they make certificate-free;
  - AG(d,3) anti-Pasch;
  - sum-hash families = profile families (107.3).
- Computed:
  - supercritical per-member counts for Q′, T and Fano sevens across the window; pencil subcritical near the top
    [float];
  - parity costs >= 1.96γ except for pencils [float; budget heuristic];
  - exact census at (8, 6, 15–17) [exact].

**Dead.**
- Size or near-optimality stability (105.3).
- Random, nibble or conflict-free constructions of a counterexample (106.2: supercritical).
- Algebraic (linear-code, sum-hash) counterexamples (107.3–107.4).
- A design-literature stability theorem: none exists. The classical analogue is false for critical configurations and
  open (BES) for supercritical ones (108).

**What remains.**
- One genuinely new structured test object: binary-code families with d(1_V, L) > 4εk. They are pencil-free by
  107.1(b) at a cost far below γ, and T-covering is plausible (heuristic).
- Every family killed so far (S, S+, §46, W) died by a pencil. This one cannot. So it is the right test case for whether
  (Σ)(a)/(c) does the work on hash-like families (§47.5(i)).
- Smallest instance with ε > 0: (k, T, n) = (16, 13, 34), r <= γk/ln 2 ≈ 16 checks (γ = 0.72; 4εk = 4, so d(1_V, L) >= 5 is needed). Q′ / Theorem T / good-seven search
  needs a member-indexed search, not the T-set enumeration. Not done.

**Self-check.**
- Φ = N h(c/N) − γ re-derived from C(n, c)/C(n − T, c − T) = C(n, T)/C(c, T).
- The Q′ polytope is that of §95(a). The pencil is the verifier's (b). Theorem T uses the §33 statement with triple = 0.
- The optimizer reproduces the core9 Fano value (G7) independently through the closed form.
- The sum identities were checked against the census: zero (b)-triples in all code1 families at ε = 0, as predicted.
- The 4ε bound for P_2 used κ_3 >= N − 2t and 3c = N + |P_2| + 2κ_3 (valid when union = V).
- The Q′ ternary bound used u_4 >= 0 and the §37 identity.
- Not independently verified.

=============================================================================================
# Part XIX — the fractional pair-cover (edge-clique-cover) LP (§115–§119)

Brief: an external reviewer suggested the fractional PAIR-cover of V by co-edges. It is not the fractional
transversal τ* of §80–§84. For a co-edge family 𝒦 on V put

    ρ*(𝒦) = min Σ w_K   subject to   Σ_{K ⊇ {x,y}} w_K >= 1 for every pair {x,y} ⊆ V,   w >= 0,

and let ρ(𝒦) be the least number of members covering all pairs. A good seven is exactly ρ <= 7. The LP dual is
ρ* = max Σ_p y_p over pair weights y >= 0 with Σ_{p ⊆ K} y_p <= 1 for every K ∈ 𝒦.
Finite units: n = |V| = Nk, members are c-sets (c = n − k), requests are T-sets. First order: c = N − 1,
ω = c − t, δ = N − 7/4 = ω + ε.
Code: `compute/paircover/`.
- `paircover.py`: ρ* as an exact rational (primal basic solution and dual, both checked in Fractions), the
  degree-cut LP ρ*_3, and ρ by SAT (CaDiCaL 1.9.5, seqcounter).
- `supR.py`: the sup of ρ* over T-covering families (MILP and best-response ascent).
- `runall.sh`.
Logs: `compute/paircover/logs/{lp_*,pc_*,dfs_n15,random_4_3_8,supR_ascent}.log`. Small random families are in
`compute/paircover/fams/`.

**Outcome.**
- **(a)** Both reviewer bounds hold [proved by hand]: C(n,2)/C(c,2) <= ρ* <= n(n−1)/(T(T−1)). At first order
  this is (N/c)² <= ρ* <= (N/t)², and the upper bound is < 7 exactly for N < √7·t ≈ 1.984 + 2.65ε.
- **(b)** The random T-set rule is optimal among rules that ignore the family (116.1). Every T-covering bound must
  be at least the pool value C(k+T,2)/C(T,2) → ((1+t)/t)² = 49/9 ≈ 5.44 (116.2). Both are proved by hand. So the
  extra c − T points can help only through an adaptive rule. Conjecture PC (sup ρ* = ((1+t)/t)², hence ρ* < 5.45
  in the whole window) is open above N = √7·t.
- **(c)** The fractional side is far from 7 and blind to the question.
  - On every stored T-covering family, ρ* is the trivial floor C(n,2)/C(c,2) (all random, greedy, code, sum and
    dump families), or 83/15 (core9), or 91/15 (pool).
  - Every family decided has a good seven: ρ = 7 at n = 15, and ρ = 6 at n = 16 and 17 [computed exact]. So
    the gap ρ/ρ* is 1.40 (n = 15, 16), 1.59 (n = 17) and 1.15 (pool). The core9 family and 11 others are
    undecided within budget.
  - **None of the stored families is a known family with no good seven.** The premise "ρ >= 8 for pool families"
    is false for T-covering pools: they have ρ = 7 (Fano) whenever 4T >= 3k with divisibility.
  - The families with ρ >= 8 and ρ* < 7 are the over-pooled families (|Y| > δ), which miss T-covering by one
    point of Y. On them ρ* moves continuously while ρ jumps (118.1).
  - Rounding ρ* cannot work. A degree-cut LP (every point in weight >= 3, valid when 2c < n + 1) sees the pool
    threshold exactly, and this is the only LP information that matters. What remains is the Fano/pencil
    structure, which is CP (§118).

## 115. The two reviewer bounds [proved by hand]

**115.1 Lower bound.** Sum the pair constraints over all C(n,2) pairs. Each K contributes w_K·C(c,2), so
Σ w_K·C(c,2) >= C(n,2), i.e. ρ* >= C(n,2)/C(c,2) = n(n−1)/(c(c−1)), which is (N/c)²(1 + O(1/k)). The bound is
attained exactly when the uniform dual y ≡ 1/C(c,2) is optimal, i.e. when 𝒦 carries a fractional 2-design.
That happens for every random, greedy, code and sum family tested (§117).

**115.2 Upper bound (random T-set rule).** T-covering gives a reply K(S) ∈ 𝒦 with S ⊆ K(S) for each T-set S.
Draw S uniformly and put w_K = α·P(K(S) = K). For a pair p, Σ_{K ⊇ p} w_K >= α·P(p ⊆ S) = α·T(T−1)/(n(n−1)).
With α = n(n−1)/(T(T−1)) this is feasible, so ρ* <= n(n−1)/(T(T−1)), which is (N/t)² at first order.
- **Where it is < 7:** N < √7·t, i.e. N < 1.9843 + 2.6458ε.
- At k = 8, T = 6 it is 7, 8 and 9.07 for n = 15, 16 and 17.
- So below N ≈ 1.984 every T-covering family has ρ* < 7, but this says nothing about ρ.

## 116. The sharpest T-covering bound on ρ*

**116.0 Minimax form [proved by hand].** Put R(n,c,T) = sup ρ*(𝒦) over T-covering 𝒦. By LP duality,
ρ*(𝒦) = max_μ 1/max_{K∈𝒦} μ(K), where μ ranges over probability measures on pairs and μ(K) = Σ_{p ⊆ K} μ_p. For
fixed μ, the T-covering family that minimises max_K μ(K) takes for each S its cheapest extension. Hence

    1/R = min_μ  max_{|S| = T}  min_{K ⊇ S, |K| = c}  μ(K).

So a bound "ρ* <= X for all T-covering families" is exactly the statement "for every μ some T-set has all its
c-extensions of μ-load >= 1/X".

**116.1 Oblivious rules cannot beat the random T-set [proved by hand].** Call a rule oblivious if it fixes a
distribution D on T-sets in advance and puts weight α·P_D(K(S) = K) on the replies.
- Let p_0 be a pair minimising P_D(p ⊆ S). By averaging, P_D(p_0 ⊆ S) <= C(T,2)/C(n,2).
- The adversary answers every S with S plus c − T points outside S ∪ p_0. This needs n − T − 2 >= c − T, i.e.
  k >= 2. The resulting family is T-covering, and p_0 ⊆ K(S) iff p_0 ⊆ S.
- So α >= n(n−1)/(T(T−1)) for every D.
The extra points help only if the requests depend on the replies.

**116.2 Lower bound from the pool [proved by hand, exact at finite k].**
- Let Y have c − T points and 𝒫 = {K : Y ⊆ K}. Its members are Y plus any T-subset of U = V ∖ Y, with
  |U| = k + T. It is T-covering: a T-set S has S ∪ Y of size <= c, which can be padded to a member.
- Pairs meeting Y lie in every member. The pairs inside U form the complete pair-cover problem for T-subsets of a
  (k+T)-set, whose ρ* is C(k+T,2)/C(T,2): 115.1 gives the lower bound, and the uniform weight attains it.
- Hence R(n,c,T) >= (k+T)(k+T−1)/(T(T−1)), which is ((1+t)/t)² at first order. That is 49/9 = 5.444 at t = 3/4,
  independent of N.
- Note |Y| = c − T is the largest pool that is T-covering (y <= ω), and the pool ρ* increases with y. Checked
  exactly: the pool family of `compute/entropy` (k=8, T=6, n=15) has ρ* = 91/15 = C(14,2)/C(6,2).
- **Consequence:** no argument from T-covering can give ρ* < 49/9 anywhere in the window. At the bottom
  (ω = 4ε, N = 1 + t + 4ε) the random bound (N/t)² equals ((1+t)/t)² + O(ε). So 115.2 is sharp up to O(ε) there,
  and the gap between 115.2 and 116.2 opens linearly in ω.

**116.3 Structured μ do not beat the pool [proved by hand, class by class].** In each class, compute
max_S min_E μ(S ∪ E), with E the c − T extra points. Every class gives at least (t/(1+t))².
- (i) μ uniform on the pairs inside a set A of mass a. With a <= 1 + t the extras hide outside A and the value is
  (t/a)². With a > 1 + t the extras must enter A and the value is ((a−1)/a)². The minimum is at a = 1 + t: the pool.
- (ii) μ uniform on A × B with |A| = |B| = b. The value is t(t + 2f)/(1 + t + f)² with f = max(0, 2b − 1 − t).
  This is increasing in f, so the minimum is again the pool value.
- (iii) Complete r-partite on a set of mass 1 + t: the same value (t/(1+t))².
- (iv) Mixtures of two pools on disjoint Y_1, Y_2. The value is ½((c − e)² + (c − ω + e)²)/(1+t)², minimised at
  e = ω/2. It is strictly larger than the pool value, by convexity.
- (v) Disjoint small cliques (a partition into blocks). The value is about t/N, far larger.

**Conjecture PC.** R = ((1+t)/t)² + o(1) throughout 5t − 2 < N < 3 − t, i.e. every T-covering family has
ρ* <= 5.445.
- Status [heuristic]. The best-response ascent of `supR.py` (k = 3..5, n = 7..13, 6 restarts each) never exceeded
  the pool value. But it also mostly failed to reach it: it found 5.67 against a pool value of 7 at (8,4,3), so the
  search is weak evidence.
- The exact MILP is hopeless beyond n = 7: big-M, with a dual bound 0.138 against a primal 0.200 at (7,4,3) after
  300 s.
- Proved only for N < √7·t (115.2), and up to O(ε) at the bottom.
- It would not matter much (§118): ρ* is not the obstruction.

## 117. Numbers: ρ*, ρ*_3, ρ on the stored families

ρ* is exact [computed exact]: a rational dual and a rational basic primal with equal totals, both checked in
Fractions. ρ*_3 is the LP with the extra constraints Σ_{K ∋ x} w_K >= 3, valid for integral covers when 2c < n + 1
(118.2) [computed float]. ρ is from SAT, starting at the proved floor max(⌈ρ*⌉, ⌈3n/c⌉), with every cover
re-checked; or "undecided". All families have k = 8 and T = 6, so t = 3/4 exactly; they are T-covering unless
marked.

| family (source) | n | c | members | ρ* (exact) | ρ*_3 (float) | ρ | ρ/ρ* |
|---|---|---|---|---|---|---|---|
| d_code, d_greedy, d_greedy_min, d_nibble, d_nibble_min, d_sum (cover) | 15 | 7 | 1085–3235 | 5 | 45/7 = 6.43 | 7 (SAT, 14–547 s) | 1.40 |
| randdump_s1 (entropy) | 15 | 7 | 3599 | 5 | 6.43 | 7 (SAT 216 s) | 1.40 |
| c1_s1, c1_s2 (cover, code1: no exact pencil) | 15 | 7 | 3200 | 5 | 6.43 | 7 (s1 SAT 942 s and DFS; s2 DFS, 4.3·10^8 nodes) | 1.40 |
| c1_s3 | 15 | 7 | 3200 | 5 | 6.43 | undecided in {7, 8} (SAT killed) | — |
| pool (entropy; Y = {0}) | 15 | 7 | 3003 | 91/15 = 6.07 | 7.000 | 7 (Fano, classes of 2; hand + checked) | 1.15 |
| fam_8_6_15_rev (core9) | 15 | 7 | 2352 | 83/15 = 5.53 | 6.667 | undecided in {7, 8} (2400 s SAT + 3000 s DFS; cf. 55.5) | — |
| d_greedy, d_greedy_min, d_nibble_min | 16 | 8 | 569–732 | 30/7 = 4.29 | 6 | 6 (SAT) | 1.40 |
| c1_s1 | 16 | 8 | 1615 | 30/7 | 6 | 6 or 7 (good seven: census 106) | — |
| d_code, d_sum, c1_s2, c1_s3 | 16 | 8 | 809–1615 | 30/7 | 6 | >= 6, undecided | — |
| d_greedy, d_greedy_min | 17 | 9 | 358 | 34/9 = 3.78 | (cut invalid) | 6 (UNSAT at 5, SAT at 6) | 1.59 |
| d_code, d_nibble_min, c1_s1..s3 (d_sum: SAT not run) | 17 | 9 | 480–1535 | 34/9 | — | >= 5 (UNSAT at 4), undecided | — |
| sevenfree (entropy; NOT T-covering, pool with \|Y\| = 2) | 15 | 7 | 1287 | 39/5 = 7.8 | 7.8 | >= 8 (degree: 35 < 39) | — |

Readings.
- **ρ* is constant on families of the same shape.** Every random, greedy, nibble, code, sum and random-dump family
  sits exactly on the floor C(n,2)/C(c,2) (5, 30/7, 34/9). Its optimal w has all point loads equal (7/3, 15/7, 2).
  Only the pool (91/15) and the hash-selected core9 family (83/15) are above the floor. All values are well below
  the random bound (7, 8, 9.07).
- **Every decided family has a good seven.** ρ = 7 at n = 15, ρ = 6 at n = 16 and at n = 17. So ρ equals the
  proved floor ⌈3n/c⌉ at n = 15, 16. The core9 family stays undecided after 2400 s of SAT and 3000 s of DFS,
  consistent with 55.5. 12 families were left undecided when the session's jobs were stopped; their logs carry
  no RESULT line (`logs/KILLED_NOTE.txt`).
- **ρ/ρ* = 1.40 on every decided floor family at n = 15, 16.** That is ⌈3n/c⌉ divided by n(n−1)/(c(c−1)). It is
  1.59 at n = 17 and 1.15 on the pool. The integral cover is pushed up to the degree floor 3n/c, while the LP
  spreads the load at N/c ≈ 2.0–2.3 per point.
- **The degree-cut LP equals its floor 3n/c on every floor family.** It is 7.000 on the pool, which is exactly at
  its Fano threshold, and 6.667 on core9.
- The not-T-covering `sevenfree` family (a pool with |Y| = 2 > ω = 1) has ρ* = 39/5 > 7, so its lack of a good
  seven is visible even fractionally at this k.
- At k = 4 (n = 8, 20 random families): ρ* ∈ [4.89, 5.14], ρ = 6 always.

## 118. What the rounding must overcome

**118.1 ρ* is continuous where ρ jumps [proved by hand].** Take the over-pooled family 𝒫_y = {K ⊇ Y}, |Y| = y.
- It is T-covering iff y <= ω.
- Its members are Y plus a (c − y)-subset of U, |U| = N − y.
- A good seven exists iff seven (c − y)-sets cover the pairs of U. When 2(c − y) < N − y this needs every point of
  U in >= 3 sets, i.e. 7(c − y) >= 3(N − y), i.e. **y <= δ**. Conversely Fano with seven equal classes gives
  ρ = 7 when y <= δ, at first order.
- But ρ*(𝒫_y) = ((N − y)/(c − y))², which is 49/9 at y = δ and moves continuously through it.
- So on one side (y = ω, T-covering) and on the other (y = δ + η, which misses T-covering by ε + η), ρ* is about
  5.44 while ρ goes from 7 to >= 8.
- Exact finite instance: k = 16, T = 12, n = 30 (N = 1.875, ε = 0, ω = δ = 2/16).
  - |Y| = 2: T-covering, ρ* = 378/66 = 5.73, and ρ = 7 (Fano with classes of 4 on 28 points).
  - |Y| = 3: ρ* = 351/55 = 6.38, ρ >= ⌈81/11⌉ = 8. It covers every 12-set that meets Y, and only those.
- **Hence no theorem of the form "ρ* <= X ⟹ ρ <= 7" (for any X >= 49/9) holds, even among families that are
  T-covering up to one point.** A rounding must use T-covering itself at precision ε, not through ρ*. This is the
  pair-cover analogue of §82.

**118.2 The degree cut is the one LP fact that matters [proved by hand].**
- If 2c < n + 1 (first order N < 2), a point lying in at most two members of a cover forces those two to have
  union V, which is impossible. So in an integral cover every r_x >= 3.
- For seven sets, Σ_x (r_x − 3) = 7c − 3N = 4δ. This is the slack count 2.1–2.3, which is exactly how CORE §2 began.
- Adding r_x >= 3 to the LP gives ρ*_3 >= 3N/c = 7 − 4δ/c < 7 in the window, and ρ*_3(𝒫_y) = max(3(N − y)/(c − y), ((N − y)/(c − y))²) = 3(N − y)/(c − y) here.
  This crosses 7 exactly at y = δ, so the degree cut decides every pool, and the pool question at
  t ≷ 3/4 (3(1+t)/t ≶ 7).
- So the LP plus the degree cut already contains everything that §2's slack count contains. It is still below 7
  on every T-covering family tested.

**118.3 What is left after the degree cut is CP [proved by hand for N < 11/6, by 1.3].**
- For N < 11/6, seven c-sets covering all pairs, with Σ(r_x − 3) = 4δ, are exactly a Fano labelling in which every
  co-type contains a pencil (1.3). An integral rounding must produce seven members with that prescribed Venn
  pattern.
- That is a static 7-certificate, and §96 shows such patterns are not forced by density. The fractional optimum is
  an averaged object (for floor families it is a uniform fractional 2-design), so it carries no Venn-pattern
  information beyond the point loads.
- Concretely, the LP solution has every point at load N/c ≈ 2.1–2.3 spread over hundreds of members (support
  105–136 at k = 8). A good seven has every point in 3 or more of exactly 7 members.
- **Randomized rounding fails by a constant, not a log.** Seven members drawn from w/ρ* leave each pair uncovered
  with probability (1 − 1/ρ*)^7 = (4/5)^7 ≈ 0.21 for the n = 15 floor families (each pair has weight exactly 1). There are Θ(k²) pairs, and with a
  fixed budget of 7 there is no concentration to exploit.
- **Iterative or exchange rounding (Jain-type, or alternating paths in clique systems) needs sparse extreme points
  or a matroid/laminar structure.** Extreme points here have support up to C(n,2) = Θ(k²), and the target 7 is a
  constant. The known clique-cover integrality results (θ vs θ*) lose log factors or need perfect-graph
  structure; neither gives an additive "< 7 ⟹ <= 7" [literature recalled, not re-checked].
- An exchange argument specific to clique systems would have to turn a fractional design into a Fano
  configuration among members. That is the structure theorem CP itself (§33(4) stability: near-pool ⟹ pencils).
  [heuristic]

**118.4 Verdict.** The pair-cover LP is a better relaxation than τ*: it is O(1), it depends on N, and with the
degree cut it reproduces the pool threshold t = 3/4 exactly. But it is uniformly below 7 on T-covering families
(conjecturally <= 49/9; proved below N = √7·t). Over-pooled families show that its value cannot separate "good
seven" from "no good seven" at the ε scale. Rounding = CP, as in §82.

## 119. Status, dead routes, what remains; self-check

**Status.**
- (1) C(n,2)/C(c,2) <= ρ* <= n(n−1)/(T(T−1)) [proved by hand]. ρ* < 7 for N < √7·t.
- (2) Random-T is optimal among oblivious rules (116.1). The pool forces sup ρ* >= 49/9 (116.2). Conjecture PC
  (sup = 49/9) is open for N >= √7·t [heuristic support only].
- (3) On the 28 stored T-covering families with k = 8, ρ* is exact. It is the floor C(n,2)/C(c,2) except for the
  pool and core9. On the 15 families decided, ρ ∈ {6, 7}, with gap 1.15–1.59. No stored T-covering family is
  known to lack a good seven; core9 is still at {7, 8}.
- (4) Over-pooled families give ρ* ≈ 49/9 < 7 together with ρ >= 8. The degree cut is the only LP-visible part of
  the integrality, and it equals §2's slack count.

**Dead (add to LEDGER).**
- Rounding the fractional pair-cover: no "ρ* small ⟹ ρ <= 7" exists (118.1).
- Oblivious extension rules (116.1).
- Randomized or iterative rounding (118.3) [heuristic].

**What remains.** Conjecture PC is not needed for CP. The only live use of this LP would be inside a stability
argument: ρ*_3 close to 7 forces near-pool structure. That is the §33(4) programme again.

**Self-check.**
- 115.1/115.2 are two-line averaging arguments.
- 116.1 uses k >= 2 for the escape points.
- 116.2's pool ρ* was checked exactly (91/15) against the formula.
- 118.1's "y <= δ ⟺ degree feasible" is 7(c − y) >= 3(N − y) ⟺ 4y <= 7c − 3N = 4δ. The finite instance was
  checked by hand: 7·11 = 77 < 81 = 3·27 and 7·12 = 84 = 3·28.
- The exact ρ* uses a basic solution recomputed in Fractions. All covers found by SAT were re-checked pair by pair.
- The UNSAT claims at n = 17 are CaDiCaL's, with no proof log kept.
- Not independently verified.

=============================================================================================
# Part XVIII — finite checks: the FKW parity family against (Σ); exact searches at true window instances (§110–§114)

Code: `compute/core12/`. Logs: `compute/core12/logs/`. Tags as usual. Here "exact" means a complete enumeration by our own
code, or a SAT refutation whose DRUP proof was re-checked by our own RUP checker (`check_drup.py`). "Solver-only" means
the answer comes from one solver run with no checked certificate.
**Outcome.**
- (A) The verified reduction CP ⇐ (Σ) passes the FKW sanity test. The FKW family at m = 3 really is (7,2) with τ > T.
  It contains no Q′ quadruple, no (b) pencil triple and no Theorem-T triangle. At general m this is proved by hand.
- But the test only bites on (b). At ε = 0, (a) and (c) fail by integer rounding (half a point). (b) fails because of
  the parity, which is the real content of the construction.
- (B) No T-covering family without a good seven exists among the profile families with q ≤ 2 cells, at every listed
  instance and at the smaller instance (10, 8, 21). The (Σ) shapes are present in every candidate family. Many of the
  good sevens found contain no (Σ) shape among their own members, which is expected and is not evidence against (Σ)
  (§114). The core9 two-order template does not survive at (10, 8, 21).
- (13, 10, ·) is not a test of CP: genuine (7,2) families with τ = 11 exist there. The smallest genuine open window
  instance is (10, 8, 21), which is missing from the reviewers' list (§112).

## 110. The FKW parity family at m = 3 [proved by hand; computed exact]

**110.1 The family.** S = X ⊔ Y with |X| = 4m and |Y| = 3m + 1, so n = 7m + 1 and k = 4m. The edges are the k-sets A
with |A ∩ X| odd. In co-edge form, c = 3m + 1 and the co-edges are the c-sets K with |K ∩ X| odd (since |X| is even).
T = 3m, so t = 3/4 and ε = 0. N = 7/4 + 1/k, ω·k = n − k − T = 1, and 4δ·k = 7c − 3n = 4.
So the family lies one point above the lower end 5t − 2 of the window, and has slack 4 points and dump 1 point.
**110.2 τ = 3m + 1 for every m >= 1 [proved by hand].**
- Y is a transversal, since every edge has |A ∩ Y| = k − |A ∩ X| >= 1.
- Let U be any set of 4m + 1 points, a = |U ∩ X| >= m. Take j ∈ {a − 1, a} odd. Then j >= m − 1, and U contains an edge
  with j points in X, because 4m − j <= 4m + 1 − a.
- So no 3m-set is a transversal.
Hence the family is T-covering at T = 3m, i.e. τ > T.
**110.3 (7,2) at m = 3 [computed exact: `fkw_spectrum.js 22 12 12`, exhaustive].**
Spectrum (co-type) model, as in the erdosproblemaday report.
- A good seven is the same thing as nonnegative integers x_I, y_I (I ⊆ [7]) with pairwise-intersecting support,
  Σx = |X|, Σy = |Y|, deg_i(x + y) = c and deg_i(x) odd.
- Hand facts used:
  - |I| = 1 is impossible (K_i would be V).
  - |I| = 2 is impossible when 2c < n.
  - Hence Σ(|I| − 3) = 7c − 3n = 4.
- Method: enumerate the heavy co-types (excess 4) up to S_7 (86 classes); DFS over the multiplicities of the 3-sets
  (intersecting support, exact degrees); then an exact DP over the X/Y split with parity.
- Result: 312 degree-feasible co-type multisets, 0 realizable with the parity. **No good seven.**
- Controls:
  - m = 2 (k = 8): 12 multisets, 3 realizable. Witnesses rebuilt as explicit sets and pair-checked, so the family fails,
    as FKW state.
  - Complete K_21^(12): bad tuples exist (the Fano blow-up).
  - Complete K_16^(9) and K_23^(13): none [exact]. This gives f(9,7) >= 8 and f(13,7) >= 11, matching FRESH_C 14.1.
  - The m = 2 control was rerun after the DFS pruning was strengthened. It gave the same 12/3 counts.
- This agrees with the erdosproblemaday report (CP-SAT + SCIP, solver-only) and with NOTES Phase A (solver).
  An independent MILP cross-check of ours (`fkw_milp.py`, all 127 co-types, no hand reduction) finds the m = 2 bad
  tuple; at m = 3 a rerun (`logs/fkw_milp_m3.log`, 40-min cap) was still running when this was written [solver-only, pending]; the result above does not depend on it.
**Verdict.** At m = 3 the FKW family is a genuine (7,2)-family with τ = 10 > T = 9 = 3k/4. So it has no good seven.

## 111. (Σ) inside the FKW family [proved by hand for every m >= 2; computed exact at m = 2, 3, 4]

Finite-k forms with ε = 0 (integer masses): n = 7m + 1, c = 3m + 1, T = 3m.
**111.1 (b) No pencil triple.**
- Three co-edges with union V and triple intersection κ: degree count 3c = n + 2κ + d_2 gives κ <= m + 1.
- The pencil needs κ >= n − 2T = m + 1. So κ = m + 1 and d_2 = 0, and the three petals P_i (size 2m) partition V ∖ κ.
- Let e = |κ ∩ X|.
  - Each |P_i ∩ X| ≡ 1 − e (mod 2), since |K_i ∩ X| is odd.
  - The petals sum to 4m − e.
  - So 3(1 − e) ≡ e (mod 2), i.e. 1 ≡ 0. Contradiction.
- The parity kills exactly the configuration that the complete family on the same 7m + 1 points does contain.
  Exhaustive Venn enumeration (`fkw_sigma.py`):
  - parity family: 0 pencils and largest κ with union V equal to m at m = 2, 3, 4;
  - complete family: one pencil class each, with κ = m + 1.
**111.2 (c) No Theorem-T triangle.**
- The conditions are a, b, d <= (T + n − 2k)/2 = m + 1/2 and a + b + d >= (3n − 3k − T)/2 = 3m + 3/2.
- These are incompatible in integers, since the maximum sum is 3m. Only rounding is at work: at ε = 0 the
  Theorem-T region is the single point a = b = d = (t + N − 2)/2.
- Enumeration: 0 in both the parity and the complete family.
**111.3 (a) No Q′ quadruple.**
- From the load identity (§37), u_3 + 2u_4 = 2s_0 + s_1 + 2 − 2m.
- σ = s_0 + s_1 <= (3T − n)/2 = m − 1/2 forces s_0 = m − 1, s_1 = 0 and u_3 = u_4 = 0. All other points lie in exactly
  two of the four members.
- Opposite pair-masses are then equal (α, β, γ), with α + β + γ = c = 3m + 1.
- The matching conditions give 2α + m − 1 <= 3m, i.e. α <= m, and likewise β, γ <= m. But α + β + γ = 3m + 1 > 3m.
  Contradiction.
- MILP (`fkw_quad.py`, solver-only), parity and complete, m = 3 and 4: the least doubled violation is 1, i.e. Q′ is
  missed by half a point.
**111.4 What the test shows.**
- The reduction is consistent with the only known (7,2)-family above 3k/4: none of the three shapes occurs.
- The complete family on the same ground set does contain a pencil, and does have a good seven, also consistent.
- The test is strong for (b) only. Pencils are excluded by the defining parity, which is the mechanism FKW use to kill
  the Fano blow-up.
- (a) and (c) are excluded by the half-point rounding that ε = 0 forces. A family with ε > 0 would test them; none is
  known (any integer family with τ >= T + 1 at T > 3k/4 would beat FKW).
- No (Σ) shape was found in a genuine no-good-seven family. **Nothing indicates that the reduction is wrong.**

## 112. Which window instances are tests; the search model [proved by hand; computed exact]

**112.1 The list.** The integer instances with 5T − 2k < n < 3k − T and k <= 16 are:
(9,7,18–19), (10,8,21), (13,10,25–28), (14,11,28–30), (15,12,31–32), (16,13,34). Of these:
- **(9,7,·) and (13,10,·) are not tests.**
  - K_16^(9) and K_23^(13) are (7,2) with τ = T + 1 (110.3 controls).
  - Padding (adding points that lie in every co-edge) makes them T-covering co-edge families without a good seven on
    n = 18, 19 and n = 25..28 points, under the literal definition.
  - The profile search finds the padded K_23 at (13,10,25) without being told: cells (23,2), profile (10,2), log
    `prof_ctrl_13_10_25_23-2.json`; MILP-certified seven-free, solver-only.
  - At (13,10) we therefore searched only *nondegenerate* families (every cell has a point outside some member). That
    is the confinement condition that V is a union of edges.
- **(10,8,21) is the smallest genuine open instance.** f(10,7) ∈ {8, 9}; τ = 9 is open. It is missing from the
  reviewers' list.
- (14,11), (15,12) and (16,13) are genuine and open as well: τ > T beats every known construction.
**112.2 Unrestricted search is out of reach.**
- At (10,8,21) there are C(21,11) = 352 716 co-edge variables and C(21,8) = 203 490 covering clauses of length
  C(13,3) = 286.
- Each lazy "no good seven" step is a pair-cover decision. Even at (8,6,15) that took more than 4 h without an answer
  (CORE 55.5).
- At (14,11,28) there are C(28,14) ≈ 4·10⁷ variables.
- The erdosproblemaday methodology (spectrum model with CP-SAT) decides one *symmetric* family. Its natural extension
  to a search is the profile model below.
**112.3 Profile families (`profile_search.py`).**
- Fix a partition V = V_1 ⊔ … ⊔ V_q. Take families that are unions of whole profile classes C(p), Σp = c. These are
  exactly the Sym(V_1) × … × Sym(V_q)-invariant families; FKW is q = 2.
- [proved by hand] T-covering ⟺ every T-profile s is dominated by a chosen p.
- [proved by hand] A good seven ⟺ seven slots in P plus per-cell co-type counts with intersecting support.
- SAT runs on the profile variables (Glucose 4, DRUP proof on), with the covering clauses and, at (13,10), the
  nondegeneracy clauses.
- Each model is shrunk greedily to a minimal covering subfamily. A MILP (HiGHS) then searches it for a good seven,
  using an up-set exactly-one-of-each-complementary-pair encoding of the support. A seven that is found is re-checked by
  plain code and cut.
- Certificate for UNSAT = the CNF + DRUP proof + logged sevens. `check_drup.py` re-derives the covering clauses from
  (k, T, n, cells), re-verifies every cut's seven by plain code, and RUP-checks the proof (deletions ignored).
  A cut is valid by monotonicity: any family containing those ≤ 7 profiles contains the seven.
- Theorem S+ (§39.4) is vacuous here (4εk − 12 < 0), so these classes were not already excluded.
- Controls:
  - (12,9,22), cells (12,10): finds exactly the FKW family {(1,9), (3,7), (5,5), (7,3), (9,1)} at the first SAT call.
    Its "no good seven" is MILP-only, solver-only.
  - (13,10,23), q = 1: finds K_23.
  - (8,6,15), cells (8,7): UNSAT, certificate verified.

## 113. Results [computed exact where the DRUP certificate is verified; see the table]

**113.1 Profile searches.** Every run ended UNSAT: no profile family of that partition is T-covering without a good
seven. The 45-min cap was never reached by any q <= 2 run.

| (k, T, n) | q = 1 | q = 2 (all partitions) | q = 3 (partitions done / total) |
|---|---|---|---|
| (10, 8, 21) | UNSAT | UNSAT 10/10 | UNSAT 19/37 (stopped) |
| (13, 10, 25) nondeg | UNSAT | UNSAT 12/12 | UNSAT 14/52 (stopped) |
| (13, 10, 26–28) nondeg | — | UNSAT 13/13, 13/13, 14/14 | — |
| (14, 11, 28) | UNSAT | UNSAT 14/14 | UNSAT 18/65 (stopped) |
| (14, 11, 29) | UNSAT | UNSAT 14/14 | UNSAT 19/70 (stopped) |
| (14, 11, 30) | UNSAT | UNSAT 15/15 | — |
| (15, 12, 31) | UNSAT | UNSAT 15/15 | — |
| (15, 12, 32) | UNSAT | UNSAT 16/16 | — |
| (16, 13, 34) | UNSAT | UNSAT 17/17 | — |

- Certificates: all 231 UNSAT runs (q = 1, 2, 3 together) have a DRUP proof accepted by `check_drup.py`. Two tampered certificates (one cut deleted; a bogus proof) were rejected.
- The q = 3 batches were stopped for time. The partitions done are the most unbalanced ones (largest first cell).
- In total there were 3 083 cuts over all runs, each a pair-checked good seven.
- What this proves [exact]: for these (k, T, n), no family invariant under the full symmetric group of each cell of any
  partition into <= 2 cells (<= 3 for the partitions listed) is a counterexample. In particular no parity-type /
  FKW-type construction (any set of allowed X-sizes, any |X|) has τ > T and property (7,2) there.
- What it does not prove: anything about families with less symmetry. Theorem S says profile families lose
  asymptotically, so this is the finite-k analogue, not progress on CP.

**113.2 The core9 template at a true window instance (`tg_window.py`, `pencil_find.js`).**
- Rule: two priority orders; the reply to S of class c is S ∪ (the first ω points of V ∖ S in order c). The class of
  every T-set is free (SAT).
- Lazy cuts on every (Σ)(b) pencil found in the current family. `pencil_find.js` is exhaustive when it says so. Pencils
  are restricted by 3c = n + 2κ + d_2, so pair overlaps lie in [n − 2T, 3c − n − (n − 2T)].
- Controls reproduce core9 exactly:
  - (8,6,16) rev: UNSAT (no pencil-free selector).
  - (8,6,15) rev: a pencil-free family of 2 352 members, exhaustive pencil check, in which local search finds no good
    seven (as `esc_8_6_15.log`).
- At **(10, 8, 21)** (ε = 1/20, ω = 3):

| orders | result |
|---|---|
| rev (one order reversed) | UNSAT after 100 rounds (2·10⁷ pencil cuts): **every selector leaves a pencil** |
| two random orders, seed 1 | UNSAT after 19 rounds |
| two random orders, seed 2 | UNSAT after 168 rounds |
| three random orders, seed 2 | UNSAT after 379 rounds |
| three random orders, seed 1 | undecided: the SAT call after round 430 (8.6·10⁷ pencil cuts) passed the 45-min cap; killed |

  [CaDiCaL, solver-only: the refutation is not certificate-checked. Every cut is a genuine pencil by construction of
  `pencil_find.js`.]
- So the template that is pencil-free and (heuristically) seven-free at ε = 0 does not survive one step into the true
  window. With ε·k = 1/2 point of slack and ω = 3 dump points, the pencil can no longer be avoided by any selector for
  these orders.
- This answers the coordinator's question for (10,8,21): the ε > 0 slack forces pencils, hence good sevens.
- (13,10,25) rev: undecided at the 45-min cap. There are 3.27·10⁶ requests and about 1.15·10⁶ members, and pencils are
  still abundant after 221 rounds. It would not be a CP test anyway (112.1).
- (16,13,34): C(34,13) ≈ 9.3·10⁸ requests; not attempted.

## 114. Structure of the forced good sevens; status; self-check

**114.1 Do the forced sevens contain (Σ) shapes? [computed exact on the logged data, `seven_shapes.py`, `sigma_profile.py`]**
- Of the 3 083 logged good sevens, 949 contain no pencil, Theorem-T triangle or Q′ among their own members.
- The smallest deficits are ½–1 point for T and Q′, and 1 point for the pencil. These are finite-k rounding sizes.
- The co-type size profiles of those 949 are mostly 3- and 4-sets with a few 5-, 6- and 7-sets, with non-Fano triples.
- **This is not evidence that (Σ) is too narrow.** (Σ) says the *family* contains a shape, not the seven. The MILP
  returns an arbitrary seven.
- At the family level, every one of 2 896 candidate families (minimal T-covering profile families met in the
  searches) contains a (Σ) shape:
  - pencil in 2 896;
  - Q′ in 2 872;
  - Theorem T in 1 047;
  - families with none: 0 [MILP per family, solver-only; witnesses re-checked by plain code].
- So these data do not suggest any new minimal finishing configuration (Σ⁺) at the family level. The seven-level data
  are exported for FABLE_C (114.2).
- Caveat: profile families contain pencils for a structural reason (Theorem S). The data cannot say whether (Σ) is
  too narrow for non-symmetric families.
**114.2 Data export for FABLE_C.** `compute/core12/forced_sevens.jsonl` (`export_sevens.py`) holds all 3 083 forced
good sevens at window instances, one JSON object per line. Each record has the seven co-edges as explicit bitmasks on
0..n−1 (cells = consecutive blocks), re-checked to cover all pairs, and the profile family it came from.
- The sub-shapes were recomputed from the bitmasks: pencil 1 881, Theorem T 90, Q′ 583. 2 134 sevens have at least
  one shape and 949 have none, matching 114.1.
- Classification is left to FABLE_C.
- The prefix-trace test was dropped on the coordinator's instruction (FABLE_C owns adaptive certificates).
**114.3 Status.**
- (A) passed. The reduction survives its only available sharp check (b). (a) and (c) are not tested at ε = 0.
- (B):
  - No profile counterexample at any listed instance, or at (10,8,21).
  - The core9 template dies at (10,8,21).
  - Unrestricted families at window instances remain out of reach (112.2).
  - Next feasible targets: profile families with q = 3, 4 at (10,8,21), and reflection- or cyclic-invariant families
    at (10,8,21). The latter cut the variable count by about 2n while keeping hash-like freedom.
**114.4 Self-check.**
- 110.2, 111.1–111.3 re-derived by hand for general m. The parity step in 111.1 was checked against the enumeration
  at m = 2, 3, 4.
- `fkw_spectrum.js`: the pruning was changed during the run. The m = 2 control was rerun on the final code and gave the
  same 12/3 counts.
- `check_drup.py` first deleted clauses as the proof said. That rejected valid proofs, because the incremental solver
  deletes reason clauses. It now ignores deletions, which is sound.
- The profile model's two equivalences (112.3) are two-line arguments. The cut validity uses only monotonicity.
- Solver-only items:
  - the MILP "no good seven" for the FKW and padded-K_23 control families;
  - the template UNSATs;
  - the per-family shape MILPs;
  - the Q′ margin MILP.
- Not independently verified.
