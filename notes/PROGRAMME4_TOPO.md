# Programme 4: go/no-go on the colouring-complex (Dold / topological Hall) method

Verdict: **NO-GO** as a proof route. The criterion is correct, and the toy version fires empirically from
tau >= k/2 + 2 on. But the connectivity statement it needs could not be proved even for triples, and the
generic connectivity bounds cannot supply it. Code: `compute/programme4/topo/`. Log: `logs/toy_all.log`.

## 1. The criterion (sevens)
**Definitions made consistent.** For a member B and c: B -> F_2^3 \ 0, put S(v) = {u != 0 : <c(p),u> = 1 for all p in B}.
We say v = (B,c) *serves* u if u is in S(v). This holds iff c(B) misses the hyperplane u^perp, i.e. iff c(B) avoids
the Fano line l_u = u^perp \ 0. So "u served" and "line l_u avoided" mean the same thing. S(v) is the solution set of
the affine system <x,u> = 1 (x in c(B)): it is nonempty for a vertex, misses 0, and has size 1, 2 or 4. Colour 0 never
occurs in a vertex, since <0,u> = 0. [proved by hand]

**Simplex <=> Fano-type seven** [proved by hand]. Pairwise compatible colourings glue to one partial colouring of the
union of their members. Extend it arbitrarily, for example by 0, to chi: V -> F_2^3; this covers points in no chosen
member. If every u is served by some vertex (B_u, chi|B_u), then B_u ⊆ R_u, which is a Fano-type seven. Repeats are
allowed: one vertex may serve up to 4 values of u. Conversely, given (chi, B_u), the vertices (B_u, chi|B_u) are
pairwise compatible and B_u serves u. Two vertices with the same member and different c are never compatible.

**Freeness** [proved by hand]. Let s be a Singer cycle (order 7, no fixed nonzero vector). It acts by (B,c) -> (B, s∘c),
and this preserves vertices and compatibility. The vertex stabilisers are trivial, because B is nonempty and
s^j c(p) != c(p). Suppose s^j fixes a simplex setwise. Since 7 is prime, the simplex then contains a full orbit
{(B, s^i c)}, and these vertices are pairwise incompatible. So no simplex is fixed, and Z_7 acts freely on |N(H)|.
On the target, s acts on the vertex set {u} of Delta^6 by u -> s^{-T}u, which is again a Singer cycle. Then
S(s·v) = s^{-T} S(v), and the only invariant face is Delta^6 itself, so the action on dDelta^6 = S^5 is free.

**The map** [proved by hand]. The reviewer's version, "simplex -> barycentre of its served set", is **not continuous**
across faces. The correct map is the affine extension of v -> barycentre(S(v)), or the same rule on the barycentric
subdivision (the served set is monotone). The image of a simplex lies in the face spanned by its served set. With no
good seven that face is proper, so f maps into S^5. The map is continuous and equivariant.

**Dold version needed** [cited; checked against the statements]. The homotopy version is Dold's theorem (Matousek,
*Using the Borsuk–Ulam theorem*, Thm 6.2.6): an n-connected G-space admits no G-map to a free G-complex of
dimension <= n. The homological form is Volovikov's theorem (Sb. Math. 191 (2000) 1259–1277; Math. Notes 59 (1996)).
Let G = Z_p, let X be fixed-point free with H~^i(X;F_p) = 0 for i < n, and let Y be finite-dimensional and
fixed-point free with H^i(Y;F_p) = 0 for i >= n. Then there is no G-map X -> Y. Take n = 6 and Y = S^5. So
**H~_i(N(H);F_7) = 0 for i <= 5 suffices.** Over a field, H~^i and H~_i vanish together for a finite complex.
**Criterion status: correct** [proved by hand, modulo the cited theorem].

**Useful model** [proved by hand]. Let P = prod_{p in V} Delta^6, with the vertices of each factor labelled by the
nonzero colours. Let F(B,c) be the face that fixes the coordinates of B at c. These faces are closed and convex, and
any set of them meets exactly when the colourings are pairwise compatible. By the nerve theorem,
N(H) ≃ U = ∪ F(B,c) ⊆ dP, and the homotopy equivalence is Z_7-equivariant. The same holds for the toy with Delta^2.

## 2. Decisive test: the toy (triples)

**Toy, stated precisely** [proved by hand]. Take colours F_2^2 \ 0, identifying a colour with the unique u it is
orthogonal to (colour i: the point is outside R_i). A vertex is (B, c: B -> {0,1,2}) with c not surjective; it
serves the colours it misses. Group: the Singer cycle Z_3 ⊆ GL_2(F_2) (cyclic shift), acting freely. Target:
dDelta^2 = S^1. Coefficients F_3; hypothesis H~_0 = H~_1 = 0. A simplex serving all three colours is exactly a good
triple (three members with empty common intersection).

So the toy criterion reads: H~_{<=1}(N_toy;F_3) = 0 implies a good triple. To reprove Lemma A0 one needs
**(T): tau >= k/2 + C implies H~_{<=1}(N_toy;F_3) = 0.**

**Computation** [computed; `toy_complex.py`, exact F_3 rank with a spanning-forest reduction]. 35 families with
k <= 4: complete families, matchings, Fano lines, PG(2,3), and 17 random tau-critical families.
- Every family **without** a good triple has nonzero low homology, as Dold requires. The star has rb0 = 2; K^(3)_4 has
  b1 = 88; K^(4)_5, the A0-tight family, has b1 = 208.
- **All 20 families with tau >= k/2 + 2 fire** (27 of 35 fire in all). Only 5 families with a good triple do not
  fire: K^(1)_2 (b1 = 4), two disjoint edges (64), K_3 (28), K^(3)_5 (1) and K^(4)_6 (181). All have tau <= k/2 + 1.5.
- Sparse tau-critical families fire earlier: all six random families with k = 3 and tau = 3 fire. For complete
  families the threshold is exactly tau >= k/2 + 2 for k = 1..4. Compared with A0 (tau >= (k+1)/2 + 1/2) the
  additive loss is 1–1.5. This is consistent with the reviewer's report: the
  method is **not refuted** at small k.

**Proof attempt for (T), and where it breaks.**
1. Connectivity is easy [proved by hand]: tau >= 2 implies N_toy is connected. To recolour one point p of B, pass
   through a vertex (B'', c|B∩B'') with B'' a member avoiding p. Monochromatic colourings link the colour pairs.
2. H_1 is the whole difficulty. Every route I tried needs, at some step, a member that avoids an entire colour
   class of a union of 2–4 members. Such a class has Theta(k) points, while tau ~ k/2 only lets a member avoid any
   set of fewer than tau points.
   - Coning a 4-cycle needs a common compatible vertex, i.e. a member avoiding the conflict set plus one colour class.
   - Canonical recolouring paths into a fixed cylinder C(B0, c0) get stuck on B0 ∩ B. There, neither B0 nor B avoids
     the point being recoloured, and a third served member is required.
   - Mayer–Vietoris on the colour at a point p (U = U_0 ∪ U_a ⊔ U_b ⊔ U_c, with U_0 ≃ N_toy(H - p)) needs
     H_1(N_toy(H - p)) to die in U. The induction loses 1 from tau per step and does not close.
3. **The generic tools are capped** [proved by hand]. Suppose H is intersecting. Then the two vertices
   (B0, const a) and (B0, const b) *totally dominate* the incompatibility graph G, whose independence complex is
   N_toy. Every (B,c) with B ∩ B0 != ∅ disagrees with at least one of them. So gamma~(G) <= 2 and the independence
   domination number i·gamma(G) <= 2. Meshulam's bound eta >= gamma~/2 and the Aharoni–Berger–Ziv bound
   eta >= i·gamma (the inputs to Aharoni–Haxell–Meshulam topological Hall) therefore give at most eta >= 2, i.e.
   "connected". The toy needs eta >= 3. The sevens need eta >= 7.
   Intersecting families are exactly the hard cases: 3k/2 <= n < 2k in the toy, where A0 is tight, and for sevens
   **every** k-uniform family in the Fano range n < 11k/6 < 2k. The Meshulam game bound was not evaluated [open].
4. Logically, (T) together with the criterion implies A0 + C. So (T) is a new statement at least as strong as A0,
   and the 2-line proof of A0 has no analogue in the complex. For sevens, the needed statement
   "tau >= (3/4 + eps)k implies H~_{<=5}(N;F_7) = 0 in the Fano range" implies (S_<). The method moves the whole
   difficulty into a connectivity theorem, and no available bound reaches it.
5. Sevens cannot be tested either [computed estimate]. A member has about 7·4^k vertices; K^(4)_7 alone gives
   about 6·10^4 vertices, and the needed range is H_{<=5}.

**Exact obstruction.** Proving (T) needs eta(N_toy) >= 3 for intersecting families with tau ~ k/2 + C. The
domination-type connectivity bounds stop at eta <= 2 there, because two monochromatic vertices of one member
dominate everything. A bespoke H_1 argument needs members that avoid Theta(k)-point colour classes, which tau ~ k/2
does not provide. Step 3 (scaling to sevens, slope 1/3) is therefore not attempted.

## 3. Matroid dictionary (side item)

Let U = {y in F_2^V : supp(y) contains a member}. The members are nonempty, so 0 is not in U.
- **tau(H) = crit(U)** [proved by hand].
  - (<=) Take a transversal T and W = {y : y|_T = 0}, of codimension |T|. The support of y in W misses T, so it
    contains no member.
  - (>=) Let W have codimension c with W ∩ U = ∅, and let P be a pivot (information) set of W, |P| = |V| - c. Some
    y in W has y|_P = 1, so supp(y) contains P. Since y is not in U, P contains no member, and V \ P is a transversal
    of size c.
- **Fano-type seven <=> U contains a PG(2,2)**, i.e. a 3-dimensional subspace minus 0 [proved by hand, for all n].
  - (=>) phi(u) = 1_{R_u} = (<chi(p),u>)_p is linear in u. Each R_u contains B_u, which is nonempty, so phi is
    injective and phi(F_2^3 \ 0) ⊆ U.
  - (<=) Let a basis w_1, w_2, w_3 be given. Put chi(p) = (w_1(p), w_2(p), w_3(p)). Then R_u = sum of u_i w_i is in U,
    so it contains some B_u. Points of colour 0 lie in no R_u, so the paper's Pi-colouring is recovered by recolouring
    them arbitrarily.

  Together with Corollary `cor:fanorange`: **for n < 11k/6, H is (7,2) iff U contains no PG(2,2)**
  [proved by hand, given Theorem `thm:class`]. For all n, (7,2) implies that U contains no PG(2,2); the converse can
  fail above 11k/6 (non-Fano sevens).
- Toy dictionary [proved by hand]: **a good triple <=> U contains a PG(1,2)** ({a, b, a+b}, i.e. U is not sum-free).
  So A0 reads: if U is a sum-free up-set of k-heavy vectors, then crit(U) <= (k+1)/2.
- Density-type critical-threshold results (Bose–Burton, Geelen–Nelson) do not apply [heuristic]. Near the extremal
  families U has vanishing density (a random subset has about n/2 < k points).
