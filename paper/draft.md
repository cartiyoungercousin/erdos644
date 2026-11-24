# Erdős Problem #644 ($f(k,7)\overset{?}{=}(3/4+o(1))k$): what is established, and what is not

**Draft for expert checking. Honest status over polish.**

> **Headline status.** We do **not** prove $f(k,7)\le(3/4+o(1))k$, and we do not disprove it. We give (i) a set of machine-checked (Lean 4/Mathlib) lemmas and reductions, (ii) hand-proved (so far unverified) reductions of the problem to a *confined covering game*, (iii) hand proofs closing several regions of that game, and (iv) hand proofs that wide families of structured counterexamples cannot exist. The remaining gap is stated exactly in §8. Every claim carries a status tag taken from `notes/LEDGER.md` at the time of writing:
>
> * **[LEAN]** formally verified in Lean 4/Mathlib (file named). Only standard axioms; no `sorry` appears in `Lean644/*.lean` (we grepped; we have not re-run the CI axiom check for this draft).
> * **[HAND]** proof sketch, **under verification**. Nobody independent has checked it. Where the ledger says "verification pending (Vn)", the verifier report is not yet available (`notes/verify/` is empty at the time of writing).
> * **[EXACT]** computed in rational/brute-force arithmetic on finite instances (a check, not a proof of the general statement).
> * **[FLOAT]** floating-point computation (evidence only).
> * **[DEAD]** refuted or abandoned.
> * **[not in ledger]** stated in the supporting notes but not listed in the ledger; included only because the requested structure needs it, with the status the notes give. See `paper/TODO.md`.
>
> Items marked **[cite?]** or **[to check]** are unverified references or numerical look-ups.

---

## 1. Introduction and known bounds

**The problem.** Let $f(k,r)$ be the least number such that every family of $k$-element sets in which every $r$ members can be hit by two points has a hitting set (transversal) of size $f(k,r)$. In the notation of the literature $f(k,r)=f(k,r,2)$: the maximum of $\tau(H)$ over $k$-uniform $H$ with property $(r,2)$. Erdős asks (problem page: erdosproblems.com/644 [cite?: exact wording of the page was recorded in `notes/NOTES.md`, not re-read here]) whether $f(k,7)=(1+o(1))\tfrac34k$, and whether for every $r\ge3$ there is $c_r$ with $f(k,r)=(1+o(1))c_rk$.

**Known results, as our notes record them.**

| $r$ | $f(k,r)$ | source (as recorded; mostly second-hand) |
|---|---|---|
| 3 | $2k$ | Erdős–Fon-Der-Flaass–Kostochka–Tuza, *Small transversals in uniform hypergraphs*, Siberian Adv. Math. 2 (1992) 82–88 [cite?: paper not accessible to us; values taken from the problem page] |
| 4 | $\lfloor 3k/2\rfloor$ | same |
| 5 | $\lfloor 5k/4\rfloor$ | same |
| 6 | $k$ | same |
| 7 | $3m+1\le f(4m,7)$ for $m\ge10$; $f(k,7)\le\lceil 7k/8\rceil$ | Fon-Der-Flaass–Kostochka–Woodall (FKW), *Transversals in uniform hypergraphs with property (7,2)*, Discrete Math. 207 (1999) 277–284 (read by us) |

Further literature recorded in `notes/LITERATURE.md`: Erdős–Hajnal–Tuza (JCTA 58 (1991) 78–84) as the origin of $f(r,p,t)$ [abstract only]; Kostochka, Combinatorica 22 (2002) 275–285 [abstract only; not seen to improve $p=7$]; Bucić–Korándi–Sudakov, arXiv:1902.05055 (read §1, §5). For $r=7$ the problem page therefore has the gap $\tfrac34k+1\le f(k,7)\le\lceil 7k/8\rceil$.

**Unrefereed 2026 claims (not verified by us; none is a result of this paper).** A manuscript `six_sevenths_v3` (repository cubres/erdos-644-research) claims $f(k,7)\le\lceil 6k/7\rceil$; a repository skyvegetable666/erdos-644-11-over-13 claims $f(k,7)\le 11k/13+8$; the paper arXiv:2610.02945 (Ansatz) lists $\lceil(6k+3)/7\rceil+1$ for $k\ge150$ as "AI-proposed". [cite?: authors, titles and dates are as in `notes/LITERATURE.md`; we have not checked them against the sources.] **We add no new upper bound for $f(k,7)$.** Our contribution is structural (reductions, closed regions, classification of counterexample shapes) plus Lean verification of several lemmas, some of which are pieces of the 6/7 manuscript.

**On the 6/7 manuscript in Lean.** The ledger lists the manuscript's Lemmas 4.1–4.8 among [LEAN] items, and `Lean644/OneCoreLemma.lean`, `TwoLarge.lean`, `HallClose.lean`, `Symmetric.lean`, etc. contain them. The *main theorem* ($\lceil 6k/7\rceil$) is only **stated** (frozen in `Lean644/Statements.lean` as `SixSeventhsStatement`; `Bridge.lean` proves that the "at most seven" wording implies Erdős's "exactly seven" wording). **We found no Lean proof of `SixSeventhsStatement` itself**; hence the 6/7 bound must not be regarded as formally verified. (An older note, `STATUS_AND_PLAN.md`, says Lemma 4.1 was still in progress; the ledger and the repository now list it as done. See TODO.)

---

## 2. Setting: the request principle and the game form

**Definitions.** $H$ is a finite family of $k$-sets. $\tau(H)>T$ means no set of $\le T$ points meets every member. $H$ has property $(7,2)$ in the **at-most convention** (`HasPropertyAtMost H 7 2`) if every subfamily with at most seven members has a transversal of size $\le2$. The at-most convention is not cosmetic: with "exactly seven", families with fewer than seven members satisfy the property vacuously, and some statements below (flat tuples) are false (PROOFS §0, E1: $k=1$, $T=1$, $H$ = two singletons). The headline statements in `Statements.lean` come in both wordings, linked by `Bridge.lean`. [LEAN]

**Request principle.** If $\tau(H)>T$ then every set $S$ with $|S|\le T$ is disjoint from some edge ($S$ is not a transversal). So, if the requester asks for $S$, *some* edge avoiding $S$ exists; an adversary who "answers" requests with such edges is exactly a family. [elementary; used in Lean as `exists_response`]

**Game form.** The requester makes requests $S_1,S_2,\dots$ of size $\le T$; the adversary answers with an edge $B_i\in H$, $B_i\cap S_i=\emptyset$. The requester wins if some $\le7$ of the replies (as a tuple, repetitions allowed) have no 2-point transversal. If she wins against every adversary, then $H$ with $\tau(H)>T$ contradicts $(7,2)$, i.e. $f(k,7)\le T$.

*Stationary adversaries are WLOG when the number of requests is unbounded (TWIN 16.2, CORE Part VII).* If requests may be repeated, a reply differing from an earlier reply to the same request only enlarges the pool, and winning is monotone in the pool. So with unboundedly many requests the adversary is a fixed family, and the game is exactly the family statement. Bounded-request versions are formally stronger (they are the form in which computation is possible).

**Co-edge form (CORE §1, [HAND]).** In a confined setting (all replies inside a ground set $V$, $|V|=N$), with $c=N-k$ and co-edges $K_i=V\setminus B_i$ ($|K_i|=c$), a pair $\{x,y\}$ misses $B_i$ iff $x,y\in K_i$. So seven replies have no 2-cover iff the seven co-edges cover all pairs of $V$ ($x=y$ included), iff the co-types $I_x=\{i:x\in K_i\}$ are non-empty and pairwise intersecting. Moreover $\tau(H)>T$ for $H$ confined to $V$ iff the co-edge family is **$T$-covering** (every $T$-subset lies in a member). Units: $k=1$, $t=T/k=\tfrac34+\varepsilon$, $N=|V|/k$, $\omega=N-1-t$ (the adversary's free mass in a full request), $\delta=N-\tfrac74$.

**Fano criterion [LEAN: `Fano.lean`, `FanoBlocks.lean`].** Label seven edges by the lines of the Fano plane. If for every point $p$ the three edges on lines through $p$ have empty common intersection, the seven edges have no 2-point transversal. (Co-edge form: every $I_x$ contains a line, equivalently a "pencil" of three concurrent lines, CORE 1.3.) `FanoBlocks.lean` gives the sequential "mandatory blocks" form: if each $B_c$ avoids $M_c$ then no 2-cover, so in a $(7,2)$-family with $\tau>T$, six edges respecting $M_2,M_4,M_5$ have $|M_6|>T$.

---

## 3. Reductions (with Lean status)

### 3.1 Flat 7-tuples and the lower side [LEAN: `FlatTuple.lean`]

**Lemma 3 (top-degree requests).** If $H$ is $k$-uniform, $\tau(H)>T$ and $3k\le4T$, there are seven edges (a tuple, possibly with repetitions) such that every point lies in at most four of them. *Proof sketch:* request in each step the $T$ points of highest current degree; counting promotions gives $N_5(7)=0$ because $3(k-T)\le T$. (FRESH_C §1.)

**Corollary 4.** In such a tuple, $\{x,y\}$ is a 2-cover iff one point has degree exactly 4 and the other lies in all three complementary edges. Consequently if all 7-tuples satisfied "some point in $\ge5$ edges" then $\tau\le\lceil3k/4\rceil$; this is tight for the complete family on $\lceil7k/4\rceil-1$ points. [Cor. 3a/3b are proved by hand in FRESH_C and PROOFS §1; the ledger lists only the Lean-verified lemma, so we quote Cor. 3a as context only.]

### 3.2 Good triples, tight-triple, trace, pair gap, stability, lopsided top, sparse triple [LEAN]

A **good triple** is three edges with empty common intersection ($E,F,G$); $W=E\cup F\cup G$; $S=|E\cap F|+|E\cap G|+|F\cap G|$, so $|W|=3k-S$. Lean-verified lemmas (each file's docstring has the statement; all are in the ledger's [LEAN] row):

* `TightTriple.lean`: if $\tau(H)>T$ then every good triple has $S\le3k-2T+1$ (sizes via a Fano template; a size formula was also checked exhaustively in Python).
* `TraceLemma.lean` (Lemma B): $2|K\cap W|>3T-|W|$ for every edge $K$ when $\tau>T$ and $(E,F,G)$ is a good triple.
* `PairGap.lean`: with $u$ a lower bound on the largest pair cell of every good triple, no pair of edges meets in $[2k-2u-T+2,\,u)$ points.
* `Stability.lean` (Thm 11.1): if every good triple has $S\ge\sigma$ and $\tau>T$ then $11T+7\sigma<17k+5$.
* `LopsidedTop.lean` (Thm 6.4, constant 26): closes the top of the lopsided regime ($28k+12\le16T+26u$).
* `SparseTriple.lean`: every good triple has $3T<k+3S$.
* `ThreeCentres.lean` (Lemma 6.1, Cor. 6.2): petals $P$ with empty common intersection and union $U$, three centres with pairwise disjoint traces on $U$: no 2-cover. Corollary: if $\tau>T$, $|P|\le4$ and $B_1\cap B_2\cap U=\emptyset$ then $|B_1\cap U|+|B_2\cap U|>T$.
* `TheoremA.lean` (Theorem A, one-anchor Fano template): if all edges lie in an $n$-set, $\tau(H)\le\lceil (n-k)/3\rceil+2\lceil k/4\rceil$; tight for $K^{(4m)}_{7m-1}$ and the FKW parity family.
* `Waste.lean`: rectangle lemma and the waste adversary (§6).
* Whether these are new is **unconfirmed**: the 1992 EFKT paper is not accessible to us, and several of these lemmas overlap with the repositories listed in §1 (e.g. the lex-min anchor is already in the 11/13 repository). [cite?]

### 3.3 Anchored reduction (TWIN §13) [LEAN for the combinatorial core; HAND for the transfer]

**Anchor lemma** [LEAN: `Anchor.lean`, `anchor_cover_mem`, `anchor_trace_iff`, `anchor_mono`, `anchor_coverable_mono`]. Let $B_a,B_b,B_c$ be edges with $B_a\cap B_b\cap B_c=\emptyset$ and $V=B_a\cup B_b\cup B_c$. Every 2-cover of any family containing them consists of two points of $V$; covering an edge $E$ depends only on $E\cap V$, monotonically.

**Theorem A$_{\rm anch}$ (anchored reduction, padding transfer) [HAND, TWIN §13.2; PROOFS §8 reports it correct].** She may run verbatim, against an open adversary, any strategy for the *anchored confined game* $G(V)$: requests inside $V$, the adversary answers with a subset of $V\setminus S$ of mass $\min(k,|V\setminus S|)$; same requests, same budget, same rounds. *Proof sketch:* feed the strategy the traces $E\cap V$, padded inside $V\setminus S$ when shorter than needed; by monotonicity, padding can only create covers, so an uncoverable padded tuple is uncoverable in reality. ∎ Consequently, as soon as three anchors exist the adversary may be taken confined to $|V|\le3k$. Anchors can always be created: some $S_2$ forces $|B_1\cap B_2|\le T$; $S_3\supseteq B_1\cap B_2$ then makes a triple with empty intersection; each re-anchoring costs at most three requests. Write $p_{ab}=|B_a\cap B_b|$, $p=\sum p_{ab}$; then $|V|=3k-p$.

**Petal generalisation** [LEAN: `PetalReduction.lean` for P1, P3(i), P4(a), P4(c), `petalActive_iff`; HAND for the strategy-transfer statement P3(ii)]. For $2\le q\le6$ petals with empty common intersection and union $U$: the *dangerous graph* $\Gamma(P)$ has $x\sim y$ iff every petal contains $x$ or $y$; its non-isolated vertices form the *active set* $U^*(P)$; $x$ is active iff the petals missing $x$ have a common point. Every 2-cover of a family containing $P$ is an edge of $\Gamma(P)$; coverability depends only on traces on $U^*$ (monotone); one centre disjoint from $U^*$ wins; three centres with pairwise disjoint traces on $U^*$ win. Hence $|U^*(P)|\le t$ for some petal set is a one-request win. PETAL §1 also records a randomised brute-force check of P1–P4 on 2063 systems [EXACT].

**Theorem B (three-grid form) [HAND, TWIN 13.3].** Anchors plus four further replies $E_1..E_4$ have no 2-cover iff for each split $(ab|c)$: $\bigcup_i (P_{ab}\setminus E_i)\times(B_c\setminus E_i)=P_{ab}\times B_c$. In co-type language: $I_x\cap I_y\ne\emptyset$ for all $x\in P_{ab}$, $y\in B_c$.

---

## 4. Case split and which regions are closed

Everything below is in the first-order scale ($k\to\infty$, masses in units of $k$, $t=\tfrac34+\varepsilon$). By §3.3 an arbitrary adversary is, after three requests, confined to the union $V$ of three anchors, with $\tfrac32k\le|V|\le3k$. The case split used in the notes is by the size/shape of this union and by the ground set $N$ of the "arena".

| Region | Result | Status |
|---|---|---|
| $|V|\le2T+O(1)$ (anchors, "Fano point") | **Theorem C**: four non-adaptive further requests win (TWIN 13.4) | [HAND] (TWIN §13) |
| $|V|\ge\tfrac{10}3k-T$, i.e. $p\le T-k/3$ | **Theorem D**: four further requests, no discard (TWIN 13.5; checked exhaustively at $k=3$) | [HAND] (TWIN §13); [EXACT] on one instance |
| Concentrated, ground set $N\le 3t-\tfrac12$ (units of $k$) | **Proposition 16.A**: seven requests, no discard | [HAND] |
| Concentrated, $3t-\tfrac12<N<3-t$ | open: this is (CP) / (Σ), §8 | open |
| Spread side, $N\ge3-t$ (petals) | Theorems J, K, L; J′, J″, DS, AP in classes (§7.2) | [HAND]; open for the class in §8.2 |

*Remark on the ledger vs the notes.* The ledger lists the anchored reduction and "Concentrated case $N\le3T-k/2$ (TWIN 16.A)" as [HAND]. CORE §1.2 identifies 16.A with the Lean file `TheoremA`; that is a mismatch we have **not** resolved (the Lean `TheoremA` is the one-anchor Fano template of §3.2, which is a different statement). We follow the ledger. Also, Theorems C, D are listed in the ledger only through "TWIN §13".

**Theorem C (small union) [HAND].** If $|V|\le2T+O(1)$, four more requests win non-adaptively. *Proof sketch.* Rounds 4–7: split $P_{12}$ into halves of request-types $\{4,7\},\{5,6\}$; $P_{13}$: $\{4,6\},\{5,7\}$; $P_{23}$: $\{4,5\},\{6,7\}$; split each $Q_c$ (points in exactly one anchor) into four parts carrying the four pairs that are not the two types of the opposite $P_{ab}$. Two 2-subsets of a 4-set are disjoint only if complementary, i.e. only inside one $P_{ab}$, so every required intersection holds; each round requests half of every part: mass $|V|/2\le T$.

**Theorem D (large union) [HAND].** If $p\le T-k/3$, four more requests win with no discard. *Proof sketch.* Every later request contains $P$, so points of $P$ lie in no later reply. A cover needs $x\in P_{ab}$ and $y\in Q_c$ in all four later replies. With $X_1=E_1\cap Q$ ($\le k$), $X_2=X_1\cap E_2$, $X_3=X_2\cap E_3$, requests 5 and 6 contain $T-p$ points of $X_1$, resp. $X_2$, so $|X_3|\le k-2(T-p)\le T-p$, and request 7 contains $X_3$. ∎

**Proposition 16.A (concentrated, $N\le 3t-\frac12$) [HAND].** If all replies lie in a known set $V$ with $|V|\le 3T-k/2-O(1)$, she wins in seven requests, no discard. *Proof sketch.* $B_1$ arbitrary; fix $a_0\subset V\setminus B_1$ of mass $\alpha=N-2t$; $S_2=a_0\cup(t-\alpha\text{ points of }B_1)$ gives $|B_1\cap B_2|\le(1-t)+\alpha$; $S_3=a_0\cup(B_1\cap B_2)$ has mass $\le2\alpha+(1-t)=2N+1-5t\le t$. Then $B_1,B_2,B_3$ are anchors, disjoint from $a_0$, with union of mass $\le N-\alpha=2t$, and Theorem C finishes. ∎ Above $3t-\frac12$ the kernel $a_0$ cannot be both large enough and affordable twice (TWIN 16.5).

**(CP) and its status (CORE §7, §33).** *For every $\varepsilon>0$ and $k\ge k_0(\varepsilon)$, $T=(\frac34+\varepsilon)k$, $k+T\le N<3k-T$: every $T$-covering family of $(N-k)$-subsets of an $N$-set contains seven members covering all pairs.* Open for $3T-k/2<N<3k-T$. Stated as a family statement by the stationarity remark of §2.

**Static certificates in the co-edge window [HAND; computed exact on instances].**

* *Slack count (CORE §2).* For any seven co-edges, $\sum_x(|I_x|-3)=4N-7=4\delta$ (units $k=1$; for $N<2$ each winning co-type has size $\ge3$). A certificate with $q$ replies used in full and $7-q$ only through their requests has slack $(q-3)(N-\frac74)+(7-q)\varepsilon$; for $q=3$ this is $4\varepsilon$ at every $N$. This explains why every "three replies plus four fixed requests" certificate is a zero-slack design while the adversary's window of free mass $\omega$ is much wider than $\varepsilon$.
* *Theorem T (triangle anchors, CORE §3).* Three co-edges with cells $a,b,d,e_i,g,\kappa$ and a split $\kappa=\kappa_4\sqcup\kappa_5\sqcup\kappa_6$ satisfying $|a|+|e_3|+|g|+|\kappa_4|\le T$ and its two cyclic analogues, and $|e_1|+|e_2|+|e_3|\le T$, are finished by four non-adaptive requests. *Proof:* the cells are the points of a Fano plane; every co-type contains a pencil. With $\kappa=\emptyset$ it is solvable iff $T\ge3k/4$ and then has tolerance $O(\varepsilon k)$.
* *Theorem Q (four free replies, CORE §4).* Four co-edges forming a quadrangle are finished by three fixed requests iff the waste $W=u_3+2u_4+s_1\le N-\frac74k+3\varepsilon k$ and the three matching loads are $\le T$. Set form Q′ (CORE §37): four members with $\sigma\le(3t-N)/2$ and balanced matchings.
* *Pool theorem P (CORE §5).* If the adversary's additions always fall into a set $Z$ known to her, $\omega\le|Z|\le N-\frac32k$, then seven requests win. *Proof:* kernel class $V_o\supseteq Z$, six classes of mass $(N-w_o)/6$; for the three lines through $o$ request $L\setminus Z''$ padded, so that $Z\setminus S=Z''$ has exactly the mass he must add; the other four lines are requested outright.

These four are the tools used in §7.1. Status of T, Q, P: [HAND] (ledger: "computed exact on instances": 1581 random triples, 1560 random quadruples, and 200 random pool adversaries per instance on small grounds, all uncoverable by brute force).

---

## 5. Exact small values

**Claim [not in ledger; status per `notes/FRESH_C.md` §14.1–14.3].** $f(6,7)=5$ and $f(7,7)=6$.

*Lower bounds.* The complete $k$-uniform family on $N$ points has $\tau=N-k+1$ and (at-most) property $(7,2)$ iff no $\le7$ co-edges of size $N-k$ cover all pairs of the $N$-set, i.e. iff the pair-covering number $C(N,N-k,2)\ge8$ (FRESH_B 1.3 [HAND]). We need, with the notation $C(v,c,2)$ of covering designs:

| $k$ | $N$ | $\tau=N-k+1$ | needed fact | status of the number |
|---|---|---|---|---|
| 5 | 9 | 5 | $C(9,4,2)\ge8$; (and $N=10$: $C(10,5,2)\le7$) | [to check] |
| 6 | 10 | 5 | $C(10,4,2)\ge8$; (and $N=11$: $C(11,5,2)\le7$) | [to check] |
| 7 | 12 | 6 | $C(12,5,2)\ge8$; (and $N=13$: $C(13,6,2)\le7$) | [to check] |

Our notes obtained the "largest $N$" column (6, 9, 10, 12, 13, 16, 17, … for $k=4,5,\dots$) from an exact integer program [EXACT, one solver, not independently re-checked]. **We attempted to compare with the La Jolla Covering Repository (ljcr.dmgordon.org); the site was unreachable from our environment and a web search returned no table entries, so no value above has been checked against the repository. [to check]** A web search did indicate that for $t=2$ and $v/k\le13/4$ exact values of $C(v,k,2)$ are known (Mills and later authors) [cite?], which covers all rows above.

*Upper bounds.* The notes' certificates (`anchor_select.js`, checked by the independent `cert_check.py`; 88, 207, 247 requester nodes; 17, 27, 37 winning shapes for $(k,T)=(6,5),(7,6),(8,7)$ with 8 requests) show that every $k$-uniform family with $\tau>k-1$ contains an uncoverable 7-subfamily. This is [EXACT] **and conditional on the anchored reduction of §3.3 (HAND)**; the checker does not re-prove TWIN §13 and uses three hand-proved facts (interchangeable points of equal type; points outside $D_j$ and fresh points are irrelevant; maximal replies suffice). Two tampered certificates are rejected. Combined with the lower bounds: $f(6,7)=5$, $f(7,7)=6$ (and $f(8,7)\le7$ is already known from FKW). All three have $T=k-1$ and say nothing about a ratio near $3/4$.

*Soundness controls.* For $k\equiv1\pmod 4$ the complete family on $\lceil7k/4\rceil$ points is still $(7,2)$ ($f(5,7)=5$, $f(9,7)=8$, $f(13,7)\ge11$), and with the FKW parity examples there are genuine $(7,2)$ families with $\tau=\lceil3k/4\rceil+1$ at $(k,T)=(4,3),(5,4),(8,6),(9,7),(12,9),(13,10),(16,12)$. At those $(k,T)$ every claimed requester win would be a bug; they are used as controls (one caught a bug). [EXACT, same status as the table above.] The first informative open cases are $(k,T)=(10,8),(11,9),(12,10),\dots$; `FAST.md` records bounded-request adversary wins at $(9,7)$ and $(10,8)$ (integrality artefacts or "plain bounded-request game dead at small $k$"), not claimed here.

---

## 6. The seven-request explanation of the known bounds

**Statement of what is and is not proved (PROOFS §6).** Let $G_m(T,k)$ be the game of §2 with $m$ requests. All items below concern restricted adversary classes; **no number is a threshold against the unrestricted adversary.**

*Proved (hand; core in Lean).*

1. **Waste adversary (Theorem 8; Lean `waste_core`, `waste_adversary` [LEAN])**: $A_1\supseteq X$, $|X|=T$, $Y$ a $k$-set disjoint from $X$, all later replies $\subseteq X\cup Y$ and $5T<4k$. Then for every request $S$ there is a point $x\notin S$ and a partner $y$ such that $\{x,y\}$ meets $A_1$, $Y$ and all four further replies. Counting core: $n$ rectangles of semi-perimeter $\le T$ in a $T\times k$ grid with $(n+1)T<4k$ leave uncovered pairs whose projections have more than $T$ points in total. Hence against this class seven requests do not suffice for $T<4k/5$ ($t^*_W(7)\ge4/5$). (PROOFS §0, E4/E5 record the corrections made to the original proof and wording.)
2. For every $m$ and $T<3k/4$ the complete family on $k+T$ points is a $(7,2)$-family with $\tau=T+1$, so $t^*(m)\ge3/4$ for all $m$. [elementary; HAND]
3. More requests never hurt the requester. [trivial]

*Computed only (exact MILP in a scale-free model, float tolerance $10^{-4}$, requester free, adversary forced inside its class; not rational-certified, not re-run in the verification pass) [FLOAT]:*

| adversary class (7 requests) | threshold | note |
|---|---|---|
| waste $W$ | $5/6$ (optimum $\operatorname{mass}(D)=5/3-T$) | hand proof gives only $4/5$ |
| balanced waste $W'$ | $0.846\ldots$, matching $11/13$ to four digits | identification with $11/13$ is numerical |
| complete family on $(1+T)k$ points, first two replies meeting in $k-T$ points, then forced | $7/8$ (sign change between $0.874$ and $0.876$) | no hand proof |

**Reading.** The notes observe that $5/6$, $11/13$ and $7/8$ are numbers that appear as upper bounds in the literature (FKW's $\lceil7k/8\rceil$; the $11k/13$ claim of §1; $5/6$ as a one-anchor bound, FRESH_C §9.1, which the notes themselves say is not the optimal requester pattern there). This is an **observation about three computed numbers**, not a theorem: nothing proved links class $W$, $W'$ or $K$ to a published argument. The remark "any proof below $7/8$ must use more than seven requests" holds only if the (uncertified, float) value $7/8$ for the complete-family class is right; the rigorous version has $4/5$ (Theorem 8) in place of $7/8$. With one discard and $m=8$ all classes tested drop to $3/4$, but those classes are forced or scripted adversaries, so the notes themselves label that evidence "optimistic" (FRESH_C §12.1): only $t^*(m)\ge3/4$ for all $m$ and the three seven-request lower bounds are solid.

---

## 7. Classification theorems ruling out structured counterexamples

The role of this section: each theorem says that a (7,2)-family (equivalently an adversary strategy) of a given structural type loses, so that a counterexample to $f(k,7)\le(\frac34+o(1))k$ must lie outside the type. **None of them proves the conjecture.** All are [HAND] with "verification pending" unless stated.

### 7.1 Concentrated window (core): Theorems S, S+, anti-plan, W

Setting: (CP) of §4; co-edge family $\mathcal C$ on $V$, $|V|=N$, $\frac32\le N\le\frac94$ at first order; a **good seven** is seven members covering all pairs.

**Theorem S (finite-partition profile families lose) [HAND; verification pending (V1)].** Let $V=V_1\sqcup\dots\sqcup V_m$ ($m$ fixed) and $\mathcal C$ a $T$-covering co-edge family invariant under every mass-preserving bijection fixing each $V_j$ (membership depends only on the profile $(|K\cap V_j|)_j$). Then for $t\ge\frac34$ and $\frac32\le N\le\frac94$ (first order) $\mathcal C$ contains a good seven.
*Proof.* $v/3$ has mass $N/3\le t$, so some profile $s$ with $v/3\le s\le v$, $|s|=t$ exists; by $T$-covering a member $K$ has profile $\pi\ge s\ge v/3$. Put $\kappa_j=(3\pi_j-v_j)/2\ge0$ and split each $V_j$ into a part of mass $\kappa_j$ and three parts of mass $(v_j-\pi_j)/2$. Let $\kappa$ be the union of the first parts and $P_1,P_2,P_3$ the unions of the others: $|\kappa|=N-\frac32$, $|P_i|=\frac12$, and $\kappa\cup P_i$ has profile $\pi$, so all three are members. They form a pencil with kernel $\kappa$, finished by CORE 35.1: halve each petal; the four transversal lines have mass $\frac34\le t$ and the Fano criterion applies. ∎
Computed check [EXACT]: brute force over every choice of the four later replies, partitions $(5,3),(5,3),(4,4),(3,3,2)$ at $(k,T,N)=(4,3,8)$: 0 failures. At finite $k$ the proof needs $3\pi_j-v_j$ even.

**Density form (CORE 39.2) [HAND; (V3)].** If $\mathcal C$ is $T$-covering and contains more than $2/3$ of one profile class $[\pi]$ with $\pi\ge v/3$ (for a partition as in 39.4), it has a good seven. (The pencil triples inside $[\pi]$ form a vertex-transitive 3-uniform hypergraph; a subfamily without a whole triple has at most $2/3$.) The constant $2/3$ is sharp for the argument.

**Theorem S+ (finite $k$, many cells) [HAND; verification pending (V1)].** Let $|V|=n$, $V=V_1\sqcup\dots\sqcup V_m$ with arbitrary sizes $v_j\ge1$, $\mathcal C$ a $T$-covering family of $(n-k)$-sets invariant under $\prod\mathrm{Sym}(V_j)$. If $n/3+m\le T$ and $m\le 4\varepsilon k-12$ (the sharpened bound of CORE §45; §39 had $\frac43\varepsilon k-4$), then $\mathcal C$ has seven members covering all pairs. *Proof idea:* the profile construction of Theorem S, with rotating shared points for odd cells; each odd cell wastes one incidence, and a three-member certificate has exactly $4\varepsilon k$ spare incidences. The bound is optimal for the pencil certificate. Construction checked exact on four instances (and one deliberate failure by rounding) [EXACT].
*Consequences.* A counterexample cannot be: a profile family of a bounded (or $o(k)$-cell) partition; a "junta" of $\le\frac43\varepsilon k$ named points on top of a bounded partition; or any family that becomes stationary with exchangeable cells after some position (*stabilisation lemma*, CORE 45.3: from a position with $q$ kept co-edges, if the reply set is orbit-closed on the $2^q$ Venn cells, $2^q\le4\varepsilon k-12$, $n/3+2^q\le T$, she wins). Note two *negative* statements proved in the same sections: (i) the regularity route "approximate by a profile family, then apply S" is [DEAD] (CORE 39.1: $T$-covering is monotone up under symmetrisation, "no good seven" is monotone down, and by Theorem S the upper closure always has a good seven); (ii) a bound of the form $c(N)\cdot k$ cells with $c$ independent of $\varepsilon$ cannot follow from slack, since the pool family is symmetric and has slack exactly $4\varepsilon k$ in every good seven (CORE 45.2c) [DEAD].

**Ordered frozen anti-plan family has a good seven [HAND + EXACT (12 instances); verification pending (V2)].** Cells $O$ (mass $o$), $U=A\cup B$, $g$, each with a fixed order; $O_1$, $U_1$ the first $\omega$ points of $O$, $U$. Rule: if $|S\cap O|<\omega$ the dump is the first $\omega$ unrequested points of $O$, otherwise the first $\omega$ unrequested points of $U$. For every parameter in the window the family contains a good seven, by Theorem P applied to **one** of its two pools: an *L-pencil* when $\omega\le t-\frac12$ (kernel of mass $N-\frac32$ contains $U_1$ and $\omega$ points of $O$), an *H-pencil* when $o<4\omega$; one always applies. The other four lines' shapes are irrelevant. Exact finite check: 12 instances, e.g. $(k,T,n,o)=(40,31,74,12),(100,76,190,40),(200,151,390,80)$, with the rule applied verbatim to real sets and all pairs checked [EXACT]. An LP scan (float) over 104 parameter points finds at least 8 of 128 shape assignments feasible at each [FLOAT].

**Theorem W (window-selected greedy rules lose) [HAND + EXACT (1200 random instances); verification pending (V2)].** A *greedy rule*: a selector $\sigma$: requests $\to$ classes and a linear order $\prec_r$ on $V$ for each class; reply $=S\cup$ (first $n-k-T$ points of $V\setminus S$ in $\prec_r$), $r=\sigma(S)$. *Frame criterion:* suppose a class $r$, a set $Z$ of $n-k-T$ points and a partition $V=\kappa\sqcup P_1\sqcup P_2\sqcup P_3$ with $|\kappa|=n-\frac32k$, $|P_i|=\frac k2$, $Z\subseteq\kappa$, such that for $S_i=(\kappa\cup P_i)\setminus Z$: (i) $\sigma(S_i)=r$ and (ii) $Z$ precedes every point of $P_j\cup P_l$ in $\prec_r$. Then the replies to $S_1,S_2,S_3$ are the three pencil lines and four requests of $3k/4$ points finish. *Window theorem:* if $\sigma(S)$ depends only on $S\cap W$ with $|W|\le T-k/2$, the criterion holds: take $r=\sigma$ of any request containing $W$, $Z$ the first $n-k-T$ points of $V\setminus W$ in $\prec_r$, $\kappa\supseteq W\cup Z$ (room: $|W|+|Z|\le n-\frac32k$). Hence an adversary whose class depends on a window of $\le T-k/2$ points loses in seven requests, for any number of classes and orders. Corollaries: juntas reading $B\le T-k/2$ points; thresholds and (first-order) profile selectors by the same frame criterion (CORE 47.3–47.4; finite-$k$ rounding for profile selectors not done). Computed exact check: 1200/1200 random adversaries (arbitrary tables $\{0,1\}^B\to R$ classes, random orders) and the twelve instances above [EXACT].
*What escapes (CORE 47.5; proved as necessity for greedy rules):* the selector must depend essentially on more than $T-k/2$ points, not be a threshold or a profile on a coarse partition, and must separate petals around every class head: hash-like on linearly many points; or the rule must be non-greedy (in-cell choice depends on the request, or cells cut by earlier replies).

**One-bit rule has a good seven [EXACT (89 instances)] (CORE §44).** A rule with two pools per cell selected by one bit read off the profile of the request on a cell disjoint from the pool: a good seven exists in all 89 exact instances ($(k,T)=(40,31),(100,76),(200,151)$, $n/k\in[1.81,2.14]$). Reason (sketch, by hand): she gives the three pencil lines the same bit value. Not a proof for general bounded-bit rules (that is Theorem W's role).

**Literal SPOIL false [EXACT] (CORE §40); SPOIL at all depths is not a disproof [HAND] (CORE §43).** The conjecture SPOIL (CORE §27: at every position and request the adversary has a dump keeping her requirement at least the baseline) is false as literally stated: an exact rational position at three kept replies, $(t,N)=(19/25,19/10)$, with a request after which every dump admits a reading with need $\le199/2000<$ base $=1/10$ (certificate by box subdivision of the dump polytope with Fraction arithmetic, `spoil_exact.py`). The corrected strategy-form statement SPOIL* ("he has a strategy keeping the need $\ge$ base at every depth") is **undecided**: it holds to depth 2 and on sampled lines to depth 3–4 [FLOAT]; at five kept replies one sampled two-request break against the one-step rule exists (CORE §41) [FLOAT, not exact]. SPOIL* at all depths would give only "no bounded-depth first-order proof of CP"; a disproof needs one explicit family (CORE §43).

*Why these theorems do not close (Σ):* the surviving counterexample shapes need linear partition complexity ($>4\varepsilon k-12$ cells by S+; at least a third of every qualifying profile class missed by 39.2), which a SPOIL-type rule has (it creates $2^d$ cells at depth $d$), and are non-greedy or hash-like (W).

### 7.2 Petal (spread) side: J, K, L; J′, J″; DS, DS-b; FF, AP; N

Setting (PETAL; units $k=1$, $t=T/k$). *Two-class setting* $\mathcal C(c,\mu)$: at all times replies fall into at most two classes; same-class overlaps $>c$, cross overlaps $\le\mu<c$; necessarily $c<1-t/2$. Write $\theta(t)=(6t-2)/5$ ($=\frac12$ at $t=\frac34$).

**Theorems J, K, L [HAND] (ledger: PETAL §3, §7, §8).**
* *Theorem J (§3).* Fix $t\ge\frac34$ and numbers $c,\lambda$ with $\lambda\le2c-1$, $3\lambda\le t-\frac13$, $1-c+7\lambda\le t$, $2\lambda\le1-c$, $t-\lambda\ge\frac23$ (e.g. $c=4t/5$, $\lambda=(9t/5-1)/7$). There is a requester strategy of $\le14$ requests such that either seven replies have no 2-cover or two replies have an overlap in the band $[\lambda,c]$. (Running intersections give four same-class petals; three centres forced far from one petal have pairwise disjoint traces by P4(c).) Beats leaky two-arena adversaries with leak $\le t/30$ (direct count: $t/26$). Simulation of 400 games [not a proof].
* *Theorem K (§7).* For four petals with no point in three of them, grids $A_r\times A'_r$ of masses $a_r,b_r$: she wins with three more requests if cross-intersecting kill designs exist with every round load $\le t$; if $\sigma=|U^*|\le1+t$ this is also necessary ($L(a,b)\le t$).
* *Theorem L (§8, matching design).* If $t\ge\frac34$, every $p_{ab}\le t-\frac12$ and $p_{ab}+p_{ac}-p_{bc}\le3t-2$ for all labellings of a spread triple, she wins in four more requests. The computed region (grid-restricted on both sides, "indicative only") shows she loses with a dominant pair $\max p_{ab}\ge\frac7{16}$ via this architecture alone.
* *Interface (PETAL 9).* Good spread triples are stateless wins; committed play cannot be escaped; the exact hole is a spread triple with dominant pair in a play that also has banded pairs (9.4).

**Theorem J′ [HAND; verification pending (V4)].** In $\mathcal C(c,\mu)$ she wins in 10 requests provided, on the line played, $1-c+\min_a|(Z_1\cup Z_2)\setminus X_a|\le t$; in the worst case $|Z_i\setminus X_a|\le3\mu$, so **$1-c+6\mu\le t$ suffices**; with negligible singles $1-c+3\mu\le t$. Proof outline: Step 1 (running intersections with request size $t/2$) gives four same-class petals $X_1..X_4$ with empty common intersection; Step 2 requests $F_j\cup(Z_{<j}\setminus X_a)$ with $F_j\subset X_a$ of mass $1-c$ forcing the reply into the other class.

**Theorem J″ [HAND; verification pending (V4)].** With the forcing petal *rotating* ($a_1,a_2,a_3$ distinct) and $F_j$ containing the whole single part of the forcing petal: **$1-c+4\mu\le t$ suffices** (10 requests). Exact replay on the extremal configuration $\mathcal Q(c)$ (point sets, $k=400$) [EXACT, one scripted adversary].

**Theorem DS (double sealing) and DS-b [HAND + EXACT replay; verification pending (V5)].** For the arena adversary $\mathcal A(t,\delta)$ (disjoint arenas of mass $1+t/2-\delta$; a reply of colour $c$ has $\ge1-\delta$ in its arena): *arena-aware* requests win in 7 requests for all $\delta<t/6$, so $\mathcal A$ is a requester win wherever $c>\theta(t)$. **DS-b (arena-blind, common-region classes CR$(n,\delta)$):** she wins in 10 requests if $n-1+7\delta\le t$ ($\delta\le t/12$ for tight arenas). Exact replay of the aware version (20/20 seeds at $(k,T,\delta)=(40,30,0.100),(480,360,0.100\ldots0.125)$ against one adversary [EXACT]).

**Lemma FF and Theorem AP [HAND + EXACT replay; verification pending (V5)].** *Lemma FF:* for a family $\mathcal F$ of sets of mass 1 with all pairwise overlaps $>c$ and $\pi(X)$ the private mass of $X$: $\tau(\mathcal F)\le1-c-\pi(X)+\varepsilon$ (request $1-c-\pi(X)+\varepsilon$ points of $X$ outside its private part). The single-mass form is **false** (complete family on mass $2-c$). *Theorem AP:* a fixed family made of two arena-with-pool classes (all sets with $\ge1-\rho_c$ in a region $R_c$), with same-class overlaps $c_X,c_Y>\theta(t)$ and $\tau(H)>t$, $t\ge112/151$, has seven edges with no 2-cover obtained in $\le10$ requests (cost $\le\max(\tau_X,2\rho_Y)+\frac83\rho_X+\varepsilon$). Replay at $k=400$, $T=300$, seven parameter rows, 20 seeds each, 20/20 [EXACT].

**Theorem N (an adversary beating the 2+2 architecture) [HAND].** Against $\mathcal A(t,\delta)$ every triple-free quadruple, at any time, has a grid $(a,b)$ with $a\ge a_0=1-t/2-\delta$, $b\ge\beta(t,\delta)$; if $L^*(a_0,\beta)>t$ (true for $\delta\le0.0510$ at $t=\frac34$, [EXACT] rational bisection) no 2+2 quadruple certificate ever exists. This says the 2+2 petal certificate is the wrong tool; the same adversary loses to the 4+3 certificates above.

**[DEAD] as obstructions:** $\mathcal A(t,\delta)$ (beaten for $\delta<t/6$ aware, $t/12$ blind) and $\mathcal K_2(c)$ ($c\ge0.5217$, killed by a mixed sealing plan; exact replay).

---

## 8. Precise statement of the remaining open problem

### 8.1 The core window: (Σ)

**Reduction CP $\Leftarrow$ (Σ) [HAND; verification pending (V3)] (CORE §37–38).** (CP) in the window follows from:

> **(Σ)** every $T$-covering co-edge family $\mathcal C$ contains (a) four members with $\sigma\le(3t-N)/2$ and balanced matchings (Q′), or (b) three members forming a pencil with kernel of mass in $[N-2t,\,N-\frac32]$, or (c) three members satisfying Theorem T,

for $N$ in the window $3t-\frac12<N<3-t$, with $t=\frac34+\varepsilon$, $\varepsilon>0$ fixed and $k\to\infty$. Here $\sigma$ is the mass of points in at most one of four members. The implication is one-way: a good seven may need five or more members used in full, so (Σ) is not known equivalent to (CP).

**Known cases of (Σ):** symmetric families (Theorem S, via (b)) and partition complexity $\le4\varepsilon k-12$ (S+); families with density $>2/3$ on a qualifying class (39.2); pool-rule adversaries (Theorem P); ordered frozen anti-plan (§46); greedy rules with a window of $\le T-k/2$ points (Theorem W); the one-bit rule (89 exact instances). **Open for:** (i) greedy rules with *hash-like* selectors on more than $(\frac14+\varepsilon)k$ points; (ii) non-greedy rules (in-cell choice depending on the request, or cells cut by earlier replies); (iii) self-cut families, i.e. general families of linear partition complexity; (iv) symmetric families with cells of bounded size $b$, $1\ll b\ll1/\varepsilon$ (a finite profile game). In the notes' words: "(Σ) for hash-like, non-greedy and self-cut families".

**Related undecided items:** strategy-form SPOIL* (§7.1) and the "five-reply candidate break" (CORE §41) [FLOAT, sampled both sides, not exact]. A *positive* answer to SPOIL* would not give a counterexample (CORE §43); a *negative* answer would give a requester gain to extract.

### 8.2 The petal side: Barrier F

**Remaining gap [open] (PETAL 23.4).** A *fixed* family whose edges fall into two classes with same-class overlaps $>c>\theta(t)$, cross overlaps $\le\mu$, $\tau>t$, and whose classes are **not** of the arena-with-pool form "at least $1-\rho$ in a region". Constraints already forced: $\tau_X,\tau_Y\le1-c-(\text{private mass})$ (Lemma FF), and it must defeat the plan game ($1-c+s\rho>t$ with rotation forcing, where $s(x)=\min(4x,\tfrac12+\tfrac32x,1+\tfrac23x)$ fits the exact LP values at twelve points, formula not proved). In the abstract class, the unclosed region is $\theta(t)<c<1-t/2$ and $4\mu>t-1+c$ (at $t=\frac34$: $\frac12<c<\frac58$). The ledger phrase: "fixed two-class families not of arena-with-pool form (petal)". Candidate structure lemma suggested by the notes (not proved): some set $R$ contains all but $\beta<1-\theta-\tau$ of every member.

### 8.3 What the full proof would need

Both sides are needed (and the interface 9.4 of PETAL: dominant-pair spread triples with banded pairs). So even granting every [HAND] statement above, the conjecture $f(k,7)\le(\frac34+o(1))k$ is **not** proved, because (CP) in the window and Barrier F remain open. The matching lower bound $f(k,7)\ge\frac34k+1$ ($4\mid k$, $k\ge4$) is FKW's.

---

## 9. What is computational and how it was checked

*Policy.* Computer results are not proofs unless certified (LEAN_POLICY #7). In particular, "solver infeasible" outputs are evidence. We classify:

| Computation | Where | Nature | Check |
|---|---|---|---|
| Lean build of the lemma files of §3 | `Lean644/*.lean` | proof | CI policy: frozen `Statements.lean` hash, no `sorry/axiom/native_decide`, `#print axioms`; we grepped for escape hatches only |
| Flat/tuple, Theorem 8 numerics, tight-triple sizes (865,364 triples) | `compute/fresh_c`, `compute/...` | brute force | agrees with hand proofs |
| Random-instance checks of Theorems T, Q, P, anchor lemma (2000 tuples), petal lemmas P1–P4 (2063 systems) | `check_core.py`, `anchors.py`, `petal_checks.py` | exact brute force on small grounds | sanity checks of hand statements |
| Exact small-$k$ game solutions (k=4..9), certified requester wins at (6,5),(7,6),(8,7) | `exact7*.{py,js}`, `anchor_select.js` + `cert_check.py` | exact search; independent replay checker; certificates, tampering tested | conditional on TWIN §13 (HAND) |
| ILP for largest $N$ with $(7,2)$ complete family | `complete_int.py` | one solver, not independently re-checked | to be compared with La Jolla [to check] |
| Seven-request class thresholds 5/6, 11/13, 7/8 | FRESH_C §10 | float MILP, tolerance $10^{-4}$ | not certified |
| Theorem S, S+, §46, W, §44 finite instances | `sym_check.py`, `sym_plus*_check.py`, `frozen_antiplan2.py`, `window_thm.py`, `onebit.py` | exact: rule applied verbatim to real sets, all pairs brute-forced; MILP only proposes classes | the verdict is the brute-force pair check |
| Literal SPOIL false | `spoil_exact.py` | rational (Fractions), box subdivision, convexity | exact; pre-existing triple readings float |
| SPOIL* depth 2–4, five-reply break, SPOIL LP | `spoil*.py` | float LP/MILP, sampled | evidence only |
| Petal replays (J″ on $\mathcal Q(c)$, DS, AP) and $L^*$ tables | `replay_q.py`, `replay43.py`, `lstar.py`, `plan_lp.py` | exact replays against *one* scripted adversary; LP up to tolerance | do not cover all adversaries in the class; the claim for all is the hand proof |
| Sunflower-Ramsey SAT ($\mathcal H(4,3)$, $\mathcal H(8,6)$ not 2-colourable) | `sunflower_ramsey.py` | SAT UNSAT | **interim, CORE §48, not in ledger; not claimed** |

A recurring caveat: replays test one adversary; hand proofs claim all adversaries in a class. Finite-$k$ instances cannot exhibit first-order margins smaller than the $O(1)$ terms ("slivers cost one point per pair"; FAST Parts 3–4).

---

## Appendix: ledger status table (verbatim classification used)

| Claim | Status |
|---|---|
| Lean-formalised lemmas (6/7 manuscript Lemmas 4.1–4.8, tight triple, Theorem A, stability 11.1, lopsided top 6.4, sparse triple, trace lemma, pair gap, three centres, Fano criterion, flat 7-tuple, Fano blocks, waste adversary, anchor/petal reductions) | LEAN |
| Anchored reduction (TWIN §13), padding transfer | HAND |
| Theorems J, K, L; Concentrated case $N\le3T-k/2$ (TWIN 16.A) | HAND |
| Theorems T, Q, pool theorem P, slack count | HAND (computed exact on instances) |
| Theorem S; density form; S+; Q′ and CP$\le$(Σ) | HAND, verification pending (V1, V3) |
| Ordered frozen anti-plan; Theorem W | HAND + EXACT, verification pending (V2) |
| Literal SPOIL false; one-bit rule | EXACT |
| SPOIL at all depths is not a disproof | HAND |
| J′, J″; DS, DS-b; FF, AP | HAND (+ EXACT replay), verification pending (V4, V5) |
| Theorem N | HAND |
| Kernel lemma, regularity reduction, $c(N)k$ cell bound, bounded-request game, $\mathcal A(t,\delta)$, $\mathcal K_2$ as obstructions | DEAD |
| Open | (Σ) for hash-like, non-greedy, self-cut families; fixed two-class families not of arena-with-pool form; strategy-form SPOIL, five-reply break |
