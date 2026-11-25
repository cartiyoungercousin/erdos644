# Programme 5: random Fano colourings and the coarse-threshold dichotomy (CTS)

Tags: [proved by hand], [computed], [heuristic], [open]. Nothing here is independently verified. Nothing committed.
Code: `compute/programme5/seven/` (§7). Setting: H k-uniform on n = (7/4+δ)k points, (k+r)-covering, T = n−k−r =
(3/4+ε)k, n < 11k/6. φ(m) = 1 − μ(m) = P(a uniform m-set contains a member); D = member-free down-set, U = up-set.

## 0. Verdict
- **The opening is correct, but its second branch is not a coarse threshold.** A counterexample needs only
  φ(4n/7) ≤ 6/7. That is a statement about *where* the threshold of U sits (between 4n/7 and k+r), not about how
  wide it is. Generic thin families have a sharp threshold, at most 5 levels wide, just below k+r.
- **Task 1.** On its own the random colouring gives **slope 3/7**, unconditionally and sharply. This is weaker than 3/11
  and equals Theorem 3H with uniform weights and the q = 0 slack budget of CORE Theorem 102.1 [proved by hand, §1].
- **CTS is false as stated** [proved by hand, §2]. Binomial random covering families are covering and thin, have no
  block and no covering coset layer, and D has density 1 − 2^{−Ω(k)} at every level ≤ k+r−O(log k).
- **Adding a light-pencil branch does not rescue CTS.** The INV-P random coset unions refute that version too [heuristic].
- **Adding seven-freeness makes CTS circular** [proved by hand, §2.4]. "D thick" is then automatic, and CTS
  becomes INV-P^L for seven-free families, i.e. (S<) itself modulo Piece B.
- **Slope 0 via this route? No**, not without a new 7-term inverse theorem at density e^{−Θ(k)}: marginal-only
  bounds stop at 3/7; the rest is the joint 7-wise law of (R_u), the recorded crux (INV-P §4, CORE §85–89).
- **By-products.** Janson closes "dense and spread" families (§1.3); the quick-check threshold families exist (the
  check is wrong as stated) but are NC blocks (§3); the 7-term index κ is ≈ 0 (random/minimal), −∞ (FKW), > 0 (§5).

## 1. Task 1: the opening, optimised
**1.1 Opening** [proved by hand]. Take χ: V → F₂³ with any class law and R_u = {p : ⟨χ(p),u⟩ = 1}.
- Fano type gives B_u ⊆ R_u for all u ≠ 0 ⇒ a good seven. So if Σ_u P(R_u ∉ U) < 1, H has a good seven, for every n.
- Seven balanced classes: each R_u is a uniform ⌊4n/7⌋- or ⌈4n/7⌉-set, so 7μ(4n/7) < 1 suffices.
- 4n/7 < k+r ⇔ ε < 3δ/7. (k+r = k+(δ−ε)k and 4n/7 = k+4δk/7.)

**1.2 What it gives alone: slope 3/7, and this is sharp** [proved by hand].
- Each point lies in exactly 4 of the 7 R_u, or in none (zero class), so Σ_u|R_u| ≤ 4n. Some R_u has size ≤ 4n/7
  (for iid laws, Σ p_u = 4(1−q₀) ≤ 4 forces some p_u ≤ 4/7).
- The only unconditional information about φ below k+r is φ ≥ |H|C(m,k)/C(n,k) ≥ C(m,k)/C(k+r,r), which is
  exponentially small. So the union bound certifies a seven unconditionally iff ⌊4n/7⌋ ≥ k+r, i.e.
  **e ≤ (3/7)s + O(1)**.
- Sharp: the families of §2.1 have φ(m) ≤ 2pC(m,k) = 2^{−Ω(k)} for m ≤ k+r−O(log k), so every exchangeable law
  (invariant under permutations of V; any class sizes, zero class, bias) has a line with P(R_u ∈ U) = 2^{−Ω(k)},
  and its union bound fails for ε < 3δ/7 − O(log k/k). This is Theorem 3H with y ≡ 1/τ, and the q = 0 budget
  S_0 = 7ε − 3δ of CORE Theorem 102.1. **Weaker than 3/11 and 1/5.**

**1.3 Janson and second moment** [proved by hand].
- For iid χ, R_u is p_u-random. Janson gives μ_u ≤ exp(−E_u + Δ_u/2), with E_u = |H|p_u^k and
  Δ_u = Σ_{B≠B′, B∩B′≠∅} p_u^{|B∪B′|}; if Δ_u ≥ E_u, use exp(−E_u²/2Δ_u).
- So **H has a good seven if Σ_u exp(−E_u + Δ_u/2) < 1**: the *dense-and-spread* branch.
- Cost: E_u ≥ ln 7 at p = 4/7 needs density 2^{jans} times the covering minimum, with jans = log₂(C(k+r,r)/C(4n/7,k)).
  That is 22–283 bits at k = 2000, and 900–14000 bits at k = 10⁵ (`logs/profile.log`).
- Stars (CORE Theorem 96.1's family G) are dense, but Δ ≫ E there. Since G is seven-free, it must, and does, have
  μ(4n/7) ≥ 3/7.
- **Marginal-only bounds stop at the union bound**: given marginals a_u, some joint law has P(∩A_u) =
  max(0, Σa_u − 6). Janson improves marginals only. FKG/second-moment lower bounds need positive dependence, but the
  sets are linearly tied (R_u + R_v = R_{u+v}) and FKW has marginals ≥ 1/2 with P(∩) = 0 (§5). 7-wise data is needed.

## 2. Task 2: CTS is false; the exact obstruction
**2.1 Proposition R** [proved by hand; Chernoff and union bounds].
- Fix 0 < ε < δ/3 with δ < 1/12, k → ∞. Let H_p contain each k-set independently with p = 2 ln C(n,k+r)/C(k+r,r).
  - (a) **Covering**: P(a given (k+r)-set is uncovered) ≤ e^{−2ln C(n,k+r)}; take a union bound. So τ ≥ T+1.
  - (b) **D thick**: whp |H_p ∩ C(W,k)| ≤ 2pC(|W|,k) for all |W| ≥ 3k/2 (Chernoff, means ≥ 3n; union over 2^n W).
    So φ(k+r−x) ≤ 4n·ln2·(r/(k+r))^x: **D has density 1 − 2^{−Ω(k)} at 4n/7 and at every level ≤ k+r−O(log k)**
    (computed: threshold width ≤ 5 levels, `jump` column).
  - (c) **Thin**: for any law π on transversals, τ*_b ≥ 1/max_x π(x ∈ M). Take π uniform on the complements of the
    member-free m*-sets (m* = k+r−O(log k)); by (b) they are a 1−o(1) fraction. Then P(x ∈ M) ≤ (1+o(1))(n−m*)/n, so
    **τ*_b ≥ (1−o(1))N/t > 7/3 ⇔ 3δ > 7ε** (computed 2.331–2.439; ≤ 7/3 only at k = 2000, δ = .01, ε/δ ≥ .25).
  - (d) **No block**: a (W,d)-complete W needs |H ∩ C(W,k)| ≥ C(w,k)/C(k+d,d). By (b) this forces
    C(k+r,r)/C(k+d,d) ≤ 4n, and since that ratio is ≥ 2^{r−d}, d ≥ r − log₂4n. Then
    |W| ≥ (7/4−ε)k + 2d + 3 > n once (δ−3ε)k > 2log₂4n + 3.
    (For ε ≥ δ/3 + O(1/k), NC with W = V closes every family anyway.)
  - (e) **No covering coset layer**: a covering layer has ≥ C(n,k)/C(k+r,r) = 2^{Ω(k)} members (`layer` column:
    ≥ 2800 bits at k = 2000), and there are ≤ 2^{n²+n} pairs (C,a), each with P(L ⊆ H_p) ≤ 2^{−|L|}.
- So H_p meets the CTS hypothesis (c = 1 − o(1), every β ∈ (0, δ−ε)) with none of the structures: **CTS is false.**
  H_p is not a (G)-counterexample [heuristic]: perfect pencils have first moment e^{(0.27…2.13)k} (CORE §57.1), then
  Lemma P1; the request-game analogue is CORE Theorem R.

**2.2 With a light-pencil branch** [heuristic, from INV-P §3]. The INV-P random coset unions have the same p.
- So φ(4n/7) ≤ 2^{phi4}, with phi4 the per-line hit exponent of INV-P's `7exp`, and D is equally thick.
- They are thin, block-free and coset-free, and every triple sum has weight ≥ λr. So
  "rich ∨ block ∨ layer ∨ light pencil" fails for λ < λ* ≈ 0.85, which is exactly the INV-P barrier.

**2.3 Which structures genuinely have coarse thresholds?** Call U *coarse on [m₁,m₂]* if c ≤ φ ≤ 1−c there, with
m₂ − m₁ = βn.
- Thin near-minimal families have **late sharp** thresholds: random families [proved, §2.1b], coset layers of codim
  Θ(k), and random coset unions. Here φ ≈ C(m,k)/2^{codim} [heuristic], jumping within O(log k) levels below k+r.
- Coset layers with few classes have **early sharp** thresholds at level k: FKW has φ(k) = 1/2 and φ(k+1) = 1
  [computed]. They defeat the union bound by a constant (Σμ = 1.5), and the 3-term relation R_u+R_v+R_{u+v} = 0 does
  the rest (§5).
- Two-block families {|B∩A| ≥ t} are sharp on the √n scale [proved by hand: hypergeometric].
- Genuinely coarse U: Russo–Margulis on the slice gives a level of total influence O(1/β), and a Friedgut-type junta
  theorem for slices ([cite?: Wimmer 2014]) makes U close in measure to an O_β(1)-junta [heuristic]. Example: all
  members through x₀ (rich; RA).
  Densities are Θ(1) here, so FAILED_ROUTES #5's objection does *not* apply, but the sub-branch is irrelevant: a
  counterexample need not be coarse anywhere.
- So **coset layers are not the canonical coarse example. Nothing in the 644 window is forced to be coarse.**

**2.4 With seven-freeness assumed** [proved by hand]. Seven-free ⇒ φ(4n/7) ≤ 6/7, by §1.1. So "seven-free + D thick
⇒ rich/block/layer" is equivalent to "seven-free, thin, block-free ⇒ contains a covering layer". That is INV-P^L
restricted to seven-free families (PROGRAMME4_INVP §1.3), which, with Piece B, is (S<). **The dichotomy is circular.**

## 3. The quick check (threshold-in-a-set families)
[proved by hand] D = {S : |S∩A| < t} covered at k+r needs t ≤ |A| − T; density ≥ 1/2 at 4n/7 needs |A| ≳ 7T/3.
"7τ/3 > n" holds only for ε > 3δ/7, so **in the open regime such families exist**. They are closed: every k-subset of
A is a member, so A is (A,0)-complete with |A| ≥ 7T/3 ≥ (7/4−ε)k + 3 and Corollary NC applies. Measured κ > 0 (§5).

## 4. Task 3: adapted colourings
- **P1-adapted with random splits** (Z → c₀, D_ij → Q_m, E_i → Q_{i+1}, each split uniformly at random)
  [proved by hand + computed]. The four completing lines R_g = Z ∪ (half of U) have size n − (3k+w)/4 ± O(√k).
  - For thick-D families (§2.1b), a line below k+r−O(log k) succeeds with probability 2^{−Ω(k)}. So randomness gains
    O(log k) in w over deterministic P1.
  - H_Z (PROGRAMME4_P1 §3) kills it outright. **c = 4 is unchanged.**
  - At k ≤ 12 random splits succeed (joint 0.25–0.60 at w = 0) while 4T−3k−6 < 0: finite size (sizes straddle k+r).
- **Anchored on a random member**: no help (κ_iid −1.3 to −3.3 or −∞, `logs/mc_*.log`); it biases the other lines.
- **Code-adapted** χ = φ∘σ (σ syndrome map, φ random linear) [proved by hand]: R_u is a dual codeword, which sees
  only parity; for random codes its weight is ≈ n/2 < k. It serves few-class layers (9′/B1), not coset unions;
  INV-P's 2^{9000} expected sevens come from *generic* balanced colourings.
- **No adapted law yields a hypothesis complementary to "D thick"**, because D thick is the generic case. The
  complementary hypotheses that do give sevens are exactly the known closed regions: light pencil (P1), dense and
  spread (§1.3), rich (RA), block (NC), few-class layer (9′/B1) [proved by hand, as compositions].
- [open] INV-P coset unions escape all of them. A second moment over (G, Γ, χ) as in Theorem R (j = 1 shared-member
  term ≈ 49(4/7)^k/(p·C(4n/7,k)) = 2^{−Ω(k)} [heuristic]) would only show the test-bed is not a counterexample.

## 5. Task 4: numerics [computed; Monte Carlo 2·10⁵–4·10⁵ colourings; all instances out of window, k ≤ 20]
κ := log₁₀(cert / Π_u marg) under **balanced** colourings (fixed sizes), the 7-term correlation index.

| family (n,k) | φ at k, k+1, … | Σμ (balanced) | marg min | cert | κ |
|---|---|---|---|---|---|
| TASKB random minimal (21,10), r = 3 | .012 .12 .57 1 | 3.00 | .571 | .020 | 0.00 |
| TASKB planted-FKW minimal (21,10) | .012 .12 .57 1 | 3.00 | .571 | .020 | 0.00 |
| TASKB (8,7,16), (12,10,23), both starts | .17 1 / .16 1 | 0.83–0.84 | .16–.17 | = marg | 0 (union bound certifies) |
| random covering (21,10,r=3), (20,10,r=2) | .06 .52 .99 1 | 0.09–0.14 | .97–.99 | .87–.91 | 0.00 |
| FKW m = 3, 4, 5 (22,12), (29,16), (36,20) | .5 1 | 1.50 | .50 | **0** | **−∞** |
| threshold {\|B∩A\| ≥ k}, (23,12), \|A\| = 21 | .22 .69 1 | 2.02 | .22 | .063 | **+0.10** |
| threshold (29,16), \|A\| = 28 | .45 1 | 1.66 | .45 | .17 | **+0.28** |
| complete K₂₀^(12), K₂₇^(16) | 1 | 4.00 | 0 | 0 | size obstruction |

- In every random-like and minimal family the seven events are independent at fixed sizes (κ = 0.00 ± 0.01).
- The FKW zero is exactly 3-term: the three short lines are a pencil {u, v, u+v}, and R_u+R_v+R_{u+v} = 0 forces an
  even trace on X.
- Asymptotic profile (`logs/profile.log`, k = 2·10³…10⁵, δ ∈ {.01,.04,.08}, ε/δ ≤ 0.3):
  φ(4n/7) ≤ 2^{−9} … 2^{−14033}; jump 1–5 levels; τ*_b bound 2.331–2.439; block margin > 0 except at k ≤ 10⁴ with
  δ = .01 or ε/δ ≥ .25 (finite-size 2log₂4n term); covering layers ≥ 2^{2800} members.

## 6. Strongest statements, exact gap, outlook
- [proved by hand] **(J)** Σ_u exp(−E_u + Δ_u/2) < 1 for some class law ⇒ good seven. Unconditionally this gives
  slope 3/7, sharp for exchangeable laws (§1.2).
- [proved by hand] **(R)** CTS is false: binomial random covering families (§2.1).
- [proved by hand] **(C)** With seven-freeness added, CTS ⇔ INV-P^L for seven-free families (§2.4).
- [proved by hand] Threshold-in-a-set families with thick D exist exactly when ε < 3δ/7, and are NC blocks (§3).
- **Exact gap.** For a thin, block-free family with marginals P(R_u ∈ U) = 2^{−Θ(k)}, show that the 7-wise joint
  law of the linearly tied sets (R_u) is not identically zero on the event that all seven are covered. Equivalently,
  U ⊇ PG(2,2) (matroid dictionary). The only known zero mechanism is linear (3-term parity, κ = −∞), and Theorem D
  caps it at e ≤ 3/2. A non-linear zero mechanism is what a counterexample must contain.
  - **Target 7INV** [open]: κ(H) ≤ −θk under balanced colourings ⇒ H correlates with a coset (an inverse theorem for
    PG(2,2)-counts at density e^{−Θ(k)}).
- **Outlook.** In principle this route reaches slope 0 only through 7INV or an equivalent 7-term supersaturation.
  The colouring framework adds nothing beyond restating it; the D-profile dichotomy carries no structure. Not
  recommended as a main line. Its useful residue is κ as a diagnostic for search (TASKB-style minimisation of κ at
  fixed density is the natural next experiment).

## 7. Reproduction (`compute/programme5/seven/`, `py -3.14`)
- `profile.py 2000 10000 100000` (< 1 s) produces `logs/profile.log`.
- `run_mc.sh` (15 families, 6 jobs, ~30 s; TASKB families from `compute/programme3/taskB/out/`) → `logs/mc_*.log`;
  plus `mc_colour.py complete:20:12` and `complete:27:16`. SPEC: file:PATH:n:k | fkw:m | complete:n:k |
  thresh:n:k:a:t | covrand:n:k:r:seed.
