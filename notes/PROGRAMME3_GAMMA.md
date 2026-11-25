# Programme 3 precheck: density exponent γ and the light-character range (Tasks C/D of the third brief)

Tags: [computed] = evaluated by script (asymptotic in k unless a k is named); [heuristic] = model or interpretation.
Code: `compute/programme3/gamma_precheck.py` (table), `gamma_hash.py` (CORE §56 densities); logs in `compute/programme3/logs/`.
Conventions (PROGRAMME2_C §0): T = (3/4+ε)k, n = Nk = (7/4+δ)k, r = n−T−k = ωk, so **ω = δ − ε**. T-covering means every
(n−T) = (k+r)-set contains a member. p = |H|/C(n,k) = e^{−γk}; h = binary entropy in nats; exponents are nats per k.

## 0. The window is almost empty [computed, from C1]
3ε ≤ δ < 1/12 forces **ε < 1/36 ≈ 0.028**. So ε = 0.03 and 0.05 have no window at all, and N = 1.76 needs ε ≤ 0.0033.
Of the 12 requested cells only (1.78, 1.80, 1.82) × 0.01 are live. Cells with ω < 0 are vacuous (n − T < k: no member fits).
γ depends on (N, ε) only through N and ω, so C1-excluded cells repeat live values (e.g. (1.82, .03) = (1.80, .01) in ω).

## 1. γ for the four kinds of family
- (a) **Minimal covering** [computed]: double counting, |H|·C(n−k, r) ≥ C(n, k+r), and C(n,k+r)C(k+r,k) = C(n,k)C(n−k,r), so
  p ≥ 1/C(k+r, k), i.e. **γ ≤ γ_a := (1/k) ln C(k+r,k) → (1+ω) h(ω/(1+ω))**. Every T-covering family has γ ≤ γ_a.
- (b) **Random covering** [computed]: p ≈ ln C(n,k+r)/C(k+r,k), so γ_b = γ_a − (ln ln C(n,k+r))/k → γ_a (gap 0.048 at k = 100; it vanishes like (ln k)/k).
- (c) **Coset, codim e**: γ = e ln2/k; covering forces e ≤ e_max = γ_a k/ln 2. At N → 11/6, ε → 0: e_max = 0.424k, the "0.43k" of B §3.
- (d) **CORE §56 greedy/head families** [computed]: members are V∖reply(S). B is a member iff some class c has an ω-set
  before min_c(B) in ≺_c whose request the selector sends to c. Closed form for hash selectors,
  p = 1 − (E(1−1/R)^{C(L,ω)})^R with P(L ≥ m) = C(n−m,k)/C(n,k), agrees with Monte Carlo on the verbatim rule code
  (4000 k-sets per rule). Only **(k, T, n) = (100, 76, 180)** (N = 1.80, ε = 0.01) is in the window; the k = 40 sizes have N ≥ 1.85.
  There γ ranges over 0.016 (hash R = 64) to 0.049 (late R = 4), against γ_a(k=100) = 0.153. At k = 40, n = 74: γ = 0.027–0.090 against γ_a = 0.236.
  The asymptotic head model is γ_head = N h(1/N) − (N−ω) h(1/(N−ω)) ≈ 0.81ω [heuristic]. These families are dense because they are greedy, not minimal.

## 2. Cutoffs and light-character counts (x = w/k) [computed]
- x1 = 2γ/ln 7 is the brief's criterion 7^{−w/2} < p. Light characters number Σ_{w<w*} C(n,w) = e^{c1·k}, with c1 = N h(x1/N).
- x3 solves N h(x/N) + γ = x ln 7. This is the best *rigorous* cutoff available: Cauchy–Schwarz plus Parseval give
  Σ_{|h|=w}|c_h| ≤ (C(n,w)/p)^{1/2}, damped by 7^{−w/2}. With only |c_h| ≤ 1 the cutoff is x2 ≈ 1.16–1.20 (beyond n/2).
- The table uses γ = γ_a, the worst case (a ≈ b ≈ c at e_max). γ_head and its x_head = 2γ_head/ln 7 are given for (d).

| N | ε | δ | ω | status | γ_a | γ_b(k=10³) | e_max/k | x1 | e^{c1 k}: c1 | x3 (c3) | 4ε | γ_head / x_head | slack/step |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1.76 | .01 | .01 | 0 | C1-excluded | 0 | 0 | 0 | 0 | 0 | .569 (1.11) | .04 | 0 / 0 | – |
| 1.76 | .03, .05 | .01 | <0 | vacuous | | | | | | | | | |
| 1.78 | .01 | .03 | .02 | **live** | .098 | .089 | .142 | .101 | .388 | .651 (1.17) | .04 | .017 / .017 | .49 |
| 1.78 | .03 | .03 | 0 | C1-excluded | 0 | 0 | 0 | 0 | 0 | .576 (1.12) | .12 | 0 / 0 | – |
| 1.78 | .05 | .03 | <0 | vacuous | | | | | | | | | |
| 1.80 | .01 | .05 | .04 | **live** | .170 | .160 | .245 | .174 | .572 | .707 (1.21) | .04 | .033 / .034 | .48 |
| 1.80 | .03 | .05 | .02 | C1-excluded | .098 | .089 | .142 | .101 | .390 | .658 (1.18) | .12 | .016 / .017 | .82 |
| 1.80 | .05 | .05 | 0 | C1-excluded | 0 | 0 | 0 | 0 | 0 | .582 (1.13) | .20 | 0 / 0 | – |
| 1.82 | .01 | .07 | .06 | **live** | .231 | .221 | .333 | .237 | .704 | .753 (1.23) | .04 | .049 / .051 | .49 |
| 1.82 | .03 | .07 | .04 | C1-excluded | .170 | .160 | .245 | .174 | .574 | .713 (1.22) | .12 | .032 / .033 | .67 |
| 1.82 | .05 | .07 | .02 | C1-excluded | .098 | .089 | .142 | .101 | .391 | .664 (1.19) | .20 | .016 / .017 | 1.15 |

For comparison, the whole cube has 2^n = e^{N ln2·k} = e^{1.23–1.26k} characters.

**Worked cell (N = 1.80, ε = 0.01)** [computed]:
- ω = 0.04; γ_a = 1.04·h(0.0385) = 1.04·0.163 = 0.170.
- x1 = 2(0.170)/1.946 = 0.174; c1 = 1.8·h(0.174/1.8) = 1.8·0.318 = 0.572.
- So w* = 0.174k against 4εk = 0.04k (4.4×) and δk = 0.05k (3.5×), with e^{0.57k} light characters against 1/p = e^{0.17k}.
- At k = 100, the §56 family (γ = 0.016–0.049) has w* = 1.6–5 points against 4εk = 4: a narrow strip.

Extremes of the window [computed]:
- N → 11/6, ε → 0: γ_a = 0.294, x1 = 0.302.
- Bottom edge δ = 3ε (ω = 2ε): γ_a ≈ 2ε ln(e/2ε), so x1/(4ε) ≈ 0.51 ln(e/2ε). This is 2.9 at ε = .005 (x1 = .058 vs .02) and 3.7 at ε = .001.
  **x1 ≥ 4ε everywhere in the window, and the ratio grows like ln(1/ε).**

## 3. Density increment against the budget 4n − 7k = 4δk [computed arithmetic; cost model heuristic]
- A coefficient |c_h| ≥ η raises density by a factor of 1 + η on a parity class, so steps ≤ γk/ln(1+η) (0.24–0.57k at η = 1/2, γ = γ_a).
- **Slack per step** = 4δk/steps = 4δ ln(1+η)/γ = **0.48–0.49 deficiency units** in the live cells. At the bottom edge it is
  ≈ 2.4/ln(e/2ε) → 0, i.e. Θ(1/log(1/ε)) per step, independent of k.
- Integral costs: a dumped point (coloop) costs 4 units (12 incidence units, B §5.7). An odd-class step forces every pencil
  sum to meet supp h, which costs up to 7 pencil units = 7/3 deficiency units when the supports are disjoint.
  The budget allows ≤ 12δk/7 = 0.05–0.12k odd steps, against 0.24–0.57k steps needed (about 5× over).
- **Verdict on (3):** o(ε) points per step is not the issue. The available slack is a constant below one deficiency unit
  per step (about 1/8 of one dumped point), shrinking like 1/log(1/ε). Costs are integers, so the increment survives only if
  all but an O(δ/γ) fraction of steps are *exactly* free: even class, with support avoiding the Ω's. A constant fraction of
  costly steps exhausts the slack 5–8×. [heuristic: assumes the adversary can make the heavy class odd, i.e. c_h < 0]

## 4. Verdict
- **The light range is essentially the whole regime for sparse families** [computed].
  - Under the brief's own criterion, w* ≈ 1.03γk is 2.5–6× the pencil scale 4εk and about 3.4× δk, with e^{0.39–0.70k}
    light characters, far more than 1/p = e^{0.10–0.23k}. So Parseval allows exponentially many light coefficients of constant size.
  - With the rigorous tools (7^{−1/2} damping, Cauchy–Schwarz plus Parseval), characters are harmless only beyond 0.65–0.75k,
    with e^{1.17–1.23k} light characters: essentially the whole cube.
  - "Heavy characters are harmless by damping alone beyond a multiple of log(1/p)" holds only under a per-weight L¹ bound
    Σ_{|h|=w}|c_h| ≤ e^{o(k)}·p^{−1/2}, which nothing gives. And the seven-tuple sum (Task C, Deliverable 1) is larger still.
- **A narrow strip only for dense families**: the head/greedy §56 type (γ ≈ 0.8ω, x_head < 4ε near the bottom edge),
  and cosets of small codimension.
- **The wall** [computed]: L∞-pseudorandom counting needs |c_h| < e^{−c k} on the light range, with c = max_{x≤x1}(N h(x/N) − x ln7/2)
  = 0.29, 0.40, 0.47 at N = 1.78, 1.80, 1.82. The increment needs |c_h| = Ω(1) *and* free steps.
  So the wall is |c_h| ∈ (e^{−0.3…0.47k}, Θ(1)) at weights up to 0.10–0.24k, for every γ ≳ 4ε (up to γ_a).
- **Can Tasks C/D work as designed?** Not for families near the covering minimum.
  - Task C's pseudorandom theorem can plausibly cover the dense end, γ ≲ 4ε: cosets of codimension e < 5.6εk (x1 < 4ε) and the §56 families. Its test at k = 100 is meaningful.
  - For γ between about 4ε and γ_a (0.10–0.23), C fails by an exponential count of light characters, and D's increment exhausts the slack about 5×.
  - Before writing the identity, Task C needs a reason that seven-free covering families are dense, γ = O(ε).
    C1(ii) (no pencils lighter than 4εk) is the natural candidate, but it is not a density statement. [heuristic]
