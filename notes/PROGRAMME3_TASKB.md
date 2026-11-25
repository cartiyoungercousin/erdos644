# Programme 3 Task B: testing C away from the threshold (decision point D3)

Tags: [exact] = exact computation by our code; [heuristic] = Monte Carlo estimate or search outcome (search failure proves
nothing). Code: `compute/programme3/taskB/` (`taskb.py` search + measures, `evalfam.py` large-panel evaluation,
`find_layers.py`, `summ.py`). Raw output: `out/log_*.txt` (snapshots), `out/sa_*.json/.npy` (trajectories, final
families), `out/eval.jsonl`. Convention as PROGRAMME2 Task 4: T-covering ⟺ τ(H) > T ⟺ every (n−T)-set contains a member;
r = n−T−k, ω = r/k, ε = (T − 3k/4)/k, N = n/k, γ = −ln(|H|/C(n,k))/k, γ_a = ln C(k+r,k)/k (minimal-covering density; limit
(1+ω)h(ω/(1+ω))).

## 0. The requested instances do not exist in the Fano range [exact, by hand]
τ ≤ n−k+1, so T-covering needs n ≥ k+T, and n = k+T forces the complete family. With 4T > 3k and n < 11k/6:
- (8,7,14), (12,10,21), (16,13,28): n < k+T, **no T-covering family at all**.
- (8,7,15), (12,10,22): n = k+T, only K_n^(k); and N = 1.875, 1.833 are not < 11/6.
- A non-complete instance (r ≥ 1) needs 3k/4 < T < 5k/6 − 1, first at **k = 17: (17,13,31)**; then (21,16,38),
  (22,17,40), (23,18,42), (25,19,45). Each has |H| ≥ C(n,k+r)/C(n−k,r) ≈ 10^7 members: out of reach here.
- So every instance below has N ≥ 2 > 11/6, and a good seven need not be Fano-type there. We minimise the **Fano-type**
  count (the object of C) and say nothing about non-Fano sevens.

Instances used (largest k first was the reviewer's preference; k = 12 only got a start-point measurement):

| (k,T,n) | N | 4T−3k | ε | r | status of τ > T for (7,2) | γ_a (finite / limit) |
|---|---|---|---|---|---|---|
| (8,7,16) | 2.00 | 4 | .125 | 1 | impossible: f(8,7) = 7 (FKW ⌈7k/8⌉) | 0.275 / 0.392 |
| (10,8,21) | 2.10 | 2 | .05 | 3 | open: f(10,7) ∈ {8,9}; smallest genuine window instance (CORE §112) | 0.566 / 0.702 |
| (12,10,23) | 1.917 | 4 | .083 | 1 | open: f(12,7) ∈ {10,11} | 0.214 / 0.294 |

## 1. Method
- **Objective** [heuristic]. W(H) = Σ_χ Π_ℓ N_ℓ(χ), χ: V → Π, N_ℓ = #{B ∈ H : B ∩ χ⁻¹(ℓ) = ∅}. W counts pairs
  (labelled Fano-type good seven, compatible colouring); W = 0 iff no Fano-type good seven. We estimate
  **mp = W/7ⁿ = E_χ Π_ℓ N_ℓ** and **cert = P_χ(min_ℓ N_ℓ ≥ 1)** (the chance that a uniform colouring certifies a seven).
  The SA objective uses a 40k-colouring panel, resampled every 3000 moves; all reported values use independent panels
  (40k during the run, 2–4·10⁵ in `evalfam.py`, with standard errors).
- **Normalisation** (reviewer). W scales like p⁷ (p = |H|/C(n,k)) for a random subfamily. **depl = mp / (p⁷ · mp(K_n^(k)))**;
  a uniformly random subfamily of the same size has depl ≈ 1 (measured as `noise` below). depl < 1 means fewer sevens than
  density alone predicts.
- **Search** [heuristic]. SA over T-covering families, covering kept exactly by a count array over (n−T)-sets
  [exact]. Move: add B−x+y, delete in random order all members that became redundant near it; Metropolis on the relative
  change of the objective. Families stay minimal (W is monotone, so redundant members are always removed).
- **Starts** (two kinds per instance, as asked): a random minimal covering family (random greedy reduction of K_n^(k)), and a
  planted linear layer {B : |B ∩ X| ≡ 1 mod 2} (FKW type, |X| = 8, 12, 12) reduced to a random minimal covering
  subfamily (so it starts with 100% of members in one coset, ρ = 2). A random codim-2 layer with random dense checks was
  never T-covering at (8,7,16) (200 tries).
- **Measures** [exact unless noted]: dim C(H) and ρ (Gaussian elimination, coset enumeration); full Walsh–Hadamard
  transform on F₂ⁿ: best coset of codim 1, 2, 3 beyond the trivial all-ones check (prop1/2/3; codim 2, 3 over the top
  120/40 functionals, so a lower bound), density of H in that coset layer (dens1); max normalised Fourier coefficient
  |E_B(−1)^{|B∩S|}| at |S| = 1..4 (and the complete-family value); τ*_b (LP + exact bitset oracle, `task1/tau_star.py`).
  The noise level of prop/Fourier is measured on a uniformly random subfamily of the same size.

## 2. Results
Start → final of each run (SA 10 min at k = 8, 20 min at k = 10, 4 min at k = 12; at k = 12 the families have ~2·10⁵
members and ~1.6·10⁴ moves change < 10% of them, so **k = 12 is a start-point comparison only**). All families are
T-covering [exact]. cert, mp, depl [heuristic, s.e. ≈ 1% (k = 8), 15–20% (k = 10), 3% (k = 12)].

| instance, start | |H| | γ | γ/γ_a | cert ×10³ | mp | **depl** | codim C, ρ | prop1 / prop2 | dens1 | max Fourier w1, w2, w3, w4 | τ*_b |
|---|---|---|---|---|---|---|---|---|---|---|---|
| (8,7,16) random s1 | 2696 → 2223 | .195 → .220 | .71 → .80 | 4.26 → 3.20 | 7.78 → 2.04 | 1.01 → 1.02 | 1,0 → 1,0 | .543/.305 → .545/.308 | .23 → .19 | .013 .085 .030 .050 | 2 → 2 |
| (8,7,16) random s2 | 2691 → 2201 | .196 → .221 | .71 → .80 | 4.27 → 3.17 | 7.61 → 1.88 | 1.00 → 1.01 | 1,0 → 1,0 | .546/.302 → .545/.308 | .21 → .19 | .008 .083 .030 .059 | 2 → 2 |
| (8,7,16) FKW layer \|X\|=8 | 2705 → 2218 | .195 → .220 | .71 → .80 | 4.13 → 3.16 | 7.07 → 1.95 | **0.89** → 0.99 | **2,2** → 1,0 | **1.0**/.550 → .624/.350 | .42 → .22 | .008 .085 .041 .054 | 2 → 2 |
| (10,8,21) random | 4859 → 4090 | .429 → .446 | .76 → .79 | .11 → .07 | .0100 → .0039 | 0.70 → 0.91 | 1,0 → 1,0 | .538/.296 → .540/.298 | .015 → .013 | .057 .066 .033 .054 | 7/3 → 7/3 |
| (10,8,21) FKW layer \|X\|=12 | 4820 → 4099 | .429 → .446 | .76 → .79 | .13 → .06 | .0156 → .0031 | 1.16 → 0.72 | **2,2** → 1,0 | **1.0**/.537 → .706/.384 | .027 → .016 | .056 .066 .036 .047 | 7/3 → 7/3 |
| (12,10,23) random | 218457 → 216136 | .152 → .153 | .71 → .72 | 1.19 → 1.17 | 9.44 → 8.68 | 1.05 → 1.04 | 1,0 → 1,0 | .523/.275 (both) | .16 | .045 .046 .010 .011 | 2.09 |
| (12,10,23) FKW layer \|X\|=12 | 215200 → 213075 | .153 → .154 | .72 → .72 | 1.13 → 1.13 | 7.14 → 6.82 | **0.88** → 0.90 | **2,2** → 1,0 | **1.0**/.527 → .982/.517 | .32 → .31 | .049 .052 .010 .011 | 2.09 |

Reference values [exact unless noted]:
- Noise level (uniformly random subfamily, same size; not covering): prop1 .56 / .55 / .525, prop2 .32 / .31 / .277 at
  k = 8 / 10 / 12; Fourier max w1..w4 = .036 .12 .061 .09 (k = 8), .07–.10 .09–.10 .055–.06 .06–.065 (k = 10),
  .048 .051 .013 .014 (k = 12). Complete family: w1 = 0 / .048 / .043, w2 = .067 / .048 / –, w3, w4 ≤ .015.
  depl of the random subfamily: 0.98–0.99 (k = 8, 12), 0.85–0.94 (k = 10, MC noise) [heuristic].
- Covering minimum (Schönheim-type, |H| ≥ C(n,k+r)/C(n−k,r)): 1430 / 1234 / 104006. ln|H| / ln(bound) of the minimisers:
  **1.06 / 1.17 / 1.06**. γ vs 4ε: .22 vs .50 (k = 8), .45 vs .20 (k = 10), .15 vs .33 (k = 12).

## 3. Trajectories (snapshots every 60 s, `out/log_*.txt`)
- **Raw count falls only by sparsification.** At (8,7,16) mp drops 7.8 → 1.9 (×4) while |H| drops 2700 → 2210; p⁷ alone
  predicts ×4.1. depl stays 1.00 ± .02 at every snapshot of both random runs. γ rises monotonically toward γ_a
  (γ/γ_a .71 → .80); the count and the density move together and nothing else changes [heuristic].
- **Random starts never drift toward a layer.** prop1, prop2, prop3, codim C (= 1, the trivial all-ones check), ρ = 0 and every
  Fourier maximum stay at their start values, which are at or below the random-subfamily noise level, at every snapshot
  (k = 8, 10, 12). τ*_b = n/(T+1) = 2, 7/3, 23/11 for every family, start and final: the uniform y = 1/τ is optimal, so τ*_b
  does not separate anything here (all families are rich by the Theorem 3 threshold 7/3 − η, except at k = 10 where it is
  on the boundary) [exact, LP].
- **Planted layers are abandoned.** The FKW start leaves its coset at the first accepted move; prop1 decays 1.0 → .72 → .67 →
  .62 (k = 8, 10 min) and 1.0 → .88 → .80 → .75 → .71 (k = 10, 20 min), while its count falls to the random-start value
  (k = 8: mp 1.95 vs 1.88–2.04; k = 10: .0031 vs .0039, within MC error). Both kinds of start end at the same place in every
  measured quantity except the residual prop1 (still decaying when the time ran out).
- **But the layer is seven-depleted at equal density**: depl 0.89 (k = 8) and 0.88 (k = 12) for the planted minimal FKW
  subfamilies vs 1.00–1.05 for random minimal covering families of the same γ (differences ≈ 8σ and 5σ). At k = 10 the MC
  error (±20%) hides it. The search does not keep this 11–16% advantage because sparsifying by 20% buys more (p⁷).
- Exact-coset obstruction is unavailable here: Cor. 7 needs 7ρ > 3(4n−7k) = 24 / 42 / 24, i.e. ρ ≥ 4 / 6 / 4, while Lemma 8
  gives ρ ≤ 2r+1 = 3 / 7 / 3 for every covering coset family. So at k = 8, 12 no linear layer can be seven-free [exact,
  by hand from the two quoted lemmas].

## 4. D3 verdict
**(iii), with a qualification.** Over T-covering families at 4T − 3k > 0 the count of Fano-type good sevens stays far above 0
(cert ≈ 3·10⁻³, 7·10⁻⁵, 1.1·10⁻³ of all colourings certify a seven), the minimisers are unstructured by every measure
(codim C = 1, best coset at noise level, light Fourier coefficients at noise level, τ*_b unchanged), random starts never
move toward a linear layer, and planted layers dissolve as the count is pushed down. The normalised count of the
minimisers is ≈ 1: they have exactly as many sevens as their density predicts. The only structure signal is that
planted FKW layers are 11–16% depleted at equal density, and that this does not grow from k = 8 to k = 12 at fixed
4T − 3k = 4 (0.89 → 0.88), whereas the conjectured mechanism needs depletion like e^{−Θ(εk)}.
So the data point to **"generic thin families have many good sevens; the problem is a counting problem (Task C)"**, and give
no support for C beyond the threshold.

Caveats (they limit the strength of the verdict):
- No instance is in the Fano range (§0); the smallest one is k = 17 with ~10⁷ members. N = 2.0, 2.1, 1.92 here.
- At these k, e^{−4εk} = e^{−4}, e^{−2}, e^{−4}: the finite-size effects are of the same order as the effect being tested.
- The search minimised the raw count, which favours sparsity. A run minimising depl at fixed |H| (or fixed γ) was not
  done; it is the right next search, since the planted layers win on that measure.
- Seven counts are Monte Carlo over uniform colourings (weighted count W), not exact counts; non-Fano sevens not counted.
- k = 12 runs were too short to move the family; only the start comparison there is informative. Single seeds at k = 10, 12.
- The Kaggle runner offered later was not used: the first Fano-range instance (17,13,31) needs ~10⁷ members and 2³¹-entry
  count arrays, which does not fit this code; a 4-CPU kernel would only buy longer k = 12 runs.

## Reproduction
`py -3.14 taskb.py k T n start seed minutes` (start: `random`, `layer=X:a:p`, `complete`, `randlayer=r`), then
`py -3.14 evalfam.py out/sa_*.json Pbig`; `showeval.py`, `summ.py` print the tables. `run_all.sh` has the local runs.
