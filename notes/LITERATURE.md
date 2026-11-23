# Literature notes — Erdős #644

Status key: [READ] read in full, [ABS] abstract / secondhand only, [MISSING] not obtained.

## 1. Papers on the problem itself

- **Erdős–Hajnal–Tuza 1991**, Local constraints ensuring small representing sets, JCTA 58, 78–84. [ABS]
  Origin of f(r,p,t). Not yet read.
- **EFKT92**: Erdős, Fon-Der-Flaass, Kostochka, Tuza, Small transversals in uniform hypergraphs,
  Siberian Adv. Math 2 (1992) 82–88. [MISSING] Exact f(r,p,2) for p = 3..6:
  2r, floor(3r/2), floor(5r/4), r. Extremal families = complete r-graphs.
- **FKW99**: Fon-Der-Flaass, Kostochka, Woodall, Discrete Math 207 (1999) 277–284. [READ]
  See NOTES.md for full summary. 3r/4 + 1 <= f(r,7,2) <= ceil(7r/8) (lower bound for r = 4k, k >= 10).
- **K02**: Kostochka, Transversals in uniform hypergraphs with property (p,2), Combinatorica 22
  (2002) 275–285. [ABS] Asymptotics "for large p and huge r" (formula not visible in abstract).
  Paywalled; author-page link serves the wrong PDF. Apparently does not improve p = 7.
- **BKS19**: Bucić, Korándi, Sudakov, Covering graphs by monochromatic trees and Helly-type
  results for hypergraphs, arXiv:1902.05055 (Combinatorica 2021). [READ §1, §5.1–5.2]
  Notation h_r(k, l) = f(r,k,l). Useful pieces:
  * Obs 5.1: h_r(l,l) = inf; h_r(l+1,l) <= r l; monotone in k; >= l.
  * Def 2.8 / Cor 2.9 (Bollobás 1965): a tau-critical r-graph with tau = t+1 has at most
    C(r+t, r) edges. => WLOG our family is critical and finite of bounded size.
  * Thm 5.2: k >= C(r+l, l) => h_r(k,l) = l.
  * Lemma 5.8 (counting trick): if a distribution on l-sets misses every edge with probability
    < 1/k, then any k edges share a covering l-set.
  * Their general bounds target l = r or k large; nothing new for (7,2).
- Search for 2020–2026 work on h_r(7,2) or f(r,7,2): nothing found.
- the-omega-institute/trureturing #9792 (AI group, open as of 2026-09): no proof; partial
  obstructions to code-based constructions and to FKW's Lemma 1 architecture.

## 2. Parent topics

- **Helly / (p,q)**: Alon–Kleitman (p,q)-theorem; Alon–Kalai–Matoušek–Meshulam (abstract set
  systems via fractional Helly + weak eps-nets); Holmsen survey arXiv:2408.05871.
  Needs bounded "dimension" — our uniformity r -> inf, so not directly applicable.
- **tau-critical hypergraphs**: Bollobás 1965 (set-pair inequality); Gyárfás–Lehel–Tuza; Tuza;
  Kézdy–Lehel arXiv:2204.02859. Fact: in a tau-critical r-graph every vertex lies in some minimum
  transversal and misses some other.
- **Turán systems**: tau(H) > t  <=>  every (n−t)-subset of V(H) contains an edge, i.e. H is a
  Turán (n, n−t, r)-system. Sidorenko survey (Graphs Combin. 1995); de Caen. Counting bound:
  |H| >= C(n,r)/C(n−t,r).

## 3. Reformulations derived here (to verify/formalize)

- **Signature (Venn) view.** For 7 sets A_1..A_7 let sig(x) = {i : x in A_i}. Then
  tau({A_i}) <= 2 iff some point has sig = [7] or two points have sig(x) ∪ sig(y) = [7].
  So property (7,2) is a condition on which of the 128 Venn regions are nonempty, and
  |A_i| = r is linear in region counts. Small/structured cases become ILPs.
- **Union-bound limit.** Complete family on n points with r = alpha n, uniform random pair:
  miss prob ~ (1−alpha)^2; need < 1/7 => tau/r <~ 0.608 < 3/4. So the true extremal behaviour
  uses exact (Fano) structure, not averaging.
- The unique-ish obstruction in FKW: complements of Fano lines, blown up.

## 4. Leads and their literature

- **A. Algebraic constructions** (parity family = coset of a binary code on X): Oddtown/Eventown,
  Frankl–Wilson modular intersection theorems; multiple parity checks / mod-q conditions.
- **B. Turán-system lower bounds** to constrain any family with tau > (3/4+eps)r.
- **C. Computation**: signature ILP; SAT for small r; criticality makes search finite.
  First experiment: does the parity family work for k = 3 (open per FKW remark: works k >= 4,
  fails k = 2)?
- **D. Proof via stability**: FKW's claims force any bad 7-tuple in a near-extremal family to be
  near-Fano; aim to show tau > (3/4+eps)r forces such a 7-tuple.
