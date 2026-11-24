# R2-core progress (adaptive template game on n = 7k/4 + c points, T = 3k/4 + g)

Code: `compute/r2core/`. Nothing committed, no Lean edits.

## Milestone 1: model fixed after a hand pass
- Notation: s = c − g. A response to a request of size T − y is the offered set minus exactly
  s + y points ("drops"), because n − T = k + s.
- Fano template with anchor E (classes a1..a4) and six response lines
  1A={a1,a2}, 1B={a3,a4}, 2A={a1,a3}, 2B={a2,a4}, 3A={a1,a4}, 3B={a2,a3} (plus b_j on group j).
  Fano criterion: every point must be absent (requested or dropped) from all lines of a star:
  an E-point from the three response lines through some a_p, a non-E point from both lines of a
  group (star b_j) or from an a-star.
- Counting: requests supply 6T = 9k/2 + 6g incidences; needs are 3k (E) + 2(3k/4 + c) (non-E)
  minus what the adversary's drops contribute. Static play gives Theorem A: c <= 3g.
  Everything therefore depends on how many of the 6s forced drops the adversary can make useless.
- The listed constraints in this instance (checked by hand, see RESULTS §2): Lemma B, Cor 6.2,
  three_centres, min-S rigidity 11.1(c) and the pair gap are vacuous at the bulk scale for
  template configurations; "no shown good triple is tight" is the only rule that bites
  (it caps the number of points absent from all three edges of a concurrent triple by
  k/4 + c − 2g).

## Milestone 2: exact LP solved (compute/r2core/template_lp.py, out/template_lp.txt)
- Hand pass found the adversary policy: at the very first response choose between "all drops
  on E-points" and "all drops outside E" after seeing the first request; at 1B drop E-points
  already requested at 1A; from 2A on drop non-E points already absent from 1A and 1B. All
  later drops are useless to the requester.
- Two-scenario exact rational LP (requester fully general in the type model, 51 variables,
  Fractions simplex): requester wins iff c <= 3g. Infeasible at c/g = 3.01, 4, 6, 10 (g = 1/100
  and g = 1/1000). Against a NON-adaptive first response (scenario fixed in advance) the
  requester wins up to c/g = 5 exactly (feasible at 5, infeasible at 5.01, both scenarios).
- Soundness: with c < 0 (complete families K_N, N < 7k/4, g < c) the LP is infeasible (stuck),
  as required; tested (c,g) = (-1%,-2%), (-2%,-5%).
- Candidate families (candidate.py, typefam): the closure of the adversary's answers is
  essentially K_n and has a bad 7-tuple (k = 8, n = 18: found and brute-force verified); the
  7-type block family of one concrete line of play is (7,2) but has tau = 2. No counterexample
  candidate results.
- Final write-up: notes/R2CORE_RESULTS.md. Nothing is running.
