# Verification backlog: PETAL 40, FABLE_C 5.4, CORE 75.3

Verdicts: PASS / FAIL / GAP. Code (independent, written from the statements): `compute/verify/backlog_pcyc.py`,
`backlog_cr.py`, `backlog_fano.py`. No counterexample found. No commits.

## (1) PETAL 40

- **Lemma PC: PASS.** Both cases re-derived. In case 2, S_E ∩ S_C = E ∩ C exactly, so |S_E ∪ S_C| = 2(1-c+ε) - m. With a
  common c for both classes one takes c = min(c_X, c_Y); the corollary μ = 2-2c-t and c >= 1-5t/9, t < 63/79 re-derived
  (63/79 and 7/12 at t = 3/4 correct). Integer form (f = k-o+1, m <= f_X+f_Y-τ(H)) tested on 300 random exact small
  families: 2815 checks, 0 failures (`backlog_pcyc.py`).
- **Lemma YC: PASS.** The three cases for z are correct; the integer form γ_Q(A) <= h_P(A)+f_Q-τ(H) passes the same
  random test. It is tight on the arena-with-pool family (k=60, T=45, ρ=7, h=23: 7 = 7).
  Minor omission: absorption needs h_P(A) <= |A|, i.e. m_P(A) > 0. A with m_P(A) = 0 has β = 1, so Φ < t excludes it
  automatically. Harmless; the line "Take G ⊆ A of mass h_P(A)" should say so.
- **Theorem CR: PASS** (fixed H, she knows H). Checked: RI with b >= 1/3 in the forced case (I_3 <= 1/3 <= b, so
  I_4 = ∅, and F∪J has mass τ_Q+b = t); thirds B_j (centre j is confined to B_j on B, so traces on B are pairwise disjoint);
  traces on A disjoint because G_j ⊇ Z_<j ∩ A; |B| <= 4β; both G_j options; the reply is in Q by absorption (resp. F hitting).
  Simulation (`backlog_cr.py`): explicit two-class arena-with-pool family, k=60, T=45, ρ=7, h=23, c=31/60 (< 7/12, so J'' does
  not apply), unforced petals, dense/greedy/random adversaries leaking into earlier replies: 120/120 wins, max request 44 <= T.
- **Tolerance arithmetic (40.3): PASS.** (151t-112)/30 re-derived; 1/24 at t = 3/4.
- **Reduction of the two-class gap to SL1: PASS, conditional.** It is not a closure: SL1 is open (as 40.7 says). The only
  extra requirements are c = min over classes, c + t > 1 (true for c > θ, t > 7/11), and τ_P >= t/2 (shown).
  The 40.6 projective-plane arithmetic (c, τ = (q²+q+1)β_0, h, cost 0.576, q >= 8) re-derived.
- **Scope note (not an error).** CR and the SL1 reduction are for fixed families only, since CR uses H to choose A, hitting
  sets and the forcing class.

## (2) FABLE_C 5.4 collinear repair: PASS

Re-derived every step: Σ r_i = 7, r = (0,0,1,0,1,2,3); the inversion |V_λ| = ½Σ_{i∈λ}ℓ_i - ⅙Σℓ gives |L_i| = ℓ_i and
Σ|V_λ| = N-y exactly; the minimum class is (N-y)/7 - η (exact fractions, three parameter sets); θ >= 0 is exactly
3(N-y)+7η <= 7t, i.e. η <= 4ε/7 at y = ω. Step 3 uses "a set containing no line is not a blocking set of the Fano plane";
that is true (every blocking set in PG(2,2) contains a line), verified over all 128 subsets. Only the largest point of the
line needs to know the earlier misses, and M_a, M_b are known at time i > a, b.
Exhaustive adaptive game (adversary picks any miss set of size <= η from Y per reply, free dump only helps): five
integer instances, 5.8M leaf plays in the largest, 0 bad sevens, max request <= T (`backlog_fano.py`).
Caveat: this is a certificate for the reply space ℳ_{Y,η} only. Remarks 5.5/5.6 (fixed plans tolerate no misses; 4ε/3) are
labelled "counts, not full proofs" and I did not check them.

## (3) CORE 75.3 transfer lemma: PASS, with two statement ambiguities

The proof is correct: at finite k a position is an exact cell vector; s <= μ gives ⌈s_I k⌉ <= μ_I k since μ_I k is an
integer; rounding adds <= 2^q <= 2^m points (cells with q < m members); T-covering at T >= tk gives replies for every
request of size <= T; the reply has exact mass c and marginal μ, with μ'_{I∪{q+1}} >= s_I, so the play is a legal play
of G_∞(t', N'). Also T-covering at T >= tk implies the t'k-requests exist, so t' < t is used only for rounding.
Ambiguities, not errors:
1. "A strategy winning against every system with (C),(E)" must be read per system (the strategy may depend on the
   family) or uniform; either suffices because CP is a statement about a known family. The lemma should say so.
2. "Win" must mean b(μ) = 0 exactly at the leaf. A win with slack ε > 0 (as in some float LPs of §77) does not transfer.
   The neighbourhood U of N' is needed only so that |V| = N'k is integral at the given N.
