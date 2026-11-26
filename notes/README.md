# Guide to the working notes

These are research logs written as the work progressed. They contain dead ends and corrections as well as results. **The authoritative status of any claim is the one in [`LEDGER.md`](LEDGER.md)**, which supersedes older notes where they disagree.

## Authoritative

| File | Content |
|---|---|
| [`LEDGER.md`](LEDGER.md) | Status of every claim: LEAN / VERIFIED / HAND / EXACT / FLOAT / DEAD |
| [`verify/`](verify/) | Independent verification reports, one per theorem group |
| [`CORE.md`](CORE.md) | The core window. §33 is a self-contained handover; later parts contain the classification theorems (S, S⁺, W, H, R), the bottom-strip proof (§90–§94) and the analyses of dead routes |
| [`PETAL.md`](PETAL.md) | The large-ground-set (petal) region: Theorems J, K, L, AP, DS, PS–PS3, CR, and the remaining residues |
| [`TWIN.md`](TWIN.md) | The confinement reduction (§13) and the crowded region (§16) |

## Programme notes (direction briefs 2–5)

Each `PROGRAMME*.md` note is a research log for one brief item; the ledger entry gives the status of its claims.

| File | Content |
|---|---|
| `PROGRAMME_2.md` | The second direction brief: the (S)-type programme, pieces A/B/C, tasks and decision points |
| `PROGRAMME2_A.md` | Piece A: rich families for large k (Theorem RA, VERIFIED) |
| `PROGRAMME2_B.md` | Piece B: covering coset families with many point classes (Theorem B1, S0, S1; HAND) |
| `PROGRAMME2_C.md` | Bridge C, near-coset half: Lemma P1, Theorems C1/C2, INV-P (P1 later VERIFIED) |
| `PROGRAMME2_NC.md` | Bridge C, near-complete lemma: Lemma NC1, Theorem NC (VERIFIED) |
| `PROGRAMME2_TASK1.md` | τ*_b for every stored family (thinness data) |
| `PROGRAMME2_TASK2.md` | The constant c* (decision D1): Theorem D and the counting bound (VERIFIED) |
| `PROGRAMME2_TASK3.md` | The adjustment step of Proposition 9: Proposition 9 false, Theorem 9′ (VERIFIED) |
| `PROGRAMME2_TASK4.md` | Measuring the bridge (D2): coset structure of seven-free data |
| `PROGRAMME3_BULK.md` | Scoping map of the bulk N ≥ 11/6 (LPs over all 716 seven types) |
| `PROGRAMME3_CX.md` | Counterexample side: BCH/RM/Kerdock cosets; Lemma Q and the BAND shape |
| `PROGRAMME3_GAMMA.md` | Density exponent γ and the light-character range (counting route precheck) |
| `PROGRAMME3_LT.md` | Light triples, PEN(1/2) and slope 3/11 (VERIFIED in `verify/PEN_P1.md`) |
| `PROGRAMME3_TASKB.md` | Task B (D3): seven-count minimisers at small k (heuristic) |
| `PROGRAMME4_CELLS.md` | Exact search over one/two/three-cell profile families; the two-cell table k = 8..20 |
| `PROGRAMME4_INVP.md` | INV-P go/no-go; the pencils-versus-sevens barrier (heuristic random coset unions) |
| `PROGRAMME4_LADDER.md` | Counterexample ladder, Rung 0: an 8-uniform (7,2) family with τ = 7, so f(8,7) = 7 (not yet verified) |
| `PROGRAMME4_P1.md` | The P1 constant: c = 4 sharp for one-pencil arguments; P1′ (HAND) |
| `PROGRAMME4_PEN.md` | PEN(η) for small r via Frankl–Wilson: slope 1/5 near 7k/4 (VERIFIED in `verify/PEN_FW.md`) |
| `PROGRAMME4_TOPO.md` | Topological rainbow criterion (no-go) and the matroid dictionary (HAND) |
| `PROGRAMME5_7INV.md` | Target 7INV: transference and the true complexity of the Fano pattern |
| `PROGRAMME5_ADAPT.md` | Adaptive finishing vs Theorem O; depth-3 spectrum game capped at 6/7; hand check of the 6/7 manuscript |
| `PROGRAMME5_ALG.md` | Algebraic angle on (S<): slice rank, Chevalley–Warning, MacWilliams (no-go) |
| `PROGRAMME5_BEAT78.md` | One-configuration lemmas cannot beat 7/8 at n ≥ 2k: Theorem O (HAND) |
| `PROGRAMME5_BELOW67.md` | Closures of the critical medium+tiny triple: Theorem P, capped at 6/7 (HAND) |
| `PROGRAMME5_BRIDGE.md` | The critical bridge configuration: joint MILP (unfinished) and seed families killed by the 2×2 grid six (partial) |
| `PROGRAMME5_BULK.md` | Region n ≥ 11k/6: two-stage dump (3/11 to n ≤ (8k+11)/3), HUB lemma (HAND) |
| `PROGRAMME5_COMPRESS.md` | Compression lemma (C): relative pencil lemma NC-P holds (HAND); other routes dead |
| `PROGRAMME5_QUAD.md` | Quadratic obstructions: Theorem QK (HAND); quadratic level sets dead as counterexamples |
| `PROGRAMME5_SEVEN.md` | Random Fano colourings (slope 3/7) and the coarse-threshold dichotomy (CTS false) |
| `PROGRAMME5_SPECTRUM.md` | Spectrum forcing at the bridge triple: cap holds in the rigid shape; open lead elsewhere (partial) |

## Supporting and historical

| File | Content |
|---|---|
| `PROOFS.md`, `FRESH_A–C.md` | Earlier proof development: flat 7-tuples, the Fano criterion, exact small cases |
| `REDTEAM.md` | Adversary constructions used to stress-test strategies |
| `FAST.md` | Exact game solver and small-case computations |
| `LITERATURE.md`, `LIT_11_13.md`, `NOTES.md` | Literature notes and the problem statement |
| `FABLE_A.md`, `FABLE_C.md` | The latest research round (multi-pool designs; the Σ₆ and size-2 co-type leads) |
| `FRONTIER.md`, `FINITE_K.md` | Intermediate-bound work and finite-$k$ repairs (in progress) |
| [`archive/`](archive/) | Superseded logs from early rounds (`R1*`, `R2CORE*`, `COMBINE_RESULTS`, `NEW_PATHS`, old plans) |
| `LEAN_POLICY.md` | Rules for the Lean development (no `sorry`, frozen statements) |
