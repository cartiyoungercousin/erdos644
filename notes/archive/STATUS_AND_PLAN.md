# Status and plan (2026-11-23, end of day 1)

## Where we are
**Bounds on f(k,7).** Published: 3k/4+1 <= f <= ceil(7k/8). Unrefereed 2026 claims: 6/7 (cubres), 11k/13+8
(skyvegetable666, the record bar of about 0.846), ceil((6k+3)/7)+1 (Ansatz). Ours: no new bound; grid
evidence only for 0.85.

**Proven in Lean (standard axioms only, CI trust check):**
- 6/7 manuscript: 12 of 18 pieces (Lemmas 3.1–3.4, 4.2–4.4, the four-edge products, ...); 4.1 WIP.
- Own lemmas: tight-triple (`TightTriple`), Theorem A (`TheoremA`), Lemma A (`SparserTriple`),
  Lemma 6.1 three centres and Cor 6.2 trace pairs (`ThreeCentres`).
- Novelty is unconfirmed: EFKT92 (Siberian Adv. Math. 2, 1992) is not accessible to us.

**Hand-proved (NEW_PATHS.md):** pair gap, Lemma B (trace), Lemma 6.3, Theorem 6.4 (top of the lopsided
regime closed for t > 2/3), Fano criterion, Theorem 8.1 (Theorem A relative to W), rigidity Lemma 8.2.

**The map (anchor = lex-min good triple, largest cell u, threshold u* = (2k-T)/3):**
| regime | status |
|---|---|
| lopsided, u >= ~0.57k | closed (Theorem 6.4, hand proof) |
| sparse, u << u* | game evidence only |
| complete-like core + lopsided near u = k/2 | OPEN |

**The barrier (NEW_PATHS §9, exact LP).** Both open regimes have the same pseudo-adversary: a locally
complete piece plus a correlated outside "pool" shared by responses. The outside overlap can be about
0.59k, against the about eps*k that Theorem 8.1 needs. None of our lemmas sees the pool. Not believed
realizable (a product family has small tau; a single fixed pool loses to one pool point per request),
but nothing proved excludes it.

**Ruled out / learned:** one-round request games cap at 5/6; tie-breakers are void in the continuum
model; fractional covers are useless; the lex-min anchor is already in the 11/13 repo.

## Options (ranked)
1. **Finish the Lean verification of 6/7** (guaranteed value). This would be the first machine-checked
   bound below 7/8 for #644. Remaining: OneCoreLemma Case 3 (memory blowup; split coverage into typed
   `have`s), Lemmas 4.5–4.8, Props 5.1/5.3, Thm 5.2, gap Props 6.2–6.4, main theorem, Audit.lean. All case
   logic is already audited in Python (0 failures). Cost: moderate; mostly mechanical.
2. **One bounded hand attack on the pool** before any big computation: generalize "one pool point per
   request" (requests that sample the pool) into a lemma that forces either small pool overlap or a
   sparser or closable triple. Budget: one Fable pass; stop if no lemma.
3. **Pool-request engine** (the second round into the pool, engine-sized). Expensive (R1b used about 840k
   tokens) and uncertain; only after option 2 says what to compute.
4. **Write-up**: the decomposition, the Lean lemmas and the barrier, as a progress note. Posting anywhere
   public (erdosproblems forum) needs an explicit OK.
5. **Literature (user)**: a library or interlibrary-loan copy of EFKT92 settles novelty of tight-triple
   and Theorem A.

Recommended: 1 and 2 in parallel (1 here, 2 by the Fable lead), then decide on 3.
