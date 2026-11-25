# Erdős Problem #644: research toward a full resolution

**Question.** Let $f(k,7)$ be the largest transversal number of a $k$-uniform family in which every at most seven members can be pierced by two points. Erdős asked whether $f(k,7) = (3/4 + o(1))\,k$.
**Known before this project:** $f(k,7) \le \lceil 7k/8 \rceil$, and $f(4m,7) \ge 3m+1$ for $m \ge 10$ (Fon-Der-Flaass, Kostochka, Woodall, *Discrete Math.* 207, 1999). Problem page: <https://www.erdosproblems.com/644>.

> **Status: not solved.** This repository holds a verified reduction of the problem, proofs closing several regions of it, theorems ruling out broad classes of counterexamples, and a precise statement of what remains open. Every claim carries an explicit verification level (see below). Nothing here should be read as a claimed solution.

## Start here

| If you want… | Read |
|---|---|
| A short, polished summary of what is established | [`reports/STATUS_REPORT.pdf`](reports/STATUS_REPORT.pdf) ([source](reports/STATUS_REPORT.tex)) |
| The status of every individual claim | [`notes/LEDGER.md`](notes/LEDGER.md) |
| A self-contained brief of the open problem, for reviewers | [`reports/EXTERNAL_BRIEF.md`](reports/EXTERNAL_BRIEF.md) |
| The full working write-up of the open region | [`notes/CORE.md`](notes/CORE.md), starting at §33 (the handover) |
| Independent verification reports | [`notes/verify/`](notes/verify/) |
| The machine-checked lemmas | [`Lean644/`](Lean644/) |
| Every result with its proof location and verification | [`docs/RESULTS.md`](docs/RESULTS.md) |
| The approaches shown not to work, and why | [`reports/FAILED_ROUTES.pdf`](reports/FAILED_ROUTES.pdf) |
| Definitions of the terms used | [`docs/GLOSSARY.md`](docs/GLOSSARY.md) |
| How to check the claims yourself | [`docs/HOW_TO_VERIFY.md`](docs/HOW_TO_VERIFY.md) |
| How the work progressed | [`docs/TIMELINE.md`](docs/TIMELINE.md) |
| A guide to all working notes | [`notes/README.md`](notes/README.md) |

## What is established (summary)

Verification levels: **LEAN** = machine-checked in Lean 4/Mathlib (standard axioms, no `sorry`). **VERIFIED** = hand proof that passed an independent adversarial check (statement-by-statement review plus independent exact computation). **EXACT** = exact computation on finite instances.

1. **Reformulation** (VERIFIED). The problem is a request game. Three answers with empty common intersection confine the analysis to their union $V$, with $|V| \le 3k$. Requester wins transfer to the general problem *when the three anchors are kept among the final seven*. For families living entirely on $V$, this gives the co-edge form: a counterexample is a family of large sets covering every $T$-subset of $V$, with no seven of them covering all pairs.
2. **Closed regions, for families confined to $V$** (VERIFIED, at first order). Write $N = |V|/k$ and $t = T/k$. The crowded region $N \le 3t-\tfrac12$ is closed. So is the bottom strip $3t-\tfrac12 < N \le 5t-2$, by a density argument based on the Frankl–Rödl theorem. The large-ground-set ("petal") region is closed against the adversary classes analysed, up to two small residues.

   **Caveat (lifting).** The confined results do not by themselves bound $f(k,7)$. Answers may leave $V$ ("far replies"), and the crowded-region and bottom-strip certificates do not keep the anchors. Transferring them needs either anchor-keeping versions or the far-replies lemma (TWIN §17, gap G2). See [`notes/FRONTIER.md`](notes/FRONTIER.md).
3. **No structured counterexamples** (VERIFIED). In the remaining window, a counterexample cannot be:
   - a bounded blow-up (Theorems S, S⁺);
   - a fixed-order rule (CORE §46);
   - a rule choosing among priority orders by a window of at most $T-k/2$ points (Theorem W), or with more than 2/3 kernel density (Theorem H);
   - a random or 6-wise independent selector (Theorem R).
4. **Methods shown not to apply** in the window (hand proofs). Junta theorems; spread and sunflower lemmas; fractional relaxation with rounding; hypergraph containers; flag algebras; density-only and forbidden-pattern arguments; adaptive links; entropy methods; covering-design stability.
5. **Lean:** about 20 lemmas, including the reductions, the Fano criterion, the flat 7-tuple lemma, and Lemmas 4.1–4.8 of an unrefereed $6/7$ manuscript. The $6/7$ theorem itself is *not* formalized.

## What remains open

1. **The core window** $5t-2 < N < 3-t$ (about $1.75k$ to $2.25k$ points), for confined families. Show that every $T$-covering co-edge family there contains seven members covering all pairs. The surviving case is deterministic, deliberately anti-correlated families. The exact statement and the three sufficient configurations $(\Sigma)$ are in the [reviewer brief](reports/REVIEWER_BRIEF.pdf).
2. **Lifting (far replies).** Transfer the confined results to general families. This needs either anchor-keeping certificates or a proof that answers leaving $V$ cannot help the adversary (TWIN §17, gap G2).
3. **Petal residues.** A pooled two-arena strip and a one-class stability statement (SL1).

A possible intermediate result: exact certification of the parked one-round "sparsest anchor" argument would give $f(k,7) \le (17/20+o(1))k$. That is below the published $7/8$, and the argument keeps the anchors, so it transfers. See [`notes/FRONTIER.md`](notes/FRONTIER.md) §4–5.

## Repository layout

- `Lean644/`: Lean 4 formalization. `Lean644/Statements.lean` holds the frozen headline statements.
- `notes/`: working notes, the claim ledger and verification reports. See [`notes/README.md`](notes/README.md).
- `reports/`: polished status report and reviewer brief.
- `paper/`: an in-progress draft write-up, with status tags on every claim.
- `compute/`: search, SAT/ILP and verification scripts with their logs.
- `scripts/`: build and trust checks.

## Building the Lean development

```
lake exe cache get
lake build
scripts/check_trust.sh
```

Feedback, corrections and refutations are welcome via issues.
