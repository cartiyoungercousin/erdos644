# How to check the claims

## Lean

```
lake exe cache get
lake build
scripts/check_trust.sh
```

`check_trust.sh` confirms two things: the frozen statements in `Lean644/Statements.lean` are unchanged, and no `sorry`, `admit`, extra axiom or `native_decide` appears. CI runs it on every push.

## Hand proofs

Each verified result has a report in `notes/verify/`. Each report gives the target section, a step-by-step check, and the independent test code that was run (in `compute/verify/`). To re-run a check, run the script named in the report with `py -3` (Python 3, with `pulp`, `highspy` and `python-sat`).

## Exact computations

Certificates and their independent checkers live next to the searches in `compute/`; see [`compute/README.md`](../compute/README.md). An UNSAT result counts as exact only when its certificate was re-checked by separate code. Otherwise it is labelled "solver-only".

## Reporting problems

Please open an issue. Counterexamples to any VERIFIED claim are especially welcome.
