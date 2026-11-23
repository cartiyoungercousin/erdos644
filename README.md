# Erdős problems research

Working repo for attacking open Erdős problems, with proofs checked in Lean 4 + Mathlib.

## Current target: Erdős #644

Let f(k,r) be the largest transversal number of a k-uniform family in which every r members
can be hit by some 2 points. Is f(k,7) = (3/4 + o(1)) k?

Known: 3k/4 + 1 <= f(k,7) <= ceil(7k/8) (Fon-Der-Flaass, Kostochka, Woodall 1999).
Problem page: https://www.erdosproblems.com/644

## Layout

- `Lean644/` – Lean formalization (definitions, lemmas, checked results)
- `notes/` – research log, proof drafts, literature notes
- `compute/` – SAT / search scripts for small cases and constructions

## Workflow

develop an argument -> formalize in Lean -> read what fails -> revise -> repeat.
`lake build` must pass; CI rechecks every push.

## Building

```
lake exe cache get
lake build
```
