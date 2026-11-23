# Lean trust policy

Goal: never "prove" something other than what we mean. AI-written Lean often passes `lake build`
by misstating the theorem, assuming something vacuous, or using an escape hatch. Rules:

1. **Statements first, human-approved, then frozen.**
   Every headline theorem lives in `Lean644/Statements.lean` with a plain-English docstring.
   The user approves the statement before any proof work. CI fails if a frozen statement changes
   (hash check), so a proof can't quietly weaken its own goal.
2. **No escape hatches.** CI rejects `sorry`, `admit`, `axiom` declarations, `native_decide`,
   `implemented_by`, `extern`, `unsafe`, `opaque`-based tricks, and `set_option` that disables
   checking. For each headline theorem CI runs `#print axioms`; the only allowed output is
   `propext`, `Classical.choice`, `Quot.sound`.
3. **Definitions have unit tests.** Each definition (transversal, tau, property (p,t), f(r,p,t))
   must reproduce known facts before use, e.g.:
   - the 7 complements of Fano lines have tau = 3 (so they violate (7,2));
   - K_6^(4) has property (7,2) and tau = 3; K_7^(4) fails (7,2);
   - a family with fewer than p edges behaves as the paper's definition says.
   At least one test must be a *negative* fact, so a vacuous/trivial definition fails.
4. **Non-vacuity.** For every theorem with hypotheses, exhibit a concrete object satisfying them.
5. **Blind back-translation.** A fresh agent that has not seen our intent reads only the Lean
   statement and writes what it means in English; we compare against the intended statement.
6. **Match the literature exactly.** Definitions follow FKW99 wording (property (p,t): every
   F ⊂ B with |F| = p has tau(F) <= t). Any deviation is documented with a proof of equivalence.
7. **Computer results are not proofs.** Solver "infeasible" answers are evidence until
   certified (independent re-check, or proved in Lean).
