#!/usr/bin/env bash
# Trust checks (notes/LEAN_POLICY.md). Run from the repo root after `lake build`.
set -euo pipefail
fail=0

# 1. Frozen statements: hash of Lean644/Statements.lean (line endings normalized).
expected=$(tr -d '\r' < scripts/frozen_statements.sha256 | awk '{print $1}')
actual=$(tr -d '\r' < Lean644/Statements.lean | sha256sum | awk '{print $1}')
if [ "$expected" != "$actual" ]; then
  echo "FAIL: Lean644/Statements.lean changed (frozen). expected $expected got $actual"
  fail=1
else
  echo "ok: frozen statements unchanged"
fi

# 2. Banned escape hatches anywhere in Lean sources (comments included, to be safe).
banned='\bsorry\b|\badmit\b|^\s*axiom\b|\bnative_decide\b|implemented_by|@\[extern|\bunsafe\b|debug\.skipKernelTC|Lean\.ofReduceBool|trustCompiler'
if grep -rnE "$banned" Lean644 Lean644.lean; then
  echo "FAIL: banned construct found (see above)"
  fail=1
else
  echo "ok: no banned constructs"
fi

# 3. Axiom audit of headline theorems (added once they exist): see Lean644/Audit.lean.
if [ -f Lean644/Audit.lean ]; then
  out=$(lake env lean Lean644/Audit.lean 2>&1)
  echo "$out"
  if echo "$out" | grep -E "depends on axioms" | grep -vE "^.*\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" | grep -q .; then
    echo "FAIL: non-standard axioms"
    fail=1
  fi
  if echo "$out" | grep -q "sorryAx"; then echo "FAIL: sorryAx"; fail=1; fi
fi

exit $fail
