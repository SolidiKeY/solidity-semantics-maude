#!/usr/bin/env bash
# src/sem/run-tests.sh — run every self-contained spec in src/sem/ and fail
# on any error. Each file ends with a `red`/`search` block that is its test
# suite (loading a file also runs everything it `load`s), with expected
# results written inline as trailing `*** …` comments per the repo
# convention. A spec is green when Maude reports no Warning (no parse or
# execution failure) and leaves no semantic term stuck — a stuck reduction
# shows up as a result still containing an unreduced internal operator.
#
# Usage:  bash src/sem/run-tests.sh   (run from the repo root or anywhere)
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Roots that transitively cover the whole sem tree via `load`:
#   NetCallback  -> Contract -> Net -> Flow -> Stmt -> Expr -> Config -> Syntax
#   examples/Bank -> Contract -> ...
#   examples/paper/*  -> paper/Domain -> Steps -> Hoare -> Contract -> ...
roots=(
  "$here/Syntax.maude"
  "$here/Config.maude"
  "$here/Expr.maude"
  "$here/Stmt.maude"
  "$here/Flow.maude"
  "$here/Net.maude"
  "$here/Contract.maude"
  "$here/NetCallback.maude"
  "$here/Hoare.maude"
  "$here/Steps.maude"
  "$here/examples/Bank.maude"
  "$here/examples/solkey/Arithmetic.maude"
  "$here/examples/solkey/Storage.maude"
  "$here/examples/solkey/Copy.maude"
  "$here/examples/solkey/Bounds.maude"
  "$here/examples/solkey/EvalOrder.maude"
  "$here/examples/solkey/Memory.maude"
  "$here/examples/solkey/PushPop.maude"
  "$here/examples/solkey/Net.maude"
  "$here/examples/solkey/MainFeatures.maude"
  "$here/examples/solkey/Bool.maude"
  "$here/examples/solkey/Branching.maude"
  "$here/examples/solkey/NseIndex.maude"
  "$here/examples/solkey/Matrix.maude"
  "$here/examples/solkey/ComplexReceiver.maude"
  "$here/examples/solkey/CrossCopy.maude"
  "$here/examples/paper/StorageExamples.maude"
  "$here/examples/paper/StorageArrays.maude"
  "$here/examples/paper/StorageDelete.maude"
  "$here/examples/paper/StorageCopyMapping.maude"
  "$here/examples/paper/StorageCopyMappingFlagged.maude"
  "$here/examples/paper/Arithmetic.maude"
  "$here/examples/paper/MemoryExamples.maude"
  "$here/examples/paper/MemoryDelete.maude"
  "$here/examples/paper/MemoryArrays.maude"
  "$here/examples/paper/StorageToMemory.maude"
  "$here/examples/paper/MemoryToStorage.maude"
  "$here/examples/paper/Payment.maude"
  "$here/examples/paper/EvalOrder.maude"
)

# A result is "stuck" if it still mentions an internal operator that a
# finished reduction must have rewritten away. (A final Conf like
# `{k(nilK) …}` from a `rew` command is legitimate, so the k-cell itself
# is not a stuck marker — only these never-final helper operators are.
# holds( catches a Hoare triple whose guard or postcondition failed to
# decide.)
stuck_re='result[^:]*:.*(eval\(|lower\(|readLoc\(|asg\(|payNet\(|call2?\(|branch\(|reqD\(|retD\(|holds\(|stuck\()'

# No benign-advisory whitelist any more. Both advisories this file used to
# tolerate were artifacts of Int sharing a kind with Exp:
#   1. `declaration for _<_ …` -- the four comparisons returned Prop while the
#      prelude's Nat ones returned Bool, in one kind;
#   2. `ambiguous term` -- a subtraction `a - b` also read as the two-element
#      field list `a (neg b)`, because Int was a Field.
# Cutting Field$Elt and Value out of Exp's kind (see Syntax.maude) removed
# both, so ANY warning is now a real failure.
benign='^$'

# A result printed at a KIND rather than a sort — `result [Foo,Bar]: …` — is
# always a failure: it means a subterm never reached a well-sorted normal
# form. stuck_re cannot catch this (the operators involved are legitimate),
# so it is checked separately.
kind_re='^result \['

# ---- lint: a comment must never begin with "(" -------------------------------
# Maude reads `***(` as a BRACKETED comment, running to the matching ")". So a
# line like  *** (SolKey foo): bar  swallows the ")" and everything after it,
# usually including the terminating "." of the NEXT equation or reduction --
# silently, with no warning and no failure. This has bitten three times; it is
# cheaper to forbid the shape than to debug it again.
badc="$(cd "$here/../.." && grep -rn --include='*.maude' -E '^[[:space:]]*\*\*\* \(' . 2>/dev/null || true)"
if [[ -n "$badc" ]]; then
  echo "FAIL  comment starts with '(' — Maude reads ***( as a bracketed comment:"
  printf '%s\n' "$badc"
  exit 1
fi

fail=0
for f in "${roots[@]}"; do
  name="${f#"$here/"}"
  out="$(maude -no-banner -batch "$f" < /dev/null 2>&1)"
  warns="$(printf '%s\n' "$out" | grep '^Warning:' | grep -Evc "$benign")"
  stuck="$(printf '%s\n' "$out" | grep -Ec "$stuck_re")"
  kinded="$(printf '%s\n' "$out" | grep -Ec "$kind_re")"
  if [[ "$warns" -ne 0 || "$stuck" -ne 0 || "$kinded" -ne 0 ]]; then
    echo "FAIL  $name  (warnings: $warns, stuck: $stuck, kinded: $kinded)"
    printf '%s\n' "$out" | grep -E '^Warning:' | head -5
    printf '%s\n' "$out" | grep -E "$stuck_re" | head -5
    printf '%s\n' "$out" | grep -E "$kind_re" | head -5
    fail=1
  else
    reds="$(printf '%s\n' "$out" | grep -c '^reduce ')"
    srch="$(printf '%s\n' "$out" | grep -c '^search ')"
    echo "ok    $name  ($reds reductions, $srch searches)"
  fi
done

exit "$fail"
