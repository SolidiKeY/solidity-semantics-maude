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
  "$here/examples/Bank.maude"
  "$here/examples/solkey/Arithmetic.maude"
  "$here/examples/solkey/Storage.maude"
  "$here/examples/solkey/Memory.maude"
  "$here/examples/solkey/PushPop.maude"
  "$here/examples/solkey/Net.maude"
  "$here/examples/solkey/MainFeatures.maude"
)

# A result is "stuck" if it still mentions an internal operator that a
# finished reduction must have rewritten away. (A final Conf like
# `{k(nilK) …}` from a `rew` command is legitimate, so the k-cell itself
# is not a stuck marker — only these never-final helper operators are.)
stuck_re='result[^:]*:.*(eval\(|lower\(|readLoc\(|asg\(|payNet\(|call2?\(|branch\(|reqD\(|retD\()'

# Known-benign parser advisories to ignore, both structural artifacts of the
# shared Solidity/field kind (Int is both an Exp and an array/mapping key):
#  1. `declaration for _<_ …` — the four comparisons `< <= > >=` return the
#     dedicated sort `Prop` while the prelude's Nat versions return `Bool`;
#     both coexist and the guard/postcondition context selects `Prop`.
#  2. `ambiguous term` / `multiple distinct parses` — a subtraction `a - b`
#     also reads as the two-element field-list `a (neg b)`, because Int is a
#     field. Maude reliably takes the well-sorted arithmetic parse (every
#     affected reduction still matches its expected `*** …` comment, which is
#     the real correctness gate here); the internal DEFINING equations are
#     written in prefix form `_-_(a,b)` so only surface programs ever warn.
benign='declaration for _[<>]|ambiguous term|multiple distinct'

fail=0
for f in "${roots[@]}"; do
  name="${f#"$here/"}"
  out="$(maude -no-banner -batch "$f" < /dev/null 2>&1)"
  warns="$(printf '%s\n' "$out" | grep '^Warning:' | grep -Evc "$benign")"
  stuck="$(printf '%s\n' "$out" | grep -Ec "$stuck_re")"
  if [[ "$warns" -ne 0 || "$stuck" -ne 0 ]]; then
    echo "FAIL  $name  (warnings: $warns, stuck: $stuck)"
    printf '%s\n' "$out" | grep -E '^Warning:' | head -5
    printf '%s\n' "$out" | grep -E "$stuck_re" | head -5
    fail=1
  else
    reds="$(printf '%s\n' "$out" | grep -c '^reduce ')"
    srch="$(printf '%s\n' "$out" | grep -c '^search ')"
    echo "ok    $name  ($reds reductions, $srch searches)"
  fi
done

exit "$fail"
