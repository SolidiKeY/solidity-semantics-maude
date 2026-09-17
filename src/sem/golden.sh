#!/usr/bin/env bash
# src/sem/golden.sh — dump every root's reduction/search OUTPUT in a stable,
# diffable form.
#
# Why this exists: run-tests.sh only greps for warnings and stuck terms. It
# does NOT compare results against the trailing `*** …` expected-value
# comments, so a `true` -> `false` flip in a Hoare triple passes it silently.
# This script is the missing gate: snapshot before a change, diff after.
#
#   bash src/sem/golden.sh > /tmp/golden.before
#   …edit…
#   bash src/sem/golden.sh > /tmp/golden.after
#   diff /tmp/golden.before /tmp/golden.after
#
# Each `reduce`/`search`/`result`/`Solution` block is folded onto ONE line with
# whitespace squeezed, so Maude's line wrapping cannot hide a change and a
# term that grows does not reflow every following line. Dropped: `rewrites:`
# (timing), and Warning/Advisory text (it carries source line numbers, which
# move whenever a file is edited — run-tests.sh is what gates warnings).
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mapfile -t roots < <(sed -n '/^roots=(/,/^)/p' "$here/run-tests.sh" \
  | grep -o '"\$here/[^"]*"' | sed "s|\"\$here/|$here/|; s|\"$||")

for f in "${roots[@]}"; do
  name="${f#"$here/"}"
  maude -no-banner -batch "$f" < /dev/null 2>&1 | awk -v n="$name" '
    function flush() { if (keep && buf != "") { gsub(/[ \t]+/, " ", buf); print n "\t" buf } buf = "" }
    /^(reduce|search|result|rewrites:|No solution|Solution|Warning|Advisory)/ {
      flush()
      keep = /^(reduce|search|result|No solution|Solution)/
      buf = $0
      next
    }
    /^[ \t]/ { if (buf != "") buf = buf " " $0; next }
    { flush(); keep = 0 }
    END { flush() }
  '
done
