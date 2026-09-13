#!/usr/bin/env bash
# Dialect "no unmarked toys" ratchet.
#
# Every `def/abbrev <name> : Dialect` in CatCrypt/ must be classified in
# scripts/dialect-manifest.txt (lowers | theory | test | review). This guards
# against a theory/optimizer/toy dialect being silently mistaken for an emit path
# (the drift that motivated it: DIALECTS.md is the prose map; this makes it
# mechanical).
#
# FAIL when: a Dialect def is not in the manifest (an UNMARKED toy), or a manifest
# entry names a dialect that no longer exists (stale).
# WARN when: the `review` bucket is non-empty (unclassified-but-tracked) — drive to 0.
#
# Usage: scripts/dialect-lowering-ratchet.sh   (run from repo root)
set -euo pipefail
cd "$(dirname "$0")/.."

MANIFEST="scripts/dialect-manifest.txt"
[ -f "$MANIFEST" ] || { echo "FAIL: $MANIFEST missing"; exit 1; }

# 1. Discover every Dialect def in the source tree (exclude .lake). Handles
#    parameterized dialects (`def x86Dialect (w : Nat) : Dialect`). Requires the
#    RESULT type to be `Dialect` (a `: Dialect` after any params) — so a
#    `Com (x86Dialect 64)`-typed def is NOT a dialect def and is excluded.
#    The RESULT type must be Dialect: `: Dialect` immediately before `:=` or EOL,
#    so a `Dialect`-typed *parameter* (`def denote (d : Dialect) : Foo`) is excluded.
discovered=$({ grep -rhoE '(def|abbrev) [A-Za-z0-9_]+.*: (VIR\.)?Dialect *(:=|where|$)' CatCrypt/ || true; } \
  | awk '{print $2}' | sort -u)

# 2. Manifest names (any bucket) and per-bucket lists.
manifest_names=$(grep -vE '^\s*#|^\s*$' "$MANIFEST" | awk '{print $2}' | sort -u || true)
review_names=$(grep -E '^review ' "$MANIFEST" | awk '{print $2}' | sort -u || true)

fail=0

# 3. Unmarked: discovered but not in the manifest.
unmarked=$(comm -23 <(printf '%s\n' "$discovered") <(printf '%s\n' "$manifest_names") || true)
if [ -n "$unmarked" ]; then
  echo "FAIL: dialect def(s) not classified in $MANIFEST (unmarked toys):"
  printf '  %s\n' $unmarked
  echo "  -> classify each as lowers|theory|test|review per DIALECTS.md."
  fail=1
fi

# 4. Stale: in the manifest but no longer a discovered def.
stale=$(comm -13 <(printf '%s\n' "$discovered") <(printf '%s\n' "$manifest_names") || true)
if [ -n "$stale" ]; then
  echo "FAIL: manifest names a dialect that no longer exists (stale):"
  printf '  %s\n' $stale
  fail=1
fi

# 5. Review bucket: tracked, warn (not a failure).
if [ -n "$review_names" ]; then
  n=$(printf '%s\n' "$review_names" | grep -c . || true)
  echo "WARN: $n dialect(s) in the 'review' bucket — classify against DIALECTS.md:"
  printf '  %s\n' $review_names
fi

if [ "$fail" -eq 0 ]; then
  nl=$(grep -cE '^lowers ' "$MANIFEST" || true)
  nt=$(grep -cE '^theory ' "$MANIFEST" || true)
  nr=$(printf '%s\n' "$review_names" | grep -c . || true)
  echo "OK: every Dialect def is classified ($nl lowers, $nt theory, $nr review)."
fi
exit $fail
