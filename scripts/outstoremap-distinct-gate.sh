#!/usr/bin/env bash
# outstoremap-distinct-gate.sh
#
# Every `def outStoreMap : OutStoreMap := [...]` must list DISTINCT
# (base, offset) pairs.
#
# `physBodyWithStores` emits one store per entry, in order, into
# `[base + off]`. Two entries with the same pair name the same cell, so the
# later store overwrites the earlier one and that output silently carries the
# wrong binding's value. Nothing in the export checks this: `outStoreSlots`
# maps entries to bindings positionally and never compares offsets, and the
# only other constraint on the map is its length. The shipped emitters satisfy
# distinctness by construction; this gate keeps it that way.
#
# Exit 0 when every map is distinct, 1 on the first collision.

set -eu

cd "$(dirname "$0")/.."

FILES=$(grep -rl "^def outStoreMap" --include='*.lean' CatCrypt/ || true)

if [ -z "$FILES" ]; then
  echo "outstoremap-distinct-gate: no outStoreMap definition found."
  echo "RESULT: SKIP"
  exit 0
fi

echo "outstoremap-distinct-gate: checking (base, offset) distinctness"
echo ""
printf '%-52s | %-7s | %s\n' "MODULE" "ENTRIES" "STATUS"
printf -- '-----------------------------------------------------+---------+--------\n'

FAILED=0

for f in $FILES; do
  # The definition body runs from `def outStoreMap` to the closing bracket;
  # take everything up to the first line containing `]`.
  body=$(awk '/^def outStoreMap/{inside=1} inside{print} inside && /\]/{exit}' "$f")

  # Each entry is ("BASE", OFF). Normalise to BASE:OFF, one per line.
  pairs=$(printf '%s' "$body" |
    grep -oE '\("[A-Za-z0-9_]+", *[0-9]+\)' |
    sed -E 's/\("([A-Za-z0-9_]+)", *([0-9]+)\)/\1:\2/')

  total=$(printf '%s' "$pairs" | grep -c . || true)
  uniq_n=$(printf '%s' "$pairs" | sort -u | grep -c . || true)

  short=$(printf '%s' "$f" | sed 's#^CatCrypt/Crypto/##')

  if [ "$total" -eq 0 ]; then
    printf '%-52s | %-7s | %s\n' "$short" "0" "empty"
  elif [ "$total" -eq "$uniq_n" ]; then
    printf '%-52s | %-7s | %s\n' "$short" "$total" "distinct"
  else
    printf '%-52s | %-7s | %s\n' "$short" "$total" "COLLISION"
    echo ""
    echo "  Repeated (base, offset) in $f:"
    printf '%s\n' "$pairs" | sort | uniq -d | sed 's/^/    /'
    FAILED=$((FAILED + 1))
  fi
done

printf -- '-----------------------------------------------------+---------+--------\n'
echo ""

if [ "$FAILED" -gt 0 ]; then
  echo "FAIL: $FAILED outStoreMap definition(s) name the same cell twice."
  echo "      The later store overwrites the earlier one, so that output"
  echo "      carries the wrong binding's value and no other check catches it."
  echo "RESULT: FAIL"
  exit 1
fi

echo "OK: every outStoreMap names distinct cells."
echo "RESULT: OK"
