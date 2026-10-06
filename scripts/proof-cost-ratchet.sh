#!/usr/bin/env bash
# Proof-cost ratchet: raised `maxHeartbeats` budgets.
#
# One MONOTONE NON-INCREASING count: the check FAILS when it GROWS and AUTO-TIGHTENS
# the baseline when it SHRINKS. Every entry of the baseline is a place where the
# package buys a proof with build time, and lowering the count is a contribution the
# ratchet records.
#
#   maxHeartbeats BUMPS — occurrences of `set_option maxHeartbeats N` with N above
#   the 200000 default. A raised budget carries a slow proof instead of fixing it;
#   the fix is to extract the expensive step as an isolated lemma over abstract
#   inputs, so the cost is paid once and the caller elaborates against a signature.
#   A lowered or removed bump shrinks the count; a new one requires a deliberate
#   re-baseline.
#
# The count is taken over CatCrypt/ AFTER stripping `/- … -/` block and `-- …` line
# comments, so a mention in prose does not count. Baseline:
# scripts/maxheartbeats-baseline.txt (first line the count, then one path per
# occurrence).
#
# `native_decide` is not counted here. The project accepts it, and a use is replaced
# only when it is measured slow or memory-heavy. scripts/check-build-cost.sh still
# refuses a new `native_decide` in a module that imports the reflection or emit
# front, where it compiles the whole pipeline natively. The per-file data in
# scripts/native-decide-baseline.txt is kept and is no longer read by this script.
#
# Usage: bash scripts/proof-cost-ratchet.sh
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

MH_BASELINE_FILE="scripts/maxheartbeats-baseline.txt"

MH_TMP="$(mktemp)"
trap 'rm -f "$MH_TMP"' EXIT

# maxHeartbeats bumps (> 200000), comment-stripped
for f in $(grep -rlE 'maxHeartbeats' --include='*.lean' CatCrypt/ 2>/dev/null || true); do
  perl -0777 -ne '
    s{/-.*?-/}{}gs; s{--[^\n]*}{}g;
    while (/set_option\s+maxHeartbeats\s+(\d+)/g) { print "'"$f"'\n" if $1 > 200000; }
  ' "$f"
done | sort > "$MH_TMP"
MH_CURRENT="$(grep -c . "$MH_TMP" || true)"

fail=0

ratchet() {  # $1=name $2=current $3=baseline_file $4=tmp(sorted files) $5=count-comment
  local name="$1" cur="$2" bfile="$3" tmp="$4"
  local base
  base="$(grep -m1 -oE '^[0-9]+' "$bfile" 2>/dev/null || echo "")"
  if [ -z "$base" ]; then
    echo "$name: seeding baseline to current ($cur)."
    { echo "$cur"; echo "# $5"; echo "# Frozen baseline; auto-tightened by scripts/proof-cost-ratchet.sh."; cat "$tmp"; } > "$bfile"
    return 0
  fi
  echo "$name: current=$cur  baseline=$base"
  if [ "$cur" -gt "$base" ]; then
    echo ""
    echo "FAIL: $name GREW ($base -> $cur)."
    echo "      New offender file(s) (not in the baseline):"
    comm -13 <(grep -E '^CatCrypt/|	CatCrypt/' "$bfile" 2>/dev/null | sed -E 's/^[0-9]+\t//' | sort) \
             <(sed -E 's/^[0-9]+\t//' "$tmp" | sort) | sed 's/^/        /'
    echo "      Fix the proof (extract the expensive step as a lemma over abstract"
    echo "      inputs), or re-baseline deliberately."
    fail=1
    return 0
  fi
  if [ "$cur" -lt "$base" ]; then
    echo "Good — $name SHRANK ($base -> $cur). Auto-tightening."
    { echo "$cur"; echo "# $5"; echo "# Frozen baseline; auto-tightened by scripts/proof-cost-ratchet.sh."; cat "$tmp"; } > "$bfile"
  fi
}

ratchet "maxHeartbeats bumps (>200000)" "$MH_CURRENT" "$MH_BASELINE_FILE" "$MH_TMP" \
  "maxHeartbeats bumps > 200000 over CatCrypt/ (one line per occurrence, file path). Goal: 0."

[ "$fail" -eq 0 ] && echo "OK: proof-cost ratchet satisfied." || exit 1
