#!/usr/bin/env bash
# Proof-cost ratchet.
#
# Two costs a proof can pay to the build rather than to the reader. Each is a
# MONOTONE NON-INCREASING dimension: the check FAILS when the count GROWS and
# AUTO-TIGHTENS the baseline when it SHRINKS. The current numbers are large and
# are meant to be read as a standing optimization target, not as a clean slate —
# every entry in either baseline is a place where the package buys a proof with
# build time, and lowering the count is a contribution the ratchet will record.
#
#   (1) maxHeartbeats BUMPS — occurrences of `set_option maxHeartbeats N` with N
#       above the 200000 default. A raised budget carries a slow proof instead of
#       fixing it; the fix is to extract the expensive step as an isolated lemma
#       over abstract inputs, so the cost is paid once and the caller elaborates
#       against a signature. A lowered or removed bump shrinks the count; a new
#       one requires a deliberate re-baseline.
#
#   (2) native_decide OCCURRENCES — each runs a computation inside the proof
#       build, adds the `ofReduceBool` compiler-trust axiom to whatever depends
#       on it, and its native compilation is a large part of what makes a
#       full-library build exceed a 16 GB machine. A KAT (`run(input) = output`)
#       or a `strContains … = true` text check is a test, not a theorem — it
#       belongs in an external harness, leaving the structural
#       `denote(emitted) = spec` theorem in the module. The construct is
#       legitimate for a general lemma discharged by finite computation over a
#       bounded type.
#
# Both counts are taken over CatCrypt/ AFTER stripping `/- … -/` block and `-- …`
# line comments, so prose mentions (this file's own doc, a docstring) don't count.
#
# Usage: bash scripts/proof-cost-ratchet.sh
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

MH_BASELINE_FILE="scripts/maxheartbeats-baseline.txt"
ND_BASELINE_FILE="scripts/native-decide-baseline.txt"

MH_TMP="$(mktemp)"; ND_TMP="$(mktemp)"
trap 'rm -f "$MH_TMP" "$ND_TMP"' EXIT

# --- Dimension 1: maxHeartbeats bumps (> 200000), comment-stripped ---
for f in $(grep -rlE 'maxHeartbeats' --include='*.lean' CatCrypt/ 2>/dev/null || true); do
  perl -0777 -ne '
    s{/-.*?-/}{}gs; s{--[^\n]*}{}g;
    while (/set_option\s+maxHeartbeats\s+(\d+)/g) { print "'"$f"'\n" if $1 > 200000; }
  ' "$f"
done | sort > "$MH_TMP"
MH_CURRENT="$(grep -c . "$MH_TMP" || true)"

# --- Dimension 2: native_decide occurrences, comment-stripped ---
for f in $(grep -rl 'native_decide' --include='*.lean' CatCrypt/ 2>/dev/null || true); do
  N="$(perl -0777 -ne 's{/-.*?-/}{}gs; s{--[^\n]*}{}g; my $c = () = /native_decide/g; print $c;' "$f")"
  # `cmd && action` as the loop's last statement makes the loop exit non-zero
  # whenever the final file has no code-level hit; under `set -e` with the loop
  # feeding a pipe, that aborts the script before either dimension is compared.
  if [ "${N:-0}" -gt 0 ]; then printf '%s\t%s\n' "$N" "$f"; fi
done | sort -k2 > "$ND_TMP"
ND_CURRENT="$(awk -F'\t' '{s+=$1} END {print s+0}' "$ND_TMP")"

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
    echo "      Fix the proof (extract-lemma for heartbeats / move the KAT to a"
    echo "      harness for native_decide), or re-baseline deliberately."
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
ratchet "native_decide occurrences" "$ND_CURRENT" "$ND_BASELINE_FILE" "$ND_TMP" \
  "native_decide occurrences over CatCrypt/ (\"<count>\t<file>\", tab-separated). Goal: burn down."

[ "$fail" -eq 0 ] && echo "OK: proof-cost ratchets satisfied." || exit 1
