#!/usr/bin/env bash
#
# UC plumbing ratchet.
#
# A `(composition plumbing)` docstring tag marks a security statement whose
# simulator is the adversary itself, or whose content is a metric lemma applied
# to bounds the surrounding structure already carries: a distance result in a
# UC-shaped statement. Such a theorem is a lift, not a reduction, and the tag is
# what keeps the two readable apart.
#
# This ratchet holds the plumbing-tag count monotone: it may fall, never rise. A
# new one means a bound was restated rather than derived. Tags marking a
# non-trivial simulator are not counted — those cannot be produced by a lift and
# are stated by hand legitimately.
#
# Usage:
#   scripts/uc-plumbing-ratchet.sh            # check against the baseline
#   scripts/uc-plumbing-ratchet.sh --list     # print the tagged sites
#   scripts/uc-plumbing-ratchet.sh --accept   # lower the baseline to current
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
BASELINE="scripts/uc-plumbing-baseline.txt"
mode="${1:-check}"

# The tag is counted whether or not a docstring line-wraps it. A single-line
# grep missed nine sites where `(composition\nplumbing)` straddles a newline,
# so the count is taken over each file with newlines folded to spaces; runs of
# whitespace inside the tag collapse to one.
count_tags() {
  local total=0 n
  while IFS= read -r f; do
    n=$(tr '\n' ' ' < "$f" | grep -o "(composition[[:space:]]\+plumbing)" | wc -l | tr -d ' ')
    total=$((total + n))
  done < <(grep -rl "composition" --include='*.lean' CatCrypt/ 2>/dev/null)
  printf '%s\n' "$total"
}

current=$(count_tags)

if [ "$mode" = "--list" ]; then
  # Single-line sites with their line numbers, then the wrapped ones by file.
  grep -rn "(composition plumbing)" --include='*.lean' CatCrypt/ | cut -d: -f1,2
  while IFS= read -r f; do
    # `grep -c` already prints 0 when it finds nothing and exits 1; a `|| echo 0`
    # would append a SECOND zero and break the arithmetic below.
    one=$(grep -c "(composition plumbing)" "$f" 2>/dev/null | head -1)
    all=$(tr '\n' ' ' < "$f" | grep -o "(composition[[:space:]]\+plumbing)" | wc -l | tr -d ' ')
    [ "$all" -gt "${one:-0}" ] && echo "$f: $((all - ${one:-0})) line-wrapped tag(s)"
  done < <(grep -rl "composition" --include='*.lean' CatCrypt/ 2>/dev/null)
  echo "-- $current plumbing-tagged sites (line-wrapped included)"
  exit 0
fi

baseline=$(head -1 "$BASELINE" 2>/dev/null | tr -dc '0-9')
baseline=${baseline:-$current}

if [ "$mode" = "--accept" ]; then
  { printf '%s\n' "$current"
    printf '# `(composition plumbing)` docstring tags in CatCrypt/*.lean.\n'
    printf '# Each marks a security statement that is a lift of an assumed bound\n'
    printf '# rather than a reduction. The count may fall, never rise.\n'
  } > "$BASELINE"
  echo "baseline set to $current"
  exit 0
fi

if [ "$current" -gt "$baseline" ]; then
  echo "FAIL: plumbing-tagged security theorems rose ($baseline -> $current)."
  echo "A statement tagged this way restates a bound it was handed. Derive the"
  echo "bound, or state the lift as what it is and leave the count where it was."
  exit 1
fi

if [ "$current" -lt "$baseline" ]; then
  echo "OK: plumbing-tagged count fell ($baseline -> $current). Run --accept to lower the baseline."
else
  echo "OK: $current plumbing-tagged UC theorems (baseline $baseline)."
fi
