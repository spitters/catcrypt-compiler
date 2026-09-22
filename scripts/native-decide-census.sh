#!/usr/bin/env bash
# Classify every `native_decide` site by what would be needed to remove it.
#
# The occurrence count alone is misleading: most sites are parameter arithmetic
# or size constants, which a kernel-targeted compiler has nothing to offer. This
# script separates the sites that are genuinely compute-bound from the ones that
# a cheaper tactic closes.
#
# Classes:
#   prime   `Nat.Prime` — a Pratt certificate closes it
#   smoke   a structural check (`.length > 0`, `.isSome`, `≠ []`) — no arithmetic
#   trivia  the goal mentions only numerals and projections — `decide`/`omega`
#   compute everything else: the addressable set for a kernel backend
#
# Usage:  scripts/native-decide-census.sh [--list-compute]
set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

LIST=${1:-}
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

# One record per site: file:line:statement-text. The statement is the theorem or
# example line, which is the line carrying `native_decide` or the nearest `:=`
# above it.
grep -rn --include=*.lean "native_decide" CatCrypt 2>/dev/null |
  grep -v "^\s*--" |
  while IFS= read -r hit; do
    f=${hit%%:*}; rest=${hit#*:}; ln=${rest%%:*}
    # take the statement as the 3 lines ending at the hit, joined
    stmt=$(sed -n "$((ln>2 ? ln-2 : 1)),${ln}p" "$f" 2>/dev/null | tr '\n' ' ')
    case "$stmt" in
      *"--"*native_decide*) continue ;;
    esac
    cls=compute
    case "$stmt" in
      *Nat.Prime*|*".Prime "*)            cls=prime  ;;
      *".length >"*|*".isSome"*|*"≠ []"*|*".length ="*|*"!= []"*) cls=smoke ;;
    esac
    if [ "$cls" = compute ]; then
      # trivia: no function application on the left of `=` beyond projections,
      # i.e. the statement's tokens are numerals, dotted names and operators.
      if printf '%s' "$stmt" |
           grep -qE ':[[:space:]]*[A-Za-z_.0-9]+[[:space:]]*(=|<|≤|>|≥)[[:space:]]*[0-9]+[[:space:]]*:=' ; then
        cls=trivia
      elif printf '%s' "$stmt" |
           grep -qE ':[[:space:]]*[A-Za-z_.0-9]+[[:space:]]*=[[:space:]]*[A-Za-z_.0-9]+[[:space:]]*[*+-][[:space:]]*[A-Za-z_.0-9]+[[:space:]]*:=' ; then
        cls=trivia
      fi
    fi
    printf '%s\t%s:%s\t%s\n' "$cls" "$f" "$ln" "$(printf '%s' "$stmt" | cut -c1-110)"
  done > "$tmp"

echo "native_decide census — $(wc -l < "$tmp") sites"
echo
awk -F'\t' '{c[$1]++} END{for (k in c) printf "  %-8s %5d\n", k, c[k]}' "$tmp" | sort -k2 -rn
echo
echo "compute-class sites by file:"
awk -F'\t' '$1=="compute"{split($2,a,":"); print a[1]}' "$tmp" | sort | uniq -c | sort -rn | head -20

if [ "$LIST" = "--list-compute" ]; then
  echo
  echo "compute-class sites:"
  awk -F'\t' '$1=="compute"{printf "  %s\n      %s\n", $2, $3}' "$tmp"
fi
