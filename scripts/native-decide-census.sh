#!/usr/bin/env bash
# Classify every `native_decide` site by what would be needed to remove it.
#
# The occurrence count alone is misleading in two ways. Prose mentions the
# tactic by name — docstrings and line comments that discuss it are not uses —
# and among the real uses most are size constants, structural checks on a
# concrete program, or single-word arithmetic, none of which a kernel-targeted
# compiler has anything to offer.
#
# A site is counted only when `native_decide` survives comment stripping: block
# comments `/- -/` (nested, including docstrings `/-- -/`) and line comments
# `--` are removed before the scan.
#
# Classes:
#   prime   `Nat.Prime` — a Pratt certificate closes it
#   smoke   a structural check (`.length`, `.isSome`, `≠ []`) — no arithmetic
#   trivia  the goal relates numerals and projections — `decide`/`omega`
#   strtab  a lookup keyed by a String literal: blocked on String equality
#           reduction, not arithmetic
#   syntax  a predicate over a concrete datatype value: a `match` on
#           constructors, or a list/option of them, decided by case analysis
#   word    concrete machine-word arithmetic: a `BitVec`/`UInt` equation, or
#           any statement carrying a hexadecimal literal, where `decide` times
#           out on 64-bit words but `bv_decide` applies
#   compute everything else: the addressable set for a kernel backend
#
# Classification is by statement text over the three stripped lines ending at
# the site, so it is conservative in one direction: a genuine computation whose
# statement happens to carry a string literal or a hex constant lands in
# `strtab` or `word`. The `compute` count is therefore an upper bound on a
# class that is itself an upper bound on what a `Nat` backend addresses — the
# class still holds compiler-pass evaluations over concrete programs, which are
# compute-bound but are not arithmetic over a finite carrier.
#
# Usage:  scripts/native-decide-census.sh [--list-compute|--list-<class>]
set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

LIST=${1:-}
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

# Strip comments file by file, keeping line numbers, and emit one record per
# surviving `native_decide` as  file<TAB>line<TAB>statement, where the statement
# is the three stripped lines ending at the hit.
strip_and_scan() {
  awk '
    function flush_ctx(   s) {
      s = prev2 " " prev1 " " cur
      gsub(/[ \t]+/, " ", s)
      return s
    }
    BEGIN { depth = 0 }
    {
      line = $0
      out = ""
      i = 1
      n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth > 0) {
          if (two == "-/") { depth--; i += 2; continue }
          if (two == "/-") { depth++; i += 2; continue }
          i++
          continue
        }
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "--") { break }          # line comment: drop the rest
        out = out substr(line, i, 1)
        i++
      }
      cur = out
      if (index(cur, "native_decide") > 0)
        printf "%s\t%d\t%s\n", FILENAME, FNR, substr(flush_ctx(), 1, 200)
      prev2 = prev1
      prev1 = cur
    }
  ' "$@"
}

mapfile -t files < <(git ls-files 'CatCrypt/**/*.lean' 'CatCrypt/*.lean' 2>/dev/null)
[ ${#files[@]} -gt 0 ] || { echo "native-decide-census: no Lean files under CatCrypt" >&2; exit 2; }

strip_and_scan "${files[@]}" |
  while IFS=$'\t' read -r f ln stmt; do
    cls=compute
    case "$stmt" in
      *Nat.Prime*|*".Prime "*)
        cls=prime ;;
      *".length"*|*".isSome"*|*".isNone"*|*"≠ []"*|*"!= []"*|*".contains"*|*".isEmpty"*)
        cls=smoke ;;
      *'"'*'"'*)
        cls=strtab ;;
      *"match "*|*"= true"*|*"= false"*|*"= some "*|*"= none"*|*"== "*)
        cls=syntax ;;
      *0x*|*BitVec*|*UInt8*|*UInt16*|*UInt32*|*UInt64*)
        cls=word ;;
    esac
    # An equation whose right side is a bare constructor decides a datatype
    # value, whatever the left side computes.
    if [ "$cls" = compute ] &&
       printf '%s' "$stmt" | grep -qE '=[[:space:]]*\.[A-Za-z]'; then
      cls=syntax
    fi
    if [ "$cls" = compute ]; then
      # trivia: a name or projection related to a numeral, or a product of two
      # names, with no function application on either side.
      if printf '%s' "$stmt" |
           grep -qE ':[[:space:]]*[A-Za-z_.0-9]+[[:space:]]*(=|<|≤|>|≥)[[:space:]]*[0-9x]+[[:space:]]*:=' ; then
        cls=trivia
      elif printf '%s' "$stmt" |
           grep -qE ':[[:space:]]*[A-Za-z_.0-9]+[[:space:]]*=[[:space:]]*[A-Za-z_.0-9]+[[:space:]]*[*+-][[:space:]]*[A-Za-z_.0-9]+[[:space:]]*:=' ; then
        cls=trivia
      fi
    fi
    printf '%s\t%s:%s\t%s\n' "$cls" "$f" "$ln" "$(printf '%s' "$stmt" | cut -c1-110)"
  done > "$tmp"

echo "native_decide census — $(wc -l < "$tmp") sites (comments stripped)"
echo
awk -F'\t' '{c[$1]++} END{for (k in c) printf "  %-8s %5d\n", k, c[k]}' "$tmp" | sort -k2 -rn
echo
echo "compute-class sites by file:"
awk -F'\t' '$1=="compute"{split($2,a,":"); print a[1]}' "$tmp" | sort | uniq -c | sort -rn | head -20

case "$LIST" in
  --list-*)
    want=${LIST#--list-}
    echo
    echo "$want-class sites:"
    awk -F'\t' -v w="$want" '$1==w{printf "  %s\n      %s\n", $2, $3}' "$tmp"
    ;;
esac
