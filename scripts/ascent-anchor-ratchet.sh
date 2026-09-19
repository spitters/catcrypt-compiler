#!/usr/bin/env bash
# Ascent-anchor ratchet.
#
# An ascent theorem relates a source program to a target computation. It says
# something about what we ship only when its target side is tied to the shipped
# artifact. Two ties count:
#
#   descent  the module welds onto a descent result (`legWeld`, a `keystone_*`
#            lemma, `rustToJasminCom_endToEnd`, `robustCompilation_source_to_x86`,
#            `com_arm_e2e`, `com_riscv_e2e`), so its target is the program the
#            verified compiler produces;
#   bytes    the module states its result over the encoded bytes (`encodeJBlock`,
#            `decodeJStream`, a `*Bytes_correct` theorem).
#
# A module also counts as anchored when a module that (transitively) imports it
# is anchored: its lemmas feed an anchored result.
#
# Everything else is unanchored and must be listed in
# scripts/ascent-anchor-baseline.txt with a reason. The unanchored count may
# fall, never rise; the bytes count may rise, never fall.
#
# LIMITS, so the number is not read for more than it says. This is a provenance
# gate, not a vacuity gate: it shows a theorem talks about the shipped artifact,
# not that its precondition is satisfiable at a reachable state, nor that its
# specification is independent of the program's own denotation (the
# model-vacuity ratchet and the satisfiability lemmas carry that). "Anchored at
# the bytes" also stops at `encodeJBlock`: the `.s` or `.o` file is written by an
# emitter run, not by a theorem, and for the AT&T text path the assembler and
# `renderLprogAtt` are trusted.
#
# Usage: bash scripts/ascent-anchor-ratchet.sh [--list | --record]
set -uo pipefail
cd "$(dirname "$0")/.."

baseline=scripts/ascent-anchor-baseline.txt
mode="${1:-}"

files=$(git ls-files 'CatCrypt/Crypto/SecureCompilation/Ascent/*.lean' \
                     'CatCrypt/Crypto/SecureCompilation/Ascent/**/*.lean' \
                     'CatCrypt/Hax/Ascent/*.lean' 'CatCrypt/Hax/Ascent/**/*.lean' | sort)
[ -n "$files" ] || { echo "ascent-anchor: no ascent modules found"; exit 1; }

# Module name of a path, and the reverse: both are the path with / and . swapped.
mod_of() { printf '%s' "${1%.lean}" | tr '/' '.'; }

descent_re='legWeld|keystone_[A-Za-z0-9_]+|rustToJasminCom_endToEnd|robustCompilation_source_to_x86|com_arm_e2e|com_riscv_e2e'
bytes_re='encodeJBlock|decodeJStream|[A-Za-z0-9_]*Bytes_correct'

# Code text only: drop block docstrings/comments and line comments, so a mention
# in prose does not anchor a module.
code_of() {
  sed -e '/\/-/,/-\//d' -e 's/--.*$//' "$1"
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
: > "$tmp/direct"      # module<TAB>kind   (descent|bytes|both)
: > "$tmp/imports"     # module<TAB>imported-ascent-module

for f in $files; do
  m=$(mod_of "$f")
  code=$(code_of "$f")
  d=0; b=0
  printf '%s' "$code" | grep -qE "$descent_re" && d=1
  printf '%s' "$code" | grep -qE "$bytes_re" && b=1
  if [ "$d$b" != "00" ]; then
    kind=$([ "$d$b" = "11" ] && echo both || { [ "$d" = 1 ] && echo descent || echo bytes; })
    printf '%s\t%s\n' "$m" "$kind" >> "$tmp/direct"
  fi
  grep -oE '^ *(public |private |meta |public meta )*import (all )?[A-Za-z0-9_.]+' "$f" |
    awk '{print $NF}' | while read -r i; do
      case "$i" in
        CatCrypt.Crypto.SecureCompilation.Ascent.*|CatCrypt.Hax.Ascent.*)
          printf '%s\t%s\n' "$m" "$i" >> "$tmp/imports" ;;
      esac
    done
done

# Anchored set: direct anchors, then everything an anchored module imports.
cut -f1 "$tmp/direct" | sort -u > "$tmp/anchored"
while :; do
  join -t'	' -1 1 -2 1 "$tmp/anchored" <(sort -t'	' -k1,1 "$tmp/imports") 2>/dev/null |
    cut -f2 | cat - "$tmp/anchored" | sort -u > "$tmp/anchored.next"
  cmp -s "$tmp/anchored" "$tmp/anchored.next" && break
  mv "$tmp/anchored.next" "$tmp/anchored"
done
rm -f "$tmp/anchored.next"

for f in $files; do mod_of "$f"; echo; done | grep -v '^$' | sort -u > "$tmp/all"
comm -23 "$tmp/all" "$tmp/anchored" > "$tmp/unanchored"

total=$(wc -l < "$tmp/all")
anch=$(wc -l < "$tmp/anchored")
unanch=$(wc -l < "$tmp/unanchored")
bytes=$(awk -F'\t' '$2 == "bytes" || $2 == "both"' "$tmp/direct" | wc -l)

if [ "$mode" = "--list" ]; then
  echo "# anchored ($anch of $total):"
  sort "$tmp/direct" | sed 's/^/  /'
  echo "# unanchored ($unanch):"
  sed 's/^/  /' "$tmp/unanchored"
  exit 0
fi

if [ "$mode" = "--record" ]; then
  {
    echo "# Ascent modules whose results are tied to neither a descent theorem nor the"
    echo "# encoded bytes. Each line: module<TAB>reason. Recorded by"
    echo "# scripts/ascent-anchor-ratchet.sh --record; the count may fall, never rise."
    while read -r m; do
      old=$(grep -P "^\Q$m\E\t" "$baseline" 2>/dev/null | head -1)
      if [ -n "$old" ]; then echo "$old"; else printf '%s\tno reason recorded\n' "$m"; fi
    done < "$tmp/unanchored"
  } > "$baseline.new"
  mv "$baseline.new" "$baseline"
  echo "ascent-anchor: recorded $unanch unanchored module(s) in $baseline"
  exit 0
fi

fail=0
if [ -f "$baseline" ]; then
  base_n=$(grep -vc '^#' "$baseline")
  new=$(comm -23 "$tmp/unanchored" <(grep -v '^#' "$baseline" | cut -f1 | sort -u))
  if [ -n "$new" ]; then
    echo "ASCENT-ANCHOR: module(s) tied to neither a descent theorem nor the encoded bytes,"
    echo "  and not in $baseline:"
    printf '%s\n' "$new" | sed 's/^/    /'
    echo "  -> weld the result onto a descent theorem, state it over the encoded bytes,"
    echo "     or record it with its reason: bash scripts/ascent-anchor-ratchet.sh --record"
    fail=1
  fi
  gone=$(comm -13 "$tmp/unanchored" <(grep -v '^#' "$baseline" | cut -f1 | sort -u))
  if [ -n "$gone" ]; then
    echo "ascent-anchor: $(printf '%s\n' "$gone" | wc -l) baseline entr(y/ies) now anchored; run --record to drop them."
  fi
else
  echo "ascent-anchor: no baseline; run --record to create $baseline"
  fail=1
fi

echo "ascent-anchor: $total ascent modules, $anch anchored ($bytes at the bytes), $unanch unanchored (baseline ${base_n:-0})."
[ "$fail" -eq 0 ] && echo "ascent-anchor: OK"
exit $fail
