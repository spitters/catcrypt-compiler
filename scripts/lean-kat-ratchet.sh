#!/usr/bin/env bash
# Known-answer tests do not belong in Lean: a theorem that checks computed
# values on fixed vectors by `native_decide` or `decide` is a KAT, and it runs
# at every build — and, as a closed term, at the start-up of every executable
# that links its module. KATs go to the external harnesses (bench/, crates/).
#
# This ratchet counts theorems and examples closed by `native_decide`/`decide`
# whose statement iterates over a vector list (`.all (fun`, `List.range N`) or
# compares a computed result with `== some`. Structural `native_decide` gates
# (`frontCom.isSome`, byte-length pins) do not match and are allowed.
#
#   scripts/lean-kat-ratchet.sh            check against the baseline (CI)
#   scripts/lean-kat-ratchet.sh --list     print every matching theorem
#   scripts/lean-kat-ratchet.sh --update   rewrite the baseline (only downward)
#
# Baseline: scripts/lean-kat-baseline.txt (first line = count). It may fall,
# never rise.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
BASE=scripts/lean-kat-baseline.txt

list() {
  { git ls-files -z '*.lean' | xargs -0 awk '
    FNR == 1 { name = ""; stmt = ""; instmt = 0 }
    /^(private |protected )?(theorem|example|lemma)[ \n]/ {
      name = FILENAME ":" FNR; stmt = ""; instmt = 1 }
    name != "" && instmt { stmt = stmt " " $0 }
    name != "" && /:= *by|:=$/ { instmt = 0 }
    name != "" && /(native_decide|by decide|decide \+kernel)/ {
      if (stmt ~ /\.all \(fun|List\.range [0-9]+\)?\.all|== some/) print name
      name = "" }
    /^$/ { name = "" }' 2>/dev/null || true; } | sort -u
}

case "${1:-}" in
  --list) list; exit 0 ;;
esac

cur=$(list | wc -l)
base=$(head -1 "$BASE" 2>/dev/null || echo "$cur")

if [ "${1:-}" = "--update" ]; then
  if [ "$cur" -gt "$base" ]; then
    echo "lean-kat-ratchet: refusing to raise the baseline ($base -> $cur)" >&2; exit 1
  fi
  echo "$cur" > "$BASE"; echo "lean-kat-ratchet: baseline $base -> $cur"; exit 0
fi

echo "In-Lean known-answer tests: current=$cur baseline=$base"
if [ "$cur" -gt "$base" ]; then
  echo "FAIL: a new in-Lean KAT. Move the vector check to the external harness;" >&2
  echo "a claim for every input is a structural lemma, not a vector battery." >&2
  git diff --name-only HEAD -- '*.lean' 2>/dev/null | head -20 | sed 's/^/  changed: /' >&2
  exit 1
fi
if [ "$cur" -lt "$base" ]; then
  echo "lean-kat-ratchet: count fell; tighten with scripts/lean-kat-ratchet.sh --update"
fi
