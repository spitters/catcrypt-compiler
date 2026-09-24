#!/usr/bin/env bash
# A known-answer check in a Lean source runs at every build, so it is written
# only with the budgeted commands `#kat` (compiled evaluation) and `#kat_kernel`
# (`decide +kernel`) of CatCryptCore.Tactics.KatGuard: each runs under a low
# heartbeat budget and a millisecond budget and fails the build at its own line
# when it exceeds either. Vector batteries that do not fit that budget go to the
# external harnesses (bench/, crates/).
#
# This ratchet counts two forms that carry no budget:
#
#   theorems  theorems and examples closed by `native_decide`/`decide` whose
#             statement iterates over a vector list (`.all (fun`,
#             `List.range N`) or compares a computed result with `== some`.
#             Structural `native_decide` gates (`frontCom.isSome`, byte-length
#             pins) do not match and are allowed.
#   evals     lines that start with a bare `#guard` or `#eval` (`#guard_msgs`
#             excluded).
#
#   scripts/lean-kat-ratchet.sh            check against the baseline (CI)
#   scripts/lean-kat-ratchet.sh --list     print every matching site
#   scripts/lean-kat-ratchet.sh --update   rewrite the baseline (only downward)
#
# Baseline: scripts/lean-kat-baseline.txt, line 1 the theorem count, line 2
# the eval count. Each may fall, never rise.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
BASE=scripts/lean-kat-baseline.txt

# The tracked Lean files that exist in the working tree. A path the index still lists
# after its file was deleted would make awk abort the rest of its batch, so the
# counts would depend on the state of the index.
lean_files() {
  git ls-files -z '*.lean' | while IFS= read -r -d '' f; do
    [ -f "$f" ] && printf '%s\0' "$f"
  done
}

list_thms() {
  { lean_files | xargs -0 -r awk '
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

list_evals() {
  { lean_files | xargs -0 -r grep -nE '^\s*#(guard|eval)\b' 2>/dev/null \
      | grep -vE ':\s*#guard_msgs' | cut -d: -f1,2 || true; } | sort -u
}

case "${1:-}" in
  --list) list_thms; list_evals; exit 0 ;;
esac

cur_t=$(list_thms | wc -l)
cur_e=$(list_evals | wc -l)
base_t=$(sed -n 1p "$BASE" 2>/dev/null); base_t=${base_t:-$cur_t}
base_e=$(sed -n 2p "$BASE" 2>/dev/null); base_e=${base_e:-$cur_e}

if [ "${1:-}" = "--update" ]; then
  if [ "$cur_t" -gt "$base_t" ] || [ "$cur_e" -gt "$base_e" ]; then
    echo "lean-kat-ratchet: refusing to raise the baseline" \
      "(theorems $base_t -> $cur_t, evals $base_e -> $cur_e)" >&2; exit 1
  fi
  printf '%s\n%s\n' "$cur_t" "$cur_e" > "$BASE"
  echo "lean-kat-ratchet: baseline theorems $base_t -> $cur_t, evals $base_e -> $cur_e"
  exit 0
fi

echo "Unbudgeted in-Lean known-answer checks: theorems current=$cur_t baseline=$base_t," \
  "evals current=$cur_e baseline=$base_e"
fail=0
if [ "$cur_t" -gt "$base_t" ]; then
  echo "FAIL: a new vector-battery theorem. State it with #kat_kernel under a low" >&2
  echo "heartbeat budget, or move it to the external harness." >&2
  fail=1
fi
if [ "$cur_e" -gt "$base_e" ]; then
  echo "FAIL: a new bare #guard/#eval. Write it as #kat (import" >&2
  echo "CatCryptCore.Tactics.KatGuard), which runs it under a time and heartbeat budget." >&2
  fail=1
fi
if [ "$fail" -eq 1 ]; then
  git diff --name-only HEAD -- '*.lean' 2>/dev/null | head -20 | sed 's/^/  changed: /' >&2
  exit 1
fi
if [ "$cur_t" -lt "$base_t" ] || [ "$cur_e" -lt "$base_e" ]; then
  echo "lean-kat-ratchet: count fell; tighten with scripts/lean-kat-ratchet.sh --update"
fi
