#!/usr/bin/env bash
# Kernel-reduction cost model for the `natKernelDialect` backend.
#
# Each file in scripts/kernel-cost/ forces kernel work with a
# `theorem ... : decide (f input = 0) = false := rfl`, so the reduction the
# competition and the `decide`/`rfl` proof path pay is the reduction measured
# here. The files import nothing, so a run needs no build and no Mathlib: the
# toolchain's `lean` binary is enough, and `Z_empty.lean` measures the startup
# to subtract.
#
# Reported cost is wall time minus that baseline, divided by the operation
# count declared in OPS below. It covers the elaborator's whnf and the kernel's
# re-check, so absolute figures are about twice the kernel's own; the ratios
# between rows are the content.
#
# Usage:
#   scripts/kernel-cost-bench.sh              # measure, print the table
#   scripts/kernel-cost-bench.sh --check      # measure and compare to baseline
#   scripts/kernel-cost-bench.sh --write      # measure and rewrite the baseline
#   LEAN_BIN=/path/to/lean scripts/kernel-cost-bench.sh   # a different toolchain
#
# --check fails when a row is more than TOL_PCT slower than its baseline. The
# box is shared, so it takes the minimum of REPS runs and allows a wide
# tolerance; this catches a representation regression, not a few percent.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

DIR=scripts/kernel-cost
BASELINE=scripts/kernel-cost-baseline.tsv
LEAN_BIN="${LEAN_BIN:-lean}"
REPS="${REPS:-3}"
TOL_PCT="${TOL_PCT:-35}"

# file:operations — the count of arithmetic operations the file's kernel work
# performs, used to normalise. Keep in step with the files themselves.
OPS="
N_nat:9000
U_uint64:9000
A_direct:9000
B_string:12000
E_wide:12000
F_struct_bv:12000
F_struct_nat:12000
G_bignat:3000
M_modmul:5000
"

command -v "$LEAN_BIN" >/dev/null 2>&1 || { echo "kernel-cost: no lean binary ($LEAN_BIN)" >&2; exit 2; }

run_min() {
  local f=$1 best="" t
  for _ in $(seq "$REPS"); do
    t=$( { /usr/bin/time -f '%e' "$LEAN_BIN" "$DIR/$f.lean" >/dev/null; } 2>&1 | tail -1 )
    case "$t" in ''|*[!0-9.]*) echo "kernel-cost: $f did not run cleanly: $t" >&2; return 1 ;; esac
    if [ -z "$best" ] || awk -v a="$t" -v b="$best" 'BEGIN{exit !(a<b)}'; then best=$t; fi
  done
  echo "$best"
}

base=$(run_min Z_empty) || exit 1
echo "baseline (startup): ${base}s   lean: $(command -v "$LEAN_BIN")   reps: $REPS"
printf '%-14s %10s %12s\n' file seconds us_per_op

tmp=$(mktemp); rc=0
for row in $OPS; do
  f=${row%%:*}; ops=${row#*:}
  [ -f "$DIR/$f.lean" ] || { echo "kernel-cost: missing $DIR/$f.lean" >&2; rc=2; continue; }
  t=$(run_min "$f") || { rc=2; continue; }
  read -r work us < <(awk -v t="$t" -v b="$base" -v n="$ops" \
    'BEGIN{w=t-b; if(w<0)w=0; printf "%.2f %.0f\n", w, w*1000000/n}')
  printf '%-14s %10s %12s\n' "$f" "$work" "$us"
  printf '%s\t%s\n' "$f" "$us" >> "$tmp"
done

if [ "${1:-}" = "--write" ]; then
  { echo "# file<TAB>us_per_op — see scripts/kernel-cost-bench.sh"; cat "$tmp"; } > "$BASELINE"
  echo "kernel-cost: baseline written to $BASELINE"
elif [ "${1:-}" = "--check" ]; then
  [ -f "$BASELINE" ] || { echo "kernel-cost: no baseline; run --write" >&2; rm -f "$tmp"; exit 2; }
  while IFS=$'\t' read -r f us; do
    case "$f" in \#*|'') continue ;; esac
    old=$(awk -F'\t' -v f="$f" '$1==f{print $2}' "$BASELINE")
    [ -n "$old" ] || { echo "kernel-cost: $f has no baseline row"; rc=2; continue; }
    if awk -v n="$us" -v o="$old" -v p="$TOL_PCT" 'BEGIN{exit !(n > o*(1+p/100))}'; then
      echo "kernel-cost: REGRESSION $f ${old} -> ${us} us/op (tolerance ${TOL_PCT}%)"
      rc=1
    fi
  done < "$tmp"
  [ "$rc" = 0 ] && echo "kernel-cost: every row within ${TOL_PCT}% of baseline"
fi
rm -f "$tmp"
exit $rc
