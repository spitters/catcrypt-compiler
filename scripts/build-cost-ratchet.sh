#!/usr/bin/env bash
# Per-module elaboration cost: a measured ratchet over `lean --profile`.
#
# The syntactic proxies for an expensive proof — a `maxHeartbeats` bump above the
# default, a `native_decide` — are things an author writes down. A proof can be
# ruinously slow with neither, and nothing notices: a full-library build that is
# OOM-killed names no module, and the heavy ones then have to be found by diffing
# olean presence by hand. This measures instead.
#
# ## Which number is the cost, and which numbers only look like it
#
# Three candidate metrics were measured on this repo before picking one.
#
#   lake's `Built <Module> (Ns)` — wall clock INCLUDING CONTENTION. Under a
#     parallel build several modules run at once, finish together, and all report
#     the same figure; five modules of very different weight each reported `(14s)`
#     in one run. A screening signal, never a cost.
#
#   process wall clock (`/usr/bin/time lake env lean`) — dominated by IMPORT
#     LOADING, not by the module's proofs. Loading a ~3 GB olean closure is ~8s
#     while the module's own elaboration is ~1s, so proof cost is noise on top.
#     Measured: appending 400 real tactic invocations moved this number 0.5s,
#     inside its own ~31% run-to-run variance. Nearly blind to what it is for.
#
#   peak RSS — a function of the IMPORT CLOSURE, not of proof difficulty. Three
#     modules sharing a closure measured 3025/3025/3045 MB while doing 3.6s to
#     10.1s of work. Worth watching (it catches a module acquiring a heavy new
#     dependency) but it is not slowness.
#
#   `lean --profile`'s `elaboration` line — the module's own work, separated from
#     `import` by Lean itself. Stable across runs (~7% variance) and sensitive to
#     the thing being ratcheted: the same 400-tactic perturbation moved it +24%.
#     THIS is the ratcheted metric.
#
# So: ratchet `elaboration`; record `import` and peak RSS as context; treat
# lake's log figures as a way to pick candidates and nothing more.
#
# Usage:
#   bash scripts/build-cost-ratchet.sh screen build.log
#   bash scripts/build-cost-ratchet.sh measure CatCrypt/Foo/Bar.lean
#   bash scripts/build-cost-ratchet.sh record  CatCrypt/Foo/Bar.lean
#   bash scripts/build-cost-ratchet.sh check
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

BASELINE="scripts/build-cost-baseline.tsv"
TACTICS="scripts/build-cost-tactics.tsv"

# Regression margins on ELABORATION only. Measured noise is ~7%; 140% plus an
# absolute floor keeps a small module's jitter from failing the build.
REL_FACTOR="140"   # percent of baseline elaboration
ABS_MS="300"       # milliseconds

# Absolute ceiling. Measured over a comparable Lean corpus, elaboration is
# min 1 ms, median 44 ms, p90 188 ms, p99 1780 ms. So a second is ~23x the median
# and puts a module in the slowest few percent: slow enough that it should carry a
# reason. `check` reports these whatever the baseline says, because a module that
# was always slow is not thereby fine.
#
# Justify one in its module docstring — what is expensive and why it is the cheapest
# correct form — or fix it. The usual cause is a proof reducing a large term rather
# than reasoning about it; the repair is to extract the expensive step as a lemma
# over abstract inputs.
#
# Note on metrics: cycles would be steadier than milliseconds, but a host with
# `perf_event_paranoid` set high forbids perf events without sudo. Elaboration ms,
# at ~7% measured variance, is the best generally available figure.
SLOW_MS="${SLOW_MS:-1000}"
# Import-closure ceiling, reported by `check` alongside the elaboration ceiling.
# 20 s is well above the median here and picks out the genuinely deep closures
# rather than every Mathlib-importing module.
IMPORT_MS="${IMPORT_MS:-20000}"
OVER_IMPORT=""

usage() {
  cat <<'EOF'
usage:
  build-cost-ratchet.sh screen <build.log>      rank modules by reported wall clock (never fails)
  build-cost-ratchet.sh measure <Module.lean>   elaboration vs import, plus the phase breakdown
  build-cost-ratchet.sh record  <Module.lean>   measure, then write/update its baseline row
  build-cost-ratchet.sh check                   re-measure every baselined module; fail on regression
  build-cost-ratchet.sh coverage                fail if the UNMEASURED module count grew (no build)
EOF
  exit 2
}

# `lean --profile` prints a summary block of "\t<phase> <value><unit>" lines with
# mixed units (ms / s). Echo one phase's value normalised to milliseconds.
profile_phase() {
  local prof="$1" phase="$2"
  printf '%s\n' "$prof" | awk -v want="$phase" '
    /^\t/ {
      line = $0; sub(/^\t/, "", line)
      if (match(line, / [0-9.]+(ms|s)$/) == 0) next
      val = substr(line, RSTART + 1); name = substr(line, 1, RSTART - 1)
      if (name != want) next
      if (val ~ /ms$/) { sub(/ms$/, "", val); printf "%.0f\n", val + 0 }
      else            { sub(/s$/,  "", val); printf "%.0f\n", val * 1000 }
      exit
    }'
}

# Measure one module alone. Echoes "<elabMs>\t<importMs>\t<peakMB>".
# Repeats, exclusion and pinning are not fussiness — without them this number is
# not reproducible. The same unchanged file across three single-sample runs
# measured 934 / 143 / 1150 ms, and on a second file 2390 / 380 / 2480 ms. A
# ratchet cannot gate on a figure that moves 8x on identical input.
#
# Three causes, one remedy each:
#   * a concurrent build steals CPU -> take a flock, so a measurement never
#     overlaps a build;
#   * page-cache state varies, and the import phase dominates (a module measured
#     5060 ms of import against 143 ms of its own elaboration) -> repeat, and let
#     the first run warm the cache;
#   * lake's worker count varies with load     -> pin cores and set
#     LEAN_NUM_THREADS so every sample sees one worker.
#
# Then report the MINIMUM, not the mean or a single shot: contention, faulting
# and scheduling only ever ADD time, so the smallest sample is the closest
# estimate of the module's intrinsic cost and is the robust statistic here.
# Peak RSS takes the MAXIMUM instead — for memory the worst case is what OOMs.
BC_REPEATS="${BC_REPEATS:-3}"
BC_CORES="${BC_CORES:-0-1}"
BC_LOCK="${TMPDIR:-/tmp}/catcrypt-heavy-build.lock"

measure_one() {
  local target="$1" prof rss elab imp i
  local best_elab="" best_imp="" max_rss=0
  exec 8>"$BC_LOCK"
  if ! flock -w 5 8; then
    echo "  (build-cost: a heavy build holds the lock; measuring anyway — treat this number as noisy)" >&2
  fi
  for i in $(seq 1 "$BC_REPEATS"); do
    # NOTE the redirection: `2>&1 >/dev/null` keeps STDERR (where the profile
    # summary and the PEAKKB line go) and discards STDOUT. Lean's DIAGNOSTICS go
    # to stdout, so they are NOT in "$prof" and no grep over it can see a
    # compile error — the exit status is the only signal available here.
    prof="$(LEAN_NUM_THREADS=1 /usr/bin/time -f 'PEAKKB %M' \
      taskset -c "$BC_CORES" lake env lean --profile "$target" 2>&1 >/dev/null)"
    lean_rc=$?
    rss="$(printf '%s\n' "$prof" | awk '/^PEAKKB /{print $2}' | tail -1)"
    elab="$(profile_phase "$prof" elaboration)"
    imp="$(profile_phase "$prof" import)"
    # A file with ERRORS still yields an elaboration figure, so a missing phase
    # was never the error check: a module whose only theorem fails to elaborate
    # still records cleanly at "elaboration 1 ms". Gate on the exit status, which
    # is the only error signal reaching this function.
    if [ "$lean_rc" -ne 0 ]; then
      if [ "$i" = 1 ]; then
        echo "FAIL: $target does not compile (lean exit $lean_rc) — refusing to record a cost for it." >&2
        echo "      Re-run it directly to see the diagnostics:" >&2
        echo "        lake env lean $target" >&2
        flock -u 8 2>/dev/null; return 1
      fi
      continue
    fi
    # Lean omits a phase whose time falls under the profiler's reporting
    # threshold, so an absent `elaboration` line on an ERROR-FREE run means the
    # module is too CHEAP to register, not that it failed. Without this a module
    # elaborating in a few ms is unrecordable and therefore invisible to
    # `check` — the same blind spot, at the other end, as one too expensive to
    # measure.
    [ -z "$elab" ] && elab=0
    [ "${rss:-0}" -gt "$max_rss" ] && max_rss="$rss"
    if [ -z "$best_elab" ] || [ "$elab" -lt "$best_elab" ]; then
      best_elab="$elab"; best_imp="${imp:-0}"
    fi
  done
  flock -u 8 2>/dev/null
  printf '%s\t%s\t%s\n' "$best_elab" "${best_imp:-0}" "$(( max_rss / 1024 ))"
}

# Per-tactic cost, aggregated by tactic kind. The default `--profile` summary reports
# only whole-module phases; `-Dprofiler.threshold=N` makes Lean emit one line per
# tactic invocation above N ms, e.g.
#
#   tactic execution of Lean.Parser.Tactic.omega took 36.4ms
#   simp took 18.6ms
#   type checking took 55.9ms
#
# That is the granularity worth recording: a module summing to 288 ms can hide three
# `omega` calls at 36/13/6.6 ms, and a regression reported as "this simp went from
# 200 ms to 4 s" is actionable where "the module got 20% slower" is not. It also
# separates `type checking` from `elaboration`, which distinguishes a slow proof from
# the kernel re-checking a large term — the failure mode behind every build blowup
# traced here.
#
# Ratchet on the summed elaboration figure (~7% variance, measured); use this for
# diagnosis, since per-invocation timings are noisier.
TACTIC_THRESHOLD="${TACTIC_THRESHOLD:-5}"
profile_tactics() {
  local target="$1"
  # `-Dprofiler` writes its per-tactic lines to STDOUT, unlike `--profile`, whose
  # summary block goes to stderr (measured: 55 rows on stdout against 2 on stderr).
  # Do not copy measure_one's `2>&1 >/dev/null` here — it discards exactly this.
  lake env lean -Dprofiler=true -Dprofiler.threshold="$TACTIC_THRESHOLD" \
      "$target" 2>/dev/null \
    | sed -E 's/\x1b\[[0-9;]*[A-Za-z]//g' \
    | awk '
        # "<name> took <v>ms" / "...s", split on the literal " took " (6 chars).
        # POSIX awk here — no gawk capture arrays, same substr style as
        # profile_phase above. Normalise the tactic-execution prefix so repeated
        # invocations of one tactic aggregate under its kind.
        {
          line = $0
          if (match(line, / took [0-9.]+(ms|s)$/) == 0) next
          name = substr(line, 1, RSTART - 1)
          val  = substr(line, RSTART + 6)
          if (val ~ /ms$/) { sub(/ms$/, "", val); ms = val + 0 }
          else             { sub(/s$/,  "", val); ms = val * 1000 }
          sub(/^tactic execution of /, "", name)
          sub(/^Lean\.Parser\.Tactic\./, "", name)
          if (name == "import") next
          cnt[name]++; tot[name] += ms
        }
        END { for (n in tot) printf "%.1f\t%d\t%s\n", tot[n], cnt[n], n }' \
    | LC_ALL=C sort -rn
}

# The costliest phases, to say WHY a module is slow. Collected into a variable
# rather than piped straight to `head`, whose SIGPIPE would trip `pipefail`.
profile_breakdown() {
  local rows
  # awk does the tab filtering: ERE has no \t escape, so `grep -E '^\t'` reads as
  # `^t` and silently matches nothing.
  rows="$(printf '%s\n' "$1" \
    | awk '/^\t/ { line=$0; sub(/^\t/,"",line)
             if (match(line, / [0-9.]+(ms|s)$/)==0) next
             v=substr(line,RSTART+1); n=substr(line,1,RSTART-1)
             if (v ~ /ms$/) { sub(/ms$/,"",v); ms=v+0 } else { sub(/s$/,"",v); ms=v*1000 }
             if (n=="elaboration" || n=="import") next
             printf "%d\t%s\n", ms, n }' \
    | LC_ALL=C sort -rn)"
  printf '%s\n' "$rows" | awk -F'\t' 'NR<=6 && NF==2 { printf "    %7.0f ms  %s\n", $1, $2 }'
}

MODE="${1:-}"; shift || usage

case "$MODE" in

screen)
  LOG="${1:-}"; [ -n "$LOG" ] && [ -f "$LOG" ] || usage
  ROWS="$(sed -E 's/\x1b\[[0-9;]*[A-Za-z]//g' "$LOG" \
    | grep -oE "Built [A-Za-z0-9_.]+ \([0-9]+(\.[0-9]+)?s\)" \
    | sed -E 's/^Built ([A-Za-z0-9_.]+) \(([0-9.]+)s\)$/\2\t\1/' \
    | LC_ALL=C sort -rn | head -20)"
  if [ -z "$ROWS" ]; then
    echo "No elaborated modules in $LOG — all cached, or the build failed early."
    exit 0
  fi
  echo "Slowest elaborated modules by REPORTED WALL CLOCK (contention included):"
  printf '%s\n' "$ROWS" | awk -F'\t' '{ printf "  %6.1fs  %s\n", $1, $2 }'
  echo ""
  echo "These figures include time spent waiting for a core, and they include"
  echo "import loading, so a high number is a candidate rather than a verdict."
  echo "Confirm one with:  bash $0 measure <path/to/Module.lean>"
  exit 0
  ;;

measure)
  TARGET="${1:-}"; [ -n "$TARGET" ] && [ -f "$TARGET" ] || usage
  echo "Elaborating $TARGET alone (its imports must already be built)."
  # Headline figures come from measure_one (repeated, locked, pinned, min-of-N) so
  # they match what `record` and `check` compare against. The extra profiling run
  # below is for the per-phase breakdown only — a single sample, diagnostic, not
  # gated on.
  R="$(measure_one "$TARGET")" || exit 1
  ELAB="$(printf '%s' "$R" | cut -f1)"
  IMP="$(printf '%s' "$R" | cut -f2)"
  RSS=$(( $(printf '%s' "$R" | cut -f3) * 1024 ))
  PROF="$(LEAN_NUM_THREADS=1 taskset -c "$BC_CORES" lake env lean --profile "$TARGET" 2>&1 >/dev/null)"
  printf '\n  elaboration: %s ms   <- the ratcheted cost, this module own elaboration\n' "$ELAB"
  printf '  import:      %s ms   <- import closure, a structural property\n' "${IMP:-?}"
  printf '  peak RSS:    %s MB   <- also closure-dominated, not proof difficulty\n' "$(( ${RSS:-0} / 1024 ))"
  echo ""
  echo "  Costliest phases within elaboration:"
  profile_breakdown "$PROF"
  exit 0
  ;;

record)
  TARGET="${1:-}"; [ -n "$TARGET" ] && [ -f "$TARGET" ] || usage
  R="$(measure_one "$TARGET")"
  elab="$(echo "$R" | cut -f1)"; imp="$(echo "$R" | cut -f2)"; mb="$(echo "$R" | cut -f3)"
  touch "$BASELINE"
  # Keep the smallest elaboration seen, so the baseline is a floor and a later
  # slowdown surfaces instead of being absorbed by one noisy run.
  awk -F'\t' -v t="$TARGET" -v e="$elab" -v i="$imp" -v m="$mb" '
    $1 == t { if ($2 + 0 < e + 0) e = $2; next }
    { print }
    END { printf "%s\t%s\t%s\t%s\n", t, e, i, m }
  ' "$BASELINE" | LC_ALL=C sort > "$BASELINE.new"
  mv "$BASELINE.new" "$BASELINE"
  # Per-tactic rows alongside, so an outlier can be attributed to a tactic rather
  # than only to a file. Replaces this module's rows rather than appending, so the
  # file stays a current picture instead of a log.
  if [ "${RECORD_TACTICS:-1}" = "1" ]; then
    touch "$TACTICS"
    # Every stage tolerates emptiness: `grep` and `sort` on no input return 1, which
    # `set -o pipefail` would turn into a silent abort of the whole record.
    tac_rows="$(profile_tactics "$TARGET" 2>/dev/null || true)"
    { awk -F'\t' -v t="$TARGET" '$2 != t' "$TACTICS" 2>/dev/null || true
      printf '%s\n' "${tac_rows:-}" \
        | awk -F'\t' -v t="$TARGET" 'NF==3 { printf "%s\t%s\t%s\t%s\n", $1, t, $2, $3 }'
    } | awk 'NF' | LC_ALL=C sort -rn > "$TACTICS.new" || true
    mv "$TACTICS.new" "$TACTICS"
  fi
  printf 'Recorded %s: elaboration %s ms (import %s ms, %s MB). Baseline has %s module(s).\n' \
    "$TARGET" "$elab" "$imp" "$mb" "$(grep -c . "$BASELINE" || true)"
  if [ "${RECORD_TACTICS:-1}" = "1" ] && [ -n "${tac_rows:-}" ]; then
    printf 'Top tactics (ms, count, kind):\n'
    printf '%s\n' "$tac_rows" | head -5 | awk -F'\t' '{ printf "  %8s ms  x%-4s %s\n", $1, $2, $3 }'
  fi
  exit 0
  ;;

coverage)
  # `check` re-measures only modules that ALREADY have a baseline row, so a
  # module absent from the baseline is never looked at — and absence is exactly
  # what an expensive module produces, because `record` writes a row only when
  # the measurement EXITS 0. A module that OOMs or exceeds the timeout fails to
  # record, stays out of the baseline, and is therefore never checked again.
  # The gate was self-selecting for cheap modules. This ratchets the size of the
  # unmeasured set instead: it may shrink, never grow, so a new module must be
  # measured (its row keeps the count flat) or it fails here.
  COVER_BASE="${COVER_BASE:-scripts/build-cost-coverage-baseline.txt}"
  measured="$(mktemp)"; tracked="$(mktemp)"
  trap 'rm -f "$measured" "$tracked"' EXIT
  # An absent cost baseline means nothing is measured yet; say so rather than
  # dying inside the pipeline below.
  touch "$BASELINE"
  cut -f1 "$BASELINE" 2>/dev/null | sort -u > "$measured"
  git ls-files 'CatCrypt/**/*.lean' 'HaxAscent/*.lean' | sort > "$tracked"
  NOW="$(comm -23 "$tracked" "$measured" | grep -c . || true)"
  if [ ! -f "$COVER_BASE" ]; then
    echo "$NOW" > "$COVER_BASE"
    echo "Seeded $COVER_BASE at $NOW unmeasured module(s)."
    exit 0
  fi
  WAS="$(tr -dc '0-9' < "$COVER_BASE")"
  echo "Unmeasured modules: current=$NOW  baseline=$WAS  (of $(grep -c . "$tracked") tracked)"
  if [ "$NOW" -gt "$WAS" ]; then
    echo ""
    echo "FAIL: the unmeasured-module count GREW ($WAS -> $NOW)."
    echo "      A module with no row in $BASELINE is never re-checked by"
    echo "      \`$0 check\`, so cost can grow in it without limit."
    echo "      Record the new module(s), then commit the updated baseline:"
    echo "        bash $0 record <path.lean>"
    echo ""
    echo "      Modules with no cost record (newest first):"
    comm -23 "$tracked" "$measured" | xargs -r ls -t 2>/dev/null | head -10 | sed 's/^/        /'
    exit 1
  fi
  if [ "$NOW" -lt "$WAS" ]; then
    echo "$NOW" > "$COVER_BASE"
    echo "Tightened $COVER_BASE: $WAS -> $NOW. Commit it."
  else
    echo "OK: no new unmeasured module."
  fi
  exit 0
  ;;

check)
  [ -f "$BASELINE" ] || { echo "No baseline at $BASELINE. Add one with: bash $0 record <Module.lean>"; exit 1; }
  N="$(grep -c . "$BASELINE" || true)"
  [ "$N" -gt 0 ] || { echo "Baseline is empty; nothing to check."; exit 0; }
  echo "Re-measuring elaboration for $N baselined module(s), one at a time."
  echo ""
  FAILED=0
  OVER_CEILING=""
  while IFS=$'\t' read -r target was_e was_i was_m; do
    [ -n "$target" ] || continue
    case "$target" in '#'*) continue ;; esac
    if [ ! -f "$target" ]; then
      echo "  GONE     $target — baselined module is absent; drop its row"
      FAILED=1; continue
    fi
    R="$(measure_one "$target")" || { FAILED=1; continue; }
    now_e="$(echo "$R" | cut -f1)"; now_i="$(echo "$R" | cut -f2)"
    verdict="$(awk -v we="$was_e" -v ne="$now_e" -v rel="$REL_FACTOR" -v ams="$ABS_MS" 'BEGIN {
      if (ne > we * rel / 100 && ne > we + ams) print "SLOW"
      else if (ne < we * 0.8) print "BETTER"
      else print "OK" }')"
    # Absolute ceiling, independent of the baseline: a module that has always been
    # slow is still slow, and a per-module floor would quietly bless it forever.
    if [ "${now_e:-0}" -gt "$SLOW_MS" ] 2>/dev/null; then
      OVER_CEILING="$OVER_CEILING$(printf '\n  %8s ms  %s' "$now_e" "$target")"
    fi
    # Import closure, reported alongside. Elaboration is the right metric for "did
    # this proof get more expensive", but it is the MINORITY of a build's wall clock:
    # a module measured at 2 ms of elaboration can carry 55,300 ms of import, and a
    # full-library run averages seconds per built module against a 44 ms median
    # elaboration. A module can therefore sit
    # far under the elaboration ceiling and still be most of the build. This is
    # reported, not failed: import depth is changed by import hygiene — splitting a
    # module, dropping an unused `import Mathlib` — not by proof work, so it is a
    # different repair with a different owner.
    if [ "${now_i:-0}" -gt "$IMPORT_MS" ] 2>/dev/null; then
      OVER_IMPORT="$OVER_IMPORT$(printf '\n  %8s ms import (%6s ms elab)  %s' "$now_i" "$now_e" "$target")"
    fi
    case "$verdict" in
      OK)     printf '  ok       %s (elab %s ms)\n' "$target" "$now_e" ;;
      BETTER) printf '  faster   %s: elab %s -> %s ms — re-record to tighten the floor\n' \
                     "$target" "$was_e" "$now_e" ;;
      SLOW)   printf '  REGRESS  %s: elab %s -> %s ms (import %s -> %s)\n' \
                     "$target" "$was_e" "$now_e" "$was_i" "$now_i"
              FAILED=1 ;;
    esac
  done < "$BASELINE"
  echo ""
  if [ -n "${OVER_CEILING:-}" ]; then
    printf 'Over the %s ms elaboration ceiling — each of these needs a reason in its module\n' "$SLOW_MS"
    printf 'docstring, or a fix:%s\n\n' "$OVER_CEILING"
  fi
  if [ -n "${OVER_IMPORT:-}" ]; then
    printf 'Over the %s ms import ceiling — these dominate BUILD wall clock even when their\n' "$IMPORT_MS"
    printf 'elaboration is trivial. The lever is import hygiene, not proof golf: drop an\n'
    printf 'unused `import Mathlib`, split the module, or depend on a narrower ancestor.%s\n\n' "$OVER_IMPORT"
  fi
  if [ "$FAILED" -ne 0 ]; then
    echo "FAIL: a baselined module got slower to elaborate."
    echo "      Run 'measure' on it to see which phase grew, then treat a slow"
    echo "      proof as a defect rather than a budget to raise — extract the"
    echo "      expensive step as a lemma over abstract inputs instead of"
    echo "      bumping maxHeartbeats. If the cost is intended, re-record the"
    echo "      row deliberately and say why in the commit message."
    exit 1
  fi
  echo "OK: no baselined module got slower to elaborate."
  ;;

*) usage ;;
esac
