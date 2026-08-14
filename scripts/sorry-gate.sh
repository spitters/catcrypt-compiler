#!/usr/bin/env bash
# Repo sorry gate.
#
# The check is the compiler's own AST-level diagnostic, never a source grep.
# Lean reports a declaration whose proof term contains `sorryAx` as
#
#   <file>:<line>:<col>: warning: declaration uses `sorry`
#
# with message kind `hasSorry` (verified against Lean 4.30.0 via `lean --json`).
# A `sorry` written in a comment, a docstring or a string literal produces no
# such message, and a declaration that reaches `sorryAx` through a tactic the
# text search would not match still produces one. That is the whole reason this
# gate reads the compiler's output rather than the sources.
#
# CI documentation elsewhere in this repo quotes
# `lake build <module> -- --run-linter=sorryIn`. Lean 4.30.0 has no
# `--run-linter` flag and Lake 5 has no `--` argument forwarding on `build`
# (checked against `lean --help`, `lake help build` and `lake help lint`; the
# package configures no `lintDriver`), so that command does not run a linter.
# `hasSorry` is the mechanism that does.
#
# ## Coverage
#
# The diagnostic is produced when a module is ELABORATED, and replayed from the
# build log when a module is served from cache. So this gate covers exactly the
# modules the surrounding build reaches — no more, and a build that is cut short
# covers only what it got to. It is not repo-wide by itself.
#
# The package's lakefile already passes `-E hasSorry`, which turns the same
# diagnostic into an error and makes a COMPLETE build refuse a `sorry`. This gate
# is what a PARTIAL build still yields: it reads the log, reports how many files
# were covered, and ratchets the per-file counts. The two are complementary —
# `-E hasSorry` is the stronger check when the build finishes, and this is the
# only one that says anything when it does not.
#
# `scripts/rot-guard-build.sh --build` is the build shape this gate is meant to
# wrap: per-module targets in batches, so coverage is attributable.
#
# ## Usage
#
#   scripts/sorry-gate.sh run <command...>   run <command>, appending its
#                                            combined output to the gate log,
#                                            and propagate its exit status
#   scripts/sorry-gate.sh check              scan the gate log and ratchet
#   scripts/sorry-gate.sh --scan <log>...    scan explicit log files
#   scripts/sorry-gate.sh --init [<log>...]  write the baseline (once)
#   scripts/sorry-gate.sh --reset            truncate the gate log
#
# BOOTSTRAP: `check` FAILS while scripts/sorry-baseline.txt is absent. Run a
# build covering the CI target set, then `--init`, review the result, and commit
# it. The baseline is deliberately not self-initializing — see the comment at
# the `[ ! -f "$BASELINE" ]` branch for why that would make the gate vacuous.
#
# `run` is a pass-through: it never changes the command's exit status, so a
# build failure still reports as a build failure. The gate's pass/fail decision
# comes from `check`.
#
# ## Ratchet
#
# `scripts/sorry-baseline.txt` records, per source file, how many `sorry`
# declarations that file is currently allowed to have. The gate FAILS when a
# file's count rises or a file not in the baseline acquires one, and rewrites
# the baseline downward when counts fall (the git check in CI then fails if the
# tightened baseline was left uncommitted — the same shape as the other
# ratchets in this directory).
#
# Positions are deliberately NOT recorded. A baseline keyed on line numbers
# churns on every unrelated edit above a sorry, which trains reviewers to
# rubber-stamp its diff.
#
# Env:
#   SORRY_GATE_LOG   gate log path (default .lake/sorry-gate.log)

set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

LOG="${SORRY_GATE_LOG:-.lake/sorry-gate.log}"
BASELINE="scripts/sorry-baseline.txt"

# The text Lean emits for a `hasSorry` diagnostic. The severity appears on
# either side of the position depending on who prints it: `lean` writes
#   <file>:<line>:<col>: warning: declaration uses `sorry`
# and Lake writes
#   warning: <file>:<line>:<col>: declaration uses `sorry`
# so the pattern anchors on the message alone, which no other diagnostic emits.
# Anchoring on `(warning|error): declaration uses` instead matched only the first
# form, and Lake's is the one a `lake build` log actually contains.
DIAG='declaration uses `sorry`'

mode="${1:---help}"
shift || true

case "$mode" in
  run)
    [ "$#" -gt 0 ] || { echo "sorry-gate: run needs a command" >&2; exit 2; }
    mkdir -p "$(dirname "$LOG")"
    "$@" 2>&1 | tee -a "$LOG"
    exit "${PIPESTATUS[0]}"
    ;;

  --reset)
    mkdir -p "$(dirname "$LOG")"
    : > "$LOG"
    exit 0
    ;;

  check|--scan|--init)
    init=0
    [ "$mode" = "--init" ] && init=1
    logs=("$@")
    [ "${#logs[@]}" -gt 0 ] || logs=("$LOG")
    for f in "${logs[@]}"; do
      if [ ! -f "$f" ]; then
        echo "sorry-gate: FAIL — no gate log at $f."
        echo "  Nothing was scanned, so this run proves nothing. Wrap the build:"
        echo "    scripts/sorry-gate.sh run lake build <targets>"
        exit 1
      fi
    done

    tmp="$(mktemp -d)"
    trap 'rm -rf "$tmp"' EXIT

    # One line per diagnostic, reduced to its source file. Lake prefixes paths
    # relative to the workspace root; strip any leading ./ and any absolute
    # prefix so the baseline is machine-independent.
    grep -hE "$DIAG" "${logs[@]}" 2>/dev/null \
      | sed -E 's/:[0-9]+:[0-9]+: ((warning|error): )?declaration uses `sorry`.*$//' \
      | sed -E "s#^.*[[:space:]]##; s#^\./##; s#^$(pwd | sed 's#[/.]#\\&#g')/##" \
      | grep -E '\.lean$' \
      | LC_ALL=C sort | uniq -c | awk '{print $1"\t"$2}' \
      | LC_ALL=C sort -k2,2 > "$tmp/cur"

    total=$(awk -F'\t' '{s+=$1} END {print s+0}' "$tmp/cur")
    files=$(wc -l < "$tmp/cur")
    echo "sorry-gate: $total sorry declaration(s) across $files file(s) in $(printf '%s ' "${logs[@]}")"

    write_baseline() {
      { echo "# Per-file sorry allowance, from a build that covered the CI target set."
        echo "# A file's count may FALL (the baseline auto-tightens) but never RISE, and a"
        echo "# file absent here may not acquire one. Coverage is the build's coverage: a"
        echo "# file the scanned build never reached is absent here, which reads as"
        echo "# 'not covered', not as 'clean'."
        echo "# Initialize: scripts/sorry-gate.sh --init  (after a full CI-equivalent build)"
        echo "# Format: <count><TAB><path>"
        cat "$1"; } > "$BASELINE"
    }

    # A missing baseline is a FAILURE, not a silent initialization. Initializing
    # here would make every run compare a log against a baseline derived from
    # that same log, which passes unconditionally — and because the fresh file is
    # untracked, the `git diff --exit-code` in CI would not catch it either. The
    # gate would then be permanently green while checking nothing.
    if [ ! -f "$BASELINE" ]; then
      if [ "$init" -eq 1 ]; then
        write_baseline "$tmp/cur"
        echo "sorry-gate: baseline initialized at $BASELINE ($total across $files files)."
        echo "  Review it and commit it. Every entry is a sorry someone must close."
        exit 0
      fi
      echo "sorry-gate: FAIL — no baseline at $BASELINE."
      echo "  Nothing to compare against, so this run proves nothing. Run a build that"
      echo "  covers the CI target set, then:  scripts/sorry-gate.sh --init"
      exit 1
    fi
    if [ "$init" -eq 1 ]; then
      echo "sorry-gate: $BASELINE already exists; --init refuses to overwrite it."
      echo "  Delete it deliberately if a full re-initialization is intended."
      exit 1
    fi

    grep -vE '^[[:space:]]*(#|$)' "$BASELINE" | LC_ALL=C sort -k2,2 > "$tmp/base"

    fail=0
    while IFS=$'\t' read -r n f; do
      [ -z "${f:-}" ] && continue
      b=$(awk -F'\t' -v F="$f" '$2==F {print $1; exit}' "$tmp/base")
      b="${b:-0}"
      if [ "$n" -gt "$b" ]; then
        echo "  FAIL: $f has $n sorry declaration(s), baseline allows $b"
        fail=1
      fi
    done < "$tmp/cur"

    if [ "$fail" -ne 0 ]; then
      echo "sorry-gate: FAIL — the sorry count grew."
      echo "  Close the sorry, or record the increase in $BASELINE with the reason."
      exit 1
    fi

    # Auto-tighten. A baseline entry for a file the scanned build did not reach
    # is KEPT: its absence from this log means "not covered", not "clean".
    : > "$tmp/new"
    while IFS=$'\t' read -r n f; do
      [ -z "${f:-}" ] && continue
      c=$(awk -F'\t' -v F="$f" '$2==F {print $1; exit}' "$tmp/cur")
      if [ -n "$c" ] && [ "$c" -lt "$n" ]; then
        printf '%s\t%s\n' "$c" "$f" >> "$tmp/new"
      else
        printf '%s\t%s\n' "$n" "$f" >> "$tmp/new"
      fi
    done < "$tmp/base"

    if ! diff -q "$tmp/base" "$tmp/new" >/dev/null 2>&1; then
      write_baseline "$tmp/new"
      echo "sorry-gate: baseline tightened — commit $BASELINE."
    fi

    echo "sorry-gate: OK."
    exit 0
    ;;

  *)
    sed -n '2,50p' "$0" | sed 's/^# \{0,1\}//'
    exit 2
    ;;
esac
