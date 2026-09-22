#!/usr/bin/env bash
# Build-cost guard: catches slow/OOM proofs that the maxHeartbeats ratchet misses.
#
# A heavy `rfl`/`decide`/`native_decide` or a monolithic tower/`Com.denote` unfold
# can exhaust kernel memory WITHOUT bumping `set_option maxHeartbeats`, so the
# proof-cost ratchet does not see it. This elaborates each changed/named module
# under a memory cap and a wall-clock timeout and FAILS on a memory overrun or a
# timeout -- i.e. a build that is not "light". A static anti-pattern lint
# (native_decide in a reflection/emit-front module, a raised recursion/heartbeat
# budget guarding a proof) runs first, cheaply.
#
# Usage:
#   scripts/check-build-cost.sh                 # modules of changed .lean files vs HEAD
#   scripts/check-build-cost.sh Mod.A Mod.B     # explicit module list
#   scripts/check-build-cost.sh --record ...    # also record each module's cost row
#
# Env:
#   BUILD_COST_TIMEOUT    per-module wall-clock cap, seconds (default 100)
#   BUILD_COST_MEM_MB     per-module memory cap passed to `lean -M` (default 4000;
#                         empty disables the cap)
#   BUILD_COST_CORES      CPU affinity range when `taskset` is present (default 0-1)
#   BUILD_COST_STATIC_ONLY=1   run only the static anti-pattern lint, no build
#   BUILD_COST_BASE       git ref the static lint ratchets against (default HEAD;
#                         set to the branch base in CI)
#   FRONT_RE              regex of reflection/emit-front module names whose import
#                         makes native_decide native-compile the whole pipeline
#                         (default below; override for a non-CatCrypt project)
#
# The build step uses `lake env lean` on each module source, so the module's
# imports must already be built (as after a full `lake build`). It runs the
# elaboration directly under `timeout`, needing no wrapper script.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

TIMEOUT="${BUILD_COST_TIMEOUT:-100}"
CORES="${BUILD_COST_CORES:-0-1}"
# The static lint ratchets each file's anti-pattern count against a git ref. A
# working-tree edit is compared against HEAD (the pre-commit case); CI compares
# against the pull-request base by exporting BUILD_COST_BASE, so a change already
# committed at HEAD is still seen as new relative to before the branch.
BASE_REF="${BUILD_COST_BASE:-HEAD}"
MEM_MB="${BUILD_COST_MEM_MB-4000}"
FRONT_RE="${FRONT_RE:-LowCTReflect|FieldDialect|VIR\.|CatCryptDialect|CryptoDialect|CompileFromHax|HaxToLowCT}"

# --- flags ---------------------------------------------------------------------
RECORD=0
args=()
for a in "$@"; do
  case "$a" in
    --record) RECORD=1 ;;
    *)        args+=( "$a" ) ;;
  esac
done
set -- "${args[@]+"${args[@]}"}"

# --- resolve the module list ---------------------------------------------------
mods=()
if [ "$#" -gt 0 ]; then
  mods=("$@")
else
  while IFS= read -r f; do
    [ -z "$f" ] && continue
    case "$f" in
      CatCrypt/*.lean) mods+=( "$(echo "${f%.lean}" | tr '/' '.')" ) ;;
    esac
  done < <(git diff --name-only HEAD -- 'CatCrypt/**/*.lean'; git ls-files --others --exclude-standard 'CatCrypt/**/*.lean')
fi

if [ "${#mods[@]}" -eq 0 ]; then
  echo "build-cost: no changed CatCrypt modules to check."
  exit 0
fi

# --- static anti-pattern lint (fast, no build) ---------------------------------
# native_decide inside a module that imports the reflection / emit front
# native-compiles the whole pipeline (multi-GB) and can OOM the build. Flag
# newly-added occurrences. The front set is FRONT_RE, overridable per project;
# its default names the modules whose import pulls in the reflection/emit
# pipeline (the LowCT reflector, the field/crypto dialects, the VIR lowering, and
# the hax-to-LowCT / compile-from-hax entry points).
static_fail=0
for m in "${mods[@]}"; do
  f="$(echo "$m" | tr '.' '/').lean"
  [ -f "$f" ] || continue
  guarded=0
  # Strip comments before looking for the tactic: a docstring that merely NAMES
  # `native_decide` (describing an imported fact, or explaining why it was avoided)
  # is not a use of it.
  # Lean line comments are `--`; block comments and docstrings are `/- ... -/` and
  # nest. Track depth per line, decide membership BEFORE the opener on that line so
  # a `/-- ... -/` one-liner is excluded while code after a closing `-/` is kept.
  code_only="$(awk '
      { line = $0
        opens = gsub(/\/-/, "&", line); closes = gsub(/-\//, "&", line)
        if (depth == 0) { sub(/--.*$/, "", $0); print }
        depth += opens - closes
        if (depth < 0) depth = 0 }' "$f")"
  # Ratcheted against HEAD, like the budget check below: what must not happen is a
  # NEW occurrence. Without the ratchet the gate would block any edit to a file
  # that already has one, including an edit that makes it dramatically cheaper.
  nd_now="$(printf '%s\n' "$code_only" | grep -cE 'native_decide' || true)"
  nd_base=0
  if git cat-file -e "$BASE_REF:$f" 2>/dev/null; then
    # `grep -c` prints its count AND exits 1 when the count is zero, so `|| echo 0`
    # would append a second zero and the numeric test below would abort on "0\n0",
    # silently disabling this branch of the lint.
    nd_base="$(git show "$BASE_REF:$f" 2>/dev/null | grep -cE 'native_decide' || true)"
  fi
  if [ "${nd_now:-0}" -gt "${nd_base:-0}" ] \
     && grep -qE "import .*($FRONT_RE)" "$f"; then
    echo "  SLOW-PROOF LINT: $f uses native_decide while importing the reflection/emit front (native-compiles the pipeline -> OOM). Use kernel decide on a small goal or a structural proof."
    static_fail=1
  fi
  # A raised recursion/heartbeat budget sitting on a proof is a strong tell that
  # the proof REDUCES a large object instead of reasoning about it. The structural
  # form is size-independent -- relate two lengths rather than compute one, induct
  # over a builder's counter rather than reduce at the concrete depth, state a
  # parametric prefix lemma rather than evaluate bytes. Raising the budget hides
  # the cost; it does not remove it.
  while IFS=: read -r ln _; do
    [ -z "$ln" ] && continue
    # Look at the few lines after the set_option for a proof it is guarding.
    # A docstring commonly sits between the set_option and the declaration, so scan
    # far enough to clear one, and stop at the first declaration of any kind so a
    # `def` further down is not mistaken for the guarded proof.
    if sed -n "${ln},$((ln + 20))p" "$f" 2>/dev/null \
         | grep -oE '^\s*(private\s+|protected\s+|noncomputable\s+|@\[[^]]*\]\s*)*(theorem|lemma|example|def|abbrev|instance|structure|inductive)\b' \
         | head -1 | grep -E '(theorem|lemma|example)\b' >/dev/null; then
      guarded=$((guarded + 1))
    fi
  done < <(grep -nE '^\s*set_option\s+(maxRecDepth|maxHeartbeats)\b' "$f" 2>/dev/null || true)
  # Ratchet per file rather than fail outright: some such sites may predate this
  # check, and a hard failure would block unrelated edits to every one of them.
  # What must not happen is a NEW one, so compare against HEAD and fail only on an
  # increase.
  if [ "$guarded" -gt 0 ]; then
    base_guarded=0
    if git cat-file -e "$BASE_REF:$f" 2>/dev/null; then
      base_guarded=$(git show "$BASE_REF:$f" 2>/dev/null \
        | grep -cE '^\s*set_option\s+(maxRecDepth|maxHeartbeats)\b' || true)
    fi
    if [ "$guarded" -gt "$base_guarded" ]; then
      echo "  SLOW-PROOF LINT: $f raises maxRecDepth/maxHeartbeats on a proof in $guarded place(s), up from $base_guarded at HEAD."
      echo "      That budget is evidence the proof reduces a large term rather than reasoning"
      echo "      about it. State it structurally: relate two lengths instead of computing one,"
      echo "      induct over a builder's counter instead of reducing at the concrete depth, or"
      echo "      prove a prefix parametrically instead of evaluating the bytes. Raising the"
      echo "      budget hides the cost. See BUILDING.md, 'Diagnosing an OOM'."
      static_fail=1
    fi
  fi
done

# BUILD_COST_STATIC_ONLY=1 stops here, before any build. The commit hook uses it so
# the anti-pattern lint runs at authoring time without paying for builds; CI runs the
# whole script.
if [ "${BUILD_COST_STATIC_ONLY:-0}" = "1" ]; then
  if [ "$static_fail" -ne 0 ]; then
    echo "build-cost: FAIL -- a staged module adds a proof-cost anti-pattern (see above)."
    exit 1
  fi
  exit 0
fi

# --- build-cost check ----------------------------------------------------------
# Affinity is applied only when `taskset` is available; the guard keeps the script
# runnable on a host without it.
TASKSET=()
if command -v taskset >/dev/null 2>&1; then
  TASKSET=(taskset -c "$CORES")
fi
MEMARG=()
if [ -n "$MEM_MB" ]; then
  MEMARG=(-M "$MEM_MB")
fi

fail=0
for m in "${mods[@]}"; do
  src="$(echo "$m" | tr '.' '/').lean"
  if [ ! -f "$src" ]; then
    echo "  (skip) $m -- no source file $src"
    continue
  fi
  start=$(date +%s 2>/dev/null || echo 0)
  out="$(timeout "$TIMEOUT" env LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}" \
      "${TASKSET[@]}" lake env lean "${MEMARG[@]}" "$src" 2>&1)"
  ec=$?
  end=$(date +%s 2>/dev/null || echo 0)
  dt=$(( end - start ))
  case "$ec" in
    0)   echo "  ok    (${dt}s)  $m" ;;
    124) echo "  SLOW  (>${TIMEOUT}s timeout)  $m  -- not a light build; extract the heavy declaration or make the rfl/ring per-coordinate"; fail=1 ;;
    137) echo "  OOM   (killed)  $m  -- heavy rfl/decide/monolithic unfold; make it per-coordinate/per-limb, never a flat reduction"; fail=1 ;;
    *)
      # `lean -M` turns a memory overrun into a kernel error at RC != 0 rather than
      # a signal; distinguish it from an ordinary compile error by the message.
      if printf '%s\n' "$out" | grep -iE 'excessive memory|memory consumption' >/dev/null; then
        echo "  OOM   (mem cap ${MEM_MB} MB)  $m  -- heavy rfl/decide/monolithic unfold; make it per-coordinate/per-limb, never a flat reduction"
      else
        echo "  build-error (exit $ec)  $m  -- re-run to see diagnostics:  lake env lean $src"
      fi
      fail=1 ;;
  esac

  # Opportunistic cost recording (only with --record). The module just elaborated,
  # so measuring its own cost is nearly free. This is what fills
  # scripts/build-cost-baseline.tsv; build-cost-ratchet.sh owns the row format.
  if [ "$ec" = 0 ] && [ "$RECORD" = 1 ]; then
    bash scripts/build-cost-ratchet.sh record "$src" >/dev/null 2>&1 \
      || echo "  (cost not recorded for $m)"
  fi
done

if [ "$static_fail" = 1 ] || [ "$fail" = 1 ]; then
  echo "build-cost: FAIL -- a changed module is not a light build (see above). Builds should be quick."
  exit 1
fi
echo "build-cost: all changed modules build light."
exit 0
