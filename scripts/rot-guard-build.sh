#!/usr/bin/env bash
# Rot-guard driver for the compiler module set.
#
# ## What this guards
#
# A module that nothing imports is elaborated only because some build target
# names it. If no target does, a change to a shared definition breaks it and
# nothing goes red — the module rots in place, and anything it contains (a
# `sorry`, a stale spec) stops being checked. This package's default target is
# the whole-library glob `CatCrypt.+`, so nominally every module is in the build
# set; in practice the full build is long enough that a run can be cut short
# before reaching the tail, and a module nobody imports is exactly the kind that
# sits in that tail.
#
# So the guarded set is the package's IMPORT ROOTS: every tracked module under
# `CatCrypt/` that no other tracked module imports. They are listed in
# scripts/rot-guard/build-roots.txt. Their transitive import closure is the
# whole library, which is what makes the coverage check below meaningful: a
# module outside that closure is one that neither is imported by anything nor is
# declared a root, i.e. one nobody has taken responsibility for building.
#
# `--build` builds each listed root as its own lake target, in batches. Lake
# elaborates one module per worker process, so the peak cost is the largest
# SINGLE import closure rather than the union of all of them, and a batch that
# dies names the modules it was building. That is the reason the list is a
# manifest and not an aggregator Lean module: an aggregator that `import`s N
# modules must load all N environments into one process at the end.
#
# Usage:
#   scripts/rot-guard-build.sh --list            module names, one per line
#   scripts/rot-guard-build.sh --check           manifest + coverage checks, no build
#   scripts/rot-guard-build.sh --affected [FILE...]
#                                                build only the roots whose import
#                                                closure contains a changed module.
#                                                FILEs are source paths; with none,
#                                                the .lean files that differ from HEAD
#                                                plus the untracked ones. Batch size
#                                                from ROT_GUARD_BATCH (default 16).
#   scripts/rot-guard-build.sh --build [BATCH]   build every listed module (BATCH per
#                                                lake invocation, default 16)
#
# `--affected` is the check for a change in progress; `--build` is the full sweep,
# for CI and before a release.
#
# On a machine whose builds share the heavy-run lock, take the lock per lake
# invocation, through the prefix, and run this script UNWRAPPED:
#
#   ROT_GUARD_PREFIX="../SSProve-lean/scripts/heavy-run.sh env LEAN_NUM_THREADS=1" \
#     bash scripts/rot-guard-build.sh --affected
#
# The lock is then released after every batch, so other builds get in between
# batches. Wrapping the script itself in heavy-run.sh holds the lock for the whole
# run, and doing both deadlocks; the script refuses that combination.
#
# Env:
#   ROT_GUARD_MANIFEST         manifest path (default scripts/rot-guard/build-roots.txt)
#   ROT_GUARD_PREFIX           command prefix for each build invocation, e.g.
#                              "env LEAN_NUM_THREADS=1" to bound the number of
#                              concurrent workers on a memory-tight box.
#   ROT_GUARD_BATCH            roots per lake invocation for --affected (default 16).
#   ROT_GUARD_WRITE_BASELINE=1 rewrite the orphan baseline from the current tree.
#   ROT_GUARD_WRITE_MANIFEST=1 regenerate the manifest from the current import graph.

set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

MANIFEST="${ROT_GUARD_MANIFEST:-scripts/rot-guard/build-roots.txt}"
ORPHAN_BASELINE="scripts/rot-guard/orphan-baseline.txt"
CI_WORKFLOW=".github/workflows/ci.yml"

# Namespaces this manifest is responsible for: the verified compiler proper.
# `Jasmin` is in scope because that is where the leaf kernels are.
TERRITORY='^CatCrypt\.Crypto\.(SecureCompilation|Optimizer|Jasmin)\.'

# The opt-in VeIR bridge library (`lake build CatCryptCompilerVeir`): its modules
# are outside the default build by design, so they are outside this manifest's
# territory. scripts/gen-module-globs.sh computes the set; the manifest must not
# list any of them.

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# Every tracked module under CatCrypt/ and HaxAscent/, as a module name.
tracked_modules() {
  git ls-files -- 'CatCrypt/*.lean' 'CatCrypt/**/*.lean' 'HaxAscent/*.lean' \
    | sed -E 's/\.lean$//; s#/#.#g' | LC_ALL=C sort -u
}

# Import edges over the tracked sources, as "module<TAB>dependency".
#
# Block comments and docstrings are stripped first. A `## Use` section that shows
# the module's own import line inside a ```lean fence otherwise reads as a
# self-import, which drops the module out of the import-root set and then reports
# it as an orphan — `Optimizer/SplitBytesSlice.lean` is exactly that shape.
import_edges() {
  git ls-files -- 'CatCrypt/*.lean' 'CatCrypt/**/*.lean' 'HaxAscent/*.lean' \
    | while IFS= read -r f; do
        m="$(echo "${f%.lean}" | tr '/' '.')"
        perl -0777 -ne 's{/-.*?-/}{}gs; s{--[^\n]*}{}g; print;' "$f" 2>/dev/null \
          | grep -hoE '^(public[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+(CatCrypt|HaxAscent)[A-Za-z0-9_.]*' \
          | sed -E "s/^(public[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+/${m}\t/"
      done
}


# Build the modules listed in file $1, $2 per lake invocation, each invocation
# under ROT_GUARD_PREFIX. Lake skips modules that are already built, so an
# interrupted run resumes where it stopped.
build_mods() {
  local list="$1" batch="$2" prefix="${ROT_GUARD_PREFIX:-}" total fail=0 i=0 ec b
  # A prefix that takes the heavy-run lock, under a process that already holds
  # it, waits on itself for ever. heavy-run.sh holds the lock on descriptor 9.
  case "$prefix" in
    *heavy-run*)
      if [ "$(readlink "/proc/$$/fd/9" 2>/dev/null)" = "${TMPDIR:-/tmp}/catcrypt-heavy-build.lock" ]; then
        echo "rot-guard: this script already runs under the heavy-run lock, and ROT_GUARD_PREFIX" >&2
        echo "  takes it again, which deadlocks. Run the script unwrapped." >&2
        return 2
      fi ;;
  esac
  total=$(wc -l < "$list")
  rm -f "$tmp"/batch.*
  split -l "$batch" "$list" "$tmp/batch."
  for b in "$tmp"/batch.*; do
    # shellcheck disable=SC2046,SC2086
    $prefix lake build $(cat "$b")
    ec=$?
    i=$(( i + $(wc -l < "$b") ))
    if [ "$ec" -ne 0 ]; then
      echo "rot-guard: FAIL — a module in this batch did not build (exit $ec):"
      sed 's/^/    /' "$b"
      fail=1
    fi
    echo "rot-guard: $i/$total modules built."
  done
  [ "$fail" -eq 0 ] || return 1
  echo "rot-guard: all $total modules built."
  return 0
}

tracked_modules > "$tmp/tracked"
bash scripts/gen-module-globs.sh --veir > "$tmp/optin" || {
  echo "rot-guard: scripts/gen-module-globs.sh --veir failed" >&2; exit 2; }

# Regenerate the manifest: the tracked modules outside the opt-in library that no
# module outside it imports. An import from an opt-in module does not count: the
# default sweep does not build the importer.
if [ "${ROT_GUARD_WRITE_MANIFEST:-0}" = "1" ]; then
  import_edges | awk -F'\t' 'NR==FNR { o[$1] = 1; next } !($1 in o) { print $2 }' "$tmp/optin" - \
    | LC_ALL=C sort -u > "$tmp/imported"
  mkdir -p "$(dirname "$MANIFEST")"
  { echo "-- Build roots: tracked modules under CatCrypt/ and HaxAscent/ that no other tracked"
    echo "-- module imports. Their transitive closure is the whole library, so a"
    echo "-- module outside it is one no target and no import reaches."
    echo "-- Regenerate with:"
    echo "--   ROT_GUARD_WRITE_MANIFEST=1 bash scripts/rot-guard-build.sh --check"
    LC_ALL=C comm -23 "$tmp/tracked" "$tmp/imported" | LC_ALL=C comm -23 - "$tmp/optin"; } > "$MANIFEST"
  echo "rot-guard: wrote $MANIFEST"
fi

if [ ! -f "$MANIFEST" ]; then
  echo "rot-guard: manifest not found: $MANIFEST" >&2
  echo "  Seed it with: ROT_GUARD_WRITE_MANIFEST=1 bash $0 --check" >&2
  exit 2
fi

# Manifest entries: strip comments and blank lines, in file order.
sed -E 's/[[:space:]]*--.*$//; s/[[:space:]]+$//' "$MANIFEST" | grep -vE '^$' > "$tmp/mods"

mode="${1:---check}"

case "$mode" in
  --list)
    cat "$tmp/mods"
    exit 0
    ;;

  --check)
    fail=0
    n=$(wc -l < "$tmp/mods")
    echo "rot-guard: manifest lists $n modules ($MANIFEST)."

    # 1. Every entry names a real, tracked source file. An entry that names
    #    nothing guards nothing, and a rename would otherwise pass silently.
    while IFS= read -r m; do
      [ -z "$m" ] && continue
      f="${m//./\/}.lean"
      if [ ! -f "$f" ]; then
        echo "  FAIL: manifest names a module with no source: $m"
        fail=1
      elif ! grep -qxF "$m" "$tmp/tracked"; then
        echo "  FAIL: manifest names an untracked module: $m"
        fail=1
      fi
    done < "$tmp/mods"

    # 2. No duplicate entries: a duplicate hides a deletion behind a stable count.
    if dups=$(LC_ALL=C sort "$tmp/mods" | uniq -d) && [ -n "$dups" ]; then
      echo "  FAIL: duplicate manifest entries:"
      printf '    %s\n' $dups
      fail=1
    fi

    # 2b. No entry belongs to the opt-in VeIR bridge library. Listing one would
    #     put the bridge back in the full sweep, which the opt-in target exists
    #     to avoid.
    if inopt=$(LC_ALL=C sort -u "$tmp/mods" | LC_ALL=C comm -12 - "$tmp/optin") && [ -n "$inopt" ]; then
      echo "  FAIL: manifest lists modules of the opt-in VeIR bridge library:"
      printf '    %s\n' $inopt
      fail=1
    fi

    # 3. Coverage. Compute the transitive import closure of every manifest entry
    #    plus every CatCrypt.* target named in the workflow, and report the
    #    modules in this manifest's territory that fall outside it.
    #
    #    The whole-library glob of the default `lean_lib` target is deliberately
    #    NOT a root here. Counting it would empty the orphan set by construction:
    #    it names every module by pattern rather than by name, which is precisely
    #    how a module nobody imports and nobody listed stays invisible until the
    #    one long build that would have reached it is cut short.
    : > "$tmp/roots"
    if [ -f "$CI_WORKFLOW" ]; then
      grep -oE '(^|[[:space:]])CatCrypt\.[A-Za-z0-9_.]+' "$CI_WORKFLOW" \
        | sed -E 's/^[[:space:]]+//; s/\.$//' | LC_ALL=C sort -u > "$tmp/ciroots"
      # Prose in the workflow's comments names modules too; keep only tokens that
      # are real modules.
      LC_ALL=C comm -12 "$tmp/ciroots" "$tmp/tracked" >> "$tmp/roots"
    fi
    cat "$tmp/mods" >> "$tmp/roots"
    LC_ALL=C sort -u "$tmp/roots" -o "$tmp/roots"

    import_edges > "$tmp/edges"

    awk -F'\t' '
      FNR==NR { adj[$1] = adj[$1] " " $2; next }
      { if (!($0 in seen)) { seen[$0]=1; queue[++qn]=$0 } }
      END {
        for (i = 1; i <= qn; i++) {
          split(adj[queue[i]], ds, " ")
          for (j in ds) {
            d = ds[j]
            if (d != "" && !(d in seen)) { seen[d]=1; queue[++qn]=d }
          }
        }
        for (m in seen) print m
      }' "$tmp/edges" "$tmp/roots" | LC_ALL=C sort -u > "$tmp/reachable"

    LC_ALL=C comm -23 "$tmp/tracked" "$tmp/reachable" | LC_ALL=C comm -23 - "$tmp/optin" \
      | grep -E "$TERRITORY" > "$tmp/orphans"
    orphans=$(wc -l < "$tmp/orphans")

    base=0
    if [ -f "$ORPHAN_BASELINE" ]; then
      base=$(grep -vE '^[[:space:]]*(#|$)' "$ORPHAN_BASELINE" 2>/dev/null | wc -l)
    fi
    echo "rot-guard: $orphans modules in this manifest's territory are reached by no build root (baseline $base)."
    if [ "$orphans" -gt "$base" ]; then
      echo "  FAIL: unguarded-orphan count rose from $base to $orphans."
      echo "        Modules that nothing imports and no root names:"
      if [ -f "$ORPHAN_BASELINE" ]; then
        LC_ALL=C comm -23 "$tmp/orphans" <(grep -vE '^\s*(#|$)' "$ORPHAN_BASELINE" | LC_ALL=C sort -u) \
          | sed 's/^/          /'
      else
        sed 's/^/          /' "$tmp/orphans"
      fi
      echo "        Add each to $MANIFEST, or record it in $ORPHAN_BASELINE with"
      echo "        the reason it is not guarded. Regenerate the manifest with:"
      echo "          ROT_GUARD_WRITE_MANIFEST=1 bash $0 --check"
      fail=1
    fi
    if [ "${ROT_GUARD_WRITE_BASELINE:-0}" = "1" ]; then
      cp "$tmp/orphans" "$tmp/newbase"
      { echo "# Modules under CatCrypt.Crypto.SecureCompilation / .Optimizer / .Jasmin that"
        echo "# no import and no manifest root reaches. They are the standing gap this"
        echo "# manifest has not closed; the check fails when the list GROWS, so a newly"
        echo "# added module in those namespaces must be imported by something, put in the"
        echo "# manifest, or recorded here with a reason. Regenerate with"
        echo "#   ROT_GUARD_WRITE_BASELINE=1 bash scripts/rot-guard-build.sh --check"
        cat "$tmp/newbase"; } > "$ORPHAN_BASELINE"
      echo "  wrote $ORPHAN_BASELINE ($orphans entries)"
    fi

    if [ "$fail" -ne 0 ]; then
      echo "rot-guard: FAIL (see above)."
      exit 1
    fi
    echo "rot-guard: manifest and coverage OK."
    exit 0
    ;;

  --build)
    build_mods "$tmp/mods" "${2:-16}"
    exit $?
    ;;

  --affected)
    shift
    # Changed sources: the arguments, or every .lean that differs from HEAD plus
    # every untracked .lean.
    if [ "$#" -gt 0 ]; then
      printf '%s\n' "$@" > "$tmp/changedfiles"
    else
      { git diff --name-only HEAD -- '*.lean'
        git ls-files --others --exclude-standard -- '*.lean'; } > "$tmp/changedfiles"
    fi
    grep -E '^(CatCrypt|HaxAscent)/.*\.lean$' "$tmp/changedfiles" \
      | sed -E 's/\.lean$//; s#/#.#g' | LC_ALL=C sort -u > "$tmp/changed"
    if [ ! -s "$tmp/changed" ]; then
      echo "rot-guard: no changed module under CatCrypt/ or HaxAscent/; nothing to build."
      exit 0
    fi

    # Every module whose import closure contains a changed module: the reverse
    # closure of the changed set over the import edges (importer <TAB> imported).
    import_edges > "$tmp/edges"
    awk -F'\t' '
      FNR==NR { rev[$2] = rev[$2] " " $1; next }
      { if (!($0 in seen)) { seen[$0]=1; queue[++qn]=$0 } }
      END {
        for (i = 1; i <= qn; i++) {
          split(rev[queue[i]], us, " ")
          for (j in us) {
            u = us[j]
            if (u != "" && !(u in seen)) { seen[u]=1; queue[++qn]=u }
          }
        }
        for (m in seen) print m
      }' "$tmp/edges" "$tmp/changed" | LC_ALL=C sort -u > "$tmp/dependents"

    # The manifest roots among them, in manifest order.
    grep -xFf "$tmp/dependents" "$tmp/mods" > "$tmp/affected" || true
    echo "rot-guard: $(wc -l < "$tmp/changed") changed modules reach $(wc -l < "$tmp/affected") of $(wc -l < "$tmp/mods") roots."
    if [ ! -s "$tmp/affected" ]; then
      echo "rot-guard: no manifest root imports a changed module."
      exit 0
    fi
    build_mods "$tmp/affected" "${ROT_GUARD_BATCH:-16}"
    exit $?
    ;;

  *)
    echo "usage: $0 [--list | --check | --build [BATCH] | --affected [FILE...]]" >&2
    exit 2
    ;;
esac
