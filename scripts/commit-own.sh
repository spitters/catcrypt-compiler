#!/usr/bin/env bash
# Commits the named paths together with module lists generated for exactly the
# committed tree, in a worktree that another session shares.
#
# The generated lists (the module block of `lakefile.lean`, the rot-guard manifest and,
# in the dev tree, the umbrella) are produced from `git ls-files`. In a shared worktree
# the working copies of those lists also name the other session's unfinished modules,
# and the pre-commit checks compare them with the tree of a partial commit, which does
# not contain those modules: a correct commit is refused. This script
#
#   1. saves the working copies of the lists,
#   2. generates the lists for `HEAD` plus the named paths, through a private index,
#   3. commits the named paths and the lists that changed,
#   4. restores the saved working copies, so the other session's lines are kept.
#
# It stops without committing when `HEAD` moves between steps 2 and 3, or when one of
# the lists is staged in the shared index (another commit is being prepared).
# No step loads Lean.
#
#   scripts/commit-own.sh -m "message" -- <path>...
#   scripts/commit-own.sh -F <message-file> -- <path>...
set -uo pipefail
ROOT="$(git rev-parse --show-toplevel)"; cd "$ROOT"

msgargs=()
while [ $# -gt 0 ]; do
  case "$1" in
    -m|-F) msgargs+=("$1" "$2"); shift 2 ;;
    --) shift; break ;;
    *) echo "usage: $0 (-m <message> | -F <file>)... -- <path>..." >&2; exit 2 ;;
  esac
done
[ ${#msgargs[@]} -gt 0 ] && [ $# -gt 0 ] || { echo "usage: $0 (-m <message> | -F <file>)... -- <path>..." >&2; exit 2; }
paths=("$@")

if [ -f scripts/gen-dev-module-globs.sh ]; then
  lists=(lakefile.lean CatCrypt.lean scripts/rot-guard/secure-compilation.txt)
  generate() { bash scripts/gen-dev-module-globs.sh >/dev/null && bash scripts/gen-umbrella.sh >/dev/null; }
else
  lists=(lakefile.lean scripts/rot-guard/build-roots.txt)
  generate() { bash scripts/gen-module-globs.sh >/dev/null \
               && ROT_GUARD_WRITE_MANIFEST=1 bash scripts/rot-guard-build.sh --check >/dev/null; }
fi

staged="$(git diff --cached --name-only -- "${lists[@]}")"
[ -z "$staged" ] || { echo "commit-own: a module list is staged in the shared index ($staged); another commit is in preparation. Retry after it lands." >&2; exit 1; }

work="$(mktemp -d)"; idx="$work/index"
# The old working-tree lists are put back (they carry the other sessions' unfinished
# modules and the hand-appended dev manifest). After a commit the generated lists are then
# regenerated against the shared index, so the working tree also carries this commit's new
# module lines and rot-guard roots; otherwise the working tree lags HEAD and the next
# session's pre-commit check sees them dropped. The regeneration reads a copy of the shared
# index to which the modules that the restored lakefile names, that exist on disk and that
# are not tracked are added: those are other sessions' unregistered modules in progress,
# and a generator reading `git ls-files` alone would drop their lines.
committed=0
added=()
restore() {
  # A refused commit leaves no intent-to-add entry of this script in the shared index.
  if [ "$committed" = 0 ] && [ ${#added[@]} -gt 0 ]; then
    git rm --cached -q -- "${added[@]}" 2>/dev/null || true
  fi
  for l in "${lists[@]}"; do [ -f "$work/$(printf '%s' "$l" | tr / _)" ] && cp "$work/$(printf '%s' "$l" | tr / _)" "$l"; done
  if [ "$committed" = 1 ]; then
    idx2="$work/index-wt"; cp "$(git rev-parse --git-path index)" "$idx2"
    grep -o 'Glob.one `[A-Za-z0-9_.]*' lakefile.lean | sed 's/^Glob.one `//' | while read -r m; do
      f="$(printf '%s' "$m" | tr . /).lean"
      [ -f "$f" ] && ! git ls-files --error-unmatch -- "$f" >/dev/null 2>&1 \
        && GIT_INDEX_FILE="$idx2" git update-index --add -- "$f"
    done
    GIT_INDEX_FILE="$idx2" generate \
      || echo "commit-own: regenerating the working-tree lists failed; run the list generators by hand." >&2
  fi
  rm -rf "$work"
}
trap restore EXIT
for l in "${lists[@]}"; do [ -f "$l" ] && cp "$l" "$work/$(printf '%s' "$l" | tr / _)"; done

for p in "${paths[@]}"; do
  if [ -e "$p" ] && ! git ls-files --error-unmatch -- "$p" >/dev/null 2>&1; then
    git add -N -- "$p" && added+=("$p")
  fi
done
head0="$(git rev-parse HEAD)"
GIT_INDEX_FILE="$idx" git read-tree HEAD
for p in "${paths[@]}"; do
  if [ -e "$p" ]; then GIT_INDEX_FILE="$idx" git update-index --add -- "$p"
  else GIT_INDEX_FILE="$idx" git update-index --force-remove -- "$p"; fi
done
# The dev manifest is appended to, not generated. Remove only the lines of modules that
# exist on disk without being part of this commit's tree (another session's unfinished
# modules); every other line, including the compiler package's modules and the comments,
# is kept.
if [ -f scripts/gen-dev-module-globs.sh ] && [ -f scripts/rot-guard/secure-compilation.txt ]; then
  { git ls-files 'CatCrypt/*.lean' 'CatCrypt/**/*.lean'
    git ls-files --others --exclude-standard 'CatCrypt/*.lean' 'CatCrypt/**/*.lean'; } \
    | LC_ALL=C sort -u > "$work/ondisk"
  GIT_INDEX_FILE="$idx" git ls-files 'CatCrypt/*.lean' 'CatCrypt/**/*.lean' | LC_ALL=C sort -u > "$work/intree"
  LC_ALL=C comm -23 "$work/ondisk" "$work/intree" | sed 's#\.lean$##; s#/#.#g' > "$work/foreign"
  awk -v f="$work/foreign" 'BEGIN{while ((getline l < f) > 0) d[l]=1} !($1 in d)' \
      scripts/rot-guard/secure-compilation.txt > "$work/manifest"
  # An empty result means the filter failed, not that the manifest is empty.
  [ -s "$work/manifest" ] || { echo "commit-own: the manifest filter produced an empty file; nothing committed." >&2; exit 1; }
  cp "$work/manifest" scripts/rot-guard/secure-compilation.txt
fi
GIT_INDEX_FILE="$idx" generate || { echo "commit-own: a list generator failed; nothing committed." >&2; exit 1; }

[ "$(git rev-parse HEAD)" = "$head0" ] || { echo "commit-own: HEAD moved while the lists were generated; nothing committed. Retry." >&2; exit 1; }
changed=()
for l in "${lists[@]}"; do git diff --quiet HEAD -- "$l" 2>/dev/null || changed+=("$l"); done
git commit "${msgargs[@]}" -- "${paths[@]}" "${changed[@]}"
rc=$?
[ "$rc" = 0 ] && committed=1
exit $rc
