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
restore() { for l in "${lists[@]}"; do [ -f "$work/$(printf '%s' "$l" | tr / _)" ] && cp "$work/$(printf '%s' "$l" | tr / _)" "$l"; done; rm -rf "$work"; }
trap restore EXIT
for l in "${lists[@]}"; do [ -f "$l" ] && cp "$l" "$work/$(printf '%s' "$l" | tr / _)"; done

for p in "${paths[@]}"; do
  [ -e "$p" ] && ! git ls-files --error-unmatch -- "$p" >/dev/null 2>&1 && git add -N -- "$p"
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
  awk 'NR==FNR{d[$0]=1; next} !($1 in d)' "$work/foreign" scripts/rot-guard/secure-compilation.txt > "$work/manifest" \
    && cp "$work/manifest" scripts/rot-guard/secure-compilation.txt
fi
GIT_INDEX_FILE="$idx" generate || { echo "commit-own: a list generator failed; nothing committed." >&2; exit 1; }

[ "$(git rev-parse HEAD)" = "$head0" ] || { echo "commit-own: HEAD moved while the lists were generated; nothing committed. Retry." >&2; exit 1; }
changed=()
for l in "${lists[@]}"; do git diff --quiet HEAD -- "$l" 2>/dev/null || changed+=("$l"); done
git commit "${msgargs[@]}" -- "${paths[@]}" "${changed[@]}"
rc=$?
exit $rc
