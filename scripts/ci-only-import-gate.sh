#!/usr/bin/env bash
# CI-only import gate.
#
# A module listed in scripts/ci-only-modules.txt costs more memory than a development
# box has, so it is built only in CI. Any module that imports it inherits that cost,
# and on a development box the symptom is a build killed by the OOM guard with nothing
# naming the cause. This gate fails when a module outside the list imports one inside
# it: a module may depend on a CI-only module only by being CI-only itself.
#
# Usage: bash scripts/ci-only-import-gate.sh        (exit 1 on a violation)
set -uo pipefail
cd "$(dirname "$0")/.."
list=scripts/ci-only-modules.txt
[ -f "$list" ] || { echo "ci-only-import-gate: no $list"; exit 0; }

# Module names of the CI-only files: path → dotted name.
mapfile -t ciMods < <(grep -v '^#' "$list" | cut -f1 | sed 's|/|.|g; s|\.lean$||' | sort -u)
[ "${#ciMods[@]}" -gt 0 ] || exit 0

pat=$(printf '%s\n' "${ciMods[@]}" | sed 's/\./\\./g' | paste -sd'|')
bad=0
while IFS= read -r f; do
  [ -f "$f" ] || continue
  mod=$(printf '%s' "$f" | sed 's|/|.|g; s|\.lean$||')
  # A CI-only module may import another.
  printf '%s\n' "${ciMods[@]}" | grep -qx "$mod" && continue
  hits=$(grep -nE "^(public |private )?(meta )?import[[:space:]]+($pat)[[:space:]]*$" "$f" || true)
  if [ -n "$hits" ]; then
    echo "ci-only-import-gate: $f imports a CI-only module:"
    printf '%s\n' "$hits" | sed 's/^/    /'
    bad=1
  fi
done < <(git ls-files 'CatCrypt/**/*.lean' '*.lean')
if [ "$bad" -ne 0 ]; then
  echo "A module that needs a CI-only module's declarations moves them down into a module both can import, or joins the list itself."
  exit 1
fi
echo "ci-only-import-gate: clean"
