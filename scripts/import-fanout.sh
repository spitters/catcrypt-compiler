#!/usr/bin/env bash
# Rebuild fan-out per module, read from the import headers without a build.
#
# The fan-out of a module M is the number of tracked modules that import M
# directly or transitively: the modules Lake rebuilds after an edit to M whose
# exported interface changes. Only imports between modules of the current
# repository are followed.
#
# Usage (from a repository root):
#   scripts/import-fanout.sh               # top 20 modules by fan-out, summary
#   scripts/import-fanout.sh --top 50      # top 50
#   scripts/import-fanout.sh MOD...        # fan-out of the named modules
#   scripts/import-fanout.sh --importers MOD   # direct importers of MOD
#
# Run it before and after narrowing imports to measure the change.

set -euo pipefail

top=20
importers=""
mods=()
while [ $# -gt 0 ]; do
  case "$1" in
    --top) top="$2"; shift 2 ;;
    --importers) importers="$2"; shift 2 ;;
    -h|--help) sed -n '2,15p' "$0"; exit 0 ;;
    *) mods+=("$1"); shift ;;
  esac
done

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

git ls-files '*.lean' | grep -v 'lakefile\.lean$' > "$tmp/files"
sed 's/\.lean$//; s#/#.#g' "$tmp/files" | sort -u > "$tmp/modules"

# Edge list "imported importer", restricted to tracked modules.
while read -r f; do
  [ -f "$f" ] || continue
  m=${f%.lean}; m=${m//\//.}
  { grep -E '^(public )?(meta )?(private )?import ' "$f" || true; } | awk -v m="$m" '{print $NF, m}'
done < "$tmp/files" | sort -u > "$tmp/edges.all"
awk 'NR==FNR {mod[$1]; next} ($1 in mod)' "$tmp/modules" "$tmp/edges.all" > "$tmp/edges"

if [ -n "$importers" ]; then
  awk -v t="$importers" '$1 == t {print $2}' "$tmp/edges" | sort
  exit 0
fi

awk '
{ imp[$1] = imp[$1] " " $2 }
FILENAME == ARGV[2] { nodes[$1] }
END {
  for (n in nodes) {
    delete seen; cnt = 0; q[0] = n; h = 0; t = 1
    while (h < t) {
      x = q[h++]; k = split(imp[x], a, " ")
      for (i = 1; i <= k; i++) if (!(a[i] in seen)) { seen[a[i]]; cnt++; q[t++] = a[i] }
    }
    print cnt, n
  }
}' "$tmp/edges" "$tmp/modules" | sort -rn > "$tmp/fanout"

if [ ${#mods[@]} -gt 0 ]; then
  for m in "${mods[@]}"; do
    awk -v m="$m" '$2 == m' "$tmp/fanout"
  done
  exit 0
fi

head -n "$top" "$tmp/fanout"
awk '{s += $1; if ($1 == 0) z++} END {
  printf "modules %d, mean fan-out %.1f, no importer %d\n", NR, s / NR, z }' "$tmp/fanout"
