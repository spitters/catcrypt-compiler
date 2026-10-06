#!/usr/bin/env bash
# Records a new module in the provenance lists that the CI gates read, with its reason,
# so that the commit which adds the module passes those gates. It complements the module
# registration (module block of the lakefile, rot-guard manifest), which is generated.
#
#   scripts/register-provenance.sh <path.lean> --infra "<reason>"
#       a module whose instruction terms are proof subjects or semantics, not an emitted
#       kernel: appended to scripts/handcom-infra-exempt.txt
#   scripts/register-provenance.sh <path.lean> --anchor "<reason>"
#       an ascent module not tied to a descent theorem or to bytes: its line in
#       scripts/ascent-anchor-baseline.txt gets the reason
#   scripts/register-provenance.sh <path.lean> --fixture
#       a module tagged `@ascent-fixture theorems: …` in its docstring: appended to
#       scripts/ascent-fixture-baseline.txt
# Several options may be given in one call. No step loads Lean.
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"; cd "$ROOT"
[ $# -ge 2 ] || { sed -n '2,15p' "$0"; exit 2; }
f="$1"; shift
[ -f "$f" ] || { echo "register-provenance: no such file: $f" >&2; exit 2; }
mod="$(printf '%s' "${f%.lean}" | tr / .)"
while [ $# -gt 0 ]; do
  case "$1" in
    --infra)
      [ -n "${2:-}" ] || { echo "--infra needs a reason" >&2; exit 2; }
      grep -q "^$f[[:space:]]" scripts/handcom-infra-exempt.txt \
        || printf '%s  # %s\n' "$f" "$2" >> scripts/handcom-infra-exempt.txt
      shift 2 ;;
    --anchor)
      [ -n "${2:-}" ] || { echo "--anchor needs a reason" >&2; exit 2; }
      grep -q "^$mod	" scripts/ascent-anchor-baseline.txt \
        || bash scripts/ascent-anchor-ratchet.sh --record >/dev/null 2>&1 || true
      python3 - "$mod" "$2" <<'PY'
import sys
mod, reason = sys.argv[1], sys.argv[2]
p = 'scripts/ascent-anchor-baseline.txt'
L = open(p).read().split('\n'); hit = False
for i, l in enumerate(L):
    if l.split('\t')[0] == mod:
        L[i] = mod + '\t' + reason; hit = True
if not hit:
    sys.exit(f"register-provenance: {mod} is not an unanchored ascent module at HEAD; commit the module first, then record the reason")
open(p, 'w').write('\n'.join(L))
PY
      shift 2 ;;
    --fixture)
      grep -q '@ascent-fixture theorems:' "$f" \
        || { echo "register-provenance: $f has no '@ascent-fixture theorems:' line in its docstring" >&2; exit 1; }
      grep -qxF "$f" scripts/ascent-fixture-baseline.txt || echo "$f" >> scripts/ascent-fixture-baseline.txt
      shift ;;
    *) echo "register-provenance: unknown option $1" >&2; exit 2 ;;
  esac
done
