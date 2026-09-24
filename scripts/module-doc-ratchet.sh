#!/usr/bin/env bash
# Module-docstring ratchet: a NEW .lean file of substance carries a module
# docstring with a `## Main results` (or `## Main definitions`) section.
#
# Why: what a module offers is described in its docstring, and the per-file
# `Main results` section is the one index that cannot rot — the commit that adds
# a theorem edits the file that describes it. A standalone index drifts, because
# nothing ties its update to the edit it describes. A minority of the files over
# the line threshold carry the section; this ratchet grows that forward on new
# files only, with no retrofit.
#
# Usage: module-doc-ratchet.sh <NewFile.lean> [...]
#   Callers pass NEW files only (pre-commit: --diff-filter=A staged; CI: added
#   vs base). Files under the exempt threshold or in exempt trees pass.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

# A file below this many lines is a shim, a re-export, or a tiny leaf; the
# section would be noise there. Dev-side CatCrypt shims are ~10 lines.
MIN_LINES=80

# Generated or mirrored trees whose files are not authored here.
EXEMPT_RE='^(.*/\.lake/)'

FAILED=0
for f in "$@"; do
  case "$f" in *.lean) ;; *) continue ;; esac
  [ -f "$f" ] || continue
  [[ "$f" =~ $EXEMPT_RE ]] && continue
  lines="$(wc -l < "$f")"
  [ "$lines" -lt "$MIN_LINES" ] && continue
  if ! grep -q '/-!' "$f"; then
    echo "FAIL: $f ($lines lines) has no module docstring (/-! ... -/)."
    FAILED=1
    continue
  fi
  if ! grep -qE '^##? Main (results|definitions)' "$f"; then
    echo "FAIL: $f ($lines lines) has a module docstring but no '## Main results'"
    echo "      (or '## Main definitions') section naming what the file exports."
    FAILED=1
  fi
done

if [ "$FAILED" -ne 0 ]; then
  echo ""
  echo "A new module states its main results in its module docstring, mathlib-style:"
  echo ""
  echo "    /-!"
  echo "    # <What this module is>"
  echo ""
  echo "    ## Main results"
  echo ""
  echo "    * \`thm_name\`: one line saying what it states"
  echo "    -/"
  echo ""
  echo "This is the index a reader and a search hit first; a file without it is"
  echo "invisible to concept search and gets rediscovered instead of reused."
  exit 1
fi
exit 0
