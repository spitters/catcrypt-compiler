#!/usr/bin/env bash
# leak-kind-wildcard-lint.sh
#
# A leak-kind function has no wildcard arm that returns the quiet class.
#
# A leakage model classes each operation of a dialect by a function into
# `LeakKind` (`VIR/ComLevelCheck.lean`). An arm `| _ => .quiet` classes every
# constructor it does not name as leaking nothing, so a constructor added to the
# operation type later is constant time by default and no proof obligation
# appears. With every constructor listed, the addition is a compile error at the
# leak model.
#
# Checked declarations: a `def`, `abbrev`, `instance` or `theorem` whose
# signature ends in `LeakKind` (the result type), or whose signature names
# `LeakModel` (the `kind :=` field of a model). Refused inside them:
#
#   | _ => .quiet            | _, _ => LeakKind.quiet
#   fun _ => .quiet          | _ =>          (with `.quiet` on the next line)
#
# and, in a function with result type `LeakKind`, an arm whose pattern is one
# variable (`| op => ...`), which covers every constructor not named above it,
# and a conditional whose last branch is the quiet class:
#
#   else .quiet              else            (with `.quiet` on the next line)
#
# which classes every name or value the conditions above it do not test as
# leaking nothing. The quiet names are to be stated (`if quiet f then .quiet
# else <a leaking class>`).
#
# Allow-list: scripts/leak-kind-wildcard-allow.txt, one `path:declaration` per
# line, `#` comments. An entry carries its justification in a comment above it.
#
# Usage:
#   bash scripts/leak-kind-wildcard-lint.sh              # the tree
#   bash scripts/leak-kind-wildcard-lint.sh FILE...      # the named files
#
# Exit 0 when no arm is refused, 1 otherwise.

set -eu

cd "$(dirname "$0")/.."

ALLOW=scripts/leak-kind-wildcard-allow.txt

if [ "$#" -gt 0 ]; then
  FILES="$*"
else
  FILES=$(grep -rlE 'LeakKind|LeakModel' --include='*.lean' CatCrypt/ || true)
fi

if [ -z "$FILES" ]; then
  echo "leak-kind-wildcard-lint: no file mentions LeakKind or LeakModel."
  echo "RESULT: SKIP"
  exit 0
fi

allowed=""
if [ -f "$ALLOW" ]; then
  allowed=$(grep -vE '^[[:space:]]*(#|$)' "$ALLOW" || true)
fi

# shellcheck disable=SC2086
hits=$(awk '
  function flush_sig() {
    s = sig
    sub(/:=.*/, "", s)
    sub(/[ \t]+where[ \t]*$/, "", s)
    sub(/[ \t]+$/, "", s)
    kindfn = (s ~ /(→|->|:)[ \t]*LeakKind$/) ? 1 : 0
    leak = (kindfn || s ~ /LeakModel/) ? 1 : 0
    insig = 0
  }
  FNR == 1 { leak = 0; insig = 0; incomment = 0; pending = 0; epending = 0; name = "" }
  {
    line = $0
    if (incomment) { if (line ~ /-\//) incomment = 0; next }
    if (line ~ /^[ \t]*\/-/) { if (line !~ /-\//) incomment = 1; next }
    if (line ~ /^[ \t]*--/) next
    sub(/[ \t]--.*/, "", line)

    if (line ~ /^[ \t]*(@\[[^]]*\][ \t]*)*((private|protected|noncomputable|public|partial|unsafe)[ \t]+)*(def|abbrev|instance|theorem|lemma|structure|inductive|opaque|example)([ \t]|$)/) {
      name = line
      sub(/^[ \t]*(@\[[^]]*\][ \t]*)*((private|protected|noncomputable|public|partial|unsafe)[ \t]+)*(def|abbrev|instance|theorem|lemma|structure|inductive|opaque|example)[ \t]*/, "", name)
      sub(/[ \t(:{[].*/, "", name)
      sig = ""; insig = 1; leak = 0; pending = 0
    }
    if (insig) {
      if (line ~ /^[ \t]*\|/) { flush_sig() }
      else {
        sig = sig " " line
        if (line ~ /:=/ || line ~ /[ \t]where[ \t]*$/) flush_sig()
      }
    }
    if (!leak) { pending = 0; epending = 0; next }

    if (epending) {
      if (line ~ /^[ \t]*$/) next
      if (line ~ /^[ \t]*(LeakKind)?\.quiet([^A-Za-z0-9_]|$)/)
        printf "%s:%d:%s:%s\n", FILENAME, ependline, name, ependtext
      epending = 0
    }
    if (kindfn) {
      if (line ~ /(^|[^A-Za-z0-9_])else[ \t]+(LeakKind)?\.quiet([^A-Za-z0-9_]|$)/)
        printf "%s:%d:%s:%s\n", FILENAME, FNR, name, $0
      else if (line ~ /(^|[^A-Za-z0-9_])else[ \t]*$/) {
        epending = 1; ependline = FNR; ependtext = $0
      }
    }

    if (pending) {
      if (line ~ /^[ \t]*$/) next
      if (line ~ /^[ \t]*(LeakKind)?\.quiet([^A-Za-z0-9_]|$)/)
        printf "%s:%d:%s:%s\n", FILENAME, pendline, name, pendtext
      pending = 0
    }
    if (line ~ /\|[ \t]*_([ \t]*,[ \t]*_)*[ \t]*=>[ \t]*(LeakKind)?\.quiet([^A-Za-z0-9_]|$)/ ||
        line ~ /fun[ \t]+_([ \t]+_)*[ \t]*=>[ \t]*(LeakKind)?\.quiet([^A-Za-z0-9_]|$)/) {
      printf "%s:%d:%s:%s\n", FILENAME, FNR, name, $0
    } else if (line ~ /\|[ \t]*_([ \t]*,[ \t]*_)*[ \t]*=>[ \t]*$/) {
      pending = 1; pendline = FNR; pendtext = $0
    } else if (kindfn && line ~ /^[ \t]*\|[ \t]*[a-z][A-Za-z0-9_]*[ \t]*=>/ &&
               line !~ /^[ \t]*\|[ \t]*(none|true|false|nil|zero)[ \t]*=>/) {
      printf "%s:%d:%s:%s\n", FILENAME, FNR, name, $0
    }
  }
' $FILES)

FAILED=0
if [ -n "$hits" ]; then
  while IFS= read -r h; do
    file=${h%%:*}; rest=${h#*:}
    lineno=${rest%%:*}; rest=${rest#*:}
    decl=${rest%%:*}; text=${rest#*:}
    if printf '%s\n' "$allowed" | grep -qxF "$file:$decl"; then
      continue
    fi
    echo "$file:$lineno: catch-all arm in the leak-kind function \`$decl\`"
    echo "    $text"
    FAILED=$((FAILED + 1))
  done <<EOF
$hits
EOF
fi

if [ "$FAILED" -gt 0 ]; then
  echo ""
  echo "FAIL: $FAILED catch-all arm(s) class unnamed constructors."
  echo "      List every constructor of the operation type, so a constructor"
  echo "      added later is a compile error at the leak model; or add"
  echo "      \`path:declaration\` to $ALLOW with its justification."
  echo "RESULT: FAIL"
  exit 1
fi

echo "OK: no leak-kind function has a wildcard arm that returns the quiet class."
echo "RESULT: OK"
