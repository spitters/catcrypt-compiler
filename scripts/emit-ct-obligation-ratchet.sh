#!/usr/bin/env bash
# Constant-time obligation ratchet for artifact-writing modules.
#
# ## What this guards
#
# A kernel emitted for cryptographic use runs on secret inputs, so its leakage
# trace must not depend on them. The compiler decides that mechanically:
# `ConstantTimeCoverage.allDirect` (every instruction addresses memory by base
# plus a compile-time displacement) and its corollary `allDirect_constant_time`,
# with `ConstIndexFold.lcmdDirect` as the same check one layer up. Nothing
# forces an emitter to instantiate them, so a module can write a kernel out with
# no constant-time result at all, and nothing goes red.
#
# This guard counts the modules that WRITE an artifact (`IO.FS.writeFile` for text,
# `IO.FS.writeBinFile` for object files) and carry no constant-time result and no
# public-data declaration. It is a ratchet:
# the count may fall, never rise. A new emitter therefore has to do one of two
# things, the same choice the comparison dialect's `publicData` flag forces on a
# comparison op (`VIR/FieldEcCmpOps.lean`):
#
#   * discharge the obligation — a `_constant_time` theorem, or `allDirect` /
#     `lcmdDirect` / `blockLeak` / `ctSafe` named in the module; or
#   * declare the kernel public-data, by adding a line to
#     scripts/ct-public-data.txt with the reason its inputs carry no secret.
#
# The second is a claim about the kernel's use, not a property the compiler can
# check, which is why it is written down per module with its justification and
# reviewed like any other text.
#
# What the count does NOT say: that the shipped bytes are constant time. Every
# available result stops at the `Lcmd` body or the gathered `JInstr` block; none
# reaches the rendered text. That gap is recorded in the coverage module's own
# docstring, and this ratchet does not paper over it.
#
# Usage:
#   scripts/emit-ct-obligation-ratchet.sh            check against the baseline
#   scripts/emit-ct-obligation-ratchet.sh --list     list the modules counted
#   CT_WRITE_BASELINE=1 scripts/emit-ct-obligation-ratchet.sh   rewrite the baseline

set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

PUBLIC_DATA="scripts/ct-public-data.txt"
BASELINE="scripts/ct-obligation-baseline.txt"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# The calls that write an artifact: text and binary.
WRITER='IO\.FS\.write(File|BinFile)'

# Markers that a module discharges the obligation for what it emits.
CT_MARKER='_constant_time|blockLeak|allDirect|lcmdDirect|ctSafe|publicData|leakTrace'

# Modules declared public-data, with their reason after '#'.
: > "$tmp/public"
if [ -f "$PUBLIC_DATA" ]; then
  grep -vE '^[[:space:]]*(#|$)' "$PUBLIC_DATA" | sed -E 's/[[:space:]]*#.*$//' \
    | sed -E 's/[[:space:]]+$//' | LC_ALL=C sort -u > "$tmp/public"
fi

# Artifact writers with neither a constant-time result nor a declaration.
: > "$tmp/missing"
git ls-files -- 'CatCrypt/*.lean' 'CatCrypt/**/*.lean' | while IFS= read -r f; do
  grep -qE "$WRITER" "$f" || continue
  grep -qE "$CT_MARKER" "$f" && continue
  grep -qxF "$f" "$tmp/public" && continue
  echo "$f"
done > "$tmp/missing"

count=$(wc -l < "$tmp/missing")

if [ "${1:-}" = "--list" ]; then
  cat "$tmp/missing"
  exit 0
fi

# A declared module that has since gained a constant-time result, or stopped
# writing an artifact, is a stale declaration: report it, do not fail on it.
if [ -s "$tmp/public" ]; then
  while IFS= read -r p; do
    [ -f "$p" ] || { echo "  stale declaration (no such file): $p"; continue; }
    grep -qE "$WRITER" "$p" || echo "  stale declaration (writes no artifact): $p"
  done < "$tmp/public"
fi

base=0
[ -f "$BASELINE" ] && base=$(grep -vE '^[[:space:]]*(#|$)' "$BASELINE" | wc -l)

if [ "${CT_WRITE_BASELINE:-0}" = "1" ]; then
  { echo "# Artifact-writing modules with no constant-time result and no public-data"
    echo "# declaration. The ratchet in scripts/emit-ct-obligation-ratchet.sh fails when"
    echo "# this list GROWS. To leave it, a module either discharges the obligation"
    echo "# (allDirect / lcmdDirect / a _constant_time theorem) or is declared"
    echo "# public-data in scripts/ct-public-data.txt with its reason."
    cat "$tmp/missing"
  } > "$BASELINE"
  echo "emit-ct: baseline rewritten with $count modules."
  exit 0
fi

echo "emit-ct: $count artifact-writing modules carry no constant-time obligation (baseline $base)."
if [ "$count" -lt "$base" ]; then
  { echo "# Artifact-writing modules with no constant-time result and no public-data"
    echo "# declaration. The ratchet in scripts/emit-ct-obligation-ratchet.sh fails when"
    echo "# this list GROWS. To leave it, a module either discharges the obligation"
    echo "# (allDirect / lcmdDirect / a _constant_time theorem) or is declared"
    echo "# public-data in scripts/ct-public-data.txt with its reason."
    cat "$tmp/missing"
  } > "$BASELINE"
  echo "emit-ct: baseline tightened from $base to $count; commit $BASELINE."
  exit 0
fi
if [ "$count" -gt "$base" ]; then
  echo "  FAIL: the count rose from $base to $count."
  echo "        Modules new to the list:"
  LC_ALL=C comm -23 <(LC_ALL=C sort -u "$tmp/missing") \
    <(grep -vE '^[[:space:]]*(#|$)' "$BASELINE" 2>/dev/null | LC_ALL=C sort -u) \
    | sed 's/^/          /'
  echo "        Each must either discharge the obligation (allDirect / lcmdDirect /"
  echo "        a _constant_time theorem) or be declared in $PUBLIC_DATA with the"
  echo "        reason its inputs are public."
  exit 1
fi
echo "OK: emit constant-time obligation ratchet satisfied."
exit 0
