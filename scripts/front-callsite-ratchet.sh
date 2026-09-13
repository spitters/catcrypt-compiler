#!/usr/bin/env bash
# Rolled-loop front call-site ratchet.
#
# The rolled-loop front is a DISPATCHED FAMILY, not a menu of entry points:
# `Dialects/FrontRoutePlan.lean` indexes it by four axes (loop shape, body front,
# continuation, post-pass), derives them from the `LowCT` source with `analyse`,
# dispatches with `compile` / `compileLoop` / `compileNested` / `compileBlock`,
# and reports an uncovered combination as a `RouteGap` naming the axis. A call
# site that instead names one of the combinators reaches past the dispatcher: it
# pins one point of the family by hand, so a route change has to be replayed at
# every such site, and the site carries the body front's `frontLoopBodyJ … = some
# update` side condition itself instead of reading the denotation off the
# dispatcher's `CompileResult`.
#
# This guard counts the modules that still do that, and FAILS when the count
# grows.
#
# ---------------------------------------------------------------------------
# DISCRIMINATOR
# ---------------------------------------------------------------------------
# A file counts when, after docstrings, line comments and string literals are
# removed, it still names one of the seven rolled-loop combinators as a bare
# identifier:
#
#     rolledForLoopN          rolledForLoopNC        rolledForLoopNV
#     rolledForLoopNRt        rolledForLoopNRtC      rolledForLoopNRtNested
#     rolledWhileNzComL
#
# The match is word-bounded on the exact identifier, which is what draws the
# three lines the task needs:
#
#   * PROSE does not count. A docstring saying a kernel is sourced through
#     `rolledForLoopNRt` describes the route; it is not a call. Comment and
#     string-literal text is stripped before the match, the same way
#     `scripts/handcom-provenance-ratchet.sh` does it.
#   * A LEMMA ABOUT A COMBINATOR does not count. `rolledForLoopNRtC_denote`,
#     `rolledForLoopNRtCont`, `rolledForLoopNRtNestedC` and the rest are distinct
#     identifiers, and `\b` after the combinator name does not match them. A site
#     whose program comes from `FrontRoutePlan.compileLoop` and whose denotation
#     proof applies the route's own `_denote` lemma is dispatched, and reads as
#     dispatched.
#   * A `#guard` PINNING A ROUTE does not count, for the same reason: those pin
#     `analyse` / `split` / `bodyFrontOf` decisions and name no combinator.
#
# EXEMPT: the front family itself, listed in scripts/front-callsite-exempt.txt —
# the modules that DEFINE the combinators, the `*Cont`/`_ret_here` equations
# relating them, the `RolledFront` bundler and the `FrontRoutePlan` dispatcher.
# Those name the combinators because they are the thing a call site is supposed
# to go through.
#
# RATCHET: the count must be MONOTONE NON-INCREASING. The guard FAILS if it GROWS
# (a new module reached past the dispatcher), and AUTO-TIGHTENS the baseline
# (rewrites scripts/front-callsite-baseline.txt) when it SHRINKS. It does not
# require migrating the existing sites; it only forbids growth while they move.
#
# Run from anywhere in the repo: `bash scripts/front-callsite-ratchet.sh`
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
BASELINE_FILE="scripts/front-callsite-baseline.txt"
EXEMPT_FILE="scripts/front-callsite-exempt.txt"

COMBINATOR_RE='\b(rolledForLoopN|rolledForLoopNC|rolledForLoopNV|rolledForLoopNRt|rolledForLoopNRtC|rolledForLoopNRtNested|rolledWhileNzComL)\b'

# Source text with docstrings/comments and string literals removed.
code_text() {
  perl -0777 -ne '
    s{/-.*?-/}{}gs;
    s{--[^\n]*}{}g;
    s{"(?:[^"\\]|\\.)*"}{""}gs;
    print;' "$1"
}

# The list may name no path at all: the front family lives in the compiler
# package (../catcrypt-compiler), which carries its own copy of this ratchet,
# and a path is listed in the tree that holds it. `grep` exits 1 on no match,
# which `set -e` must not read as a failure.
exempt_paths() {
  { sed 's/[[:space:]]*#.*$//' "$EXEMPT_FILE" | grep -E '^(CatCrypt|bench)/' || true; } | sort
}

# The exemption list is keyed by path, so a rename silently voids an exemption
# and turns the renamed front module into a phantom "new call site". Every listed
# path must resolve to a file.
STALE_EXEMPT="$(exempt_paths | while IFS= read -r p; do [ -f "$p" ] || echo "$p"; done)"
if [ -n "$STALE_EXEMPT" ]; then
  echo "FAIL: $EXEMPT_FILE names path(s) that do not exist."
  echo "      Point each line at the current path, or drop it if the module is gone:"
  printf '        %s\n' $STALE_EXEMPT
  exit 1
fi

EXEMPT_LIST="$(mktemp)"
TMP="$(mktemp)"
trap 'rm -f "$EXEMPT_LIST" "$TMP"' EXIT
exempt_paths > "$EXEMPT_LIST"

{
  for f in $(grep -rlE 'rolled(ForLoopN|WhileNzComL)' --include='*.lean' CatCrypt/ bench/); do
    if grep -qxF "$f" "$EXEMPT_LIST"; then continue; fi
    if code_text "$f" | grep -E "$COMBINATOR_RE" >/dev/null; then echo "$f"; fi
  done
} | sort -u > "$TMP"
CURRENT="$(grep -c . "$TMP" || true)"

# Baseline = first integer line; the file also stores the sorted path list (after
# the count) so a FAIL can name exactly which module is new, and a reviewer can
# see which sites are left.
baseline_paths() {
  { sed 's/[[:space:]]*#.*$//' "$BASELINE_FILE" | grep -E '^(CatCrypt|bench)/' || true; } | sort
}
BASELINE="$(grep -m1 -oE '^[0-9]+' "$BASELINE_FILE" || echo 0)"
echo "Rolled-loop combinator call sites: current=$CURRENT  baseline=$BASELINE  (FrontRoutePlan-dispatched sites exempt)"

if [ "$CURRENT" -gt "$BASELINE" ]; then
  echo ""
  echo "FAIL: the rolled-loop combinator call-site count GREW ($BASELINE -> $CURRENT)."
  echo "      The rolled-loop front is a dispatched family: route the new site through"
  echo "      FrontRoutePlan.compile (whole LowCT source in, plan + CompileResult out —"
  echo "      its denote_prog carries no front hypothesis), or, when the site fixes the"
  echo "      axes itself, through FrontRoutePlan.compileLoop / compileNested /"
  echo "      compileBlock at the axis literals. See"
  echo "      CatCrypt/Crypto/SecureCompilation/Dialects/FrontRoutePlan.lean."
  echo "      NEW call site(s) (not in the baseline):"
  comm -13 <(baseline_paths) "$TMP" | sed 's/^/        /'
  exit 1
fi

if [ "$CURRENT" -lt "$BASELINE" ]; then
  echo ""
  echo "Good — the count SHRANK ($BASELINE -> $CURRENT). Auto-tightening the baseline."
  {
    echo "$CURRENT"
    echo "# Modules naming a rolled-loop front combinator directly rather than reaching"
    echo "# it through FrontRoutePlan (frozen baseline; auto-tightened by"
    echo "# scripts/front-callsite-ratchet.sh). First line = count; the paths below are"
    echo "# the sites left to migrate."
    cat "$TMP"
  } > "$BASELINE_FILE"
fi

echo "OK: rolled-loop front call-site ratchet satisfied."
