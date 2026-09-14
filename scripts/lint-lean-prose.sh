#!/usr/bin/env bash
# Flag changelog / defensive / LLM-diction prose in Lean docstrings and comments.
#
# Rule: git is the changelog. A Lean docstring states what the definition or
# theorem IS, plainly — no "extends/unlike/no longer" (changelog), no
# "honest/genuine/faithful/not merely" (defensive), no "workhorse/leverage/
# seamless" (inflated diction).
#
# Usage:
#   scripts/lint-lean-prose.sh [FILE ...]        # lint the given files
#   scripts/lint-lean-prose.sh                   # lint staged .lean files
#   scripts/lint-lean-prose.sh --docs            # lint the documents in DOCLIST
#
# Exit 1 if any banned phrase is found. The pattern set is deliberately
# high-confidence (words that essentially never appear in Lean code), so a hit is
# a real prose smell, not a false positive. Judgment-call filler (robust,
# powerful, comprehensive, previously, "not just") is NOT hard-gated here.
#
# SCOPE: this is a per-file lint, not a tree-wide gate. 913 of the 1984 tracked
# `.lean` files in this package carry at least one hit, so running it over the
# whole tree would be permanently red and therefore ignored. CI runs it on files a
# change ADDS, and the pre-commit hook runs it on staged files; both are ratchets
# that clean the tree forward.
#
# `--docs` gates the documents named in scripts/prose-lint-docs.txt, and fails when
# a tracked Markdown file, Verso manual file (`docs/*.lean`) or blueprint source
# (`blueprint/*.tex`) is not named there.
set -uo pipefail

DOCLIST="scripts/prose-lint-docs.txt"

files=("$@")
if [ "${1:-}" = "--docs" ]; then
  root="$(git rev-parse --show-toplevel 2>/dev/null)" && cd "$root" || exit 2
  [ -f "$DOCLIST" ] || { echo "lint-lean-prose: no $DOCLIST"; exit 2; }
  mapfile -t files < <(grep -vE '^\s*(#|$)' "$DOCLIST")
  missing=0
  for f in "${files[@]}"; do
    [ -f "$f" ] || { echo "  MISSING: $f (listed in $DOCLIST)"; missing=1; }
  done
  [ "$missing" -eq 1 ] && { echo "lint-lean-prose: $DOCLIST names a file that does not exist — a rename left it stale."; exit 1; }
  unlisted=$(LC_ALL=C comm -23 \
    <(git ls-files '*.md' 'docs/*.lean' 'blueprint/*.tex' | grep -vx 'docs/lakefile.lean' | LC_ALL=C sort) \
    <(printf '%s\n' "${files[@]}" | LC_ALL=C sort))
  if [ -n "$unlisted" ]; then
    printf '  UNLISTED: %s\n' $unlisted
    echo "lint-lean-prose: tracked document(s) above are not in $DOCLIST; add each to the list."
    exit 1
  fi
elif [ ${#files[@]} -eq 0 ]; then
  mapfile -t files < <(git diff --cached --name-only --diff-filter=ACM 2>/dev/null | grep '\.lean$')
fi
[ ${#files[@]} -eq 0 ] && exit 0

# Defensive/boast, changelog, meta/self-talk, inflated LLM diction.
pat='honestly|honest scope|honest reduction|honest answer|honest about|being honest|to be honest|the honest truth|genuine|genuinely|not merely|merely trusted|this file gives|no longer|worth noting|it .s worth|in short|the upshot|for now|workhorse|load-bearing|cornerstone|backbone|linchpin|keystone|leverage|utilize|seamless|state-of-the-art|cutting-edge|game-changer|revolutionize|tapestry|delve|deep dive|not merely trusted|verdict|not fabricated|stated not claimed|the stopped attempt|the genuine gains'

# Domain vocabulary that shares a word with the banned set: the (genuine UC)
# docstring tag and the honest-verifier / honest-majority / honest-party crypto
# terms. A line matching one of these is exempt.
exempt='genuine UC|honest.?verifier|honest.?majorit|honest part|honest.?but.?curious|honest prover|honest sender|honest receiver|inductive Verdict|Finding\.verdict|\.verdict with|verdict : Verdict'

hits=0
for f in "${files[@]}"; do
  [ -f "$f" ] || continue
  while IFS= read -r line; do
    echo "  $f:$line"
    hits=$((hits + 1))
  done < <(grep -niE "\b(${pat})\b" "$f" | grep -viE "$exempt")
done

if [ "$hits" -gt 0 ]; then
  echo ""
  echo "lint-lean-prose: $hits changelog/defensive/LLM-diction phrase(s) in Lean docstrings."
  echo "Rule: git is the changelog; state what the definition/theorem IS, plainly."
  exit 1
fi
exit 0
