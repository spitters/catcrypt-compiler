#!/usr/bin/env bash
# Ascent no-miracle (non-vacuity) ratchet.
#
# `CorresJ SR P fa c := ∀ st a, SR st a → P a → SR (runBlock st c) (fa a)` and
# `BytesCorresJ SR P fa n bs := ∃ c, decodeJStream n bs = some c ∧ CorresJ SR P fa c`
# are refinement judgments in a partial style: if the state relation `SR` and the
# guard `P` have no common witness, the judgment holds of every `c` (and, for
# `BytesCorresJ`, of every `n`/`bs` too) with no content about the block at all. This
# is the seL4/AutoCorres `no_fail`/`empty_fail` situation transplanted: a hole in the
# precondition is a hole the correspondence proof can fall through, silently.
#
# `srmem_carryMulMid_satisfiable` (Ascent/CarryMulCorres.lean) is the existing
# instance of the discharge: `∃ st a, SRmem carryMulMidCells st a`, an explicit state
# and array satisfying the layout. This script generalises that pattern into a
# ratchet: every `SR`-named state-relation this tree passes to `CorresJ` or
# `BytesCorresJ` must have such a witness statement, in the module that states the
# correspondence or a module that module imports.
#
# SCOPE, read before trusting the number this script prints:
#
#   * It recognises only NAMED state relations matching `SR[A-Za-z0-9]+` — the
#     `def`/`abbrev SRxxx (state) (abstract) : Prop` layout-predicate convention this
#     tree already uses uniformly (`SRmem`, `SRm`, `SRcarry`, `SRx`, `SRalloc`, …,
#     30+ instances). It does NOT check the GUARD argument (`P` above): in this tree
#     that argument is almost always an inline lambda (`fun a => a.stage = 0 ∧ …`,
#     93 occurrences), which a line-oriented grep cannot name or reason about. A
#     module can pass this script while its guard alone is unsatisfiable; that
#     obligation is not covered here and needs either a naming convention for
#     guards or an LSP-driven checker.
#   * The witness search is per state-relation HEAD IDENTIFIER, not per fully
#     applied term. `SRmem carryMulMidCells` and `SRmem carryMulTailCells` are both
#     "the predicate SRmem" to this script; if a module used `SRmem` at a third,
#     unwitnessed cell list, this script would not notice as long as `SRmem` has a
#     witness for SOME argument somewhere in scope. `srmem_carryMulMid_satisfiable`
#     and `srmem_carryMulTail_satisfiable` both exist today, so this is not yet a
#     live gap, but it is a real one: state it, do not fix it silently here.
#   * A witness is recognised when `∃` and the state-relation's identifier appear
#     within a two-line sliding window — the shape every witness in this tree today
#     has (`∃ st a, SRmem carryMulMidCells st a`, or the same with the relation
#     wrapped by a combinator that pushes it onto the next line). A witness whose
#     `∃` and identifier are three or more lines apart is invisible to this script.
#   * "Module M states a correspondence over SR" is recognised when `CorresJ` or
#     `BytesCorresJ` and an `SR`-token appear within a two-line sliding window (the
#     judgment name on its own line, its first argument — possibly wrapped in one
#     combinator such as `FrameRel SRm` or `SRalloc ns ρ SRm` — on the next, this
#     tree's common line break). A judgment name and its state-relation argument
#     spread across three or more lines is still invisible to this script.
#   * Committed (HEAD) modules only, for the reasons `ascent-anchor-ratchet.sh`
#     already documents (concurrent-session snapshot races): read that script's
#     header before changing the snapshot mechanics here, they are copied from it.
#
# Usage: bash scripts/ascent-nonvacuity-ratchet.sh [--list | --record]
set -uo pipefail
cd "$(dirname "$0")/.."

baseline=scripts/ascent-nonvacuity-baseline.txt
mode="${1:-}"

files=$(git ls-tree -r --name-only HEAD -- CatCrypt/Crypto/SecureCompilation/Ascent \
                                           CatCrypt/Hax/Ascent | grep '\.lean$' | sort)
[ -n "$files" ] || { echo "ascent-nonvacuity: no ascent modules found"; exit 1; }

mod_of() { printf '%s' "${1%.lean}" | tr '/' '.'; }

# Same robust-snapshot mechanics as ascent-anchor-ratchet.sh: HEAD only, retried
# archive-then-extract with a count check, because a `git show` per file or a bare
# working-tree read races with concurrent sessions and gives a different verdict
# run to run.
snap=$(mktemp -d)
trap 'rm -rf "$snap" "${tmp:-}"' EXIT
want=$(printf "%s\n" "$files" | wc -l)
ok=0
for _ in 1 2 3; do
  rm -rf "${snap:?}"/* 2>/dev/null
  if git archive HEAD -- CatCrypt/Crypto/SecureCompilation/Ascent CatCrypt/Hax/Ascent \
       > "$snap/.snapshot.tar" 2>/dev/null &&
     tar -x -C "$snap" -f "$snap/.snapshot.tar" 2>/dev/null &&
     [ "$(find "$snap" -name '*.lean' | wc -l)" -eq "$want" ]; then
    ok=1; break
  fi
done
[ "$ok" -eq 1 ] || { echo "ascent-nonvacuity: cannot snapshot HEAD ($want modules expected)"; exit 1; }
file_text() { cat "$snap/$1"; }
# Strip block comments/docstrings and line comments. NOT the `sed -e '/\/-/,/-\//d'`
# pattern `ascent-anchor-ratchet.sh` uses: GNU sed's regex end-address is searched
# for starting on the line AFTER the start address matched, even when the start
# line itself already contains the end pattern, so two adjacent single-line
# docstrings (`/-- x. -/` ... `/-- y. -/`) delete everything between them, not just
# themselves (measured 2026-09-19: `printf 'a\n/-- x. -/\nb\nc\n/-- y. -/\nd\n' | sed
# -e '/\/-/,/-\//d'` prints only `a` and `d`, silently swallowing `b` and `c`, and
# swallowed a real theorem statement between two single-line docstrings in
# S2nMontmulP384Framed.lean while developing this script). A one-pass depth-counted
# scan closes a block comment on the same line it opens on. It does not handle a
# `/-`/`-/`/`--` token appearing inside a string literal; none of the state
# relations or witness statements this script looks for occur inside a string in
# this tree.
code_of() {
  file_text "$1" | awk '
    { line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        c2 = substr(line, i, 2)
        if (!indoc && c2 == "--") break
        if (!indoc && c2 == "/-") { indoc++; i += 2; continue }
        if (indoc && c2 == "-/") { indoc--; if (indoc < 0) indoc = 0; i += 2; continue }
        if (!indoc) out = out substr(line, i, 1)
        i++
      }
      print out
    }'
}

tmp=$(mktemp -d)
: > "$tmp/uses"      # module<TAB>SR-name    (module states a correspondence over SR-name)
: > "$tmp/witness"   # module<TAB>SR-name    (module's OWN code witnesses SR-name)
: > "$tmp/imports"   # module<TAB>imported-ascent-module

for f in $files; do
  m=$(mod_of "$f")
  code=$(code_of "$f")

  # Lines stating a correspondence: the judgment name and an SR-token within a
  # two-line sliding window (see SCOPE above for what this misses).
  windows=$(awk 'NR>1{print prev " " $0} {prev=$0}' <<< "$code")
  judgment_lines=$(grep -E 'CorresJ |CorresJ$|BytesCorresJ' <<< "$windows" || true)
  if [ -n "$judgment_lines" ]; then
    grep -oE 'SR[A-Za-z0-9]+' <<< "$judgment_lines" | sort -u | while read -r name; do
      printf '%s\t%s\n' "$m" "$name" >> "$tmp/uses"
    done
  fi

  # Witness windows: ∃ and an SR-token within a two-line sliding window, anywhere in
  # the module (the theorem name is not constrained; `_satisfiable` is this tree's
  # convention but not required).
  exist_windows=$(grep -F '∃' <<< "$windows" || true)
  if [ -n "$exist_windows" ]; then
    grep -oE 'SR[A-Za-z0-9]+' <<< "$exist_windows" | sort -u | while read -r name; do
      printf '%s\t%s\n' "$m" "$name" >> "$tmp/witness"
    done
  fi

  file_text "$f" | grep -oE "^ *(public |private |meta |public meta )*import (all )?[A-Za-z0-9_.]+" |
    awk '{print $NF}' | while read -r i; do
      case "$i" in
        CatCrypt.Crypto.SecureCompilation.Ascent.*|CatCrypt.Hax.Ascent.*)
          printf '%s\t%s\n' "$m" "$i" >> "$tmp/imports" ;;
      esac
    done
done

sort -u -o "$tmp/uses" "$tmp/uses"
sort -u -o "$tmp/witness" "$tmp/witness"
sort -u -o "$tmp/imports" "$tmp/imports"

# For each module, its transitive ascent-import closure (including itself): a plain
# per-node BFS over the import edges (both sides small — well under a thousand
# edges — so the O(V*E) cost of a BFS per node is not worth trading for a fixpoint
# join, which is exactly the kind of collation-order-sensitive construction that
# made the anchor ratchet flap run to run; see its header).
awk -F'\t' '
  { adj[$1 SUBSEP ++cnt[$1]] = $2; seen[$1] = 1; seen[$2] = 1 }
  END {
    for (m in seen) {
      delete visited
      visited[m] = 1
      queue[0] = m; qs = 0; qe = 1
      while (qs < qe) {
        cur = queue[qs]; qs++
        for (k = 1; k <= cnt[cur]; k++) {
          nxt = adj[cur SUBSEP k]
          if (!(nxt in visited)) { visited[nxt] = 1; queue[qe] = nxt; qe++ }
        }
      }
      for (v in visited) print m "\t" v
    }
  }
' "$tmp/imports" > "$tmp/closure_pairs"

# violations: (module, name) in uses such that no module in module's closure has a
# matching witness line.
: > "$tmp/violations"
: > "$tmp/ok"
while IFS=$'\t' read -r m name; do
  found=0
  closure_ms=$(grep -P "^\Q$m\E\t" "$tmp/closure_pairs" | cut -f2)
  [ -z "$closure_ms" ] && closure_ms="$m"
  while IFS= read -r cm; do
    [ -z "$cm" ] && continue
    if grep -qP "^\Q$cm\E\t\Q$name\E\$" "$tmp/witness"; then found=1; break; fi
  done <<< "$closure_ms"
  if [ "$found" -eq 1 ]; then
    printf '%s\t%s\n' "$m" "$name" >> "$tmp/ok"
  else
    printf '%s\t%s\n' "$m" "$name" >> "$tmp/violations"
  fi
done < "$tmp/uses"

sort -u -o "$tmp/violations" "$tmp/violations"
sort -u -o "$tmp/ok" "$tmp/ok"

n_uses=$(wc -l < "$tmp/uses")
n_ok=$(wc -l < "$tmp/ok")
n_bad=$(wc -l < "$tmp/violations")

if [ "$mode" = "--list" ]; then
  echo "# witnessed ($n_ok of $n_uses module/predicate pairs):"
  sed 's/^/  /' "$tmp/ok"
  echo "# unwitnessed ($n_bad):"
  sed 's/^/  /' "$tmp/violations"
  exit 0
fi

if [ "$mode" = "--record" ]; then
  {
    echo "# Ascent module/predicate pairs where a module states CorresJ or BytesCorresJ"
    echo "# over a named SR-style state relation with no satisfiability witness (a"
    echo "# theorem \`∃ st a, SRxxx ... st a\`, or equivalent) in the module or a module it"
    echo "# imports. Each line: module<TAB>SR-name<TAB>reason. Recorded by"
    echo "# scripts/ascent-nonvacuity-ratchet.sh --record."
    while IFS=$'\t' read -r m name; do
      old=$(grep -P "^\Q$m\E\t\Q$name\E\t" "$baseline" 2>/dev/null | head -1)
      if [ -n "$old" ]; then echo "$old"; else printf '%s\t%s\tno reason recorded\n' "$m" "$name"; fi
    done < "$tmp/violations"
  } > "$baseline.new"
  mv "$baseline.new" "$baseline"
  echo "ascent-nonvacuity: recorded $n_bad unwitnessed pair(s) in $baseline"
  exit 0
fi

fail=0
if [ -f "$baseline" ]; then
  base_keys=$(grep -v '^#' "$baseline" | cut -f1,2 | sort -u)
  new=$(comm -23 <(cut -f1,2 "$tmp/violations" | sort -u) <(printf '%s\n' "$base_keys"))
  if [ -n "$new" ]; then
    echo "ASCENT-NONVACUITY: module/predicate pair with no satisfiability witness,"
    echo "  and not in $baseline:"
    printf '%s\n' "$new" | sed 's/^/    /'
    echo "  -> add a \`∃ st a, SRxxx ... st a\`-shaped witness (see"
    echo "     Ascent/CarryMulCorres.lean's srmem_carryMulMid_satisfiable), or record"
    echo "     it with its reason: bash scripts/ascent-nonvacuity-ratchet.sh --record"
    fail=1
  fi
  gone=$(comm -13 <(cut -f1,2 "$tmp/violations" | sort -u) <(printf '%s\n' "$base_keys"))
  if [ -n "$gone" ]; then
    echo "ascent-nonvacuity: $(printf '%s\n' "$gone" | grep -c .) baseline entr(y/ies) now witnessed; run --record to drop them."
  fi
else
  echo "ascent-nonvacuity: no baseline; run --record to create $baseline"
  fail=1
fi

base_n=$(grep -vc '^#' "$baseline" 2>/dev/null || echo 0)
echo "ascent-nonvacuity: $n_uses module/predicate pair(s) state a correspondence over a named SR-predicate, $n_ok witnessed, $n_bad unwitnessed (baseline ${base_n})."
[ "$fail" -eq 0 ] && echo "ascent-nonvacuity: OK"
exit $fail
