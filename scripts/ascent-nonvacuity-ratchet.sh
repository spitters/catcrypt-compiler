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
#     30+ instances).
#   * The GUARD argument (`P` above) is checked SEPARATELY, by the second ratchet
#     below (the `guardsat` pass, baseline `scripts/ascent-guardsat-baseline.txt`),
#     because a script cannot see through the inline lambda (`fun a => a.stage = 0
#     ∧ …`, 93 occurrences in this tree) that argument almost always is. That pass
#     does not read the lambda either — nothing textual can — it only checks that a
#     THEOREM exists pairing the correspondence with a witness; the pairing itself
#     is checked by Lean's unifier at elaboration
#     (`CatCrypt/Crypto/SecureCompilation/Ascent/GuardSatisfiable.lean`), not by
#     this script. See "GUARD-SATISFIABILITY SCOPE" below for what that pass can
#     and cannot see. A module can pass the state-relation check below while its
#     guard is unsatisfiable; that is exactly the gap the second pass targets.
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
# GUARD-SATISFIABILITY SCOPE (the `guardsat` pass), read before trusting IT:
#
#   * A candidate is a theorem whose header, after comment-stripping, is exactly
#     `theorem NAME :` (optionally `private`/`protected`/`noncomputable`-prefixed)
#     with nothing else before the colon — i.e. a CLOSED statement, no explicit or
#     implicit binder — and whose body, before the first `:=`, mentions `CorresJ`
#     or `BytesCorresJ`. This is deliberately narrow: it is exactly the shape a
#     `GuardSatisfiable.corresJ_guardSat`/`bytesCorresJ_guardSat` application can
#     discharge (their `SR`/`P` come from the named constant's own zero-argument
#     type). A lemma taking hypotheses or bound variables before its `CorresJ`
#     conclusion (`corresJ_row`, `corresJ_append`, `encodeJBlock_bytesCorresJ`, …) is
#     invisible here on purpose: its guard is not a fixed closed term, so there is
#     nothing concrete to witness until some caller instantiates it — and that
#     instantiation, if it is itself a closed `NAME :` theorem, is caught in its own
#     right.
#   * A candidate is considered discharged when `corresJ_guardSat` or
#     `bytesCorresJ_guardSat`, followed by the candidate's exact name as a whole
#     word, appears in ANY ascent module. The pairing is not confined to the
#     candidate's import closure: a `_guardSat` corollary lives in a module that
#     IMPORTS the one stating the correspondence, since that is where the theorem is
#     in scope, which is the opposite direction from the state-relation pass. A Lean
#     theorem name is unambiguous, so the name alone identifies the candidate.
#     This script does NOT check that the paired witness has the right type,
#     or even that the pairing elaborates — it only checks that the pairing was
#     ATTEMPTED. The elaborator is the actual check: `corresJ_guardSat`/
#     `bytesCorresJ_guardSat` are stated with `SR`/`P` implicit
#     (`GuardSatisfiable.lean`), so Lean reads them off the candidate's own
#     elaborated type at the call site and rejects a witness of the wrong guard as
#     an ordinary type error. A `guard_satisfiable`-shaped call that fails to build
#     is a build failure, not a silent pass here — but this script cannot itself
#     tell a build failure from a build nobody has run; it is a presence check, and
#     the orchestrator's build is what makes the presence load-bearing.
#   * `Bytes_correct`-shaped results (`∃ c, decodeJStream n bs = some c ∧ ∀ st, …`)
#     are not `CorresJ`/`BytesCorresJ` at all — no named guard, no vacuity mode — so
#     this pass does not flag them, correctly: nothing.
#
# Usage: bash scripts/ascent-nonvacuity-ratchet.sh [--list | --record]
set -uo pipefail
cd "$(dirname "$0")/.."

baseline=scripts/ascent-nonvacuity-baseline.txt
guardsat_baseline=scripts/ascent-guardsat-baseline.txt
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
: > "$tmp/gs_candidates"  # module<TAB>theorem-name (a closed CorresJ/BytesCorresJ theorem)
: > "$tmp/gs_discharged"  # module<TAB>theorem-name (module's OWN code pairs it with a guardSat call)

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

  # Guard-satisfiability candidates: a CLOSED `theorem NAME :` header (no binder
  # before the colon) whose body, up to the first `:=`, mentions `CorresJ` or
  # `BytesCorresJ` (see "GUARD-SATISFIABILITY SCOPE" above for exactly why this
  # shape and no other).
  gs_names=$(awk '
    /^[[:space:]]*((private|protected|noncomputable)[[:space:]]+)*theorem[[:space:]]+[A-Za-z0-9_.'"'"']+[[:space:]]*:[[:space:]]*$/ {
      line = $0
      sub(/^[[:space:]]*/, "", line)
      sub(/^((private|protected|noncomputable)[[:space:]]+)*theorem[[:space:]]+/, "", line)
      sub(/[[:space:]]*:[[:space:]]*$/, "", line)
      name = line; pending = 1; found = 0; next
    }
    pending {
      if ($0 ~ /CorresJ|BytesCorresJ/) found = 1
      if ($0 ~ /:=/) { pending = 0; if (found) print name }
    }
  ' <<< "$code")
  if [ -n "$gs_names" ]; then
    while read -r name; do
      [ -z "$name" ] && continue
      printf '%s\t%s\n' "$m" "$name" >> "$tmp/gs_candidates"
    done <<< "$gs_names"
  fi

  # Guard-satisfiability discharge attempts: a `corresJ_guardSat`/
  # `bytesCorresJ_guardSat` call and the candidate's name within the same two-line
  # window used above. This only records that a pairing was ATTEMPTED; whether it
  # elaborates is Lean's job, not this script's (see the scope note).
  gs_calls=$(grep -oP '(corresJ_guardSat|bytesCorresJ_guardSat)\s+\K[A-Za-z0-9_.]+' <<< "$windows" || true)
  if [ -n "$gs_calls" ]; then
    while read -r name; do
      [ -z "$name" ] && continue
      printf '%s\t%s\n' "$m" "$name" >> "$tmp/gs_discharged"
    done <<< "$gs_calls"
  fi
done

sort -u -o "$tmp/uses" "$tmp/uses"
sort -u -o "$tmp/witness" "$tmp/witness"
sort -u -o "$tmp/imports" "$tmp/imports"
sort -u -o "$tmp/gs_candidates" "$tmp/gs_candidates"
sort -u -o "$tmp/gs_discharged" "$tmp/gs_discharged"

# For each module, its transitive ascent-import closure (including itself): a plain
# per-node BFS over the import edges (both sides small — well under a thousand
# edges — so the O(V*E) cost of a BFS per node is not worth trading for a fixpoint
# join, which is exactly the kind of collation-order-sensitive construction that
# made the anchor ratchet flap run to run; see its header).
awk -F'\t' '
  # The increment is its own statement: under mawk 1.3.4, the `awk` on this box,
  # `adj[$1 SUBSEP ++cnt[$1]] = $2` does not commit the increment before the subscript
  # concatenation reads it, so every counter stays empty and each node ends up with no
  # outgoing edges (measured 2026-09-19).
  { cnt[$1]++; adj[$1 SUBSEP cnt[$1]] = $2; seen[$1] = 1; seen[$2] = 1 }
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

# guardsat violations: a candidate (module, theorem-name) for which no ascent module
# attempts a corresJ_guardSat/bytesCorresJ_guardSat pairing.
: > "$tmp/gs_violations"
: > "$tmp/gs_ok"
while IFS=$'\t' read -r m name; do
  found=0
  # The pairing may sit in ANY ascent module, not only in the candidate's own import
  # closure: a `_guardSat` corollary naturally lives in a module that IMPORTS the one
  # stating the correspondence, since that is where the theorem is in scope, which is
  # the opposite direction. Match on the theorem name, which is unambiguous here.
  if grep -qP "\t\Q$name\E\$" "$tmp/gs_discharged"; then found=1; fi
  if [ "$found" -eq 1 ]; then
    printf '%s\t%s\n' "$m" "$name" >> "$tmp/gs_ok"
  else
    printf '%s\t%s\n' "$m" "$name" >> "$tmp/gs_violations"
  fi
done < "$tmp/gs_candidates"

sort -u -o "$tmp/gs_violations" "$tmp/gs_violations"
sort -u -o "$tmp/gs_ok" "$tmp/gs_ok"

n_uses=$(wc -l < "$tmp/uses")
n_ok=$(wc -l < "$tmp/ok")
n_bad=$(wc -l < "$tmp/violations")
n_gs=$(wc -l < "$tmp/gs_candidates")
n_gs_ok=$(wc -l < "$tmp/gs_ok")
n_gs_bad=$(wc -l < "$tmp/gs_violations")

if [ "$mode" = "--list" ]; then
  echo "# state-relation: witnessed ($n_ok of $n_uses module/predicate pairs):"
  sed 's/^/  /' "$tmp/ok"
  echo "# state-relation: unwitnessed ($n_bad):"
  sed 's/^/  /' "$tmp/violations"
  echo "# guard: discharged ($n_gs_ok of $n_gs closed CorresJ/BytesCorresJ theorems):"
  sed 's/^/  /' "$tmp/gs_ok"
  echo "# guard: undischarged ($n_gs_bad):"
  sed 's/^/  /' "$tmp/gs_violations"
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
  {
    echo "# Ascent module/theorem pairs where a CLOSED CorresJ/BytesCorresJ theorem has"
    echo "# no corresJ_guardSat/bytesCorresJ_guardSat pairing attempt (see"
    echo "# CatCrypt/Crypto/SecureCompilation/Ascent/GuardSatisfiable.lean) in the module"
    echo "# or a module it imports. Each line: module<TAB>theorem-name<TAB>reason."
    echo "# Recorded by scripts/ascent-nonvacuity-ratchet.sh --record."
    while IFS=$'\t' read -r m name; do
      old=$(grep -P "^\Q$m\E\t\Q$name\E\t" "$guardsat_baseline" 2>/dev/null | head -1)
      if [ -n "$old" ]; then echo "$old"; else printf '%s\t%s\tno reason recorded\n' "$m" "$name"; fi
    done < "$tmp/gs_violations"
  } > "$guardsat_baseline.new"
  mv "$guardsat_baseline.new" "$guardsat_baseline"
  echo "ascent-nonvacuity: recorded $n_bad unwitnessed state-relation pair(s) in $baseline"
  echo "ascent-nonvacuity: recorded $n_gs_bad undischarged guard obligation(s) in $guardsat_baseline"
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

if [ -f "$guardsat_baseline" ]; then
  gs_base_keys=$(grep -v '^#' "$guardsat_baseline" | cut -f1,2 | sort -u)
  gs_new=$(comm -23 <(cut -f1,2 "$tmp/gs_violations" | sort -u) <(printf '%s\n' "$gs_base_keys"))
  if [ -n "$gs_new" ]; then
    echo "ASCENT-GUARDSAT: closed CorresJ/BytesCorresJ theorem with no"
    echo "  corresJ_guardSat/bytesCorresJ_guardSat pairing attempt, and not in"
    echo "  $guardsat_baseline:"
    printf '%s\n' "$gs_new" | sed 's/^/    /'
    echo "  -> add \`theorem foo_guardSat : ∃ st a, SR st a ∧ P a :=\`"
    echo "     \`  corresJ_guardSat foo w\` (or \`bytesCorresJ_guardSat\`), \`w\` a joint"
    echo "     witness (see Ascent/Demos/S2nMontmulP384GuardSat.lean), or record it"
    echo "     with its reason: bash scripts/ascent-nonvacuity-ratchet.sh --record"
    fail=1
  fi
  gs_gone=$(comm -13 <(cut -f1,2 "$tmp/gs_violations" | sort -u) <(printf '%s\n' "$gs_base_keys"))
  if [ -n "$gs_gone" ]; then
    echo "ascent-nonvacuity: $(printf '%s\n' "$gs_gone" | grep -c .) guardsat baseline entr(y/ies) now discharged; run --record to drop them."
  fi
else
  echo "ascent-nonvacuity: no guardsat baseline; run --record to create $guardsat_baseline"
  fail=1
fi

base_n=$(grep -vc '^#' "$baseline" 2>/dev/null || echo 0)
gs_base_n=$(grep -vc '^#' "$guardsat_baseline" 2>/dev/null || echo 0)
echo "ascent-nonvacuity: $n_uses module/predicate pair(s) state a correspondence over a named SR-predicate, $n_ok witnessed, $n_bad unwitnessed (baseline ${base_n})."
echo "ascent-nonvacuity: $n_gs closed CorresJ/BytesCorresJ theorem(s) found, $n_gs_ok guard-discharged, $n_gs_bad undischarged (baseline ${gs_base_n})."
[ "$fail" -eq 0 ] && echo "ascent-nonvacuity: OK"
exit $fail
