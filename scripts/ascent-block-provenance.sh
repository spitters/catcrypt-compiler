#!/usr/bin/env bash
# Ascent block-provenance ratchet.
#
# The descent has a standing rule (EMIT_PROVENANCE.md, scripts/audit_emit_provenance.sh,
# scripts/handcom-provenance-ratchet.sh): an emit kernel is GENERATED through a verified
# front, never hand-authored as `Com` / `Lcmd` / `JInstr` / `.s`. The ascent has no such
# rule, so an ascent module can state a correspondence (`CorresJ`, `BytesCorresJ`, or a
# direct `runBlock st <block>` equation) about a `List (JInstr n)` that no front produced
# and that is not a documented translation of third-party assembly either: a hand-typed
# instruction list whose only warrant is that this module says so.
#
# This script classifies every CONCRETE block an ascent module states such a
# correspondence about into one of three classes:
#
#   GENERATED  the block is produced by a front / a Com-to-block translation in the
#              same descent chain the compiler ships (`reifyLowCT`, `translateDialectControl`,
#              `cryptoDialectToJasminCom`, `rolledForLoopN`, `FieldEmitGoldenPath`,
#              `RelationalCompile`, `emitDialectOwnedArr`, `fieldToJasminLimbs`,
#              `fieldToJasminWord`, `FrontRoutePlan.compile*`, `translBB`,
#              `loweringL.lowerMulti` — the same marker vocabulary
#              scripts/handcom-provenance-ratchet.sh already uses for the descent side).
#   IMPORTED   the block is a documented translation of third-party assembly: it lives
#              under `Ascent/Imported/`, or its defining module carries a `## Provenance`
#              section (source file + commit + hash, an importer script such as
#              `bench/s2n_import/import_s2n.sh` / `import_owned.sh`, or `NasmParse.parseNasm`)
#              — the convention `Imported/Fe25519MulShipped.lean` and
#              `X86Backend/CarryMulBlock.lean` already use.
#   HAND       neither of the above: a literal instruction list authored in place, with
#              no front and no documented external source. This is the default when a
#              defining module clears neither test — matching the descent ratchet's own
#              "counts unless cleared" rule.
#
# HOW A "BLOCK" IS FOUND (read this before trusting a negative). This script does not
# elaborate Lean; it cannot name the 4th argument of an arbitrary `CorresJ` application.
# Instead it uses this tree's own naming convention: a concrete instruction list is a
# `def`/`abbrev` whose name matches `[a-z][A-Za-z0-9_]*[Bb]lock[A-Za-z0-9_]*`
# (`carryMulBlock`, `feAddBlock`, `s2nMontmulP384Block`, …), which this tree already
# uses uniformly for `List (JInstr n)` values (482 such definitions repo-wide). A module
# is judged to "state a correspondence about" such a name when the name and one of
# `CorresJ`, `BytesCorresJ`, `runBlock` appear within a two-line sliding window of its
# code text (comments/docstrings stripped) — the same window convention
# scripts/ascent-nonvacuity-ratchet.sh uses for state-relation names, for the same
# reason: the judgment and its argument are usually one line break apart in this tree's
# style, and a wider or narrower window would mis-set that tradeoff differently.
#
# WHAT THIS MISSES (by construction, not oversight):
#   * A block bound under a name NOT matching the `...Block` convention is invisible —
#     e.g. the toy kernels in CorresRelational.lean / LegWeld.lean / EmitBridge.lean,
#     which are universally-quantified INFRA lemmas over an abstract `c`/`com`/`jcom`
#     with no concrete instance in scope; they correctly produce no candidate here, but
#     a real *named* concrete kernel using an unconventional name would also be missed.
#   * A judgment/name pair more than one line apart is invisible (the window is 2 lines).
#   * DEFINITION RESOLUTION is per whole FILE, not per sub-term: if a file assembles a
#     block from segments (`s2nMontmulP384Block := seg1 ++ seg2 ++ …`), the file's own
#     markers (front / Provenance) decide the whole block, because in every case audited
#     while writing this script the segments and their provenance prose live in the SAME
#     file as the top-level name. A block built from segments whose provenance prose
#     lives in a DIFFERENT file than the top-level name would be misclassified by
#     whichever markers happen to be in the top-level file.
#   * AMBIGUOUS NAMES: several `...Block` names are defined more than once across
#     backends (`feAddBlock`/`feMulBlock`/`feSqrBlock`/`feSubBlock` each have an x86,
#     ARM and RISC-V definition). This script resolves a name against the CITING
#     module's transitive `CatCrypt.*` import closure (a repo-wide BFS over `import`
#     lines, computed the same way scripts/ascent-nonvacuity-ratchet.sh closes the
#     ascent-only import graph, but over the whole tree here because a block's definer
#     is very often outside Ascent/ entirely, e.g. in `X86Backend/`). Zero or more than
#     one definer surviving that intersection is reported as UNRESOLVED / AMBIGUOUS
#     rather than guessed, and is baselined like a HAND entry: absence of evidence that
#     a block is generated or imported is not evidence that it is safe.
#   * The FRONT/IMPORTED marker scan is textual (does the file mention the marker
#     string), exactly like scripts/handcom-provenance-ratchet.sh's Detector A: a marker
#     anywhere in the defining file clears the whole file, so a file that fronts SOME of
#     its blocks and hand-authors OTHERS reads as generated for all of them. This is the
#     same, already-documented gap that script's header calls out for the descent side.
#   * Committed (HEAD) modules only, for the reason scripts/ascent-anchor-ratchet.sh's
#     header already gives (a concurrent session's working tree is not a stable read);
#     the snapshot mechanics below are copied from that script.
#
# Usage: bash scripts/ascent-block-provenance.sh [--list | --record]
set -uo pipefail
cd "$(dirname "$0")/.."

baseline=scripts/ascent-block-provenance-baseline.txt
mode="${1:-}"

ascent_files=$(git ls-tree -r --name-only HEAD -- CatCrypt/Crypto/SecureCompilation/Ascent \
                                                  HaxAscent/Ascent HaxAscent/Calculus | grep '\.lean$' | sort)
[ -n "$ascent_files" ] || { echo "ascent-block-provenance: no ascent modules found"; exit 1; }

all_files=$(git ls-tree -r --name-only HEAD -- CatCrypt HaxAscent | grep '\.lean$' | sort)

mod_of() { printf '%s' "${1%.lean}" | tr '/' '.'; }

# Robust HEAD snapshot of the whole CatCrypt/ and HaxAscent/ trees (a block's definer is very often
# outside Ascent/), retried with a count check: see ascent-anchor-ratchet.sh's header
# for why a bare `git show`/working-tree read is unsafe under concurrent sessions.
snap=$(mktemp -d)
trap 'rm -rf "$snap" "${tmp:-}"' EXIT
want=$(printf "%s\n" "$all_files" | wc -l)
ok=0
for _ in 1 2 3; do
  rm -rf "${snap:?}"/* 2>/dev/null
  if git archive HEAD -- CatCrypt HaxAscent > "$snap/.snapshot.tar" 2>/dev/null &&
     tar -x -C "$snap" -f "$snap/.snapshot.tar" 2>/dev/null &&
     [ "$(find "$snap" -name '*.lean' | wc -l)" -eq "$want" ]; then
    ok=1; break
  fi
done
[ "$ok" -eq 1 ] || { echo "ascent-block-provenance: cannot snapshot HEAD ($want modules expected)"; exit 1; }
file_text() { cat "$snap/$1"; }

# Depth-counted comment/docstring stripper, closing a block on the line that opens it —
# copied from ascent-anchor-ratchet.sh (NOT `sed -e '/\/-/,/-\//d'`, whose end address is
# searched starting on the line AFTER the start line, which deletes everything between
# two adjacent one-line docstrings).
code_of() {
  file_text "$1" | awk '
    BEGIN { depth = 0 }
    {
      out = ""; i = 1; n = length($0)
      while (i <= n) {
        two = substr($0, i, 2)
        if (depth > 0) {
          if (two == "-/") { depth--; i += 2 }
          else if (two == "/-") { depth++; i += 2 }
          else i++
        } else if (two == "/-") { depth++; i += 2 }
        else if (two == "--") { break }
        else { out = out substr($0, i, 1); i++ }
      }
      print out
    }'
}

tmp=$(mktemp -d)

# --- 1. Repo-wide import graph (CatCrypt.* and HaxAscent.* edges only) ---------------------------
: > "$tmp/imports"
for f in $all_files; do
  m=$(mod_of "$f")
  file_text "$f" | grep -oE "^ *(public |private |meta |public meta )*import (all )?(CatCrypt|HaxAscent)[A-Za-z0-9_.]+" |
    awk '{print $NF}' | while read -r i; do printf '%s\t%s\n' "$m" "$i" >> "$tmp/imports"; done
done
sort -u -o "$tmp/imports" "$tmp/imports"

# --- 2. Repo-wide index of "Block"-named CONSTANT def/abbrev sites ----------------
# Raw grep, not comment-stripped: a `def`/`abbrev` at column 1 (mathlib style, this
# tree's convention) inside a block comment would be a false positive, but none was
# observed while calibrating this script; stripping comments for all 2566 files on
# every run would multiply this script's cost for a case not seen in practice.
#
# A NAME matching `...Block...` is kept only when it is a CONSTANT: the name is
# followed (skipping only whitespace) directly by `:` or `:=`, with no parameter
# binder `(`/`{`/`[` in between, and — when a type ascription is given — that
# ascription contains no `→` before the first `:=` on the same line. This is what
# separates a kernel value (`def carryMulBlock : List (JInstr 64) := […]`, `def
# feAddBlock : List BOp := […]`) from a COMBINATOR that merely takes a block as an
# argument or returns a function of one (`def runBlock {w} (s) : List (JInstr w) →
# JState w`, `def renameBlock (ρ) (block) : List I := …`, `def lowerBlock : {Γ} →
# ArithBlock Γ → … := …`): each of those has a binder or a `→` the filter below
# rejects. Calibrated against this tree's `runBlock`/`renameBlock`/`renameBlockS`/
# `lowerBlock`/`encodeJBlock`/`loopBlock`/`runBlockA`/`runBlockM`/`runBlockStep`,
# none of which is a candidate after this filter, and against
# `carryMulBlock`/`feAddBlock`/`feMulBlock`/`s2nMontmulP384Block`, all of which are.
# GAP: a constant whose type ascription contains `→` only on a continuation line
# (never observed for a concrete block type in this tree, which is always the
# single-line `List (JInstr n)` / `List BOp` / `List ROp64`) would still pass.
: > "$tmp/blockdefs"   # blockName<TAB>module
for f in $all_files; do
  m=$(mod_of "$f")
  file_text "$f" | awk -v mod="$m" '
    /^[[:space:]]*(def|abbrev)[[:space:]]+[a-zA-Z_][A-Za-z0-9_]*[Bb]lock[A-Za-z0-9_]*[[:space:]]*(:|:=)/ {
      line = $0
      sub(/^[[:space:]]*(def|abbrev)[[:space:]]+/, "", line)
      name = line
      sub(/[[:space:]]*(:|:=).*/, "", name)
      rest = line
      sub("^" name, "", rest)
      sub(/^[[:space:]]*/, "", rest)
      # reject a function type: an arrow before the first := on this line
      typepart = rest
      if (index(typepart, ":=") > 0) typepart = substr(typepart, 1, index(typepart, ":=") - 1)
      if (index(typepart, "\xe2\x86\x92") == 0) print name "\t" mod
    }' >> "$tmp/blockdefs"
done
sort -u -o "$tmp/blockdefs" "$tmp/blockdefs"

# --- 3. Candidate (module, blockName) correspondence pairs, ascent modules only ---
: > "$tmp/uses"
for f in $ascent_files; do
  m=$(mod_of "$f")
  code=$(code_of "$f")
  windows=$(awk 'NR>1{print prev " " $0} {prev=$0}' <<< "$code")
  judgment_lines=$(grep -E 'CorresJ |CorresJ$|BytesCorresJ|runBlock' <<< "$windows" || true)
  if [ -n "$judgment_lines" ]; then
    grep -oE '[a-z][A-Za-z0-9_]*[Bb]lock[A-Za-z0-9_]*' <<< "$judgment_lines" | sort -u | while read -r name; do
      # keep only names that resolve in the repo-wide block-def index
      if grep -qP "^\Q$name\E\t" "$tmp/blockdefs"; then
        printf '%s\t%s\n' "$m" "$name" >> "$tmp/uses"
      fi
    done
  fi
done
sort -u -o "$tmp/uses" "$tmp/uses"

n_pairs=$(wc -l < "$tmp/uses")
if [ "$n_pairs" -eq 0 ]; then
  echo "ascent-block-provenance: 0 module/block correspondence pairs found"
  exit 0
fi

# --- 4. Transitive CatCrypt.*/HaxAscent.* import closure, per ascent module that has a pair ---
# One awk pass over the whole import graph, BFS per start module, ALL start modules
# in one invocation (not one awk process per module: this repo's `.lean` tree has a
# few thousand import edges, so re-parsing them once per citing module needlessly
# multiplies the cost).
#
# `cnt[$1]++` is a SEPARATE statement from the `adj[...] = $2` assignment that reads
# it, deliberately: the one-liner `adj[$1 SUBSEP ++cnt[$1]] = $2`
# (scripts/ascent-anchor-ratchet.sh's and scripts/ascent-nonvacuity-ratchet.sh's own
# idiom) evaluates unreliably under mawk 1.3.4 (the `awk` on this box, `/usr/bin/awk
# -> mawk`): measured 2026-09-19, `printf 'a\tx\na\ty\nb\tz\n' | awk -F'\t' '{
# adj[$1 SUBSEP ++cnt[$1]] = $2 } END { for (k in cnt) print k, cnt[k] }'` prints
# `cnt[k]` EMPTY for every `k`, because mawk does not commit `cnt[$1]` back to the
# array before the surrounding subscript concatenation reads it — the assignment
# silently constructs a global running counter instead of a per-key one, so a BFS
# built on it decides every node's outgoing edge count `cnt[cur]` is 0 for every
# start module whose only "edge" mawk records collides with that shared counter.
# Splitting the increment from its use avoids the whole question of evaluation
# order. GAWK does not have this bug (both forms agree there), so this only shows
# up where mawk is `/usr/bin/awk`, which is this box.
cut -f1 "$tmp/uses" | sort -u > "$tmp/starts"
awk -F'\t' -v startfile="$tmp/starts" '
  BEGIN { while ((getline line < startfile) > 0) starts[line] = 1 }
  { cnt[$1]++; adj[$1 SUBSEP cnt[$1]] = $2 }
  END {
    for (m in starts) {
      delete visited
      visited[m] = 1; queue[0] = m; qs = 0; qe = 1
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
' "$tmp/imports" > "$tmp/closure"

# --- 5. Markers ---------------------------------------------------------------
front_re='reifyLowCT|translateDialectControl|cryptoDialectToJasminCom|rolledForLoopN|FieldEmitGoldenPath|RelationalCompile|emitDialectOwnedArr|fieldToJasminLimbs|fieldToJasminWord|FrontRoutePlan\.(compile|compileLoop|compileNested|compileBlock)|translBB|loweringL\.lowerMulti'
imported_re='## Provenance|PROVENANCE\.md|NasmParse|parseNasm|import_s2n\.sh|import_owned\.sh|s2n_import'

classify_file() {
  local path="$1" block="${2:-}"
  case "$path" in
    */Ascent/Imported/*) echo IMPORTED; return ;;
  esac
  # The IMPORTED markers (`## Provenance`, `PROVENANCE.md`, `NasmParse`, …) are
  # PROSE — this tree states a block's third-party provenance in its module
  # docstring (X86Backend/CarryMulBlock.lean, Imported/Fe25519MulShipped.lean), so
  # this check reads the RAW file text, unlike the FRONT check below: stripping
  # comments first (as code_of does) would strip the very prose this test looks
  # for and misclassify every documented import as HAND.
  if grep -qE "$imported_re" <<< "$(file_text "$path")"; then echo IMPORTED; return; fi
  # FRONT markers are code identifiers (function applications), checked over the
  # DEFINING FILE ONLY — deliberately not its import closure. A closure-wide check
  # was tried while calibrating this script and produces false GENERATED verdicts:
  # this tree's Ascent modules cross-import heavily, so a front marker used
  # ANYWHERE in a definer's closure (for an unrelated block, in an unrelated
  # module) cleared blocks that do not go anywhere near a front — measured on
  # `s2nMontmulP384FramedBlock` (`framePrologue ++ s2nMontmulP384Block ++
  # frameEpilogue`, a hand-written frame around an IMPORTED payload), which the
  # closure-wide version misclassified GENERATED. A false GENERATED hides a real
  # gap; a false HAND only adds one conservative baseline entry — so this script
  # accepts the narrower, file-local check and its own documented miss instead
  # (`combSelectBlock` in `X86Backend/CombSelectKernel.lean`, which RENDERS a
  # `Com` that `X86Backend/CombSelectFront.lean` — a file it imports — builds
  # through `translateDialectControl`/`cryptoDialectToJasminCom`: the front call is
  # one hop away, and this script does not follow it, so `combSelectBlock` reads
  # HAND here though its payload is front-built).
  local code; code=$(code_of "$path")
  # A block whose own definition opens a literal instruction list is HAND, whatever
  # else the file mentions. A module can cite the front that verifies the algebra it
  # transcribes while still writing the instructions out by hand, and crediting the
  # citation would report a generated block where none exists (measured on
  # Demos/FieldWordAddCorres.lean, which states the front's own denotation theorem
  # and then hand-writes the twelve instructions).
  if grep -qE "def[[:space:]]+$block\b[^=]*:=[[:space:]]*\[" <<< "$code" ||
     grep -A2 -E "def[[:space:]]+$block\b" <<< "$code" | grep -qE '^[[:space:]]*\[' ; then
    echo HAND; return
  fi
  if grep -qE "$front_re" <<< "$code"; then echo GENERATED; return; fi
  echo HAND
}

# module -> file path lookup
: > "$tmp/mod2file"
for f in $all_files; do printf '%s\t%s\n' "$(mod_of "$f")" "$f" >> "$tmp/mod2file"; done

: > "$tmp/classified"   # module<TAB>blockName<TAB>class<TAB>definer(s)
while IFS=$'\t' read -r m name; do
  definers=$(grep -P "^\Q$name\E\t" "$tmp/blockdefs" | cut -f2)
  closure_ms=$(grep -P "^\Q$m\E\t" "$tmp/closure" | cut -f2)
  resolved=$(comm -12 <(sort -u <<< "$definers") <(sort -u <<< "$closure_ms"))
  n_resolved=$(printf '%s\n' "$resolved" | grep -c . || true)
  if [ "$n_resolved" -eq 0 ]; then
    printf '%s\t%s\tUNRESOLVED\t%s\n' "$m" "$name" "$(printf '%s' "$definers" | tr '\n' ',')" >> "$tmp/classified"
  elif [ "$n_resolved" -gt 1 ]; then
    printf '%s\t%s\tAMBIGUOUS\t%s\n' "$m" "$name" "$(printf '%s' "$resolved" | tr '\n' ',')" >> "$tmp/classified"
  else
    def_mod="$resolved"
    def_file=$(grep -P "^\Q$def_mod\E\t" "$tmp/mod2file" | cut -f2 | head -1)
    cls=$(classify_file "$def_file" "$name")
    printf '%s\t%s\t%s\t%s\n' "$m" "$name" "$cls" "$def_mod" >> "$tmp/classified"
  fi
done < "$tmp/uses"
sort -u -o "$tmp/classified" "$tmp/classified"

# A key needs baselining unless it is affirmatively GENERATED or IMPORTED. HAND,
# UNRESOLVED and AMBIGUOUS are all "not shown safe" and are gated together: the
# absence of a front or a documented import is not evidence a block is either.
: > "$tmp/uncleared"
awk -F'\t' '$3 != "GENERATED" && $3 != "IMPORTED" { print $1 "\t" $2 "\t" $3 "\t" $4 }' "$tmp/classified" > "$tmp/uncleared"

n_total=$(wc -l < "$tmp/classified")
n_gen=$(grep -c $'\tGENERATED\t' "$tmp/classified" || true)
n_imp=$(grep -c $'\tIMPORTED\t' "$tmp/classified" || true)
n_bad=$(wc -l < "$tmp/uncleared")

if [ "$mode" = "--list" ]; then
  echo "# classified ($n_total pairs: $n_gen GENERATED, $n_imp IMPORTED, $n_bad uncleared):"
  sort "$tmp/classified" | sed 's/^/  /'
  echo "# uncleared ($n_bad) — HAND, UNRESOLVED or AMBIGUOUS:"
  sed 's/^/  /' "$tmp/uncleared"
  exit 0
fi

if [ "$mode" = "--record" ]; then
  {
    echo "# Ascent module/block pairs whose block is not affirmatively GENERATED (a"
    echo "# verified front produced it) or IMPORTED (a documented translation of"
    echo "# third-party assembly): HAND (a literal instruction list with neither),"
    echo "# UNRESOLVED (the name's definer is not in the citing module's transitive"
    echo "# import closure) or AMBIGUOUS (more than one definer is). Each line:"
    echo "# module<TAB>blockName<TAB>kind<TAB>reason. Recorded by"
    echo "# scripts/ascent-block-provenance.sh --record; the count may fall, never rise."
    while IFS=$'\t' read -r m name kind info; do
      old=$(grep -P "^\Q$m\E\t\Q$name\E\t" "$baseline" 2>/dev/null | head -1)
      if [ -n "$old" ]; then
        echo "$old"
      else
        printf '%s\t%s\t%s\tno reason recorded (candidate definer(s): %s)\n' "$m" "$name" "$kind" "$info"
      fi
    done < "$tmp/uncleared"
  } > "$baseline.new"
  mv "$baseline.new" "$baseline"
  echo "ascent-block-provenance: recorded $n_bad uncleared pair(s) in $baseline"
  exit 0
fi

fail=0
if [ -f "$baseline" ]; then
  base_keys=$(grep -v '^#' "$baseline" | cut -f1,2 | sort -u)
  new=$(comm -23 <(cut -f1,2 "$tmp/uncleared" | sort -u) <(printf '%s\n' "$base_keys"))
  if [ -n "$new" ]; then
    echo "ASCENT-BLOCK-PROVENANCE: module/block pair not shown GENERATED or IMPORTED,"
    echo "  and not in $baseline:"
    printf '%s\n' "$new" | sed 's/^/    /'
    echo "  -> route the block through a front, document its import provenance, or"
    echo "     record it: bash scripts/ascent-block-provenance.sh --record"
    fail=1
  fi
  gone=$(comm -13 <(cut -f1,2 "$tmp/uncleared" | sort -u) <(printf '%s\n' "$base_keys"))
  if [ -n "$gone" ]; then
    echo "ascent-block-provenance: $(printf '%s\n' "$gone" | grep -c .) baseline entr(y/ies) now cleared; run --record to drop them."
  fi
else
  echo "ascent-block-provenance: no baseline; run --record to create $baseline"
  fail=1
fi

base_n=$(grep -vc '^#' "$baseline" 2>/dev/null || echo 0)
echo "ascent-block-provenance: $n_total pair(s), $n_gen GENERATED, $n_imp IMPORTED, $n_bad uncleared (baseline ${base_n:-0})."
[ "$fail" -eq 0 ] && echo "ascent-block-provenance: OK"
exit $fail
