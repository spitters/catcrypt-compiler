#!/usr/bin/env bash
# Ascent-anchor ratchet.
#
# An ascent theorem relates a source program to a target computation. It says
# something about what we ship only when its target side is tied to the shipped
# artifact. Two ties count:
#
#   descent  the module welds onto a descent result (`legWeld`, a `keystone_*`
#            lemma, `rustToJasminCom_endToEnd`, `robustCompilation_source_to_x86`,
#            `com_arm_e2e`, `com_riscv_e2e`), so its target is the program the
#            verified compiler produces;
#   bytes    the module states its result over the encoded bytes (`encodeJBlock`, `encodeLfundefBytes`,
#            `decodeJStream`, `decodeLprog`, a `*Bytes_correct` theorem).
#
# A module also counts as anchored when a module that (transitively) imports it
# is anchored: its lemmas feed an anchored result.
#
# SCOPE. A module needs an anchor only when it states a correspondence at concrete
# code, by either of two textual tests over its code text:
#
#   block    a constant `...Block...` definition of this repository appears within a
#            two-line window of a correspondence judgment (`Corres…`, `BytesCorres…`)
#            or a block run (`runBlock`, `runRBlock…`): the detection of
#            scripts/audit_emit_provenance.sh for ascent module/block pairs, over
#            the judgments of every backend;
#   program  the module itself defines an instruction list or a program (a `def` or
#            `abbrev`, with or without parameters, whose result type is
#            `List (JInstr n)`, `List ROp64`, `List BOp`, `List RInst64`,
#            `List BBStmt`, `Lcmd`, `Lprog`, `Linstr…`, `Com …`, `ComL …`, `LowCT` or
#            `RustSrc`) and mentions a correspondence judgment (`Corres…`,
#            `BytesCorres…`) or a block run (`runBlock`, `runRBlock…`).
#
# A generic rule module (its programs are variables), a definitions-only module and
# infrastructure that defines no code state nothing about a particular program, so
# they need neither an anchor nor a row.
#
# An unanchored module in scope must be listed in
# scripts/ascent-anchor-baseline.txt with a reason
# (`bash scripts/register-provenance.sh <path.lean> --anchor "<reason>"`). The count
# of such modules may fall, never rise.
#
# The scope test is textual. It misses a module that states its result about a
# program defined in another module under a name without `Block`, and a statement
# about concrete code that uses none of the judgment names above (a constant-time
# statement, a denotation equation).
#
# LIMITS, so the number is not read for more than it says. This is a provenance
# gate, not a vacuity gate: it shows a theorem talks about the shipped artifact,
# not that its precondition is satisfiable at a reachable state, nor that its
# specification is independent of the program's own denotation (the
# model-vacuity ratchet and the satisfiability lemmas carry that). "Anchored at
# the bytes" also stops at `encodeJBlock`: the `.s` or `.o` file is written by an
# emitter run, not by a theorem, and for the AT&T text path the assembler and
# `renderLprogAtt` are trusted.
#
# Usage: bash scripts/ascent-anchor-ratchet.sh [--list | --record]
set -uo pipefail
cd "$(dirname "$0")/.."

baseline=scripts/ascent-anchor-baseline.txt
mode="${1:-}"

# Committed modules only. A module that exists in the index or the working tree but
# not in HEAD is being written right now by one of the concurrent sessions; reading it
# gives a different verdict from one run to the next, and CI classifies a commit.
files=$(git ls-tree -r --name-only HEAD -- CatCrypt/Crypto/SecureCompilation/Ascent \
                                           HaxAscent/Ascent HaxAscent/Calculus | grep '\.lean$' | sort)
[ -n "$files" ] || { echo "ascent-anchor: no ascent modules found"; exit 1; }

# Module name of a path, and the reverse: both are the path with / and . swapped.
mod_of() { printf '%s' "${1%.lean}" | tr '/' '.'; }

# Each name below concludes a `Com jasminDialect` (or a machine block) that agrees with
# the source execution it is given, so a module reaching one states its result about the
# program the verified pipeline produces.
descent_re='legWeld|keystone_[A-Za-z0-9_]+|rustToJasminCom_endToEnd|robustCompilation_source_to_x86|com_arm_e2e|com_riscv_e2e|transU_to_jasminCom_endToEnd|translateDialectGuarded_jasmin'
bytes_re='encodeJBlock|decodeJStream|encodeLfundefBytes|decodeLprog|[A-Za-z0-9_]*Bytes_correct'

# Modules that mention the byte route but carry the byte fact as a HYPOTHESIS (a theorem
# of the form `decodeJStream … = some block → …`) state no result over the shipped bytes.
# The text match cannot tell an assumed decode from a proved one, so they are listed
# here with the missing lemma, and neither they nor the modules they import count as
# anchored through them.
conditional=scripts/ascent-anchor-conditional.txt

# Code text only: drop block docstrings/comments and line comments, so a mention
# in prose does not anchor a module. The content comes from HEAD, not the working
# tree: the tree is shared with concurrent sessions, and reading a file mid-edit
# gives a different verdict run to run (measured 2026-09-19). HEAD is also what CI
# checks out, so the local verdict and the CI verdict agree.
# One snapshot of the commit, extracted once: a `git show` per file races with the
# concurrent sessions' git activity and returns truncated content for some of them,
# which changed the verdict run to run (measured 2026-09-19, same HEAD).
snap=$(mktemp -d)
trap 'rm -rf "$snap" "${tmp:-}"' EXIT
# `git archive | tar` exits 0 on a truncated archive, and truncation happens when
# another session holds the repository busy; an incomplete snapshot silently drops
# anchors. Extract to a file, check git's own status, and verify the count.
want=$(printf "%s\n" "$files" | wc -l)
ok=0
for _ in 1 2 3; do
  rm -rf "${snap:?}"/* 2>/dev/null
  if git archive HEAD -- CatCrypt/Crypto/SecureCompilation/Ascent HaxAscent/Ascent HaxAscent/Calculus \
       > "$snap/.snapshot.tar" 2>/dev/null &&
     tar -x -C "$snap" -f "$snap/.snapshot.tar" 2>/dev/null &&
     [ "$(find "$snap" -name '*.lean' | wc -l)" -eq "$want" ]; then
    ok=1; break
  fi
done
[ "$ok" -eq 1 ] || { echo "ascent-anchor: cannot snapshot HEAD ($want modules expected)"; exit 1; }
file_text() {
  if [ -f "$snap/$1" ]; then cat "$snap/$1"; else cat "$1"; fi
}
# Strip block comments and docstrings character by character, closing a block on the
# line that opened it. `sed -e '/\/-/,/-\//d'` cannot do this: its end address is
# searched from the line AFTER the start, so two adjacent one-line docstrings delete
# everything between them (measured 2026-09-19), which silently hid code from the
# markers below.
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

# Constant `...Block...` definitions of the repository at HEAD: the name is followed
# by `:` or `:=` with no parameter binder, and its type has no arrow. This is the
# index scripts/audit_emit_provenance.sh builds for ascent module/block pairs.
git grep -hE '^[[:space:]]*(def|abbrev)[[:space:]]+[a-zA-Z_][A-Za-z0-9_]*[Bb]lock[A-Za-z0-9_]*[[:space:]]*(:|:=)' \
    HEAD -- CatCrypt HaxAscent 2>/dev/null | awk '
  {
    line = $0
    sub(/^[[:space:]]*(def|abbrev)[[:space:]]+/, "", line)
    name = line; sub(/[[:space:]]*(:|:=).*/, "", name)
    rest = substr(line, length(name) + 1)
    if (index(rest, ":=") > 0) rest = substr(rest, 1, index(rest, ":=") - 1)
    if (index(rest, "\xe2\x86\x92") == 0) print name
  }' | sort -u > "$tmp/blocknames"

# 0 iff the code text on stdin states a correspondence at concrete code (see SCOPE).
judgment_re='(^|[^A-Za-z0-9_])(Corres[A-Za-z0-9_]*|BytesCorres[A-Za-z0-9_]*|run[A-Z]?Block[A-Za-z0-9_]*)'
concrete_code() {
  local code="$1" names
  # block: a constant block name within two lines of a judgment.
  names=$(awk 'NR>1{print prev " " $0} {prev=$0}' <<< "$code" |
            grep -E "$judgment_re" |
            grep -oE '[a-z][A-Za-z0-9_]*[Bb]lock[A-Za-z0-9_]*' | sort -u || true)
  if [ -n "$names" ] && [ -n "$(comm -12 <(printf '%s\n' "$names") "$tmp/blocknames")" ]; then
    return 0
  fi
  # program: the module defines code and mentions a judgment or a block run.
  grep -qE "$judgment_re" <<< "$code" || return 1
  perl -CSD -0777 -ne '
    while (/^[ \t]*(?:private |protected |noncomputable )*(?:def|abbrev)[ \t]+[A-Za-z_][A-Za-z0-9_\x27.]*((?:[^\n]*\n){0,3}?[^\n]*?)(?::=|\n[ \t]*\|)/mg) {
      my $sig = $1;
      $sig =~ s/.*\x{2192}//s;          # result type: after the last arrow,
      $sig =~ s/.* : //s;               # then after the last binder colon
      $sig =~ s/^[\s:]+//;
      if ($sig =~ /^(?:List \((?:JInstr|RInstr)\b|List (?:ROp64|BOp|RInst64|BBStmt|LowCT)\b|Lcmd\b|Lprog|Linstr|ComL? |LowCT\b|RustSrc\b)/) { $hit = 1; last }
    }
    END { exit($hit ? 0 : 1) }' <<< "$code"
}

: > "$tmp/concrete"    # modules that state a correspondence at concrete code
: > "$tmp/direct"      # module<TAB>kind   (descent|bytes|both)
: > "$tmp/imports"     # module<TAB>imported-ascent-module

for f in $files; do
  m=$(mod_of "$f")
  code=$(code_of "$f")
  d=0; b=0
  concrete_code "$code" && echo "$m" >> "$tmp/concrete"
  # Here-strings, not pipes: under `pipefail`, `grep -q` closes the pipe as soon as it
  # matches, the upstream `sed` dies of SIGPIPE, and the pipeline reports failure on a
  # match — timing-dependent, and it made the verdict flap run to run (2026-09-19).
  grep -qE "$descent_re" <<< "$code" && d=1
  grep -qE "$bytes_re" <<< "$code" && b=1
  if [ "$b" = 1 ] && [ -f "$conditional" ] && grep -qxF "$m" <(grep -v '^#' "$conditional" | cut -f1); then b=0; fi
  if [ "$d$b" != "00" ]; then
    kind=$([ "$d$b" = "11" ] && echo both || { [ "$d" = 1 ] && echo descent || echo bytes; })
    printf '%s\t%s\n' "$m" "$kind" >> "$tmp/direct"
  fi
  file_text "$f" | grep -oE "^ *(public |private |meta |public meta )*import (all )?[A-Za-z0-9_.]+" |
    awk '{print $NF}' | while read -r i; do
      case "$i" in
        CatCrypt.Crypto.SecureCompilation.Ascent.*|HaxAscent.Ascent.*|HaxAscent.Calculus.*)
          printf '%s\t%s\n' "$m" "$i" >> "$tmp/imports" ;;
      esac
    done
done

# Anchored set: the direct anchors, closed under "an anchored module imports it".
# One awk pass rather than a join fixpoint: join needs both inputs in one collation,
# and mixing a whole-line sort with a keyed sort made the closure disagree with
# itself between runs on identical input (measured 2026-09-19).
awk -F'\t' '
  FNR == NR { anchored[$1] = 1; next }
  { imp[$1] = imp[$1] "\t" $2 }
  END {
    changed = 1
    while (changed) {
      changed = 0
      for (m in anchored) {
        if (m in imp && !(m in expanded)) {
          expanded[m] = 1
          n = split(imp[m], xs, "\t")
          for (i = 1; i <= n; i++)
            if (xs[i] != "" && !(xs[i] in anchored)) { anchored[xs[i]] = 1; changed = 1 }
        }
      }
    }
    for (m in anchored) print m
  }
' <(cut -f1 "$tmp/direct") "$tmp/imports" | sort -u > "$tmp/anchored"

for f in $files; do mod_of "$f"; echo; done | grep -v '^$' | sort -u > "$tmp/all"
sort -u -o "$tmp/concrete" "$tmp/concrete"
comm -23 "$tmp/all" "$tmp/anchored" > "$tmp/unanchored-all"
# In scope: unanchored modules that state a correspondence at concrete code.
comm -12 "$tmp/unanchored-all" "$tmp/concrete" > "$tmp/unanchored"

total=$(wc -l < "$tmp/all")
anch=$(wc -l < "$tmp/anchored")
unanch=$(wc -l < "$tmp/unanchored")
unanch_all=$(wc -l < "$tmp/unanchored-all")
bytes=$(awk -F'\t' '$2 == "bytes" || $2 == "both"' "$tmp/direct" | wc -l)

if [ "$mode" = "--list" ]; then
  echo "# anchored ($anch of $total):"
  sort "$tmp/direct" | sed 's/^/  /'
  echo "# unanchored, stating a correspondence at concrete code ($unanch):"
  sed 's/^/  /' "$tmp/unanchored"
  echo "# unanchored, out of scope: rules, definitions, infrastructure ($((unanch_all - unanch))):"
  comm -23 "$tmp/unanchored-all" "$tmp/unanchored" | sed 's/^/  /'
  exit 0
fi

if [ "$mode" = "--record" ]; then
  {
    echo "# Ascent modules that state a correspondence at concrete code and whose results"
    echo "# are tied to neither a descent theorem nor the encoded bytes. Each line:"
    echo "# module<TAB>reason. Recorded by scripts/ascent-anchor-ratchet.sh --record; the"
    echo "# count may fall, never rise."
    while read -r m; do
      old=$(grep -P "^\Q$m\E\t" "$baseline" 2>/dev/null | head -1)
      if [ -n "$old" ]; then echo "$old"; else printf '%s\tno reason recorded\n' "$m"; fi
    done < "$tmp/unanchored"
  } > "$baseline.new"
  mv "$baseline.new" "$baseline"
  echo "ascent-anchor: recorded $unanch unanchored module(s) in $baseline"
  if grep -q $'\tno reason recorded$' "$baseline"; then
    echo "ascent-anchor: row(s) without a reason; the check fails until each has one:"
    grep $'\tno reason recorded$' "$baseline" | cut -f1 | sed 's/^/    /'
  fi
  exit 0
fi

fail=0
if [ -f "$baseline" ]; then
  base_n=$(grep -vc '^#' "$baseline")
  new=$(comm -23 "$tmp/unanchored" <(grep -v '^#' "$baseline" | cut -f1 | sort -u))
  if [ -n "$new" ]; then
    echo "ASCENT-ANCHOR: module(s) stating a correspondence at concrete code, tied to neither"
    echo "  a descent theorem nor the encoded bytes, and not in $baseline:"
    printf '%s\n' "$new" | sed 's/^/    /'
    echo "  -> weld the result onto a descent theorem, state it over the encoded bytes,"
    echo "     or record it with its reason:"
    echo "       bash scripts/register-provenance.sh <path.lean> --anchor \"<reason>\""
    fail=1
  fi
  noreason=$(grep -v '^#' "$baseline" | awk -F'\t' '$2 == "" || $2 == "no reason recorded" { print $1 }')
  if [ -n "$noreason" ]; then
    echo "ASCENT-ANCHOR: baseline row(s) without a reason:"
    printf '%s\n' "$noreason" | sed 's/^/    /'
    fail=1
  fi
  gone=$(comm -13 "$tmp/unanchored" <(grep -v '^#' "$baseline" | cut -f1 | sort -u))
  if [ -n "$gone" ]; then
    echo "ascent-anchor: $(printf '%s\n' "$gone" | wc -l) baseline entr(y/ies) now anchored; run --record to drop them."
  fi
else
  echo "ascent-anchor: no baseline; run --record to create $baseline"
  fail=1
fi

echo "ascent-anchor: $total ascent modules, $anch anchored ($bytes at the bytes), $unanch unanchored at concrete code (baseline ${base_n:-0}), $((unanch_all - unanch)) unanchored out of scope."
[ "$fail" -eq 0 ] && echo "ascent-anchor: OK"
exit $fail
