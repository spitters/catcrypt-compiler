#!/usr/bin/env bash
# Compare the imported owned-backend functions, printed back by
# `AsmPrinter.renderBlockBody` (reemit_owned.lean), with their source files,
# instruction by instruction.
#
# Usage: bench/s2n_import/compare_owned.sh [MODULE ...]
#
#   MODULE     a module name from owned_kernels.txt; default: every module there
#   REEMIT_DIR (environment) the directory holding MODULE.s; default gen/owned
#   OWNED_ASM  (environment) the directory holding the source files; default
#              ../SSProve-lean/crates/catcrypt-ed25519/asm relative to this
#              repository
#
# For each module, reads gen/owned/MODULE.s (written by reemit_owned.lean) and
# the function SYMBOL of the source file, removes from the source the frame the
# importer omits (a leading `endbr64`, `pushq` sequence and `leaq -N(%rsp), %rsp`
# or `subq $N, %rsp`; a trailing `leaq N(%rsp), %rsp` or `addq $N, %rsp`, `popq`
# sequence and `ret`), normalises both sides (see `norm` below and README.md),
# and compares them line by line.  Prints the instruction counts and every
# differing pair; exits 1 when any module differs or a file is missing.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
asm="${OWNED_ASM:-$repo/../SSProve-lean/crates/catcrypt-ed25519/asm}"
manifest="$here/owned_kernels.txt"
redir="${REEMIT_DIR:-$here/gen/owned}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# The normalisation, applied to both sides.  Each rule rewrites one spelling
# into another spelling of the same instruction:
#   * comments (`# ...`) are removed, whitespace is collapsed, and each comma
#     is followed by one space;
#   * mnemonic aliases: `setb` = `setc`, `adcx` = `adcxq`, `adox` = `adoxq`,
#     `mulx` = `mulxq`, `retq` = `ret`, `callq` = `call`, `cmovnzq` =
#     `cmovneq`, `cmovzq` = `cmoveq`, `cmovcq` = `cmovbq`;
#   * `movl $v, %r32` is written `movq $v, %r64` (both write the zero-extended
#     immediate; the importer translates the first to the second);
#   * a memory operand without displacement, `(...)`, is written `0(...)`;
#   * `D(%b, %b, 0)` is written `D(%b)` (the importer's index-free `lea`).
cat > "$tmp/norm.awk" <<'AWK'
BEGIN {
    A["setb"] = "setc"; A["adcx"] = "adcxq"; A["adox"] = "adoxq"; A["mulx"] = "mulxq"
    A["retq"] = "ret"; A["callq"] = "call"; A["cmovnzq"] = "cmovneq"
    A["cmovzq"] = "cmoveq"; A["cmovcq"] = "cmovbq"
    W["%eax"] = "%rax"; W["%ebx"] = "%rbx"; W["%ecx"] = "%rcx"; W["%edx"] = "%rdx"
    W["%esi"] = "%rsi"; W["%edi"] = "%rdi"; W["%ebp"] = "%rbp"
    for (i = 8; i <= 15; i++) W["%r" i "d"] = "%r" i
}
function norm(s,    p, mn, rest, out, q, inner, n, parts) {
    p = index(s, "#"); if (p) s = substr(s, 1, p - 1)
    gsub(/[ \t]+/, " ", s); sub(/^ /, "", s); sub(/ $/, "", s)
    gsub(/ *, */, ", ", s)
    p = index(s, " ")
    if (p) { mn = substr(s, 1, p - 1); rest = substr(s, p + 1) } else { mn = s; rest = "" }
    if (mn in A) mn = A[mn]
    if (mn == "movl" && rest ~ /^\$[0-9]+, %[a-z0-9]+$/) {
        q = substr(rest, index(rest, " ") + 1)
        if (q in W) { mn = "movq"; rest = substr(rest, 1, index(rest, " ")) W[q] }
    }
    if (substr(rest, 1, 1) == "(") rest = "0" rest
    gsub(/, \(/, ", 0(", rest)
    # D(%b, %b, 0) -> D(%b)
    out = ""
    while ((p = index(rest, "(")) > 0) {
        q = index(substr(rest, p), ")")
        inner = substr(rest, p + 1, q - 2)
        n = split(inner, parts, ", ")
        if (n == 3 && parts[1] == parts[2] && parts[3] == "0") inner = parts[1]
        out = out substr(rest, 1, p) inner ")"
        rest = substr(rest, p + q)
    }
    rest = out rest
    return (rest == "") ? mn : mn " " rest
}
{ print norm($0) }
AWK

# The instruction lines of function $2 in file $1, frame removed.
source_body() {
  awk -v sym="$2" '
    function t(s) { p = index(s, "#"); if (p) s = substr(s, 1, p - 1); gsub(/^[ \t]+|[ \t]+$/, "", s); return s }
    { s = t($0) }
    s == "" { next }
    !f && s == sym ":" { f = 1; next }
    f && (s ~ /^\./ || s ~ /^[A-Za-z0-9_.$]+:$/) { exit }
    f { L[++n] = s; if (s ~ /^retq?$/) exit }
    END {
      a = 1
      while (a <= n && (L[a] == "endbr64" || L[a] ~ /^pushq / || L[a] ~ /^leaq -[0-9]+\(%rsp\), *%rsp$/ || L[a] ~ /^subq \$[0-9]+, *%rsp$/)) a++
      b = n
      while (b >= a && (L[b] ~ /^retq?$/ || L[b] ~ /^popq / || L[b] ~ /^leaq [0-9]+\(%rsp\), *%rsp$/ || L[b] ~ /^addq \$[0-9]+, *%rsp$/)) b--
      for (i = a; i <= b; i++) print L[i]
    }' "$1"
}

normalise() {
  awk -f "$tmp/norm.awk" "$1"
}

# Self-test of the normalisation on the fixtures when called with --selftest.
if [ "${1:-}" = "--selftest" ]; then
  src="$2" re="$3" sym="$4"
  source_body "$src" "$sym" > "$tmp/s.txt"
  normalise "$tmp/s.txt" > "$tmp/sn.txt"
  grep -v '^[[:space:]]*$' "$re" > "$tmp/r.txt"
  normalise "$tmp/r.txt" > "$tmp/rn.txt"
  diff "$tmp/sn.txt" "$tmp/rn.txt" && echo "compare_owned: self-test agrees ($(wc -l < "$tmp/sn.txt") lines)"
  exit
fi

if [ $# -gt 0 ]; then mods=("$@"); else
  mapfile -t mods < <(awk '!/^[ \t]*(#|$)/ { print $1 }' "$manifest")
fi

status=0
for m in "${mods[@]}"; do
  read -r _ file sym < <(awk -v m="$m" '$1 == m { print; exit }' "$manifest") || true
  if [ -z "${file:-}" ]; then echo "compare_owned: $m is not in $manifest" >&2; status=1; continue; fi
  src="$asm/$file"
  re="$redir/$m.s"
  [ -f "$src" ] || { echo "compare_owned: no source $src; set OWNED_ASM" >&2; status=1; continue; }
  [ -f "$re" ] || { echo "compare_owned: no $re; run make reemit-owned" >&2; status=1; continue; }
  source_body "$src" "$sym" > "$tmp/s.txt"
  normalise "$tmp/s.txt" > "$tmp/sn.txt"
  grep -v '^[[:space:]]*$' "$re" > "$tmp/r.txt" || true
  normalise "$tmp/r.txt" > "$tmp/rn.txt"
  ns="$(wc -l < "$tmp/sn.txt")"; nr="$(wc -l < "$tmp/rn.txt")"
  nd="$(paste -d '\n' "$tmp/sn.txt" "$tmp/rn.txt" | awk 'NR % 2 == 1 { a = $0; next } a != $0 { d++ } END { print d + 0 }')"
  if [ "$ns" -eq "$nr" ] && [ "$nd" -eq 0 ]; then
    printf '%-26s %-36s lines %5d  identical after normalisation\n' "$m" "$sym" "$ns"
  else
    status=1
    printf '%-26s %-36s source %5d  re-emitted %5d  differing lines %d\n' "$m" "$sym" "$ns" "$nr" "$nd"
    diff "$tmp/sn.txt" "$tmp/rn.txt" | head -40 || true
  fi
done
exit "$status"
