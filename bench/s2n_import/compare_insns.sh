#!/usr/bin/env bash
# Compare the re-emitted and encoded kernels with s2n-bignum's object code,
# instruction by instruction.
#
# Usage: bench/s2n_import/compare_insns.sh [KERNEL [S2N_ARCHIVE]]
#
#   KERNEL       the s2n-bignum symbol; default bignum_montmul_p384
#   S2N_ARCHIVE  default: the vendored x86/libs2nbignum.a
#
# Assembles gen/KERNEL_reemitted.s (and gen/KERNEL_encoded.s, when present)
# with `as`, disassembles them and KERNEL from the archive, and prints for
# each: the instruction count, the function size in bytes, and the number of
# memory operands based on %rsp or %rbp (stack-frame operands); then the
# instructions whose disassembly differs from the archive's.  Exits 1 when an
# instruction count differs from the archive's.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
sym="${1:-bignum_montmul_p384}"
archive="${2:-$repo/bench/reference_install/s2n-bignum/x86/libs2nbignum.a}"
src="$here/gen/${sym}_reemitted.s"
enc="$here/gen/${sym}_encoded.s"
[ -f "$src" ] || { echo "compare_insns: no $src; run make reemit" >&2; exit 2; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# The instruction lines of one function in `objdump -d` output, as
# "mnemonic operands" with the address and any comment removed.
body() {
  awk -v fn="<$1>:" '$2 == fn { f = 1; next } f && /^$/ { f = 0 } f && /^[ \t]+[0-9a-f]+:/' \
    | cut -f2- | sed 's/ *#.*//; s/[ \t][ \t]*/ /g; s/ $//'
}
# The size of one symbol in an archive, from its .size directive.
symsize() {
  local h
  h="$(nm -S --defined-only "$1" | awk -v s="$2" '$4 == s { print $2; exit }')"
  [ -n "$h" ] && echo $((16#$h))
}
# The size of the .text section of an object holding one function.
textsize() {
  size -A "$1" | awk '$1 == ".text" { print $2 }'
}

report() {
  local label="$1" file="$2" bytes="$3"
  printf '%-22s instructions %4d   bytes %5s   stack-frame operands %d\n' "$label" \
    "$(wc -l < "$file")" "$bytes" "$(grep -cE '\((%rsp|%rbp)' "$file" || true)"
}

objdump -d --no-show-raw-insn "$archive" --disassemble="$sym" | body "$sym" > "$tmp/s2n.txt"
report "s2n-bignum archive" "$tmp/s2n.txt" "$(symsize "$archive" "$sym")"

as -o "$tmp/re.o" "$src"
objdump -d --no-show-raw-insn "$tmp/re.o" | body "${sym}_reemitted" > "$tmp/re.txt"
report "re-emitted" "$tmp/re.txt" "$(textsize "$tmp/re.o")"

files=(re)
if [ -f "$enc" ]; then
  as -o "$tmp/en.o" "$enc"
  objdump -d --no-show-raw-insn "$tmp/en.o" | body "${sym}_encoded" > "$tmp/en.txt"
  report "encoded" "$tmp/en.txt" "$(textsize "$tmp/en.o")"
  files+=(en)
fi

status=0
for f in "${files[@]}"; do
  label=re-emitted; [ "$f" = en ] && label=encoded
  echo
  echo "instructions whose disassembly differs (s2n-bignum < , $label >):"
  diff "$tmp/s2n.txt" "$tmp/$f.txt" | grep '^[<>]' | sort | uniq -c || true
  [ "$(wc -l < "$tmp/s2n.txt")" -eq "$(wc -l < "$tmp/$f.txt")" ] || status=1
done
if [ -f "$enc" ]; then
  echo
  echo "instructions whose disassembly differs (re-emitted < , encoded >):"
  diff "$tmp/re.txt" "$tmp/en.txt" | grep '^[<>]' | sort | uniq -c || true
fi
exit "$status"
