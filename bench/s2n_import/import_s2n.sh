#!/usr/bin/env bash
# Import one s2n-bignum x86-64 AT&T kernel as a Lean `List (JInstr 64)`.
#
# Usage (from any directory):
#   bench/s2n_import/import_s2n.sh KERNEL [S2N_ROOT] [OUT_LEAN]
#
#   KERNEL    the s2n-bignum symbol, with a parameter file
#             kernels/KERNEL.sh (bignum_montmul_p384, bignum_montsqr_p384)
#   S2N_ROOT  the s2n-bignum checkout; default bench/reference_install/s2n-bignum
#   OUT_LEAN  the Lean module to write; default
#             CatCrypt/Crypto/SecureCompilation/Ascent/Demos/<ident>.lean, with
#             <ident> taken from the parameter file
#   CPP       the preprocessor command; default `cpp`
#
# The parameter file pins the source: the checkout's commit and the source
# file's SHA-256 must equal the pinned values.  The script runs the C
# preprocessor over the assembly source, hands the result to translate.awk,
# and writes the module only when the translation succeeds.  It does not
# modify the checkout.  See README.md for the accepted shapes.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
[ $# -ge 1 ] || { echo "usage: import_s2n.sh KERNEL [S2N_ROOT] [OUT_LEAN]" >&2; exit 2; }
sym="$1"
conf="$here/kernels/$sym.sh"
[ -f "$conf" ] || { echo "import_s2n: no parameter file $conf" >&2; exit 2; }
ident="" length_tactic="" src_dir="" pin_commit="" pin_sha256="" macros="" computes="" description="" convention=""
# shellcheck source=/dev/null
. "$conf"
for v in ident src_dir pin_commit pin_sha256 macros computes description convention; do
  [ -n "${!v}" ] || { echo "import_s2n: $conf does not set \`$v\`" >&2; exit 2; }
done
lident="$(echo "${ident:0:1}" | tr '[:upper:]' '[:lower:]')${ident:1}"
length_tactic="${length_tactic:-unfold ${lident}Block; simp only [List.length_append]; rfl}"

root="${2:-$repo/bench/reference_install/s2n-bignum}"
out="${3:-$repo/CatCrypt/Crypto/SecureCompilation/Ascent/Demos/$ident.lean}"
cpp_cmd="${CPP:-cpp}"

rel="x86_att/$src_dir/$sym.S"
src="$root/$rel"
[ -f "$src" ] || { echo "import_s2n: no source file $src" >&2; exit 2; }

commit="$(git -C "$root" rev-parse HEAD 2>/dev/null || echo unknown)"
if [ "$commit" != unknown ] && [ -n "$(git -C "$root" status --porcelain -- "$rel" 2>/dev/null)" ]; then
  echo "import_s2n: $rel differs from the checkout's commit $commit" >&2
  exit 2
fi
if [ "$commit" != "$pin_commit" ]; then
  echo "import_s2n: the checkout is at $commit; $conf pins $pin_commit" >&2
  exit 2
fi
sha="$(sha256sum "$src" | cut -d' ' -f1)"
if [ "$sha" != "$pin_sha256" ]; then
  echo "import_s2n: $rel has SHA-256 $sha; $conf pins $pin_sha256" >&2
  exit 2
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# Preprocess from the x86_att directory, as s2n-bignum's own Makefile does.
( cd "$root/x86_att" && $cpp_cmd -I ../include "$src_dir/$sym.S" ) > "$tmp/pre.s"

awk -v sym="$sym" -v summary="$tmp/summary" \
  -v prefix="${lident}Seg" -v block="${lident}Block" \
  -f "$here/translate.awk" "$tmp/pre.s" > "$tmp/body.lean"

get() { awk -v k="$1" '$1 == k { print $2 }' "$tmp/summary"; }
n="$(get instructions)"
nseg="$(get segments)"
cuts="$(get cuts)"
maxseg="$(get maxseg)"
frame="$(awk '$1 == "frame" { $1 = ""; sub(/^ /, ""); print }' "$tmp/summary")"
endbr="$(get endbr)"
xorl="$(get xorl)"
movl="$(get movl)"
adcl="$(get adcl)"
adclregs="$(get adclreg | sort)"
if [ "$(echo "$adclregs" | wc -w)" -gt 1 ]; then
  echo "import_s2n: \`adcl\` on more than one register ($adclregs); the module text names one" >&2
  exit 2
fi
counts="$(awk '$1 == "mnemonic" { print $3, $2 }' "$tmp/summary" | sort -k1,1nr -k2,2 \
  | awk '{ printf("%s`%s` %s", NR > 1 ? ", " : "", $2, $1) }')"
mnemonics="$(echo "The block has $n instructions: $counts." | fold -s -w 84 | sed 's/ *$//')"
nframe="$(echo "$frame" | wc -w)"
frame_list="$(echo "$frame" | awk '{ for (i = 1; i <= NF; i++) printf("%s`%s`", i > 1 ? ", " : "", $i) }')"
if [ "$endbr" = 1 ]; then entry="\`endbr64\`, "; else entry=""; fi
convention="${convention//@FRAME@/$frame_list}"

# The bullet on the 32-bit forms.
if [ "$adcl" -gt 0 ]; then
  r32="$adclregs"
  r64="$(echo "$r32" | awk '{ r = $1; if (r ~ /d$/) print substr(r, 1, length(r) - 1); else print "%r" substr(r, 3) }')"
  forms="* The source uses 32-bit instruction forms in three positions, each translated to
  the 64-bit form with equal register value and flags: $xorl \`xorl %r, %r\` zeroing
  idioms to \`xor_\`, $movl \`movl \$imm, %r\` zero-extending moves to \`mov\`, and $adcl
  \`adcl $r32, $r32\` to \`adc\`, the last accepted only where the preceding instruction
  that touches \`$r64\` is \`xorl $r32, $r32\` in the same macro expansion."
else
  parts=()
  [ "$xorl" -gt 0 ] && parts+=("$xorl \`xorl %r, %r\` zeroing idioms to \`xor_\`")
  [ "$movl" -gt 0 ] && parts+=("$movl \`movl \$imm, %r\` zero-extending moves to \`mov\`")
  case "${#parts[@]}" in
    0) forms="* The source uses no 32-bit instruction form." ;;
    1) forms="* The source uses one 32-bit instruction form, translated to the 64-bit form with equal register value and flags: ${parts[0]}." ;;
    2) forms="* The source uses two 32-bit instruction forms, each translated to the 64-bit form with equal register value and flags: ${parts[0]} and ${parts[1]}." ;;
  esac
  forms="$(echo "$forms" | fold -s -w 84 | sed 's/ *$//; 2,$s/^/  /')"
fi

# The bullet on the segments.
segs="* \`${lident}Seg01\` … \`${lident}Seg$(printf '%02d' "$nseg")\`: the block in $nseg segments, one per
  paragraph of the source (a run of instructions with no blank or comment line between
  them), each a literal \`List (JInstr 64)\`."
if [ "$cuts" -gt 0 ]; then
  segs="$(echo "* \`${lident}Seg01\` … \`${lident}Seg$(printf '%02d' "$nseg")\`: the block in $nseg segments, each a literal \`List (JInstr 64)\`. A segment is a paragraph of the source (a run of instructions with no blank or comment line between them); a paragraph of more than $maxseg instructions is divided into near-equal parts at source lines, so no macro expansion is divided." \
    | fold -s -w 84 | sed 's/ *$//; 2,$s/^/  /')"
fi

cat > "$tmp/module.lean" <<EOF
/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
/-
The instruction list in this file is a translation of \`$rel\` from
s2n-bignum (https://github.com/awslabs/s2n-bignum), which carries the notice:

  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# s2n-bignum's \`$sym\` as a \`JInstr 64\` block

$description

## Provenance

* Source: \`$rel\` in s2n-bignum at commit
  \`$commit\`, file SHA-256
  \`$sha\`.
  s2n-bignum is licensed Apache-2.0 OR ISC OR MIT-0; its copyright notice is
  reproduced in the comment at the top of this file.
* Produced by \`bench/s2n_import/import_s2n.sh\`, which runs the C preprocessor over
  the source and translates each instruction to one \`JInstr 64\` constructor. The
  comment after each element gives the source line of the instruction (a macro
  invocation, for the instructions of $macros) and its text.
  The importer is not trusted: whether this list computes $computes is
  the subject of the correctness proof over it in a sibling module.
* Omitted from the list: the assembler directives and the frame, which is
  ${entry}\`pushq\` of $frame_list on entry, and the
  matching \`popq\` sequence and \`retq\` on exit ($((endbr + 2 * nframe + 1)) instructions).
* Registers keep their physical names (\`"%rax"\`, …, \`"%r15"\`); no register
  allocation is involved.
$forms

$mnemonics

## Calling convention

$convention

## Main results

$segs
* \`${lident}Block\`: the block, the concatenation of the segments.
* \`${lident}Block_length\`: the block has $n instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.$ident

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

EOF
cat "$tmp/body.lean" >> "$tmp/module.lean"
cat >> "$tmp/module.lean" <<EOF

/-- The block has $n instructions. The length of each segment is computed by \`rfl\`;
    the whole list at once exceeds the default recursion depth. -/
theorem ${lident}Block_length : ${lident}Block.length = $n := by
  $length_tactic

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.$ident
EOF

mkdir -p "$(dirname "$out")"
cp "$tmp/module.lean" "$out"
echo "import_s2n: wrote $out ($n instructions in $nseg segments; frame ${entry}$frame)"
