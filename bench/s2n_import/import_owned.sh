#!/usr/bin/env bash
# Import one function of an x86-64 AT&T file printed by CatCrypt's owned
# backend as a Lean `List (JInstr 64)` (or `List CallSeg`, when the function
# contains `call`).
#
# Usage (from any directory):
#   bench/s2n_import/import_owned.sh FILE.s MODULE_NAME [SYMBOL]
#
#   FILE.s       the assembly file
#   MODULE_NAME  the Lean module name, e.g. Ed25519MaddShipped; the module is
#                CatCrypt.Crypto.SecureCompilation.Ascent.Imported.MODULE_NAME
#   SYMBOL       the function to import; required when the file defines more
#                than one function, otherwise the one function of the file
#   OUT_LEAN     (environment) the Lean file to write; default
#                CatCrypt/Crypto/SecureCompilation/Ascent/Imported/MODULE_NAME.lean
#   MAXSEG       (environment) the largest segment, in instructions; default 32
#   SRC_REV      (environment) a commit of the git repository holding FILE.s;
#                when set, the file is read as it is at that commit
#                (`git show SRC_REV:path`) instead of from the working tree
#
# The module docstring records the file's path relative to its git repository,
# that repository's commit (SRC_REV when set), whether the file is tracked and
# unchanged there, and the file's SHA-256.  The script writes the module only when the translation
# succeeds; on an instruction outside the accepted shapes it prints
# `file:line: message` and exits 1, leaving the module unchanged.  See README.md,
# section "Importing the owned backend's output".
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
[ $# -ge 2 ] && [ $# -le 3 ] || { echo "usage: import_owned.sh FILE.s MODULE_NAME [SYMBOL]" >&2; exit 2; }
src="$1"
mod="$2"
[[ "$mod" =~ ^[A-Z][A-Za-z0-9]*$ ]] || { echo "import_owned: MODULE_NAME must be a capitalised identifier: $mod" >&2; exit 2; }
srcdir="$(cd "$(dirname "$src")" && pwd)"
src="$srcdir/$(basename "$src")"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# The text to translate: the working-tree file, or the file at SRC_REV.
rev="${SRC_REV:-}"
if [ -n "$rev" ]; then
  git -C "$srcdir" show "$rev:./$(basename "$src")" > "$tmp/src.s" 2>/dev/null || {
    echo "import_owned: $src is not in the git repository at commit $rev" >&2; exit 2; }
  input="$tmp/src.s"
else
  [ -f "$src" ] || { echo "import_owned: no file $src" >&2; exit 2; }
  input="$src"
fi

mapfile -t fns < <(awk '/^[A-Za-z_][A-Za-z0-9_.$]*:[ \t]*$/ { sub(/:[ \t]*$/, ""); print }' "$input")
if [ $# -eq 3 ]; then
  sym="$3"
  printf '%s\n' "${fns[@]}" | grep -qxF -- "$sym" || {
    echo "import_owned: $src defines no function \`$sym\` (it defines: ${fns[*]:-none})" >&2; exit 2; }
else
  [ "${#fns[@]}" -eq 1 ] || {
    echo "import_owned: $src defines ${#fns[@]} functions (${fns[*]:-none}); name one as SYMBOL" >&2; exit 2; }
  sym="${fns[0]}"
fi

lmod="$(echo "${mod:0:1}" | tr '[:upper:]' '[:lower:]')${mod:1}"
out="${OUT_LEAN:-$repo/CatCrypt/Crypto/SecureCompilation/Ascent/Imported/$mod.lean}"
ns="CatCrypt.Crypto.SecureCompilation.Ascent.Imported.$mod"

# Provenance of the input file.
if top="$(git -C "$srcdir" rev-parse --show-toplevel 2>/dev/null)"; then
  rel="${src#"$top"/}"
  reponame="$(basename "$top")"
  if [ -n "$rev" ]; then
    commit="$(git -C "$top" rev-parse "$rev^{commit}")"
    state="tracked and unchanged at that commit"
  elif git -C "$top" ls-files --error-unmatch -- "$rel" >/dev/null 2>&1; then
    commit="$(git -C "$top" rev-parse HEAD)"
    if [ -z "$(git -C "$top" status --porcelain -- "$rel")" ]; then
      state="tracked and unchanged at that commit"
    else
      state="tracked, with local changes against that commit"
    fi
  else
    commit="$(git -C "$top" rev-parse HEAD)"
    state="not tracked by git"
  fi
  where="\`$rel\` in the \`$reponame\` repository at commit \`$commit\` ($state)"
else
  where="\`$src\`, outside any git repository"
fi
sha="$(sha256sum "$input" | cut -d' ' -f1)"

awk -v sym="$sym" -v summary="$tmp/summary" -v maxseg="${MAXSEG:-32}" \
  -v prefix="${lmod}Seg" -v partprefix="${lmod}Part" -v block="${lmod}Block" \
  -v prologue="${lmod}Prologue" -v epilogue="${lmod}Epilogue" \
  -f "$here/translate_owned.awk" "$input" > "$tmp/body.lean"

get() { awk -v k="$1" '$1 == k { $1 = ""; sub(/^ /, ""); print }' "$tmp/summary"; }
n="$(get instructions)"
nseg="$(get segments)"
nparts="$(get parts)"
parts="$(awk '$1 == "part" { print $2 }' "$tmp/summary")"
ncall="$(get calls)"
maxseg="$(get maxseg)"
push="$(get push)"
npush="$(get npush)"
falloc="$(get framealloc)"
frel="$(get framerelease)"
ret="$(get ret)"
endbr="$(get endbr)"
saves="$(get saves)"
restores="$(get restores)"
movl="$(get movl)"
setcf="$(get setcfused)"
setcc="$(get setcc)"
lea="$(get lea)"
rebased="$(awk '$1 == "rebased" { print $2 }' "$tmp/summary" | sort | awk '{ printf("%s`%s`", NR > 1 ? ", " : "", $1) }')"
callees="$(awk '$1 == "callee" { print $3, $2 }' "$tmp/summary" | sort -k1,1nr -k2,2 \
  | awk '{ printf("%s`%s` %s", NR > 1 ? ", " : "", $2, $1) }')"
counts="$(awk '$1 == "mnemonic" { print $3, $2 }' "$tmp/summary" | sort -k1,1nr -k2,2 \
  | awk '{ printf("%s`%s` %s", NR > 1 ? ", " : "", $2, $1) }')"
has_btq="$(awk '$1 == "mnemonic" && $2 == "btq" { print $3 }' "$tmp/summary")"

wrap() { fold -s -w 84 | sed 's/ *$//'; }
bullet() { echo "$1" | fold -s -w 82 | sed 's/ *$//; 1s/^/* /; 2,$s/^/  /'; }

if [ "$nseg" -ge 100 ]; then w=3; else w=2; fi
first="$(printf "%s%0${w}d" "${lmod}Seg" 1)"
last="$(printf "%s%0${w}d" "${lmod}Seg" "$nseg")"

# The frame: what is dropped, what is kept.
dropped=()
ndrop=0
[ "$endbr" = 1 ] && { dropped+=("\`endbr64\`"); ndrop=$((ndrop + 1)); }
if [ "$npush" -gt 0 ]; then
  plist="$(echo "$push" | awk '{ for (i = 1; i <= NF; i++) printf("%s`%s`", i > 1 ? ", " : "", $i) }')"
  dropped+=("\`pushq\` of $plist on entry and the \`popq\` sequence in reverse order on exit")
  ndrop=$((ndrop + 2 * npush))
fi
if [ -n "$falloc" ]; then
  dropped+=("the stack allocation \`$falloc\` and its release \`$frel\`")
  ndrop=$((ndrop + 2))
fi
dropped+=("\`$ret\`")
ndrop=$((ndrop + 1))
droptext="$(printf '%s; ' "${dropped[@]}")"
droptext="${droptext%; }"
frame_b="$(bullet "Omitted from the list: the assembler directives and the $ndrop frame instruction$( [ "$ndrop" -gt 1 ] && echo s), each checked by the importer: $droptext.")"
if [ "$endbr" = 1 ]; then fexcl="\`endbr64\` and \`$ret\`"; else fexcl="\`$ret\`"; fi
frame_b="$frame_b
$(bullet "\`${lmod}Prologue\` and \`${lmod}Epilogue\` are the frame instructions before and after the block, $fexcl excluded: each \`pushq r\` as \`lea \"%rsp\" \"%rsp\" \"%rsp\" 0 (-8)\` followed by \`storeMem \"%rsp\" 0 (.reg r)\`, each \`popq r\` as \`loadMem r \"%rsp\" 0\` followed by \`lea \"%rsp\" \"%rsp\" \"%rsp\" 0 8\`, and the stack allocation and its release as the instruction the text contains. \`lea\` writes no flag, as \`pushq\` and \`popq\` write none.")"
if [ -n "$falloc" ]; then
  rsp_b="$(bullet "Every other instruction is kept, \`%rsp\`-relative moves included, as \`storeMem \"%rsp\" off\` and \`loadMem r \"%rsp\" off\`. Their offsets are relative to \`%rsp\` after the omitted allocation, and \`%rsp\` is constant in the body.")"
else
  rsp_b="$(bullet "Every other instruction is kept, \`%rsp\`-relative moves included, as \`storeMem \"%rsp\" off\` and \`loadMem r \"%rsp\" off\`. \`%rsp\` is constant in the body.")"
fi
if [ "$saves" -gt 0 ]; then
  s="The first $saves instructions store registers into \`%rsp\` slots and form segment 1."
  if [ "$restores" -gt 0 ]; then
    s="$s The last $restores instructions load callee-saved registers back from the slots segment 1 stored them to, and form the last segment."
  fi
  rsp_b="$rsp_b
$(bullet "$s")"
fi

mem_b="$(bullet "\`JasminModel\` keys memory by the name of the base register and a byte offset, at word granularity. A proof over this block is a statement about that model; it agrees with the processor where each base register holds one address throughout the block and distinct names address disjoint words.")"
if [ -n "$rebased" ]; then
  mem_b="$mem_b
$(bullet "The block writes $rebased between memory accesses through it, so the accesses through that register before and after the write share one memory bank in the model.")"
fi
aliased="$(awk '$1 == "aliased" { print $2, $3 }' "$tmp/summary" | sort \
  | awk '{ printf("%s`%s` (from `%s`)", NR > 1 ? ", " : "", $1, $2) }')"
if [ -n "$aliased" ]; then
  mem_b="$mem_b
$(bullet "The block accesses memory through registers that a \`leaq\` set to an address computed from another register: $aliased. In the model those accesses use the bank of the register's own name, which is unrelated to the bank of the register the address was computed from.")"
fi

forms=()
[ "$setcf" -gt 0 ] && forms+=("$(bullet "Each of the $setcf pairs \`setc %r8; movzbq %r8, %r64\` on one register is the single element \`setc r64\` (\`JasminModel.evalInstr_setc_eq_setcc_movzx\`); its comment gives both source instructions.")")
[ "$setcc" -gt 0 ] && forms+=("$(bullet "$setcc \`setc\` instructions without a following \`movzbq\` are \`setcc .b\`.")")
[ "$movl" -gt 0 ] && forms+=("$(bullet "The $movl instructions \`movl \$imm, %r32\` are \`mov r64 (.imm imm)\`: both write the zero-extended immediate and no flag.")")
[ "$lea" -gt 0 ] && forms+=("$(bullet "An index-free \`leaq off(%b), %d\` is \`lea d b b 0 off\`, whose value \`b + b * 0 + off\` is \`b + off\`; \`JInstr.lea\` has no index-free form ($lea instructions).")")
[ -n "$has_btq" ] && forms+=("$(bullet "The $has_btq instructions \`btq \$k, %r\` are \`bt\`, which writes \`CF\` only. The Intel SDM leaves \`OF\`, \`SF\` and \`PF\` undefined after \`BT\`; the importer checks that no \`adox\` reads \`OF\` before a later instruction writes it.")")
formtext="$(printf '%s\n' "${forms[@]+"${forms[@]}"}")"

if [ "$ncall" -gt 0 ]; then
  call_b="$(bullet "The function makes $ncall calls: $callees. \`JInstr\` has no call instruction, so the block is a \`List CallSeg\` (\`Ascent.Imported.CallSeg\`): runs of instructions, each followed by the call that ends it, if any. The effect of a call is outside \`JasminModel\`.")"
  import_extra="public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.CallSeg"
  blocktype="\`List CallSeg\`"
else
  call_b=""
  import_extra="public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel"
  blocktype="\`List (JInstr 64)\`"
fi

mnemonics="$(echo "The block has $n instructions. Source instructions by mnemonic: $counts." | wrap)"

if [ "$nseg" -eq 1 ]; then
  segs="$(bullet "\`$first\`: the block as one segment, a literal $blocktype.")"
else
  segs="$(bullet "\`$first\` … \`$last\`: the block in $nseg segments, each a literal $blocktype. A segment ends after a call, after the entry run of \`%rsp\` stores, before the exit run of \`%rsp\` loads, and after $maxseg instructions.")"
fi

if [ "$nparts" -gt 0 ]; then
  pfirst="$(echo "$parts" | head -1)"; plast="$(echo "$parts" | tail -1)"
  if [ "$ncall" -gt 0 ]; then cnt="its instruction count and its call count"; else cnt="its instruction count"; fi
  partsline="$(bullet "\`$pfirst\` … \`$plast\`: the segments in $nparts parts of at most 16 consecutive segments, each with lemmas giving $cnt.")"
  unit="parts"
else
  partsline=""
  unit="segments"
  if [ "$nseg" -eq 1 ]; then unit="segment"; fi
fi

if [ "$nseg" -eq 1 ]; then blockdesc="the block, equal to its one segment"; else blockdesc="the block, the concatenation of the $unit"; fi

if [ "$ncall" -gt 0 ]; then
  results="* \`${lmod}Block_instrs\`: the block has $n instructions.
* \`${lmod}Block_calls\`: the block makes $ncall calls."
else
  results="* \`${lmod}Block_length\`: the block has $n instructions."
fi

cat > "$tmp/module.lean" <<EOF
/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

$import_extra

/-!
# \`$sym\` from the owned backend's output as a \`JInstr 64\` block

$(echo "\`${lmod}Block\` is the body of the function \`$sym\` in an x86-64 AT&T file printed by CatCrypt's owned backend, translated instruction by instruction. The file's producer is recorded in \`PROVENANCE.md\` next to it, where one exists." | wrap)

## Provenance

$(bullet "Source: $where, file SHA-256 \`$sha\`.")
* Produced by \`bench/s2n_import/import_owned.sh\`, which translates each instruction
  to one \`JInstr 64\` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and \`bench/s2n_import/compare_owned.sh\` checks that the list, printed
  back by \`AsmPrinter.renderBlockBody\`, is the source's instruction sequence.
$frame_b
$rsp_b
* Registers keep their physical names (\`"%rax"\`, …, \`"%r15"\`, \`"%rsp"\`); no
  register allocation is involved.
$mem_b
$formtext
${call_b:+$call_b
}
$mnemonics

## Main definitions

$segs
${partsline:+$partsline
}* \`${lmod}Block\`: $blockdesc.
$(bullet "\`${lmod}Prologue\`, \`${lmod}Epilogue\`: the frame instructions before and after the block.")

## Main results

$results
-/

@[expose] public section

set_option autoImplicit false

namespace $ns

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

EOF
# Drop the empty line left by an empty form list.
awk 'BEGIN { blank = 0 } { if ($0 == "") { if (blank) next; blank = 1 } else blank = 0; print }' \
  "$tmp/module.lean" > "$tmp/module2.lean"
cat "$tmp/body.lean" >> "$tmp/module2.lean"
# The count theorems.  Without parts, each segment's count is computed by
# `rfl`; with parts, the part lemmas are rewritten and the sum of numerals is
# closed by `simp`.
if [ "$nparts" -gt 0 ]; then
  lens="$(for p in $parts; do printf ', %s_length' "$p"; done)"
  insts="$(for p in $parts; do printf ', %s_instrs' "$p"; done)"
  cals="$(for p in $parts; do printf ', %s_calls' "$p"; done)"
  fin=""
  how="the count of each part is a lemma above"
else
  lens="" insts="" cals=""
  fin="
  rfl"
  how="the count of each segment is computed by \`rfl\`"
fi
# A block of one segment has no `++` to rewrite; its count is computed by `rfl`.
wrapsimp() {
  if [ "$nseg" -eq 1 ]; then echo "  rfl"; return; fi
  echo "  simp only [$1]" | fold -s -w 98 | sed 's/ *$//; 2,$s/^/    /'
}
if [ "$nseg" -eq 1 ]; then fin=""; how="its count is computed by \`rfl\`"; fi
if [ "$ncall" -gt 0 ]; then
  cat >> "$tmp/module2.lean" <<EOF

/-- The block has $n instructions; $how. -/
theorem ${lmod}Block_instrs :
    (CallSeg.instrs ${lmod}Block).length = $n := by
  unfold ${lmod}Block
$(wrapsimp "CallSeg.instrs_append, List.length_append$insts")$fin

/-- The block makes $ncall calls; $how. -/
theorem ${lmod}Block_calls :
    (CallSeg.callees ${lmod}Block).length = $ncall := by
  unfold ${lmod}Block
$(wrapsimp "CallSeg.callees_append, List.length_append$cals")$fin

end $ns
EOF
else
  cat >> "$tmp/module2.lean" <<EOF

/-- The block has $n instructions; $how. -/
theorem ${lmod}Block_length :
    ${lmod}Block.length = $n := by
  unfold ${lmod}Block
$(wrapsimp "List.length_append$lens")$fin

end $ns
EOF
fi

mkdir -p "$(dirname "$out")"
cp "$tmp/module2.lean" "$out"
echo "import_owned: wrote $out ($sym: $n instructions, $ncall calls, $nseg segments, $nparts parts)"
