/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.YmmDialectOps

/-!
# Owned AT&T `.s` printer for the 256-bit `YmmOp` family (no `Avx2YmmModel`)

This is the dialect-side sibling of `VsimdAsmPrint` (128-bit `SimdOp`) and
`VpackZmmAsmPrint` (512-bit pack), for the unified 256-bit `YmmOp` family of
`YmmDialectOps.lean`. It renders a straight-line YMM kernel — the VEX.256 / AVX2
ML-DSA NTT register set plus the `vmovdqu` moves/loads/stores — to AT&T-syntax
assembly text, with the function frame the signed NTT kernel needs.

The rendering is **byte-identical** to the bespoke
`X86Backend/Avx2YmmAsmPrinter.lean` (`renderYInst`/`renderYFundef`): every
operand order, `$imm`/tab format, and the 2-pointer-ABI frame
(`.type … @function`, `movq %rdi, %rax`, `.note.GNU-stack`, `.p2align 5`) match
that printer verbatim, so the emitted NTT/mpn `.s` artifacts the bench KATs
already validate are unchanged. The only import is `YmmDialectOps` (for `YmmOp`
and its `attMnemonic`); there is NO dependency on the bespoke `Avx2YmmModel`.

The mnemonic strings come from `YmmOp.attMnemonic`; the operand order and arity
are keyed on the `YmmOp` constructor (binary `vpmuldq`/`vpsubq`/`vpaddd`/
`vpsubd`/`vpblendd`, unary `vmovshdup`/`vpshufd`/`vpermq`, with the `imm8`-
carrying permutes baking the immediate into a leading `$imm` operand). The
`vmovdqu` move/load/store arms are not `YmmOp`s (they leave/enter memory), so
they are separate `YmmInstr` constructors with their own literal mnemonic.

## Where the trust boundary is (identical posture to the bespoke printer)

The printer is a syntactic map (one instruction arm → one AT&T line, fixed
physical-register names, no instruction selection / scheduling / regalloc) and
`gas` performs only assembly. The trusted edge is: the printer is correct AT&T
syntax for each mnemonic, and `gas` encodes each mnemonic per the SDM.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

/-! ## 1. Memory operand (= the bespoke `YMem`) -/

/-- A 256-bit memory operand: a base register name plus a signed displacement.
    The dialect-side twin of `Avx2Ymm.YMem`. -/
structure YmmMem where
  base : String
  disp : Int

/-- Print a `YmmMem` operand as AT&T `disp(%base)` — the displacement is omitted
    when zero (gas's bare `(%base)` form). Copied verbatim from
    `Avx2Ymm.renderYMem`. -/
def renderYmmMem (m : YmmMem) : String :=
  let d := m.disp
  if d = 0 then "(" ++ m.base ++ ")"
  else toString d ++ "(" ++ m.base ++ ")"

/-! ## 2. The instruction type

A `YmmInstr` is either a `YmmOp` over named `%ymm` registers (`alu`) or one of
the three `vmovdqu` register/memory moves (which are not `YmmOp`s — they cross
the register/memory boundary). -/

/-- One YMM instruction: a `YmmOp` ALU op over named registers, or a `vmovdqu`
    register move / load / store. -/
inductive YmmInstr where
  /-- A `YmmOp` over named `%ymm` registers, `dst` and the operand list `srcs`
      (one for the unary ops, two for the binary ops). -/
  | alu (op : YmmOp) (dst : String) (srcs : List String)
  /-- `vmovdqu src, dst` — a register-to-register move. -/
  | ymov (dst src : String)
  /-- `vmovdqu disp(%base), dst` — a load. -/
  | yload (dst : String) (mem : YmmMem)
  /-- `vmovdqu src, disp(%base)` — a store. -/
  | ystore (mem : YmmMem) (src : String)

/-! ## 3. Per-instruction renderer

Dispatch on the `YmmOp` constructor for the operand order/arity, taking the
mnemonic from `YmmOp.attMnemonic`. The AT&T VEX order is `op src2, src1, dst`
for the binary ops, `op src, dst` for the unary move, and the `imm8`-carriers
take a leading `$imm`. Every arm matches `Avx2Ymm.renderYInst` byte-for-byte for
the same logical instruction. -/

/-- Render one `YmmInstr` to its AT&T asm line (`%ymm` registers, VEX.256).
    Byte-identical to `Avx2Ymm.renderYInst` for the corresponding instruction. -/
def renderYmmInstr : YmmInstr → String
  | .alu op dst srcs =>
      let mn := op.attMnemonic
      match op, srcs with
      -- imm8-carrying binary blend: `\t<mn>\t$imm, src2, src1, dst`
      | .vpblendd imm, [a, b] =>
          "\t" ++ mn ++ "\t$" ++ toString imm ++ ", " ++ b ++ ", " ++ a ++ ", " ++ dst
      -- imm8-carrying unary permutes: `\t<mn>\t$imm, src, dst`
      | .vpshufd imm, [a] =>
          "\t" ++ mn ++ "\t$" ++ toString imm ++ ", " ++ a ++ ", " ++ dst
      | .vpermq imm, [a] =>
          "\t" ++ mn ++ "\t$" ++ toString imm ++ ", " ++ a ++ ", " ++ dst
      -- unary high-dup move: `\tvmovshdup\tsrc, dst`
      | .vmovshdup, [a] =>
          "\t" ++ mn ++ "\t" ++ a ++ ", " ++ dst
      -- binary ALU (vpmuldq/vpsubq/vpaddd/vpsubd): `\t<mn>\tsrc2, src1, dst`
      | _, [a, b] =>
          "\t" ++ mn ++ "\t" ++ b ++ ", " ++ a ++ ", " ++ dst
      -- ill-formed operand list (wrong arity): visible rejection for gas
      | _, _ =>
          "\t# <ill-formed YmmOp operands for " ++ mn ++ ">"
  | .ymov dst src    => "\tvmovdqu\t" ++ src ++ ", " ++ dst
  | .yload dst mem   => "\tvmovdqu\t" ++ renderYmmMem mem ++ ", " ++ dst
  | .ystore mem src  => "\tvmovdqu\t" ++ src ++ ", " ++ renderYmmMem mem

/-- Print a whole block's instruction lines (one per `YmmInstr`). -/
def renderYmmBlockBody (block : List YmmInstr) : List String :=
  block.map renderYmmInstr

/-! ## 4. The function frame (verbatim from `Avx2Ymm.renderYFundef`)

The signed ML-DSA NTT kernel is leaf, uses no callee-saved GP registers, touches
only `%ymm` and the two argument pointers (`%rdi` = `r`, `%rsi` = `aux`), and
returns `r`. The frame is the symbol directives, the body, the `movq %rdi, %rax`
return-value move, and `ret`. Reproduced VERBATIM from `renderYFundef` — the
exact directive set + tabs is load-bearing for byte-identity with the bespoke
printer (and hence the bench KATs). -/

/-- Render a complete AT&T function: header directives, label, body, ABI
    epilogue (`movq %rdi, %rax ; ret`). Copied verbatim from
    `Avx2Ymm.renderYFundef`. -/
def renderYmmFundef (name : String) (block : List YmmInstr) : List String :=
  [ "\t.att_syntax"
  , "\t.text"
  , "\t.p2align\t5"
  , "\t.globl\t" ++ name
  , "\t.type\t" ++ name ++ ", @function"
  , name ++ ":" ]
  ++ renderYmmBlockBody block
  ++ [ "\tmovq\t%rdi, %rax"
     , "\tret"
     , "\t.section\t.note.GNU-stack,\"\",@progbits" ]

/-- The function text as a single `\n`-joined string (ready to write to a `.s`).
    Matches `Avx2Ymm.renderYFundefText`. -/
def renderYmmFundefText (name : String) (block : List YmmInstr) : String :=
  String.intercalate "\n" (renderYmmFundef name block) ++ "\n"

/-! ## 5. Syntax pins (the bespoke printer's 14 pins, on `renderYmmInstr`)

Each reproduces an `Avx2YmmAsmPrinter` `example` with the SAME expected AT&T
string, asserting `renderYmmInstr` is byte-identical to `renderYInst`. -/

/-- `vpmuldq %ymm4, %ymm2, %ymm6` (reference `.s` line 13). -/
example : renderYmmInstr (.alu .vpmuldq "%ymm6" ["%ymm2", "%ymm4"])
    = "\tvpmuldq\t%ymm4, %ymm2, %ymm6" := by native_decide

/-- `vmovshdup %ymm4, %ymm5` (reference line 12). -/
example : renderYmmInstr (.alu .vmovshdup "%ymm5" ["%ymm4"])
    = "\tvmovshdup\t%ymm4, %ymm5" := by native_decide

/-- `vpsubq %ymm4, %ymm6, %ymm6` (reference line 19). -/
example : renderYmmInstr (.alu .vpsubq "%ymm6" ["%ymm6", "%ymm4"])
    = "\tvpsubq\t%ymm4, %ymm6, %ymm6" := by native_decide

/-- `vpblendd $170, %ymm2, %ymm6, %ymm2` (reference line 22). -/
example : renderYmmInstr (.alu (.vpblendd 170) "%ymm2" ["%ymm6", "%ymm2"])
    = "\tvpblendd\t$170, %ymm2, %ymm6, %ymm2" := by native_decide

/-- `vpaddd %ymm2, %ymm1, %ymm3` (reference line 23). -/
example : renderYmmInstr (.alu .vpaddd "%ymm3" ["%ymm1", "%ymm2"])
    = "\tvpaddd\t%ymm2, %ymm1, %ymm3" := by native_decide

/-- `vpsubd %ymm2, %ymm1, %ymm1` (reference line 24). -/
example : renderYmmInstr (.alu .vpsubd "%ymm1" ["%ymm1", "%ymm2"])
    = "\tvpsubd\t%ymm2, %ymm1, %ymm1" := by native_decide

/-- `vpermq $238, %ymm1, %ymm5` (reference line 1531). -/
example : renderYmmInstr (.alu (.vpermq 238) "%ymm5" ["%ymm1"])
    = "\tvpermq\t$238, %ymm1, %ymm5" := by native_decide

/-- `vpshufd $245, %ymm1, %ymm5` (reference line 2811). -/
example : renderYmmInstr (.alu (.vpshufd 245) "%ymm5" ["%ymm1"])
    = "\tvpshufd\t$245, %ymm1, %ymm5" := by native_decide

/-- `vmovdqu (%rsi), %ymm0` — zero-displacement load (reference line 7). -/
example : renderYmmInstr (.yload "%ymm0" ⟨"%rsi", 0⟩)
    = "\tvmovdqu\t(%rsi), %ymm0" := by native_decide

/-- `vmovdqu 512(%rdi), %ymm4` — positive-displacement load (reference line 11). -/
example : renderYmmInstr (.yload "%ymm4" ⟨"%rdi", 512⟩)
    = "\tvmovdqu\t512(%rdi), %ymm4" := by native_decide

/-- `vmovdqu %ymm3, (%rdi)` — zero-displacement store (reference line 329). -/
example : renderYmmInstr (.ystore ⟨"%rdi", 0⟩ "%ymm3")
    = "\tvmovdqu\t%ymm3, (%rdi)" := by native_decide

/-- `vmovdqu %ymm1, 512(%rdi)` — positive-displacement store (reference line 26). -/
example : renderYmmInstr (.ystore ⟨"%rdi", 512⟩ "%ymm1")
    = "\tvmovdqu\t%ymm1, 512(%rdi)" := by native_decide

/-! ## 6. Frame pins (byte-identical to `renderYFundef`'s header/epilogue) -/

/-- The frame header carries the symbol directives and the AT&T label
    (identical to `Avx2Ymm.renderYFundef`'s header pin). -/
example :
    (renderYmmFundef "dsa_ntt_proto" []).take 6
      = [ "\t.att_syntax", "\t.text", "\t.p2align\t5"
        , "\t.globl\tdsa_ntt_proto", "\t.type\tdsa_ntt_proto, @function"
        , "dsa_ntt_proto:" ] := by native_decide

/-- The frame epilogue is the 2-pointer-ABI return (`r` in `%rax`) + `ret`
    (identical to `Avx2Ymm.renderYFundef`'s epilogue pin). -/
example :
    (renderYmmFundef "dsa_ntt_proto" []).drop 6
      = [ "\tmovq\t%rdi, %rax", "\tret"
        , "\t.section\t.note.GNU-stack,\"\",@progbits" ] := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
