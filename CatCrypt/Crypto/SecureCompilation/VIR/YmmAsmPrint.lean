/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.YmmDialectOps
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmDialectOps

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
are keyed on the `YmmOp` constructor: plain binary ops print `src2, src1, dst`
through a catch-all arm, unary `vmovshdup` prints `src, dst`, and the `imm8`-
carrying permutes (`vpshufd`/`vpermq`/`vpblendd`) and lane shifts
(`vpsrlq`/`vpsllq`/`vpsrld`/`vpslld`) bake the immediate into a leading `$imm`
operand. The `vmovdqu` move/load/store arms are not `YmmOp`s (they leave/enter
memory), so they are separate `YmmInstr` constructors with their own literal
mnemonic.

## Named-symbol memory operands (§7)

`YmmMem` is base-plus-displacement, which cannot spell a rip-relative reference
to a `.rodata` label: `⟨"sym(%rip)", 0⟩` would print `(sym(%rip))`, which `gas`
rejects. `YmmSymMem` is the second operand form — a symbol name plus a byte
offset into it, printed `sym(%rip)` / `sym+8(%rip)` / `sym-8(%rip)`. It is
carried by `YmmSymInstr`, an instruction layer that lifts every `YmmInstr`
through `.plain` and adds the two symbol-sourced loads (`vmovdqu` of a 256-bit
constant, `vpbroadcastq` of a single qword). `YmmMem`, `YmmInstr` and every
renderer over them are unchanged, and `renderYmmSymBlockBody_plain` /
`renderYmmSymFundef_plain` state that a `.plain`-only block renders to the same
lines as before.

## What a symbol operand asserts, and what the render establishes

A symbol operand names a memory location; printing it says nothing about the
bytes at that location. `YmmOp.denote` is a function on register values, and
`YmmInstr` has no memory semantics at all (`MpnSimdExtractEmit.evalXInst`, the
one model over it, treats `.yload`/`.ystore` as register-file no-ops), so a
kernel that reads a mask from `c_M26(%rip)` and then proves a lane identity
about the loaded register has assumed the mask value rather than derived it.

Three obligations sit behind such an operand:

* **the reference resolves to a defined label.** `ymmSymsDefined` pairs each
  referenced symbol with a name in the `.rodata` definition list, and
  `ymmSymsDefined_iff` characterises it as list inclusion. This one is checked
  in Lean.
* **the label holds the intended value.** The `.rodata` `.quad` list is the
  definition; discharging this means deriving those words from the Lean datum
  the kernel's specification uses, so the constant is written once, and running
  a machine semantics that seeds the symbol's memory.
  `X86Backend/RodataProbe.tableGet_value` is what that looks like at the scalar
  tier: it seeds the symbol bank and runs `runBlock`. There is no 256-bit
  counterpart, so at this tier the value rests on the emitted `.quad` list and
  the external byte KAT.
* **`gas` and `ld` resolve `sym(%rip)` to the address of the `.rodata` label**
  under PIE/PIC. This is the assembler/linker trust the backend's other
  rip-relative leaves already carry (`AsmPrinter.JInstr.loadSym`).

## Where the trust boundary is (identical posture to the bespoke printer)

The printer is a syntactic map (one instruction arm → one AT&T line, fixed
physical-register names, no instruction selection / scheduling / regalloc) and
`gas` performs only assembly. The trusted edge is: the printer is correct AT&T
syntax for each mnemonic, and `gas` encodes each mnemonic per the SDM.
-/

@[expose] public section

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
  /-- `vpternlogq $imm, src2, src1, dst` — `dst := ternlogW imm dst src1 src2`.
      It reads its destination as the high input, so it is three-input and is
      kept out of `YmmOp`, whose denotation reads at most two operands.
      AVX-512VL (EVEX). -/
  | ternlog (imm : Nat) (dst src1 src2 : String)

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
      -- imm8-carrying unary lane shifts: `\t<mn>\t$imm, src, dst`
      | .vpsrlq imm, [a] =>
          "\t" ++ mn ++ "\t$" ++ toString imm ++ ", " ++ a ++ ", " ++ dst
      | .vpsllq imm, [a] =>
          "\t" ++ mn ++ "\t$" ++ toString imm ++ ", " ++ a ++ ", " ++ dst
      | .vpsrld imm, [a] =>
          "\t" ++ mn ++ "\t$" ++ toString imm ++ ", " ++ a ++ ", " ++ dst
      | .vpslld imm, [a] =>
          "\t" ++ mn ++ "\t$" ++ toString imm ++ ", " ++ a ++ ", " ++ dst
      -- imm8-carrying unary lane rotate (AVX-512VL): `\tvprolq\t$imm, src, dst`
      | .vprolq imm, [a] =>
          "\t" ++ mn ++ "\t$" ++ toString imm ++ ", " ++ a ++ ", " ++ dst
      -- unary high-dup move: `\tvmovshdup\tsrc, dst`
      | .vmovshdup, [a] =>
          "\t" ++ mn ++ "\t" ++ a ++ ", " ++ dst
      -- plain binary ALU (vpmuldq/vpsubq/vpaddd/vpsubd/vpmuludq/vpaddq/vpmullq/
      -- vpand/vpor/vpxor/vpshufb): `\t<mn>\tsrc2, src1, dst`
      | _, [a, b] =>
          "\t" ++ mn ++ "\t" ++ b ++ ", " ++ a ++ ", " ++ dst
      -- ill-formed operand list (wrong arity): visible rejection for gas
      | _, _ =>
          "\t# <ill-formed YmmOp operands for " ++ mn ++ ">"
  | .ymov dst src    => "\tvmovdqu\t" ++ src ++ ", " ++ dst
  | .yload dst mem   => "\tvmovdqu\t" ++ renderYmmMem mem ++ ", " ++ dst
  | .ystore mem src  => "\tvmovdqu\t" ++ src ++ ", " ++ renderYmmMem mem
  | .ternlog imm d b c =>
      "\tvpternlogq\t$" ++ toString imm ++ ", " ++ c ++ ", " ++ b ++ ", " ++ d

/-- Print a whole block's instruction lines (one per `YmmInstr`). -/
def renderYmmBlockBody (block : List YmmInstr) : List String :=
  block.map renderYmmInstr

/-! ## 4. The function frame (verbatim from `Avx2Ymm.renderYFundef`)

The signed ML-DSA NTT kernel is leaf, uses no callee-saved GP registers, touches
only `%ymm` and the two argument pointers (`%rdi` = `r`, `%rsi` = `aux`), and
returns `r`. The frame is the symbol directives, the body, the `movq %rdi, %rax`
return-value move, and `ret`. The exact directive set and tab placement is what
byte-identity with `renderYFundef`, and hence with the bench KATs, rests on. -/

/-- The six frame header lines: the AT&T/section directives, the alignment, the
    symbol directives, and the function label. -/
def ymmFrameHeader (name : String) : List String :=
  [ "\t.att_syntax"
  , "\t.text"
  , "\t.p2align\t5"
  , "\t.globl\t" ++ name
  , "\t.type\t" ++ name ++ ", @function"
  , name ++ ":" ]

/-- The three frame footer lines: the 2-pointer-ABI return-value move, `ret`, and
    the non-executable-stack note. -/
def ymmFrameFooter : List String :=
  [ "\tmovq\t%rdi, %rax"
  , "\tret"
  , "\t.section\t.note.GNU-stack,\"\",@progbits" ]

/-- Render a complete AT&T function: header directives, label, body, ABI
    epilogue (`movq %rdi, %rax ; ret`). Copied verbatim from
    `Avx2Ymm.renderYFundef`. -/
def renderYmmFundef (name : String) (block : List YmmInstr) : List String :=
  ymmFrameHeader name ++ renderYmmBlockBody block ++ ymmFrameFooter

/-- The function text as a single `\n`-joined string (ready to write to a `.s`).
    Matches `Avx2Ymm.renderYFundefText`. -/
def renderYmmFundefText (name : String) (block : List YmmInstr) : String :=
  String.intercalate "\n" (renderYmmFundef name block) ++ "\n"

/-! ## 5. Syntax pins (the bespoke printer's 14 pins, on `renderYmmInstr`)

Each reproduces an `Avx2YmmAsmPrinter` `example` with the SAME expected AT&T
string, asserting `renderYmmInstr` is byte-identical to `renderYInst`. -/

-- `vpmuldq %ymm4, %ymm2, %ymm6` (reference `.s` line 13).
#guard renderYmmInstr (.alu .vpmuldq "%ymm6" ["%ymm2", "%ymm4"])
    == "\tvpmuldq\t%ymm4, %ymm2, %ymm6"

-- `vmovshdup %ymm4, %ymm5` (reference line 12).
#guard renderYmmInstr (.alu .vmovshdup "%ymm5" ["%ymm4"])
    == "\tvmovshdup\t%ymm4, %ymm5"

-- `vpsubq %ymm4, %ymm6, %ymm6` (reference line 19).
#guard renderYmmInstr (.alu .vpsubq "%ymm6" ["%ymm6", "%ymm4"])
    == "\tvpsubq\t%ymm4, %ymm6, %ymm6"

-- `vpblendd $170, %ymm2, %ymm6, %ymm2` (reference line 22).
#guard renderYmmInstr (.alu (.vpblendd 170) "%ymm2" ["%ymm6", "%ymm2"])
    == "\tvpblendd\t$170, %ymm2, %ymm6, %ymm2"

-- `vpaddd %ymm2, %ymm1, %ymm3` (reference line 23).
#guard renderYmmInstr (.alu .vpaddd "%ymm3" ["%ymm1", "%ymm2"])
    == "\tvpaddd\t%ymm2, %ymm1, %ymm3"

-- `vpsubd %ymm2, %ymm1, %ymm1` (reference line 24).
#guard renderYmmInstr (.alu .vpsubd "%ymm1" ["%ymm1", "%ymm2"])
    == "\tvpsubd\t%ymm2, %ymm1, %ymm1"

-- `vpermq $238, %ymm1, %ymm5` (reference line 1531).
#guard renderYmmInstr (.alu (.vpermq 238) "%ymm5" ["%ymm1"])
    == "\tvpermq\t$238, %ymm1, %ymm5"

-- `vpshufd $245, %ymm1, %ymm5` (reference line 2811).
#guard renderYmmInstr (.alu (.vpshufd 245) "%ymm5" ["%ymm1"])
    == "\tvpshufd\t$245, %ymm1, %ymm5"

-- `vmovdqu (%rsi), %ymm0` — zero-displacement load (reference line 7).
#guard renderYmmInstr (.yload "%ymm0" ⟨"%rsi", 0⟩)
    == "\tvmovdqu\t(%rsi), %ymm0"

-- `vmovdqu 512(%rdi), %ymm4` — positive-displacement load (reference line 11).
#guard renderYmmInstr (.yload "%ymm4" ⟨"%rdi", 512⟩)
    == "\tvmovdqu\t512(%rdi), %ymm4"

-- `vmovdqu %ymm3, (%rdi)` — zero-displacement store (reference line 329).
#guard renderYmmInstr (.ystore ⟨"%rdi", 0⟩ "%ymm3")
    == "\tvmovdqu\t%ymm3, (%rdi)"

-- `vmovdqu %ymm1, 512(%rdi)` — positive-displacement store (reference line 26).
#guard renderYmmInstr (.ystore ⟨"%rdi", 512⟩ "%ymm1")
    == "\tvmovdqu\t%ymm1, 512(%rdi)"

/-! ## 5b. Syntax pins for the added ALU ops

Operand order is keyed to real emitted lines: `vpxor %ymm2, %ymm5, %ymm5` and
`vpslld $12, %ymm3, %ymm6` (`bench/chacha_compare/gen_owned_simd/`),
`vpaddq %ymm21, %ymm16, %ymm16` and `vpsrlq $26, %ymm16, %ymm22`
(`bench/poly1305_compare/gen_owned_ymm/`). Those artifacts separate mnemonic
from operands with a SPACE; this printer uses a TAB, matching the ML-DSA NTT
reference `.s` it is pinned against. `gas` accepts either. -/

-- `vpmuludq %ymm5, %ymm0, %ymm16` — plain binary, `src2, src1, dst`.
#guard renderYmmInstr (.alu .vpmuludq "%ymm16" ["%ymm0", "%ymm5"])
    == "\tvpmuludq\t%ymm5, %ymm0, %ymm16"

-- `vpaddq %ymm21, %ymm16, %ymm16` — plain binary.
#guard renderYmmInstr (.alu .vpaddq "%ymm16" ["%ymm16", "%ymm21"])
    == "\tvpaddq\t%ymm21, %ymm16, %ymm16"

-- `vpmullq %ymm15, %ymm23, %ymm23` — plain binary.
#guard renderYmmInstr (.alu .vpmullq "%ymm23" ["%ymm23", "%ymm15"])
    == "\tvpmullq\t%ymm15, %ymm23, %ymm23"

-- `vpand %ymm14, %ymm16, %ymm16` — the VEX spelling of the artifacts'
-- EVEX `vpandq`.
#guard renderYmmInstr (.alu .vpand "%ymm16" ["%ymm16", "%ymm14"])
    == "\tvpand\t%ymm14, %ymm16, %ymm16"

-- `vpor %ymm3, %ymm6, %ymm3` — plain binary.
#guard renderYmmInstr (.alu .vpor "%ymm3" ["%ymm6", "%ymm3"])
    == "\tvpor\t%ymm3, %ymm6, %ymm3"

-- `vpxor %ymm2, %ymm5, %ymm5` — plain binary.
#guard renderYmmInstr (.alu .vpxor "%ymm5" ["%ymm5", "%ymm2"])
    == "\tvpxor\t%ymm2, %ymm5, %ymm5"

-- `vpshufb %ymm0, %ymm5, %ymm5` — binary, `src1` = data, `src2` = control.
#guard renderYmmInstr (.alu .vpshufb "%ymm5" ["%ymm5", "%ymm0"])
    == "\tvpshufb\t%ymm0, %ymm5, %ymm5"

-- `vpsrlq $26, %ymm16, %ymm22` — imm8-carrying unary shift.
#guard renderYmmInstr (.alu (.vpsrlq 26) "%ymm22" ["%ymm16"])
    == "\tvpsrlq\t$26, %ymm16, %ymm22"

-- `vpsllq $23, %ymm20, %ymm21` — imm8-carrying unary shift.
#guard renderYmmInstr (.alu (.vpsllq 23) "%ymm21" ["%ymm20"])
    == "\tvpsllq\t$23, %ymm20, %ymm21"

-- `vpsrld $20, %ymm3, %ymm3` — imm8-carrying unary shift.
#guard renderYmmInstr (.alu (.vpsrld 20) "%ymm3" ["%ymm3"])
    == "\tvpsrld\t$20, %ymm3, %ymm3"

-- `vpslld $12, %ymm3, %ymm6` — imm8-carrying unary shift.
#guard renderYmmInstr (.alu (.vpslld 12) "%ymm6" ["%ymm3"])
    == "\tvpslld\t$12, %ymm3, %ymm6"

/-! ## 6. Frame pins (byte-identical to `renderYFundef`'s header/epilogue) -/

-- The frame header carries the symbol directives and the AT&T label
-- (identical to `Avx2Ymm.renderYFundef`'s header pin).
#guard
    (renderYmmFundef "dsa_ntt_proto" []).take 6
      == [ "\t.att_syntax", "\t.text", "\t.p2align\t5"
        , "\t.globl\tdsa_ntt_proto", "\t.type\tdsa_ntt_proto, @function"
        , "dsa_ntt_proto:" ]

-- The frame epilogue is the 2-pointer-ABI return (`r` in `%rax`) + `ret`
-- (identical to `Avx2Ymm.renderYFundef`'s epilogue pin).
#guard
    (renderYmmFundef "dsa_ntt_proto" []).drop 6
      == [ "\tmovq\t%rdi, %rax", "\tret"
        , "\t.section\t.note.GNU-stack,\"\",@progbits" ]

/-! ## 7. Named-symbol (rip-relative) operands and the instruction layer over them

`YmmMem` addresses memory through a base register; a `.rodata` constant is
addressed through its symbol name and the instruction pointer. `YmmSymMem` is
that second form, and `YmmSymInstr` is the instruction type that carries it: it
lifts every `YmmInstr` through `.plain` and adds the two symbol-sourced loads the
256-bit kernels need. This is the same extension shape as
`X86Backend/MpnSimdExtractEmit.XInst` (lift the base instruction type, add arms
with their own literal mnemonics), which keeps `YmmInstr` and both of its
existing consumers untouched.

The arms are loads only. A `.rodata` symbol is read-only, so there is no
symbol-destination store; a memory-source ALU form (`vpxor sym(%rip), %ymm0,
%ymm0`, as `VIR/KeccakAvx2Emit` spells it inline) is a further arm, not part of
this operand. -/

/-- A rip-relative 256-bit memory operand: a symbol name plus a byte offset into
    the object it labels. `disp = 0` addresses the symbol itself; `disp = 32`
    addresses the second 256-bit constant of a table laid out at that label. -/
structure YmmSymMem where
  /-- The `.rodata` label name. -/
  sym : String
  /-- Byte offset added to the symbol's address. -/
  disp : Int

/-- The symbol operand at offset zero. -/
def ymmSym (name : String) : YmmSymMem := ⟨name, 0⟩

/-- Print a `YmmSymMem` as AT&T rip-relative `sym(%rip)`, with a signed
    symbol-relative offset when it is non-zero (`sym+32(%rip)`,
    `sym-8(%rip)`). -/
def renderYmmSymMem (m : YmmSymMem) : String :=
  if m.disp = 0 then m.sym ++ "(%rip)"
  else if m.disp > 0 then m.sym ++ "+" ++ toString m.disp ++ "(%rip)"
  else m.sym ++ toString m.disp ++ "(%rip)"

/-- One instruction of a kernel that reads `.rodata` constants: any `YmmInstr`,
    or one of the two symbol-sourced loads. -/
inductive YmmSymInstr where
  /-- A base `YmmInstr` (ALU op, register move, base+displacement load/store). -/
  | plain (i : YmmInstr)
  /-- `vmovdqu sym(%rip), dst` — load a 256-bit constant. -/
  | yloadSym (dst : String) (mem : YmmSymMem)
  /-- `vpbroadcastq sym(%rip), dst` — load one qword and replicate it across the
      four 64-bit lanes. -/
  | ybcastqSym (dst : String) (mem : YmmSymMem)

/-- Render one `YmmSymInstr` to its AT&T asm line. The `.plain` arm is
    `renderYmmInstr`; the two symbol arms carry their own literal mnemonic and
    print `src, dst` (AT&T load order). -/
def renderYmmSymInstr : YmmSymInstr → String
  | .plain i => renderYmmInstr i
  | .yloadSym dst mem => "\tvmovdqu\t" ++ renderYmmSymMem mem ++ ", " ++ dst
  | .ybcastqSym dst mem => "\tvpbroadcastq\t" ++ renderYmmSymMem mem ++ ", " ++ dst

/-- Print a whole symbol-layer block's instruction lines. -/
def renderYmmSymBlockBody (block : List YmmSymInstr) : List String :=
  block.map renderYmmSymInstr

/-- Render a complete AT&T function over the symbol layer, with the frame of
    `renderYmmFundef` (the shared `ymmFrameHeader` / `ymmFrameFooter`). -/
def renderYmmSymFundef (name : String) (block : List YmmSymInstr) : List String :=
  ymmFrameHeader name ++ renderYmmSymBlockBody block ++ ymmFrameFooter

/-- The symbol-layer function text as a single `\n`-joined string. -/
def renderYmmSymFundefText (name : String) (block : List YmmSymInstr) : String :=
  String.intercalate "\n" (renderYmmSymFundef name block) ++ "\n"

/-! ### The symbol layer prints the base layer unchanged

A block with no symbol operand renders to exactly the lines the base printer
produces, so moving a kernel onto `YmmSymInstr` before it references any
constant does not change its bytes. -/

/-- The `.plain` arm is `renderYmmInstr`. -/
theorem renderYmmSymInstr_plain (i : YmmInstr) :
    renderYmmSymInstr (.plain i) = renderYmmInstr i := rfl

/-- A `.plain`-only block renders to the base printer's lines. -/
theorem renderYmmSymBlockBody_plain (block : List YmmInstr) :
    renderYmmSymBlockBody (block.map .plain) = renderYmmBlockBody block := by
  simp [renderYmmSymBlockBody, renderYmmBlockBody, List.map_map,
    renderYmmSymInstr_plain]

/-- A `.plain`-only function renders to the base printer's function, frame
    included. -/
theorem renderYmmSymFundef_plain (name : String) (block : List YmmInstr) :
    renderYmmSymFundef name (block.map .plain) = renderYmmFundef name block := by
  simp [renderYmmSymFundef, renderYmmFundef, renderYmmSymBlockBody_plain]

/-! ### Pairing each symbol reference with a definition

`ymmSymRefs` collects the symbols a block reads; `ymmSymsDefined` checks each
against a list of defined `.rodata` label names. This is the one obligation of
the three in the module docstring that is checked here: it rules out a reference
to a constant the kernel never defines (a link error, or worse a coincidental
match with an unrelated global), and says nothing about the bytes at the label. -/

/-- The `.rodata` symbol an instruction reads, if any. -/
def YmmSymInstr.symRef : YmmSymInstr → Option String
  | .plain _ => none
  | .yloadSym _ mem => some mem.sym
  | .ybcastqSym _ mem => some mem.sym

/-- The distinct `.rodata` symbols a block reads, in first-reference order. -/
def ymmSymRefs (block : List YmmSymInstr) : List String :=
  (block.filterMap YmmSymInstr.symRef).eraseDups

/-- Every symbol the block reads appears in `defs` (the defined `.rodata` label
    names). -/
def ymmSymsDefined (block : List YmmSymInstr) (defs : List String) : Bool :=
  (ymmSymRefs block).all (fun s => defs.contains s)

/-- `ymmSymsDefined` is inclusion of the referenced symbols in the defined
    names. -/
theorem ymmSymsDefined_iff (block : List YmmSymInstr) (defs : List String) :
    ymmSymsDefined block defs = true ↔ ∀ s ∈ ymmSymRefs block, s ∈ defs := by
  simp [ymmSymsDefined, List.all_eq_true]

/-! ### Syntax pins for the symbol operand and its two arms

Spellings audited against `gas`: `vmovdqu fa_M26(%rip), %ymm3` and
`vpbroadcastq LEA_MASK32(%rip), %ymm0` are the forms the ristretto and LEA/LSH
artifacts use. These are `#guard`s rather than `native_decide` examples, so they
carry no axiom. -/

/- `vmovdqu fa_M26(%rip), %ymm3` — 256-bit constant load at offset zero. -/
#guard renderYmmSymInstr (.yloadSym "%ymm3" (ymmSym "fa_M26"))
  == "\tvmovdqu\tfa_M26(%rip), %ymm3"

/- `vpbroadcastq LEA_MASK32(%rip), %ymm0` — single-qword broadcast. -/
#guard renderYmmSymInstr (.ybcastqSym "%ymm0" (ymmSym "LEA_MASK32"))
  == "\tvpbroadcastq\tLEA_MASK32(%rip), %ymm0"

/- A positive symbol-relative offset prints as `sym+disp(%rip)`. -/
#guard renderYmmSymMem ⟨"fa_2P", 32⟩ == "fa_2P+32(%rip)"

/- A negative symbol-relative offset prints as `sym-disp(%rip)`. -/
#guard renderYmmSymMem ⟨"fa_2P", -32⟩ == "fa_2P-32(%rip)"

/- A `.plain` arm prints exactly the base printer's line. -/
#guard renderYmmSymInstr (.plain (.yload "%ymm4" ⟨"%rdi", 512⟩))
  == "\tvmovdqu\t512(%rdi), %ymm4"

/- Two references to one symbol collect once; a `.plain` arm references none. -/
#guard ymmSymRefs [ .yloadSym "%ymm3" (ymmSym "fa_M26")
                  , .plain (.ymov "%ymm4" "%ymm3")
                  , .ybcastqSym "%ymm5" ⟨"fa_M26", 8⟩ ] == ["fa_M26"]

/- A reference with a definition passes; one without fails. -/
#guard ymmSymsDefined [.yloadSym "%ymm3" (ymmSym "fa_M26")] ["fa_M26", "fa_C19"]
#guard !ymmSymsDefined [.yloadSym "%ymm3" (ymmSym "fa_M25")] ["fa_M26", "fa_C19"]

end CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
