/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# AT&T asm printer for the scalar `JInstr` machine instructions (the trust boundary)

`Avx512AsmPrinter.lean` prints the **ZMM** subset (`ZInstr`) to AT&T-syntax
AVX-512 assembly. This module is its **scalar** counterpart: it prints a
`JInstr w` block — the scalar + ADX/BMI2 instruction set of `JasminModel.lean`,
the same set lowered to `Com (x86Dialect w)` by `X86Dialect.lowerBlock` — to
AT&T-syntax x86-64 assembly text (`movq`/`addq`/`adcq`/.../`mulx`/`adcx`/`adox`,
`%rN` operands), to be assembled by `gas`/`cc`.

## Where the trust boundary is (precise)

The **verified artifact** is `Com (x86Dialect w) → JasminModel.runBlock` (the
`X86Dialect.lowerBlock` pass + `X86Dialect.lowerBlock_denote`, down to the
differentially-validated `JasminModel.evalInstr` semantics, itself a line-for-line
transcription of Jasmin's Rocq `x86_instr_decl.v` validated in
`TranslationValidation.lean`). This printer + `gas` is the *thin* trust boundary,
much narrower than trusting jasminc's full lowering, because:

* the printer is a **syntactic** map: one `JInstr` arm → one AT&T mnemonic line,
  with a fixed register assignment (`allocGp`, first-seen order over the
  callee/caller GP pool). There is no instruction selection, no scheduling, no
  optimization — the mnemonic and its operand registers are determined by the
  `JInstr` constructor and the allocator, nothing else.
* `gas` then performs only **assembly** (mnemonic+operands → encoded bytes), the
  same final step the jasmin chain trusts. We run no optimizing compiler over the
  kernel body.

So the trusted-but-unverified surface is: (the printer is correct AT&T syntax for
each mnemonic) ∧ (`gas` encodes each mnemonic per the Intel SDM). The
function prologue/epilogue that loads arguments into the named registers and
stores results (`renderLeafFn`) is likewise trusted scaffolding, *outside* the
verified straight-line body: the verified claim covers the body's
`runBlock`/`evalInstr` transform, not the System V calling-convention glue.

## Register allocation

A `JInstr` block uses SSA-style string names. `allocGp` assigns each distinct
name a fixed `%rN` (in first-seen order over a fixed GP pool that excludes
`%rsp`). It is the generic linear scan `GenericRegAlloc.firstFitScan` over names
that are all live together, which is first-fit (`allocGp_eq_zip`). Names past the
pool are left unmapped (`allocOverflow`); the spilling allocator is
`Optimizer.SpillingRegAlloc`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. Register allocation: name → %rN -/

/-- The general-purpose 64-bit register pool, in a fixed allocation order.
    `%rsp` (stack pointer) and `%rbp` (frame base) are excluded so first-fit
    allocation never clobbers the frame. Order chosen so the System-V argument
    registers come first, easing the leaf-function ABI glue. -/
def gpPool : List String :=
  [ "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9", "%r10", "%r11",
    "%rax", "%rbx", "%r12", "%r13", "%r14", "%r15" ]

/-- The register name(s) read by an operand (`[]` for an immediate). -/
def srcNames : JOperand → List String
  | .reg r => [r]
  | .imm _ => []

/-- The (dst names, src names) read/written by one `JInstr` — for collecting the
    distinct register names of a block in first-seen order. -/
def jinstrNames : {w : Nat} → JInstr w → List String
  | _, .mov d s   => d :: srcNames s
  | _, .add d s   => d :: srcNames s
  | _, .sub d s   => d :: srcNames s
  | _, .adc d s   => d :: srcNames s
  | _, .sbb d s   => d :: srcNames s
  | _, .imul d s  => d :: srcNames s
  | _, .neg d     => [d]
  | _, .setc d    => [d]
  | _, .and_ d s  => d :: srcNames s
  | _, .test a b  => a :: srcNames b
  | _, .or_ d s   => d :: srcNames s
  | _, .xor_ d s  => d :: srcNames s
  | _, .shl d s   => d :: srcNames s
  | _, .shr d s   => d :: srcNames s
  | _, .sar d s   => d :: srcNames s
  | _, .cmove d s  => d :: srcNames s
  | _, .cmovne d s => d :: srcNames s
  | _, .cmovb d s  => d :: srcNames s
  | _, .mulx dh dl a b => dh :: dl :: srcNames a ++ srcNames b
  | _, .mulxMem dh dl a base _ => dh :: dl :: base :: srcNames a
  | _, .adcx d s  => d :: srcNames s
  | _, .adox d s  => d :: srcNames s
  | _, .loadMem d base _   => d :: [base]
  | _, .storeMem base _ s  => base :: srcNames s
  | _, .loadMemIdx d base idx _   => d :: base :: [idx]
  | _, .storeMemIdx base idx _ s  => base :: idx :: srcNames s
  -- `loadSym dst sym` writes the base register `dst`; `sym` is a `.rodata`
  -- *symbol* (an assembler label), NOT a register name, so it is not allocated.
  -- `cmp a b` has no destination: both operands are reads, and both are allocated.
  | _, .cmp a b   => a :: srcNames b
  | _, .not_ d    => [d]
  | _, .andn d a b => [d, a, b]
  | _, .rol d amt | _, .ror d amt => d :: srcNames amt
  | _, .rorx d src amt => d :: src :: srcNames amt
  | _, .shlx d src cnt | _, .shrx d src cnt | _, .sarx d src cnt => [d, src, cnt]
  -- the extension moves' `srcW` is a width, not a register name.
  | _, .movzx d _ src | _, .movsx d _ src => [d, src]
  -- `lea` names a destination and the two address registers; `scale`/`off` are literals.
  | _, .lea d base idx _ _ => [d, base, idx]
  | _, .loadSym d _   => [d]
  | _, .inc d | _, .dec d => [d]
  | _, .clc | _, .stc => []
  | _, .xchg a b => [a, b]
  | _, .imulri d s _ => [d, s]
  -- the widening multiplies name their implicit `%rdx`/`%rax` destinations and the source.
  | _, .mul dh dl s | _, .imulWide dh dl s => [dh, dl, s]
  | _, .shld d s amt | _, .shrd d s amt => d :: s :: srcNames amt
  | _, .rcl d amt | _, .rcr d amt => d :: srcNames amt
  | _, .cmovcc _ d s => d :: srcNames s
  | _, .setcc _ d => [d]
  | _, .testN _ a b => a :: srcNames b
  | _, .bt a b | _, .btr a b | _, .bts a b => a :: srcNames b
  -- the memory-operand arithmetic names its register destination and the base register.
  | _, .addMem d base _ | _, .adcxMem d base _ | _, .adoxMem d base _
  | _, .imulMem d base _ | _, .imulriMem d base _ _ => [d, base]
  | _, .cmpMem a base _ => [a, base]
  | _, .cmovccMem _ d base _ => [d, base]
  | _, .aluMem _ d base _ => [d, base]
  | _, .andnMem d a base _ => [d, a, base]
  | _, .addToMem base _ s => base :: srcNames s
  | _, .bzhi d src idx => [d, src, idx]

/-- Collect the distinct register names of a block, in first-seen order. -/
def blockNames {w : Nat} (block : List (JInstr w)) : List String :=
  (block.flatMap jinstrNames).foldl
    (fun acc n => if acc.contains n then acc else acc ++ [n]) []

/-- A register assignment: an association list name → "%rN". -/
abbrev GpAlloc := List (String × String)

/-- First-fit allocation: assign each distinct block name the next free pool
    register, with any `pinned` names forced first (used to fix arguments to
    their System-V argument registers). The unpinned names go through the generic
    linear scan with every name live throughout (`GenericRegAlloc.firstFitScan`). -/
def allocGp {w : Nat} (pinned : GpAlloc) (block : List (JInstr w)) : GpAlloc :=
  let used := pinned.map Prod.snd
  let pool := gpPool.filter (fun r => ¬ used.contains r)
  let free := blockNames block |>.filter (fun n => (pinned.lookup n).isNone)
  pinned ++ CatCrypt.Crypto.Optimizer.GenericRegAlloc.firstFitScan pool free

/-- `allocGp` pairs the unpinned block names with the unpinned pool registers in order. -/
theorem allocGp_eq_zip {w : Nat} (pinned : GpAlloc) (block : List (JInstr w)) :
    allocGp pinned block
      = pinned ++ ((blockNames block).filter (fun n => (pinned.lookup n).isNone)).zip
          (gpPool.filter (fun r => ¬ (pinned.map Prod.snd).contains r)) := by
  rw [allocGp, CatCrypt.Crypto.Optimizer.GenericRegAlloc.firstFitScan_eq_zip]

/-- The distinct GP names a block needs beyond the pinned ones, and the number
    of pool registers available for them. The block fits the budget iff
    `gpFreeNames.length ≤ gpFreeSlots`. -/
def gpFreeNames {w : Nat} (pinned : GpAlloc) (block : List (JInstr w)) : List String :=
  blockNames block |>.filter (fun n => (pinned.lookup n).isNone)

/-- The number of pool registers free for non-pinned names. -/
def gpFreeSlots (pinned : GpAlloc) : Nat :=
  let used := pinned.map Prod.snd
  (gpPool.filter (fun r => ¬ used.contains r)).length

/-- `none` iff `allocGp` assigns every required name a distinct pool register;
    `some overflow` lists the names that `allocGp` would leave unmapped (because
    the free pool is exhausted), which `regOf` would then silently alias onto
    `%rax`, a register collision. A budget-aware emitter must check this is
    `none` before trusting the rendered block. -/
def allocOverflow {w : Nat} (pinned : GpAlloc) (block : List (JInstr w)) :
    Option (List String) :=
  let alloc := allocGp pinned block
  let mapped := alloc.map Prod.fst
  let names := gpFreeNames pinned block
  -- names that `free.zip pool` truncated away (free.length > pool.length)
  let unmapped := names.filter (fun n => ¬ mapped.contains n)
  if unmapped.isEmpty then none else some unmapped

/-- The `%rN` register a name is assigned. An unmapped name (only possible when
    `allocOverflow ≠ none`, i.e. the pool was exhausted) returns the explicit
    sentinel `<UNALLOCATED:n>` rather than silently aliasing onto a live `%rax`:
    the assembler then rejects the emitted text, so a budget overflow can never
    pass as valid code through a silent `%rax` alias. Callers that have
    verified `allocOverflow = none` never hit the sentinel. -/
def regOf (alloc : GpAlloc) (n : String) : String :=
  (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- Render an operand: a register name → its `%rN`; an immediate → `$v`. -/
def renderOperand (alloc : GpAlloc) : JOperand → String
  | .reg r => regOf alloc r
  | .imm v => "$" ++ toString v

/-- The AT&T 8-bit (low byte) subregister name for a `%rN` 64-bit register name
    (`"%rax" → "%al"`, `"%r8" → "%r8b"`). Used by `SETcc`, which writes a byte
    destination; the printer then `MOVZBQ`-zero-extends it to the full register. -/
def gpReg8 (r : String) : String :=
  match r with
  | "%rax" => "%al"  | "%rcx" => "%cl"  | "%rdx" => "%dl"  | "%rbx" => "%bl"
  | "%rsp" => "%spl" | "%rbp" => "%bpl" | "%rsi" => "%sil" | "%rdi" => "%dil"
  | "%r8"  => "%r8b" | "%r9"  => "%r9b" | "%r10" => "%r10b" | "%r11" => "%r11b"
  | "%r12" => "%r12b"| "%r13" => "%r13b"| "%r14" => "%r14b" | "%r15" => "%r15b"
  | other  => other

/-- The AT&T 16-bit subregister name for a `%rN` 64-bit register name
    (`"%rax" → "%ax"`, `"%r8" → "%r8w"`). The source operand of a 16-bit-source
    `MOVZX`/`MOVSX` is a word register. -/
def gpReg16 (r : String) : String :=
  match r with
  | "%rax" => "%ax"  | "%rcx" => "%cx"  | "%rdx" => "%dx"  | "%rbx" => "%bx"
  | "%rsp" => "%sp"  | "%rbp" => "%bp"  | "%rsi" => "%si"  | "%rdi" => "%di"
  | "%r8"  => "%r8w" | "%r9"  => "%r9w" | "%r10" => "%r10w" | "%r11" => "%r11w"
  | "%r12" => "%r12w"| "%r13" => "%r13w"| "%r14" => "%r14w" | "%r15" => "%r15w"
  | other  => other

/-- The AT&T 32-bit subregister name for a `%rN` 64-bit register name
    (`"%rax" → "%eax"`, `"%r8" → "%r8d"`). A 32-bit-source zero extension is
    written `movl %src32, %dst32`, since writing a 32-bit destination register
    zeroes the upper half. -/
def gpReg32 (r : String) : String :=
  match r with
  | "%rax" => "%eax" | "%rcx" => "%ecx" | "%rdx" => "%edx" | "%rbx" => "%ebx"
  | "%rsp" => "%esp" | "%rbp" => "%ebp" | "%rsi" => "%esi" | "%rdi" => "%edi"
  | "%r8"  => "%r8d" | "%r9"  => "%r9d" | "%r10" => "%r10d" | "%r11" => "%r11d"
  | "%r12" => "%r12d"| "%r13" => "%r13d"| "%r14" => "%r14d" | "%r15" => "%r15d"
  | other  => other

/-- The AT&T condition-code suffix of a Jasmin condition, in the spelling GNU as
    accepts after `set` and `cmov`: `nb` is `ae`, `nbe` is `a`, `nl` is `ge` and
    `nle` is `g`; the other twelve keep their `Condt` name. -/
def condSuffix : Condt → String
  | .o => "o"  | .no => "no" | .b => "b"   | .nb => "ae"
  | .e => "e"  | .ne => "ne" | .be => "be" | .nbe => "a"
  | .s => "s"  | .ns => "ns" | .p => "p"   | .np => "np"
  | .l => "l"  | .nl => "ge" | .le => "le" | .nle => "g"

/-- A shift or rotate count: an immediate prints as `$v`; a register prints as its
    low byte, the `%cl` operand the count-by-register encodings take. -/
def renderCount (alloc : GpAlloc) : JOperand → String
  | .reg r => gpReg8 (regOf alloc r)
  | .imm v => "$" ++ toString v

/-- An operand at operand size `sz`: a register as its `sz`-bit subregister name
    (`%al`, `%ax`, `%eax`, `%rax` at 8, 16, 32, 64), an immediate as `$v`. Any
    other size prints as a bracketed sentinel the assembler rejects. -/
def renderOperandN (sz : Nat) (alloc : GpAlloc) : JOperand → String
  | .imm v => "$" ++ toString v
  | .reg r =>
      let q := regOf alloc r
      match sz with
      | 8  => gpReg8 q
      | 16 => gpReg16 q
      | 32 => gpReg32 q
      | 64 => q
      | n  => "<UNSUPPORTED-WIDTH:" ++ toString n ++ ">"

/-! ## 2. The AT&T mnemonic printer (one line per `JInstr`)

AT&T two-operand order is `op src, dst` (`addq %rB, %rA` ≡ `A := A + B`). Shifts
take the count first (`shlq $imm, %rA`). The three/four-operand BMI2 forms
(`mulx`) and the ADX carry ops (`adcx`/`adox`) follow the GNU-as encoding. -/

/-- Print one `JInstr` to its AT&T asm line (64-bit `q` suffix, scalar GP regs).
    One arm → one line; no instruction selection or scheduling. -/
def renderJInstr {w : Nat} (alloc : GpAlloc) : JInstr w → String
  | .mov d s   => "\tmovq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .add d s   => "\taddq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .sub d s   => "\tsubq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .adc d s   => "\tadcq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .sbb d s   => "\tsbbq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  -- `IMUL` has no two-operand immediate form: an immediate multiplier uses the
  -- three-operand `imulq $imm, %src, %dst` (here src = dst), a register
  -- multiplier the two-operand `imulq %src, %dst`.
  | .imul d s  =>
      match s with
      | .imm _ => "\timulq " ++ renderOperand alloc s ++ ", " ++ regOf alloc d
                    ++ ", " ++ regOf alloc d
      | .reg _ => "\timulq " ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .neg d     => "\tnegq "  ++ regOf alloc d
  -- `SETcc` writes a byte destination; the model's `setc` arm stores the *full*
  -- zero-extended flag value, so the printer emits the `setb`/`movzbq` pair that
  -- realises that: `setb %dl` sets the low byte from CF, `movzbq %dl, %rdx`
  -- zero-extends to the full 64-bit register (matching `evalInstr`'s
  -- `if CF then 1 else 0` write). Two AT&T lines for the one model arm.
  | .setc d    =>
      let r := regOf alloc d
      "\tsetb " ++ gpReg8 r ++ "\n\tmovzbq " ++ gpReg8 r ++ ", " ++ r
  | .and_ d s  => "\tandq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .test a b  => "\ttestq " ++ renderOperand alloc b ++ ", " ++ regOf alloc a
  -- AT&T `cmpq src, a` computes `a - src` and writes the five flags; `a` is a read,
  -- and no register is written.
  | .cmp a b   => "\tcmpq "  ++ renderOperand alloc b ++ ", " ++ regOf alloc a
  | .not_ d    => "\tnotq "  ++ regOf alloc d
  -- BMI1 `ANDN dst, src1, src2` = `dst := ~src1 & src2`; AT&T reverses the operand
  -- order to `andnq %src2, %src1, %dst`.
  | .andn d a b =>
      "\tandnq " ++ regOf alloc b ++ ", " ++ regOf alloc a ++ ", " ++ regOf alloc d
  | .rol d amt => "\trolq "  ++ renderOperand alloc amt ++ ", " ++ regOf alloc d
  | .ror d amt => "\trorq "  ++ renderOperand alloc amt ++ ", " ++ regOf alloc d
  -- BMI2 three-operand forms: AT&T lists the count/shift first, then the source,
  -- then the destination.
  | .rorx d src amt =>
      "\trorxq " ++ renderOperand alloc amt ++ ", " ++ regOf alloc src
        ++ ", " ++ regOf alloc d
  | .shlx d src cnt =>
      "\tshlxq " ++ regOf alloc cnt ++ ", " ++ regOf alloc src ++ ", " ++ regOf alloc d
  | .shrx d src cnt =>
      "\tshrxq " ++ regOf alloc cnt ++ ", " ++ regOf alloc src ++ ", " ++ regOf alloc d
  | .sarx d src cnt =>
      "\tsarxq " ++ regOf alloc cnt ++ ", " ++ regOf alloc src ++ ", " ++ regOf alloc d
  -- Zero extension to 64 bits, by source width: `movzbq`/`movzwq` for the byte and
  -- word sources, `movl %src32, %dst32` for a 32-bit source (writing a 32-bit
  -- destination zeroes the upper half; the SDM has no `movzlq`), and a plain `movq`
  -- for the identity at 64. Any other width has no x86 form, so it renders as a
  -- bracketed sentinel the assembler rejects rather than a wrong instruction.
  | .movzx d sw src =>
      match sw with
      | 8  => "\tmovzbq " ++ gpReg8 (regOf alloc src) ++ ", " ++ regOf alloc d
      | 16 => "\tmovzwq " ++ gpReg16 (regOf alloc src) ++ ", " ++ regOf alloc d
      | 32 => "\tmovl "   ++ gpReg32 (regOf alloc src) ++ ", " ++ gpReg32 (regOf alloc d)
      | 64 => "\tmovq "   ++ regOf alloc src ++ ", " ++ regOf alloc d
      | n  => "\t<UNSUPPORTED-MOVZX-WIDTH:" ++ toString n ++ ">"
  -- Sign extension to 64 bits, by source width: `movsbq`/`movswq`/`movslq`, and a
  -- plain `movq` for the identity at 64. Other widths render as the same sentinel.
  | .movsx d sw src =>
      match sw with
      | 8  => "\tmovsbq " ++ gpReg8 (regOf alloc src) ++ ", " ++ regOf alloc d
      | 16 => "\tmovswq " ++ gpReg16 (regOf alloc src) ++ ", " ++ regOf alloc d
      | 32 => "\tmovslq " ++ gpReg32 (regOf alloc src) ++ ", " ++ regOf alloc d
      | 64 => "\tmovq "   ++ regOf alloc src ++ ", " ++ regOf alloc d
      | n  => "\t<UNSUPPORTED-MOVSX-WIDTH:" ++ toString n ++ ">"
  -- `leaq off(%base, %idx, scale), %dst` computes the address in the AGU and writes
  -- it to `dst`; it performs no memory access.
  | .lea d base idx scale off =>
      "\tleaq " ++ toString off ++ "(" ++ regOf alloc base ++ ", " ++ regOf alloc idx
        ++ ", " ++ toString scale ++ "), " ++ regOf alloc d
  | .or_ d s   => "\torq "   ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .xor_ d s  => "\txorq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .shl d s   => "\tshlq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .shr d s   => "\tshrq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .sar d s   => "\tsarq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .cmove d s  => "\tcmoveq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .cmovne d s => "\tcmovneq " ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .cmovb d s  => "\tcmovbq "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  -- AT&T `mulx src2, dstLo, dstHi`; the implicit src1 is %rdx.
  | .mulx dh dl a b =>
      "\tmulx " ++ renderOperand alloc b ++ ", " ++ regOf alloc dl ++ ", " ++ regOf alloc dh
      ++ "  # src1=%rdx=" ++ renderOperand alloc a
  -- AT&T memory-operand `mulxq off(%base), %dstLo, %dstHi`; the implicit src1 is
  -- %rdx. The second source is read straight from `[base + off]` (s2n's fold of
  -- the multiplicand load into the MULX).
  | .mulxMem dh dl a base off =>
      "\tmulxq " ++ toString off ++ "(" ++ regOf alloc base ++ "), "
      ++ regOf alloc dl ++ ", " ++ regOf alloc dh
      ++ "  # src1=%rdx=" ++ renderOperand alloc a
  | .adcx d s  => "\tadcx "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  | .adox d s  => "\tadox "  ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  -- AT&T memory operand `movq off(%base), %dst` (load) / `movq %src, off(%base)`
  -- (store). A zero offset prints as `(%base)`.
  | .loadMem d base off =>
      "\tmovq " ++ toString off ++ "(" ++ regOf alloc base ++ "), " ++ regOf alloc d
  | .storeMem base off s =>
      "\tmovq " ++ renderOperand alloc s ++ ", " ++ toString off ++ "(" ++ regOf alloc base ++ ")"
  -- AT&T SIB memory operand `movq (%base, %idx, scale), %dst` (gather load) /
  -- `movq %src, (%base, %idx, scale)` (scatter store). `scale` is the byte
  -- stride (1/2/4/8); the static displacement is 0.
  | .loadMemIdx d base idx scale =>
      "\tmovq (" ++ regOf alloc base ++ ", " ++ regOf alloc idx ++ ", "
        ++ toString scale ++ "), " ++ regOf alloc d
  | .storeMemIdx base idx scale s =>
      "\tmovq " ++ renderOperand alloc s ++ ", (" ++ regOf alloc base ++ ", "
        ++ regOf alloc idx ++ ", " ++ toString scale ++ ")"
  -- AT&T RIP-relative load-effective-address of a `.rodata` symbol:
  -- `leaq sym(%rip), %dst`. `sym` is emitted verbatim (it is an assembler label,
  -- not a register); `dst` is resolved through the allocator like any GP base.
  | .loadSym d sym =>
      "\tleaq " ++ sym ++ "(%rip), " ++ regOf alloc d
  | .inc d     => "\tincq "  ++ regOf alloc d
  | .dec d     => "\tdecq "  ++ regOf alloc d
  | .clc       => "\tclc"
  | .stc       => "\tstc"
  | .xchg a b  => "\txchgq " ++ regOf alloc b ++ ", " ++ regOf alloc a
  -- three-operand `imulq $imm, %src, %dst` = `dst := src * imm`.
  | .imulri d s imm =>
      "\timulq $" ++ toString imm ++ ", " ++ regOf alloc s ++ ", " ++ regOf alloc d
  -- One-operand widening multiplies: the hardware reads `%rax` and writes `%rdx:%rax`;
  -- the destinations the model names are recorded in a comment, as `mulx` records its
  -- implicit source.
  | .mul dh dl s =>
      "\tmulq " ++ regOf alloc s
      ++ "  # hi=%rdx=" ++ regOf alloc dh ++ " lo=%rax=" ++ regOf alloc dl
  | .imulWide dh dl s =>
      "\timulq " ++ regOf alloc s
      ++ "  # hi=%rdx=" ++ regOf alloc dh ++ " lo=%rax=" ++ regOf alloc dl
  -- AT&T `shldq count, %src, %dst`; a register count is `%cl`.
  | .shld d s amt =>
      "\tshldq " ++ renderCount alloc amt ++ ", " ++ regOf alloc s ++ ", " ++ regOf alloc d
  | .shrd d s amt =>
      "\tshrdq " ++ renderCount alloc amt ++ ", " ++ regOf alloc s ++ ", " ++ regOf alloc d
  | .rcl d amt => "\trclq "  ++ renderCount alloc amt ++ ", " ++ regOf alloc d
  | .rcr d amt => "\trcrq "  ++ renderCount alloc amt ++ ", " ++ regOf alloc d
  | .cmovcc c d s =>
      "\tcmov" ++ condSuffix c ++ "q " ++ renderOperand alloc s ++ ", " ++ regOf alloc d
  -- `SETcc` writes the low byte only; the upper bits of the register keep their
  -- values (`setcc` is modeled under `MSB_MERGE`), so no zero extension follows.
  | .setcc c d => "\tset" ++ condSuffix c ++ " " ++ gpReg8 (regOf alloc d)
  -- `TEST` at an explicit size: the `b`/`w`/`l`/`q` suffix and the subregister names
  -- of that size.
  | .testN sz a b =>
      let sfx := match sz with
        | 8 => "b" | 16 => "w" | 32 => "l" | 64 => "q"
        | n => "<UNSUPPORTED-TEST-WIDTH:" ++ toString n ++ ">"
      "\ttest" ++ sfx ++ " " ++ renderOperandN sz alloc b ++ ", "
        ++ renderOperandN sz alloc (.reg a)
  | .bt a b    => "\tbtq "   ++ renderOperand alloc b ++ ", " ++ regOf alloc a
  | .btr d b   => "\tbtrq "  ++ renderOperand alloc b ++ ", " ++ regOf alloc d
  | .bts d b   => "\tbtsq "  ++ renderOperand alloc b ++ ", " ++ regOf alloc d
  -- AT&T memory operands `off(%base)` for the memory kinds of `ADD`, `ADCX`, `ADOX`
  -- and `IMUL`: `addq off(%base), %dst`, `addq %src, off(%base)`,
  -- `imulq $imm, off(%base), %dst`.
  | .addMem d base off =>
      "\taddq " ++ toString off ++ "(" ++ regOf alloc base ++ "), " ++ regOf alloc d
  | .addToMem base off s =>
      "\taddq " ++ renderOperand alloc s ++ ", " ++ toString off ++ "(" ++ regOf alloc base ++ ")"
  | .adcxMem d base off =>
      "\tadcxq " ++ toString off ++ "(" ++ regOf alloc base ++ "), " ++ regOf alloc d
  | .adoxMem d base off =>
      "\tadoxq " ++ toString off ++ "(" ++ regOf alloc base ++ "), " ++ regOf alloc d
  | .imulMem d base off =>
      "\timulq " ++ toString off ++ "(" ++ regOf alloc base ++ "), " ++ regOf alloc d
  | .imulriMem d base off imm =>
      "\timulq $" ++ toString imm ++ ", " ++ toString off ++ "(" ++ regOf alloc base ++ "), "
        ++ regOf alloc d
  | .cmpMem a base off =>
      "\tcmpq " ++ toString off ++ "(" ++ regOf alloc base ++ "), " ++ regOf alloc a
  | .cmovccMem c d base off =>
      "\tcmov" ++ condSuffix c ++ "q " ++ toString off ++ "(" ++ regOf alloc base ++ "), "
        ++ regOf alloc d
  | .aluMem op d base off =>
      "\t" ++ (match op with | .sub => "subq" | .and_ => "andq" | .or_ => "orq" | .xor_ => "xorq")
        ++ " " ++ toString off ++ "(" ++ regOf alloc base ++ "), " ++ regOf alloc d
  -- BMI1 `ANDN dst, src1, m64`; AT&T lists the memory source, `src1`, then the destination.
  | .andnMem d a base off =>
      "\tandnq " ++ toString off ++ "(" ++ regOf alloc base ++ "), " ++ regOf alloc a ++ ", "
        ++ regOf alloc d
  -- BMI2 `BZHI dst, src, idx`; AT&T lists the index, the source, then the destination.
  | .bzhi d src idx =>
      "\tbzhiq " ++ regOf alloc idx ++ ", " ++ regOf alloc src ++ ", " ++ regOf alloc d

/-- Print a whole block's instruction lines (one per `JInstr`). -/
def renderBlockBody {w : Nat} (alloc : GpAlloc) (block : List (JInstr w)) : List String :=
  block.map (renderJInstr alloc)

/-! ## 2b. Spill-aware rendering — consume `SpillingRegAlloc.Slot` decisions

The first-fit `allocGp` / `regOf` path above is non-spilling: on a body with more
distinct names than the GP pool it leaves the overflow names unmapped and `regOf`
emits the `<UNALLOCATED:n>` sentinel. `SpillingRegAlloc.spillAlloc` instead produces,
per name, a `Slot` decision — either a pool register (`resident`) or a frame byte
offset (`spilled`). This section is the **additive** renderer that consumes those
decisions; the `allocGp`/`regOf` path above is left untouched (every other kernel's
emit + its `*Asm_shape`/`*_length` theorems depend on it).

The renderer never sees the `Slot` type directly (to keep `AsmPrinter` free of the
`Optimizer` dependency): the caller passes a precomputed **resident allocation**
(`name → "%rN"` for the names that stayed in registers, an ordinary `GpAlloc`) plus,
per instruction, the **spilled-name reload/store data** as it appears in the
spill-materialised block. Concretely the caller renders the *original* block one
instruction at a time, and for each instruction supplies the (≤ k) spilled names it
touches and their frame offsets; this renderer assigns each spilled name a distinct
reserved **working register**, emits the reload(s) before the instruction, the
instruction with operands resolved (resident → pool reg, spilled → working reg), and
the store-back(s) after a spilled destination.

For the X25519 application the per-instruction spilled-name footprint is at most two
(`SpillingRegAlloc.workRegs` reserves exactly two), so two working registers always
suffice; the renderer is parametric in the working-register list and the frame base. -/

/-- The reserved working registers a spilled operand is reloaded into. Mirrors
    `SpillingRegAlloc.workRegs`; kept here so `AsmPrinter` has no `Optimizer`
    dependency. -/
def spillWorkRegs : List String := ["%r14", "%r15"]

/-- A per-instruction spill view: the resident allocation (`name → "%rN"`), the frame
    base register name (e.g. `"fp"`), and the spilled names this instruction
    reads / writes with their frame byte offsets. The caller derives this from the
    `spillAlloc` decisions; the renderer turns it into reload + instruction + store
    lines. -/
structure SpillView where
  /-- name → "%rN" for register-resident names (the pool registers). -/
  resident : GpAlloc
  /-- the frame base register name (mapped to its `%rN` via `resident`). -/
  frameBase : String
  /-- spilled names read by this instruction, with their frame byte offsets. -/
  spilledReads : List (String × Int)
  /-- spilled names written by this instruction, with their frame byte offsets. -/
  spilledWrites : List (String × Int)

/-- The distinct spilled names this instruction touches (reads ∪ writes), in
    read-then-write first-seen order. A spilled name that is both read and written
    (a two-address destination) appears once. -/
def SpillView.touchedSpills (v : SpillView) : List String :=
  (v.spilledReads.map Prod.fst ++ v.spilledWrites.map Prod.fst).foldl
    (fun acc n => if acc.contains n then acc else acc ++ [n]) []

/-- Assign each touched spilled name a distinct working register (first-fit over
    `spillWorkRegs`). The X25519 body touches ≤ 2 spills per instruction, so the two
    reserved working registers always suffice; if a body ever exceeds the working set
    a name falls off the end and `regOf` of the resulting (resident ∪ work) alloc
    yields the `<UNALLOCATED>` sentinel — the same explicit-failure discipline as the
    non-spilling path, never a silent alias. The assignment is
    `GenericRegAlloc.firstFitScan`, equal to `touchedSpills.zip spillWorkRegs`
    (`SpillView.workAlloc_eq_zip`). -/
def SpillView.workAlloc (v : SpillView) : GpAlloc :=
  CatCrypt.Crypto.Optimizer.GenericRegAlloc.firstFitScan spillWorkRegs v.touchedSpills

/-- The working-register assignment pairs the touched spills with `spillWorkRegs` in
    order. -/
theorem SpillView.workAlloc_eq_zip (v : SpillView) :
    v.workAlloc = v.touchedSpills.zip spillWorkRegs :=
  CatCrypt.Crypto.Optimizer.GenericRegAlloc.firstFitScan_eq_zip _ _

/-- The full per-instruction allocation the spill renderer uses: resident names map
    to their pool register, the (≤ 2) spilled names this instruction touches map to
    distinct working registers. -/
def SpillView.alloc (v : SpillView) : GpAlloc :=
  v.resident ++ v.workAlloc

/-- The reserved register that `MULX`/`MULXMEM` read as their implicit first source
    (`src1`). On x86 this is always `%rdx`. The per-program-point renderer
    materialises a `mulx`'s `src1` operand into `%rdx` immediately before the
    instruction, so the allocator must **reserve** `%rdx` (never hand it to a
    register-resident value) — see `X25519MonoLadderMem2Reg.framePinsRA`. -/
def mulxSrc1Reg : String := "%rdx"

/-- The implicit-`%rdx` materialisation line(s) for a `mulx`/`mulxMem`: move the
    instruction's first source (resolved to its physical register by `alloc`) into
    `%rdx`. For non-`mulx` instructions this is empty.

    The model's `JInstr.mulx dh dl a b` reads `a` **by name** (`a.eval s`), so the
    gas realisation must put `a`'s value into the hardware `%rdx` that the `mulx`
    encoding reads. The bare `renderJInstr` only *comments* `# src1=%rdx=a`,
    assuming `a` is pinned to `%rdx`; spilling RA gives no such pin, so the
    materialisation must be explicit. An immediate `a` needs no move (it
    cannot be a `mulx` src1 here).

    **Pin-aware elision.** When the pin-aware allocator already binds the
    multiplier `a` to `%rdx` (`SpillingRegAlloc.spillAllocPinned`), `regOf alloc r`
    is already `mulxSrc1Reg` and the move would be a redundant `movq %rdx, %rdx`.
    We elide it: `a`'s value is already live in `%rdx` (set once when the multiplier
    name was loaded), exactly mirroring s2n's MULX schedule. This avoids a per-
    multiply `movq → %rdx` on each of the 193 multiplies. The
    elision is semantics-preserving: a `movq %rdx, %rdx` writes `%rdx` the value it
    already holds, so dropping it leaves the hardware `mulx` reading the same src1. -/
def mulxRdxSetup (alloc : GpAlloc) : JInstr 64 → List String
  | .mulx _ _ a _ =>
      match a with
      | .reg r => let s := regOf alloc r; if s == mulxSrc1Reg then [] else ["\tmovq " ++ s ++ ", " ++ mulxSrc1Reg]
      | .imm _ => []
  | .mulxMem _ _ a _ _ =>
      match a with
      | .reg r => let s := regOf alloc r; if s == mulxSrc1Reg then [] else ["\tmovq " ++ s ++ ", " ++ mulxSrc1Reg]
      | .imm _ => []
  | _ => []

/-- Render one instruction under its `SpillView`, **per program point**:

    1. reload each spilled read into its working register (`movq off(%fp), %work`);
    2. for a `mulx`/`mulxMem`, materialise the `src1` operand into `%rdx`
       (`mulxRdxSetup`) — the implicit-source register the hardware `mulx` reads;
    3. emit the instruction with operands resolved by `SpillView.alloc` (resident →
       pool reg, spilled → working reg, `mulx` src1 → `%rdx`);
    4. store each spilled write back to its frame cell (`movq %work, off(%fp)`).

    Resident-only non-`mulx` instructions reduce to a single line identical to the
    non-spilling `renderJInstr`. Because the caller reserves `%rdx` from the resident
    pool, neither the reload nor the `%rdx` setup can clobber a simultaneously-live
    resident value — this is the per-program-point realisation that closes the
    global-alias defect. -/
def renderJInstrSpilled (v : SpillView) (i : JInstr 64) : List String :=
  let alloc := v.alloc
  let fpReg := regOf v.resident v.frameBase
  let reloads := v.spilledReads.map (fun (n, off) =>
    "\tmovq " ++ toString off ++ "(" ++ fpReg ++ "), " ++ regOf alloc n)
  let stores := v.spilledWrites.map (fun (n, off) =>
    "\tmovq " ++ regOf alloc n ++ ", " ++ toString off ++ "(" ++ fpReg ++ ")")
  reloads ++ mulxRdxSetup alloc i ++ (renderJInstr alloc i :: stores)

/-! ## 3. Leaf-function wrapper (trusted ABI scaffolding)

`renderLeafFn` wraps a rendered straight-line body in a minimal System-V leaf
function: a label + `.globl`, the body lines, and a `ret`. The argument-loading
and result-storing glue is supplied by the caller as `prologue`/`epilogue` line
lists, and is **trusted scaffolding outside the verified body** (the verified
claim is about the body's `runBlock`/`evalInstr` transform, not the ABI glue). -/

/-- Emit a `.s` text for a leaf function `name` whose body is `bodyLines`,
    framed by `prologue` (arg load) and `epilogue` (result store + `ret`). -/
def renderLeafFn (name : String) (prologue bodyLines epilogue : List String) : String :=
  let header :=
    [ "\t.text", "\t.globl " ++ name, "\t.type " ++ name ++ ", @function", name ++ ":" ]
  -- A non-executable-stack note (quiets the GNU linker on the emitted object).
  let footer := [ "\t.section .note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n" (header ++ prologue ++ bodyLines ++ epilogue ++ footer) ++ "\n"

/-! ## 4. The System V AMD64 ABI layer

A hand-written prologue/epilogue for the per-kernel emitters
(`Fe25519MulKernel.feMulAsm`, `BignumMontMulKernel.mul48Asm`, …), an unconditional
`pushq` of every callee-saved register plus a manual `movq %rdx, <reg>` to free
`%rdx` for `MULX`, is both **over-conservative** (it saves registers the body
never touches) and **uncomputed** (no check that the saves match what the
allocation clobbers, no stack-alignment discipline). This section is the owned
backend's principled System V AMD64 ABI layer: given a function *signature* (the
ordered argument names + their class) and a register allocation, it computes the
argument-register moves, the *minimal* callee-saved save/restore set (exactly the
callee-saved registers the allocation uses), and the 16-byte stack-alignment pad,
and emits the framed leaf with `renderLeafFn`.

The ABI glue remains trusted scaffolding *outside* the `runBlock`-verified body —
but it is **derived from the allocation by a single function**, not copied by
hand per kernel, so the save set provably covers exactly the clobbered
callee-saved registers and the alignment is computed, not assumed.

### The convention (System V AMD64, §3.2)

* **Integer/pointer arguments** go in `%rdi, %rsi, %rdx, %rcx, %r8, %r9` (then the
  stack); the integer return is `%rax` (`:rdx` for the 128-bit pair).
* **Callee-saved**: `%rbx, %rbp, %r12, %r13, %r14, %r15` (and `%rsp`). A function
  that writes any of these must restore it before returning.
* **Caller-saved (scratch)**: `%rax, %rcx, %rdx, %rsi, %rdi, %r8–%r11` — free to
  clobber.
* **Stack alignment & the red zone**: at the point of a `call`, `%rsp` must be
  16-byte aligned; on function entry (just after the return address is pushed)
  `%rsp ≡ 8 (mod 16)`. The 128 bytes below `%rsp` (`%rsp-128 .. %rsp-1`) are the
  **red zone** (§3.2.2): a leaf function — one that makes no `call` — may use them
  as scratch *without* moving `%rsp`, because no signal handler or callee will
  clobber that region. Our kernels are leaves, so instead of a
  `pushq … ; subq $pad` frame we save each used callee-saved register with a
  single `movq %reg, -8*(i+1)(%rsp)` into the red zone and reload it on exit. This
  leaves `%rsp` untouched (so it stays the entry-aligned `≡ 8 (mod 16)`, fully
  ABI-conformant and re-callable), saves only the registers the body clobbers,
  and is leaner than both a `pushq`/`popq`+pad scaffold and jasmin's
  `lea/and` realign idiom (the prologue overhead of `bignum_mul_4_8`).
  (A kernel containing a `call` is not a leaf and needs an `%rsp`-moving frame;
  the word kernels here never call.) -/

/-- The System V AMD64 integer/pointer argument registers, in order. The *i*-th
    integer/pointer argument is passed in `intArgRegs[i]` (arguments beyond the
    sixth go on the stack — out of scope for the leaf kernels). -/
def intArgRegs : List String := ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"]

/-- The System V AMD64 integer return register (the second-half pair register for
    a 128-bit return is `%rdx`). -/
def intRetReg : String := "%rax"

/-- The callee-saved general-purpose registers under System V AMD64: a function
    that clobbers any of these must save/restore it. `%rsp` is handled by the
    push/pop accounting itself; `%rbp` is included (we do not reserve it as a frame
    pointer — the kernels are frame-pointer-omitting leaves). -/
def calleeSavedRegs : List String :=
  ["%rbx", "%rbp", "%r12", "%r13", "%r14", "%r15"]

/-- The callee-saved registers a given allocation actually binds, in
    `calleeSavedRegs` order. These are exactly the registers the emitted body may
    write, so exactly these must be saved/restored. -/
def usedCalleeSaved (alloc : GpAlloc) : List String :=
  let bound := alloc.map Prod.snd
  calleeSavedRegs.filter (fun r => bound.contains r)

/-- A System V argument's class for the leaf-ABI glue. We only need the integer/
    pointer class for the word kernels; the constructor is kept open for a future
    `sse` (xmm) class without breaking callers. -/
inductive ArgClass where
  /-- An integer or pointer argument: passed in the next `intArgRegs` slot. -/
  | intPtr : ArgClass
deriving DecidableEq, Repr

/-- A function argument: the SSA/source name the body refers to it by, and its ABI
    class. The *i*-th `intPtr` argument arrives in `intArgRegs[i]`. -/
structure AbiArg where
  /-- The source name the body refers to this argument by. -/
  name : String
  /-- The argument's ABI class (currently always `intPtr`). -/
  cls  : ArgClass
deriving Repr

/-- The home register the *i*-th integer/pointer argument arrives in. Out-of-range
    indices (a 7th+ integer argument, stack-passed) yield `none`. -/
def intArgHome (i : Nat) : Option String := intArgRegs[i]?

/-- The argument-marshalling moves: for each `intPtr` argument, if the allocation
    binds its name to a register **different** from its ABI home register, emit a
    `movq %home, %dst` that copies the incoming value into place. When the name is
    already allocated to its home register (the common pointer-argument case, e.g.
    `z`→`%rdi`) no move is emitted. When a name is allocated to a *later* argument's
    home this is still a single straight move because the allocator pins arguments
    to distinct registers (no overlap cycle); the canonical use is the `MULX`
    multiplier living in `%rdx` while the third pointer argument (also `%rdx` on
    entry) is moved out to a free register — the computed form of a hand-written
    `movq %rdx, <yreg>`. -/
def argMarshalMoves (alloc : GpAlloc) (args : List AbiArg) : List String :=
  let indexed := args.zipIdx
  indexed.filterMap (fun (a, i) =>
    match a.cls, intArgHome i with
    | .intPtr, some home =>
        let dst := regOf alloc a.name
        if dst == home then none
        else some ("\tmovq " ++ home ++ ", " ++ dst)
    | _, none => none)

/-- The byte offset (below `%rsp`) of the *i*-th saved callee-saved register's
    red-zone slot. Slot `i` lives at `-8*(i+1)(%rsp)`; the first save is at
    `-8(%rsp)`, the second at `-16(%rsp)`, … The System V AMD64 red zone is the
    128 bytes below `%rsp` (`%rsp-128 .. %rsp-1`) that a **leaf** function may use
    as scratch without adjusting `%rsp`: no signal handler or called function
    touches it (§3.2.2). At most six callee-saved registers need saving (48 bytes
    of the 128), so the slots never escape the red zone. -/
def redZoneSlotOff (i : Nat) : Int := -8 * (Int.ofNat i + 1)

/-- The callee-saved save sequence — the **leaf red-zone idiom** (matching the
    light `lea/and`-style frame jasmin emits, but leaner: no `%rsp` adjustment at
    all). For each used callee-saved register we emit a single
    `movq %reg, -8*(i+1)(%rsp)` storing it into its red-zone slot, in
    `calleeSavedRegs` order. No `pushq`, no `subq`, no alignment pad: because the
    kernels are leaves (they make no `call`), `%rsp` stays 16-byte aligned on
    entry, the red zone is never clobbered, and the entire `push/pop/sub` scaffold
    collapses to one `movq` per saved register. The restore sequence
    (`abiRestore`) is its exact mirror — the same slot offsets reloaded.

    This is the same red-zone save discipline the VIR Jasmin export already uses
    for the callee-saved GPRs (`JasminLprogExport.abiSave*`); it avoids the
    heavier `pushq … ; subq $8` prologue, which costs the owned `bignum_mul_4_8`
    ~6% over jasmin. -/
def abiSave (alloc : GpAlloc) : List String :=
  (usedCalleeSaved alloc).zipIdx.map (fun (r, i) =>
    "\tmovq " ++ r ++ ", " ++ toString (redZoneSlotOff i) ++ "(%rsp)")

/-- The callee-saved restore sequence: the mirror of `abiSave` — reload each saved
    register from its red-zone slot `movq -8*(i+1)(%rsp), %reg`, in
    `calleeSavedRegs` order. No `%rsp` movement (no `addq`/`popq`), since the saves
    never moved `%rsp`. -/
def abiRestore (alloc : GpAlloc) : List String :=
  (usedCalleeSaved alloc).zipIdx.map (fun (r, i) =>
    "\tmovq " ++ toString (redZoneSlotOff i) ++ "(%rsp), " ++ r)

/-- Render a full System V AMD64 leaf function from a *signature* and an
    allocation, computing the ABI glue rather than hand-writing it:

    * **prologue** = save the (minimal) used callee-saved set into the leaf red
      zone (`abiSave`, one `movq` per register, no `%rsp` adjustment), then the
      argument-marshalling moves (`argMarshalMoves`);
    * **body** = the caller-supplied `bodyLines` (the `runBlock`-verified straight
      line, one line per `JInstr`);
    * **epilogue** = the caller-supplied `resultStores` (the result-writing moves,
      part of the verified body's effect on memory), then restore the saved set
      (`abiRestore`), then `ret`.

    The save set is **exactly** the callee-saved registers the allocation binds, so
    the function clobbers nothing it does not restore; the order of save vs.
    arg-marshal matters (saves first, so a marshal target that happens to be a
    callee-saved register is already preserved). This is the single ABI definition
    the kernels share — no per-kernel hand-written `pushq`/`popq`/`movq %rdx`. -/
def renderSysVLeafFn (name : String) (alloc : GpAlloc) (args : List AbiArg)
    (bodyLines resultStores : List String) : String :=
  renderLeafFn name
    (abiSave alloc ++ argMarshalMoves alloc args)
    bodyLines
    (resultStores ++ abiRestore alloc ++ ["\tret"])

end CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
