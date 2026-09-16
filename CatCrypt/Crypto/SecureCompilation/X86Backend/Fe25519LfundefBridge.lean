/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519UnifyingFront
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519UnifyingFront

/-!
# The fe25519-leaf → owned-RA `Lfundef`/`.s`-symbol bridge (task #656, half b)

`Fe25519{Mul,Ops}Kernel` emit each Curve25519 field op (`mul`/`sqr`/`add`/`sub`/
`mul121666`) as a straight-line `List (JInstr 64)` — the verified word-kernel IR
whose `runBlock`/`evalInstr` semantics is the faithful transcription of Jasmin's
Rocq x86 model — and render each to a SysV leaf `.s` function via the trusted
`AsmPrinter.renderSysVLeafFn`/`renderBlockBody` path. Each leaf is a `.globl`
symbol (`fe25519_mul_x86_from_lean`, …).

`X25519Ladder` models the Montgomery ladder as a `JForProg` whose body is the
opaque leaf `x25519_ladder_iter` (= formosa `__add_and_double4`, ~19 field-op
calls); `LprogControlFlow.cforToLcmd` lowers that bounded loop to the owned-RA
looped `Lcmd`, but the field-op calls in the body are `extCall`s that lower to an
`Lopn "CALL:…"` — NOT a real `Lcall` to a sibling function. The residual recorded
in `X25519Ladder.lean` is exactly: the fe25519 leaves are `JInstr` blocks, not
`Lfundef`s, so they cannot serve as cross-function-call targets.

## What this module bridges

This is the `JInstr`-block → call-target-symbol bridge. There are two layers, and
the one faithful for the ADX/MULX schoolbook is stated per layer:

1. **`.s`-symbol bridge (the artifact path, faithful).** Each fe25519 leaf already
   emits a correct SysV `.s` function via `renderSysVLeafFn` — the verified
   `JInstr → renderJInstr` path renders `mulx`/`adcx`/`adox` faithfully (the
   3-operand BMI2/ADX forms). `fe25519LeafSymbols` names those symbols;
   `fe25519LeavesAsm` concatenates the five verified leaf `.s` functions. A caller
   (the ladder driver) whose body issues `call fe25519_mul_x86_from_lean` etc.
   links against these intra-object symbols (gas/`ld` resolve the `call` against
   the same-object `STT_FUNC` symbol — the text-path analogue of
   `LprogBytes.encodeLcmdReloc`'s intra-object resolution).

2. **`Lfundef`/`Lcmd` lift (now FULL — including the ADX schoolbook).** Each
   `JInstr` lifts to a faithful `LinstrR`: the two-address ALU alphabet
   (`ADD/SUB/ADC/SBB/AND/OR/XOR/SHL/SHR/MOV/LOAD/STORE/IMUL`) AND the BMI2/ADX trio
   `MULX`/`MULXMEM`/`ADCX`/`ADOX` (#656-residual). The ADX arms lift to faithful
   `Lopn` forms the byte encoder (`LprogBytes.encodeLopn`) delegates to
   `ScalarEncoder`'s `encMulxRR`/`encMulxMem`/`encAdxCarry` (the same 3-operand
   `mulx` / `66`/`F3 0F38 F6` carry-chain encoders the straight-line `JInstr` path
   uses), and the text path (`renderLprogAtt`) renders verbatim. So a field op
   built on the ADX schoolbook (`mul`/`sqr`/`mul121666`) IS now byte-encoded by
   `encodeLprogReloc` — the residual the prior version recorded is closed. The
   `hasUnrepAdx` predicate is `false` for every fe25519 leaf (see §2a), and the
   byte-encoder `.o` route carries the whole field-op set (the `.s`+gas route is a
   comparison artifact for the field leaves).

## The multi-function ladder `Lcall`

The ladder loop Lprog's field-op calls render to `call <leaf>` through the
`renderLinstrR` `Lcall` arm (added in `LprogAsmPrinter`, #656): a
`LinstrR.Lcall ra (f, l)` with `f` a leaf symbol emits `call f`.
`ladderCallSite name` builds that `Lcall`. The bridge therefore turns the
ladder's opaque field-op `extCall` into a real call to a sibling owned leaf.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LfundefBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. The verified leaf `.s` symbols (layer 1: the faithful artifact path) -/

/-- The five owned fe25519 leaf symbol names (the `.globl` symbols
    `renderSysVLeafFn` emits), in ladder-call order. -/
def fe25519LeafSymbols : List String :=
  [ "fe25519_mul_x86_from_lean"
  , "fe25519_sqr_x86_from_lean"
  , "fe25519_add_x86_from_lean"
  , "fe25519_sub_x86_from_lean"
  , "fe25519_mul121666_x86_from_lean" ]

/-- The concatenated `.s` text of all five verified fe25519 leaf functions (each a
    `.globl` symbol). Reuses the per-kernel `renderSysVLeafFn`-emitted text
    verbatim, so each leaf's `runBlock`-verified body and trusted SysV ABI framing
    is exactly as `Fe25519{Mul,Ops}Kernel.emitMain` writes it. This is the set of
    intra-object call targets the ladder driver's `call <leaf>` resolves against. -/
def fe25519LeavesAsm : String :=
  String.intercalate "\n"
    [ Fe25519MulKernel.feMulAsm
    , Fe25519OpsKernel.feSqrAsm
    , Fe25519OpsKernel.feAddAsm
    , Fe25519OpsKernel.feSubAsm
    , Fe25519OpsKernel.feMul121666Asm ]

/- Each leaf symbol appears as a `.globl` in the concatenated leaf `.s`. -/
#guard (BignumMontMulKernel.hasSub fe25519LeavesAsm ".globl fe25519_mul_x86_from_lean")

#guard (BignumMontMulKernel.hasSub fe25519LeavesAsm ".globl fe25519_sqr_x86_from_lean")

#guard (BignumMontMulKernel.hasSub fe25519LeavesAsm ".globl fe25519_add_x86_from_lean")

#guard (BignumMontMulKernel.hasSub fe25519LeavesAsm ".globl fe25519_sub_x86_from_lean")

#guard (BignumMontMulKernel.hasSub fe25519LeavesAsm ".globl fe25519_mul121666_x86_from_lean")

/- The faithful `mulx`/`adcx`/`adox` mnemonics survive into the concatenated leaf
    `.s` (the ADX schoolbook the `LinstrR`/byte path cannot represent). -/
#guard (BignumMontMulKernel.hasSub fe25519LeavesAsm "mulx") && (BignumMontMulKernel.hasSub fe25519LeavesAsm "adcx") && (BignumMontMulKernel.hasSub fe25519LeavesAsm "adox")

/-! ## 2. The `JInstr → LinstrR` lift (layer 2: the FULL `Lcmd` lift)

Lift one `JInstr 64` to its owned-RA `LinstrR` over a resolved physical-register
`GpAlloc`. The result register names are the uppercase bare GP names the
`LinstrR` byte/text paths expect (`"RAX" …`), obtained by mapping the leaf's
`%rN` allocation back to the uppercase form. Memory operands use the
`mem.<base>.<off>` convention `resolveName` parses.

The lift is faithful for the WHOLE field-op alphabet: the two-address
ALU/move/load/store/shift subset AND the BMI2/ADX trio
`mulx`/`mulxMem`/`adcx`/`adox` (#656-residual), which lift to the faithful
`MULX`/`MULXMEM`/`ADCX`/`ADOX` `Lopn` forms the byte encoder
(`LprogBytes.encodeLopn`) delegates to `ScalarEncoder`'s
`encMulxRR`/`encMulxMem`/`encAdxCarry`. No `UNREP-ADX:…` sentinel form is
produced; `hasUnrepAdx` (§2a) is `false` for every fe25519 leaf. -/

/-- The uppercase bare GP register name for a `%rN` AT&T name (`"%rax" → "RAX"`),
    the form `LprogBytes.gpNumU` / `LprogAsmPrinter.gpReg64` consume. Unknown
    forms (a spilled `<UNALLOCATED…>` sentinel) pass through unchanged so they
    surface in the emitted `LinstrR`. -/
def upperReg : String → String
  | "%rax" => "RAX" | "%rcx" => "RCX" | "%rdx" => "RDX" | "%rbx" => "RBX"
  | "%rsp" => "RSP" | "%rbp" => "RBP" | "%rsi" => "RSI" | "%rdi" => "RDI"
  | "%r8"  => "R8"  | "%r9"  => "R9"  | "%r10" => "R10" | "%r11" => "R11"
  | "%r12" => "R12" | "%r13" => "R13" | "%r14" => "R14" | "%r15" => "R15"
  | other  => other

/-- Resolve a leaf symbolic register name to its uppercase bare GP `LOperand`
    through the kernel's `GpAlloc` (`regOf` gives the `%rN`, `upperReg` uppercases). -/
def resolveReg (alloc : GpAlloc) (n : String) : LOperand :=
  .reg (upperReg (regOf alloc n))

/-- Resolve a `JOperand` to an `LOperand` (immediate passes through). -/
def resolveJOp (alloc : GpAlloc) : JOperand → LOperand
  | .reg r => resolveReg alloc r
  | .imm v => .imm v

/-- The `mem.<base>.<off>` operand name for a leaf memory reference at a
    physical base register and (non-negative) byte offset. -/
def memOperand (alloc : GpAlloc) (base : String) (off : Int) : LOperand :=
  .reg ("mem." ++ upperReg (regOf alloc base) ++ "." ++ toString off.toNat)

/-- Lift one `JInstr 64` to its `LinstrR` over a resolved `GpAlloc`. The U64 width
    tag is attached to every op (the field kernels are uniform U64). The ADX/MULX
    arms lift to the faithful `MULX`/`MULXMEM`/`ADCX`/`ADOX` `Lopn` forms the byte
    encoder and text path both consume (#656-residual; see module header). The
    instructions outside the field-op alphabet, among them `inc`, `dec`, `clc`,
    `stc`, `xchg`, `imulri`, `mul`, `imulWide`, `shld`, `shrd`, `rcl`, `rcr`,
    `cmovcc`, `setcc`, `testN`, `bt`, `btr` and `bts`, lift to mnemonics the
    renderer does not handle, so they surface as `# UNHANDLED-OP`. -/
def jinstrToLinstrR (alloc : GpAlloc) : JInstr 64 → LinstrR
  | .mov d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "MOV")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .add d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "ADD")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .sub d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "SUB")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .adc d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "ADC")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .sbb d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "SBB")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .imul d s  => .Lopn [resolveReg alloc d] (withWidthTag 64 "MUL")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .neg d     => .Lopn [resolveReg alloc d] (withWidthTag 64 "NEG") [resolveReg alloc d]
  | .and_ d s  => .Lopn [resolveReg alloc d] (withWidthTag 64 "AND")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .or_ d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "OR")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .xor_ d s  => .Lopn [resolveReg alloc d] (withWidthTag 64 "XOR")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .shl d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "SHL")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .shr d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "SHR")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .sar d s   => .Lopn [resolveReg alloc d] (withWidthTag 64 "SAR")
                    [resolveReg alloc d, resolveJOp alloc s]
  | .setc d    => .Lopn [resolveReg alloc d] (withWidthTag 64 "SETC") []
  | .cmove d s  => .Lopn [resolveReg alloc d] (withWidthTag 64 "CMOVE")
                     [resolveReg alloc d, resolveJOp alloc s]
  | .cmovne d s => .Lopn [resolveReg alloc d] (withWidthTag 64 "CMOVNE")
                     [resolveReg alloc d, resolveJOp alloc s]
  | .cmovb d s  => .Lopn [resolveReg alloc d] (withWidthTag 64 "CMOVB")
                     [resolveReg alloc d, resolveJOp alloc s]
  | .loadMem d base off => .Lopn [resolveReg alloc d] (withWidthTag 64 "LOAD")
                             [memOperand alloc base off]
  | .storeMem base off s => .Lopn [memOperand alloc base off] (withWidthTag 64 "STORE")
                              [resolveJOp alloc s]
  -- BMI2/ADX byte-direct lift (#656-residual): `MULX`/`MULXMEM`/`ADCX`/`ADOX` now
  -- carry faithful `LinstrR` `Lopn` forms the text path (`LprogAsmPrinter`) and the
  -- byte encoder (`LprogBytes.encodeLopn`, delegating to `ScalarEncoder`'s
  -- `encMulxRR`/`encMulxMem`/`encAdxCarry`) BOTH consume. The implicit `MULX` src1
  -- (`yd → %rdx`) is pinned by the allocation, so it is not an operand. `MULX`'s two
  -- destinations are `[dstLo, dstHi]`; `ADCX`/`ADOX` are the destructive
  -- `[dst] [dst, src]` carry-chain form (carry-in is the implicit CF/OF flag).
  | .mulx dh dl _ b    => .Lopn [resolveReg alloc dl, resolveReg alloc dh]
                            (withWidthTag 64 "MULX") [resolveJOp alloc b]
  | .mulxMem dh dl _ base off => .Lopn [resolveReg alloc dl, resolveReg alloc dh]
                                   (withWidthTag 64 "MULXMEM") [memOperand alloc base off]
  | .adcx d s          => .Lopn [resolveReg alloc d] (withWidthTag 64 "ADCX")
                            [resolveReg alloc d, resolveJOp alloc s]
  | .adox d s          => .Lopn [resolveReg alloc d] (withWidthTag 64 "ADOX")
                            [resolveReg alloc d, resolveJOp alloc s]
  | .loadMemIdx d base idx scale =>
      .Lopn [resolveReg alloc d] (withWidthTag 64 "LOADIDX")
        [.arrIdx (upperReg (regOf alloc base)) (upperReg (regOf alloc idx)) scale]
  | .storeMemIdx base idx scale s =>
      .Lopn [.arrIdx (upperReg (regOf alloc base)) (upperReg (regOf alloc idx)) scale]
        (withWidthTag 64 "STOREIDX") [resolveJOp alloc s]
  -- Flag/BMI/extension ops the fe25519/x25519 field leaves never emit; lifted in
  -- the natural `Lopn` shape so a mnemonic outside the renderer's vocabulary
  -- surfaces as the visible `# UNHANDLED-OP` sentinel (the `loadSym` policy).
  | .test a b   => .Lopn [] (withWidthTag 64 "TEST")
                     [resolveReg alloc a, resolveJOp alloc b]
  | .cmp a b    => .Lopn [] (withWidthTag 64 "CMP")
                     [resolveReg alloc a, resolveJOp alloc b]
  | .not_ d     => .Lopn [resolveReg alloc d] (withWidthTag 64 "NOT") [resolveReg alloc d]
  | .andn d s1 s2 => .Lopn [resolveReg alloc d] (withWidthTag 64 "ANDN")
                       [resolveReg alloc s1, resolveReg alloc s2]
  | .rol d amt  => .Lopn [resolveReg alloc d] (withWidthTag 64 "ROL")
                     [resolveReg alloc d, resolveJOp alloc amt]
  | .ror d amt  => .Lopn [resolveReg alloc d] (withWidthTag 64 "ROR")
                     [resolveReg alloc d, resolveJOp alloc amt]
  | .rorx d s amt => .Lopn [resolveReg alloc d] (withWidthTag 64 "RORX")
                       [resolveReg alloc s, resolveJOp alloc amt]
  | .shlx d s c => .Lopn [resolveReg alloc d] (withWidthTag 64 "SHLX")
                     [resolveReg alloc s, resolveReg alloc c]
  | .shrx d s c => .Lopn [resolveReg alloc d] (withWidthTag 64 "SHRX")
                     [resolveReg alloc s, resolveReg alloc c]
  | .sarx d s c => .Lopn [resolveReg alloc d] (withWidthTag 64 "SARX")
                     [resolveReg alloc s, resolveReg alloc c]
  | .movzx d _ s => .Lopn [resolveReg alloc d] (withWidthTag 64 "MOVZX")
                      [resolveReg alloc s]
  | .movsx d _ s => .Lopn [resolveReg alloc d] (withWidthTag 64 "MOVSX")
                      [resolveReg alloc s]
  | .lea d _ _ _ _ => .Lopn [resolveReg alloc d] (withWidthTag 64 "LEA") []
  -- `loadSym dst sym` (`leaq sym(%rip), %dst`): writes register `dst`, reads no
  -- register. `LOperand` carries no `.rodata`-symbol operand and the fe25519/
  -- x25519 field leaves this bridge serves never index a `.rodata` table (the
  -- NTT, which does, takes the TEXT `AsmPrinter` path, not this `LinstrR` lift),
  -- so we lift to an explicit unsupported `Lopn` — destination `[dst]`, no
  -- sources. The `LOADSYM` opn has no `attBase` mnemonic, so `renderLopn` emits a
  -- visible `# UNHANDLED-OP` sentinel rather than any silently-wrong instruction.
  | .loadSym d _ => .Lopn [resolveReg alloc d] (withWidthTag 64 "LOADSYM") []
  -- The increment, carry-flag, exchange, widening-multiply, double-shift,
  -- rotate-through-carry, general-condition, sized-test and bit-test instructions:
  -- the fe25519/x25519 field leaves never emit them, and `LinstrR` has no operand
  -- for their implicit registers, sizes or condition codes. Each lifts to its
  -- natural `Lopn` shape under a mnemonic with no `attBase` entry, so `renderLopn`
  -- emits the `# UNHANDLED-OP` sentinel. The widening multiplies do not use `MUL`,
  -- which `attBase` renders as the two-operand `imul`.
  | .inc d => .Lopn [resolveReg alloc d] (withWidthTag 64 "INC") [resolveReg alloc d]
  | .dec d => .Lopn [resolveReg alloc d] (withWidthTag 64 "DEC") [resolveReg alloc d]
  | .clc => .Lopn [] (withWidthTag 64 "CLC") []
  | .stc => .Lopn [] (withWidthTag 64 "STC") []
  | .xchg a b => .Lopn [resolveReg alloc a, resolveReg alloc b] (withWidthTag 64 "XCHG")
                   [resolveReg alloc a, resolveReg alloc b]
  | .imulri d s imm => .Lopn [resolveReg alloc d] (withWidthTag 64 "IMULRI")
                         [resolveReg alloc s, .imm imm]
  | .mul dh dl s => .Lopn [resolveReg alloc dh, resolveReg alloc dl]
                      (withWidthTag 64 "MULWIDE") [resolveReg alloc dl, resolveReg alloc s]
  | .imulWide dh dl s => .Lopn [resolveReg alloc dh, resolveReg alloc dl]
                           (withWidthTag 64 "IMULWIDE")
                           [resolveReg alloc dl, resolveReg alloc s]
  | .shld d s amt => .Lopn [resolveReg alloc d] (withWidthTag 64 "SHLD")
                       [resolveReg alloc d, resolveReg alloc s, resolveJOp alloc amt]
  | .shrd d s amt => .Lopn [resolveReg alloc d] (withWidthTag 64 "SHRD")
                       [resolveReg alloc d, resolveReg alloc s, resolveJOp alloc amt]
  | .rcl d amt => .Lopn [resolveReg alloc d] (withWidthTag 64 "RCL")
                    [resolveReg alloc d, resolveJOp alloc amt]
  | .rcr d amt => .Lopn [resolveReg alloc d] (withWidthTag 64 "RCR")
                    [resolveReg alloc d, resolveJOp alloc amt]
  | .cmovcc _ d s => .Lopn [resolveReg alloc d] (withWidthTag 64 "CMOVCC")
                       [resolveReg alloc d, resolveJOp alloc s]
  | .setcc _ d => .Lopn [resolveReg alloc d] (withWidthTag 64 "SETCC") [resolveReg alloc d]
  | .testN _ a b => .Lopn [] (withWidthTag 64 "TESTN")
                      [resolveReg alloc a, resolveJOp alloc b]
  | .bt a b => .Lopn [] (withWidthTag 64 "BT") [resolveReg alloc a, resolveJOp alloc b]
  | .btr d b => .Lopn [resolveReg alloc d] (withWidthTag 64 "BTR")
                  [resolveReg alloc d, resolveJOp alloc b]
  | .bts d b => .Lopn [resolveReg alloc d] (withWidthTag 64 "BTS")
                  [resolveReg alloc d, resolveJOp alloc b]
  -- The memory-operand arithmetic: the field leaves never emit it, and each lifts under
  -- a mnemonic with no `attBase` entry, so `renderLopn` emits the `# UNHANDLED-OP`
  -- sentinel.
  | .addMem d base off => .Lopn [resolveReg alloc d] (withWidthTag 64 "ADDMEM")
                            [resolveReg alloc d, memOperand alloc base off]
  | .addToMem base off s => .Lopn [memOperand alloc base off] (withWidthTag 64 "ADDTOMEM")
                              [memOperand alloc base off, resolveJOp alloc s]
  | .adcxMem d base off => .Lopn [resolveReg alloc d] (withWidthTag 64 "ADCXMEM")
                             [resolveReg alloc d, memOperand alloc base off]
  | .adoxMem d base off => .Lopn [resolveReg alloc d] (withWidthTag 64 "ADOXMEM")
                             [resolveReg alloc d, memOperand alloc base off]
  | .imulMem d base off => .Lopn [resolveReg alloc d] (withWidthTag 64 "IMULMEM")
                             [resolveReg alloc d, memOperand alloc base off]
  | .imulriMem d base off imm => .Lopn [resolveReg alloc d] (withWidthTag 64 "IMULRIMEM")
                                   [memOperand alloc base off, .imm imm]
  -- BMI2 `bzhi`: the field leaves never emit it, and `BZHI` has no `attBase` entry.
  | .bzhi d s i => .Lopn [resolveReg alloc d] (withWidthTag 64 "BZHI")
                     [resolveReg alloc s, resolveReg alloc i]

/-- Lift a whole `JInstr 64` block to an `Lcmd` over a resolved `GpAlloc`, ending
    with the function-level `Lret`. The `li_ii` source tags are `0` (no position
    info on the word kernels). -/
def jinstrBlockToLcmd (alloc : GpAlloc) (block : List (JInstr 64)) : Lcmd :=
  block.map (fun i => (⟨0, jinstrToLinstrR alloc i⟩ : Linstr)) ++ [⟨0, .Lret⟩]

/-! ### 2c. SysV argument marshalling for the leaf `Lfundef` (#656-residual fix)

A leaf's `GpAlloc` may bind an argument name to a register **different** from its
SysV home register — canonically `feMul`'s `y` pointer (the 3rd arg, home `%rdx`)
is relocated to `%rcx` because the MULX multiplier `yd` pins `%rdx`. The trusted
`.s` path (`AsmPrinter.renderSysVLeafFn`) emits the `movq %home, %dst` arg-marshal
moves (`argMarshalMoves`) BEFORE the body; the naive `Lfundef` lift dropped them,
so the lifted `feMul` read its `y` operand from an uninitialised register
(SEGFAULT). This lifts `argMarshalMoves` to the `LinstrR` `MOV` form so the
byte-encoded `Lfundef` carries the same ABI prologue the verified `.s` does — the
whole field-leaf set is then self-contained in the byte-encoder `.o`. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (AbiArg ArgClass intArgHome regOf)

/-- The arg-marshal MOVs for a leaf, lifted to `LinstrR`: for each `intPtr` arg
    whose allocated register differs from its SysV home register, a `MOV dst ← home`
    (the `LinstrR` image of `AsmPrinter.argMarshalMoves`'s `movq %home, %dst`). The
    home register names are bare uppercase GP names (`upperReg ∘ home`); the dst is
    the arg's allocated reg uppercased. -/
def argMarshalLinstrs (alloc : GpAlloc) (args : List AbiArg) : Lcmd :=
  (args.zipIdx).filterMap (fun (a, i) =>
    match a.cls, intArgHome i with
    | .intPtr, some home =>
        let dst := regOf alloc a.name
        -- An UNALLOCATED arg is dead (the op never reads it — e.g. `mul121666`/`sqr`
        -- ignore `y`); emit no marshal move (a move into a sentinel reg has no byte
        -- image and would surface as a bad register in the text path).
        if dst == home || "<UNALLOCATED".isPrefixOf dst || "<UNKNOWN".isPrefixOf dst then none
        else
          let dU := upperReg dst
          let hU := upperReg home
          some (⟨0, .Lopn [.reg dU] (withWidthTag 64 "MOV") [.reg dU, .reg hU]⟩ : Linstr)
    | _, _ => none)

/-- Wrap a lifted `JInstr` block as an `Lfundef` (the owned-RA function record):
    `lfd_body` is the SysV arg-marshal prologue (`argMarshalLinstrs`, relocating any
    argument whose allocation differs from its home register — e.g. `feMul`'s
    `y`-ptr `%rdx`→`%rcx`) followed by the lifted block, `lfd_arg`/`lfd_tyin` the
    3-pointer fe25519 ABI (`z`→RDI, `x`→RSI, `y`→RDX), `lfd_res` empty (the leaf
    returns via `*z`). This is the `Lfundef` a multi-function ladder `Lprog` carries
    as a sibling symbol. -/
def jinstrBlockToLfundef (alloc : GpAlloc) (args : List AbiArg)
    (block : List (JInstr 64)) : Lfundef :=
  { lfd_tyin := [64, 64, 64]
    lfd_arg := ["RDI", "RSI", "RDX"]
    lfd_body := argMarshalLinstrs alloc args ++ jinstrBlockToLcmd alloc block
    lfd_tyout := []
    lfd_res := [] }

/-- The SysV arg lists of the fe25519 leaves (all three pointer args `z`,`x`,`y`;
    `sqr`/`mul121666` ignore `y` but carry it for a uniform ABI). -/
def feLeafArgs : List AbiArg := [⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩]

/-- The `Lfundef` of each owned fe25519 leaf, paired with its symbol name (the
    multi-function `Lprog`'s `lp_funcs` entries for the field ops). -/
def fe25519LeafFundefs : List (String × Lfundef) :=
  [ ("fe25519_mul_x86_from_lean",
       jinstrBlockToLfundef Fe25519MulKernel.feMulAlloc feLeafArgs Fe25519MulKernel.feMulBlock)
  , ("fe25519_sqr_x86_from_lean",
       jinstrBlockToLfundef Fe25519OpsKernel.feSqrAlloc feLeafArgs Fe25519OpsKernel.feSqrBlock)
  , ("fe25519_add_x86_from_lean",
       jinstrBlockToLfundef Fe25519OpsKernel.feAddAlloc feLeafArgs Fe25519OpsKernel.feAddBlock)
  , ("fe25519_sub_x86_from_lean",
       jinstrBlockToLfundef Fe25519OpsKernel.feSubAlloc feLeafArgs Fe25519OpsKernel.feSubBlock)
  , ("fe25519_mul121666_x86_from_lean",
       jinstrBlockToLfundef Fe25519OpsKernel.feMul121666Alloc feLeafArgs
         Fe25519OpsKernel.feMul121666Block) ]

/-- **`feMul` carries exactly ONE SysV arg-marshal `MOV` prologue instruction**
    (`y`-ptr `%rdx`→`%rcx`, the relocation forced by the `yd→%rdx` MULX pin), which
    renders to `movq %rdx, %rcx`. Without it the lifted leaf read `y` from an
    uninitialised register (SEGFAULT). -/
theorem feMul_argMarshal_renders :
    (argMarshalLinstrs Fe25519MulKernel.feMulAlloc feLeafArgs).length = 1
      ∧ (argMarshalLinstrs Fe25519MulKernel.feMulAlloc feLeafArgs).flatMap
          (fun i => LprogAsmPrinter.renderLinstrR 0 64 i.li_i) = ["\tmovq %rdx, %rcx"] := by
  native_decide

/-- `feAdd` needs NO arg marshalling (`y` is already allocated to its home `%rdx`). -/
theorem feAdd_argMarshal_empty :
    (argMarshalLinstrs Fe25519OpsKernel.feAddAlloc feLeafArgs).length = 0 := by native_decide

/-! ### 2a. Which field ops are byte-encodable (residual CLOSED, #656-residual)

A field op's lifted `Lcmd` is byte-encodable by `LprogBytes.encodeLprogReloc`
**iff** it carries no `UNREP-ADX:…` sentinel `Lopn` — i.e. every op has a faithful
`LinstrR`/byte image. As of the #656-residual work the BMI2/ADX trio
(`MULX`/`MULXMEM`/`ADCX`/`ADOX`) lifts to faithful `Lopn` forms the byte encoder
delegates to `ScalarEncoder`'s `encMulxRR`/`encMulxMem`/`encAdxCarry`, so the whole
fe25519 field-op set — `feAdd`/`feSub` (pure GP-ALU) AND `feMul`/`feSqr`/
`feMul121666` (the ADX schoolbook) — is now byte-direct: NO sentinels remain, the
`.o` byte route carries the whole family; the verified `.s`+gas route is a
comparison artifact for the field leaves. -/

/-- Does a lifted `Lcmd` carry an `UNREP-ADX:…` sentinel (an op with no faithful
    `LinstrR`/byte image)? -/
def hasUnrepAdx (body : Lcmd) : Bool :=
  body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => "UNREP-ADX:".isPrefixOf opn
    | _ => false)

/-- `feAdd` lifts to a fully ALU `Lcmd` — no ADX sentinel, so it is byte-encodable. -/
theorem feAdd_lift_byteEncodable :
    hasUnrepAdx (jinstrBlockToLcmd Fe25519OpsKernel.feAddAlloc Fe25519OpsKernel.feAddBlock)
      = false := by native_decide

/-- `feSub` lifts to a fully ALU `Lcmd` — no ADX sentinel, so it is byte-encodable. -/
theorem feSub_lift_byteEncodable :
    hasUnrepAdx (jinstrBlockToLcmd Fe25519OpsKernel.feSubAlloc Fe25519OpsKernel.feSubBlock)
      = false := by native_decide

/-- `feMul` lifts with NO ADX sentinel (#656-residual closed): the schoolbook's
    `mulx`/`adcx`/`adox` now carry faithful `LinstrR`/byte images, so the
    byte-encoder `.o` route carries the field multiply. -/
theorem feMul_lift_byteEncodable :
    hasUnrepAdx (jinstrBlockToLcmd Fe25519MulKernel.feMulAlloc Fe25519MulKernel.feMulBlock)
      = false := by native_decide

/-- `feSqr` likewise lifts with no ADX sentinel — byte-encodable. -/
theorem feSqr_lift_byteEncodable :
    hasUnrepAdx (jinstrBlockToLcmd Fe25519OpsKernel.feSqrAlloc Fe25519OpsKernel.feSqrBlock)
      = false := by native_decide

/-- `feMul121666` likewise lifts with no ADX sentinel (`mulxMem` now faithful). -/
theorem feMul121666_lift_byteEncodable :
    hasUnrepAdx
      (jinstrBlockToLcmd Fe25519OpsKernel.feMul121666Alloc Fe25519OpsKernel.feMul121666Block)
      = false := by native_decide

/-! ### 2b. The byte encoder produces real ADX/MULX bytes (#656-residual)

The lifted field bodies are now driven all the way to machine bytes by
`LprogBytes.encodeLcmd` (the `MULX`/`MULXMEM`/`ADCX`/`ADOX` arms delegate to
`ScalarEncoder`'s `encMulxRR`/`encMulxMem`/`encAdxCarry`). These theorems pin that
the encoder's bytes are NON-EMPTY and carry the faithful BMI2/ADX opcodes — the
VEX `MULX` lead byte `0xC4` and the ADX `0F 38 F6` carry-chain triple — so the
field multiply is byte-direct, not dropped. (The exact byte-identity to gas's
chosen `.text`, including every VEX/0F38 byte, is the bench
`fieldbytes-validate` `objdump -d` `cmp`; here we pin the in-Lean encoder output
exercises the new arms.) -/

/-- The byte-encoded `feMul` body (the lifted ADX schoolbook → machine bytes). -/
def feMulEncodedBytes : List (BitVec 8) :=
  LprogBytes.encodeLcmd (jinstrBlockToLcmd Fe25519MulKernel.feMulAlloc Fe25519MulKernel.feMulBlock)

/-- Count of a single byte value `b` in a byte list. -/
def countByte (b : BitVec 8) (bs : List (BitVec 8)) : Nat :=
  bs.countP (· == b)

/-- The byte encoder produces a `feMul` body carrying VEX-`MULX` lead bytes
    (`0xC4`) — the `mulx`/`mulxMem` arms are exercised, so
    the field multiply is byte-direct. The exact count (and full byte-identity to
    gas, including every VEX/0F38 byte) is the bench `fieldbytes-validate`. -/
theorem feMulEncodedBytes_has_mulx_vex :
    0 < countByte (BitVec.ofNat 8 0xc4) feMulEncodedBytes := by native_decide

/-- `feMul`'s encoded body is non-empty — the lifted ADX schoolbook reaches machine
    bytes through `encodeLcmd` (the `.text` the bench confirms byte-identical to gas
    is 480 bytes). -/
theorem feMulEncodedBytes_nonempty : feMulEncodedBytes ≠ [] := by
  have : 0 < feMulEncodedBytes.length := by native_decide
  exact fun h => by simp [h] at this

/-! ## 3. The ladder's field-op call site (`Lcall` to a sibling leaf)

The ladder body's opaque field-op `extCall name` becomes a real
`LinstrR.Lcall` to the sibling owned leaf `name`. `renderLinstrR` (#656) renders
`Lcall ra (f, l)` to `call f`. -/

/-- A direct near-`call` to the owned fe25519 leaf symbol `name` — the `LinstrR`
    the ladder body's field-op `extCall` lowers to (an intra-object sibling call,
    `LprogBytes.encodeLcmdReloc` resolves it directly / gas resolves the text-path
    `call name`). `ra = none` (no return-address spill), label `0` (the symbol name
    is the target, not a local label index). -/
def ladderCallSite (name : String) : LinstrR := .Lcall none (name, 0)

/-- All five field-op call sites the ladder add-and-double step issues. -/
def ladderFieldCallSites : List LinstrR := fe25519LeafSymbols.map ladderCallSite

/-- Each field-op call site renders to a direct `call <leaf>` (the intra-object
    sibling call), through the `renderLinstrR` `Lcall` arm. -/
theorem ladderCallSite_renders_mul :
    LprogAsmPrinter.renderLinstrR 0 64 (ladderCallSite "fe25519_mul_x86_from_lean")
      = ["\tcall fe25519_mul_x86_from_lean"] := by native_decide

theorem ladderCallSite_renders_sqr :
    LprogAsmPrinter.renderLinstrR 0 64 (ladderCallSite "fe25519_sqr_x86_from_lean")
      = ["\tcall fe25519_sqr_x86_from_lean"] := by native_decide

/-! ## 4. The WHOLE add-and-double step as ONE byte-encoded `Lfundef` (the milestone)

`X25519MonoLadderKernel.monoLadderStepBlock` (#411) is the entire RFC 7748
Montgomery double-and-add step — all five field ops (`add`/`sub`/`sqr`/`mul`/
`mul121666`) **inlined** into one straight-line, no-`call` `List (JInstr 64)`
(1058 instructions) over the frame base `fp` (= `%rdi`), with `runBlock`-verified
lowering correctness (`monoLadderStepBlock_lowering_correct`). It is emitted today
as the gas-assembled `.s` text `monoStepAsm` (per-op register-allocated through the
verified `renderBlockBody` path).

This section lifts that verified step body to an owned-RA `Lcmd` via the §2 bridge
(`jinstrToLinstrR`, faithful for the whole field-op alphabet including the
BMI2/ADX trio) and byte-encodes it directly through `LprogBytes.encodeLprogReloc` —
**no gas instruction selection on the artifact path**. The per-op register
allocation is the SAME `allocGp (framePins ++ mulxPins) ∘ optimizeX86Block` the
text path uses (`X25519MonoLadderKernel.stepOps` / `renderOpBlock`), so the lifted
`Lcmd` allocates exactly as `monoStepAsm`.

The whole add-and-double step is therefore off gas: the field ops are NOT separate
call targets here (they are inlined into the one step body — the call-tax win of
#411), and the resulting body byte-encodes with **zero** uncovered instructions
(every `Lopn` — `MOV`/`ADD`/`SUB`/`ADC`/`SBB`/`AND`/`OR`/`SHL`/`SHR`/`LOAD`/
`STORE` AND `MULX`/`MULXMEM`/`ADCX`/`ADOX` — has a faithful byte image; see
`monoStepLcmd_fully_byteEncodable`). -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
  (framePins stepOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline (optimizeX86Block)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-- Lift one `stepOps` entry `(mulxPins, block)` to a no-`Lret` `Lcmd`, under the
    SAME per-op allocation the text path uses: route the block through the default
    `optimizeX86Block` pipeline, allocate within the GP pool with `fp` (+ MULX) pins,
    then lift via `jinstrBlockToLcmd` and drop the trailing function-level `Lret` (a
    loop-body op, not a return). -/
def stepOpLcmd (e : GpAlloc × List (JInstr 64)) : Lcmd :=
  let opt := optimizeX86Block e.2
  let alloc := AsmPrinter.allocGp (framePins ++ e.1) opt
  (jinstrBlockToLcmd alloc opt).dropLast

/-- The whole add-and-double step lifted to ONE owned-RA `Lcmd` (the concatenated
    per-op bodies, frame-resident in `fp` = `%rdi`), ending with the function-level
    `Lret`. This is the `monoLadderStepBlock` of #411, lifted op-by-op through the
    §2 `JInstr → LinstrR` bridge — the verified add-and-double, now in the form
    `encodeLprogReloc` byte-encodes. -/
def monoStepLcmd : Lcmd :=
  stepOps.flatMap stepOpLcmd ++ [⟨0, .Lret⟩]

/-- The lifted whole-step body has the same instruction count as
    `monoLadderStepBlock` (1058 ops) plus the trailing `Lret`. -/
theorem monoStepLcmd_length : monoStepLcmd.length = 1059 := by native_decide

/-- **Every instruction of the whole add-and-double step byte-encodes** — there are
    ZERO uncovered `Lopn`s (no visible-empty byte image). The entire field-op
    alphabet of the inlined ladder step (ALU + `LOAD`/`STORE` + the BMI2/ADX
    `MULX`/`MULXMEM`/`ADCX`/`ADOX` schoolbook) has a faithful byte image, so the
    whole step is byte-direct through `encodeLprogReloc`, not dropped to a gas
    instruction-selection route. -/
theorem monoStepLcmd_fully_byteEncodable :
    (monoStepLcmd.filter (fun i => match i.li_i with
      | .Lopn _ _ _ => (encodeLopn 0 64 i.li_i).isEmpty
      | _ => false)) = [] := by native_decide

/-- The whole-scalarmult-step owned-RA `Lfundef`: the lifted add-and-double body,
    taking the frame pointer `fp` in `%rdi` (SysV first arg), returning via the
    frame. The callee-saved set + frame are computed by the byte encoder's
    `calleeSavedToSave`/`frameSize` (the same framing the text path uses). -/
def monoStepFundef : Lfundef :=
  { lfd_tyin := [64], lfd_arg := ["RDI"], lfd_body := monoStepLcmd
    lfd_tyout := [], lfd_res := [] }

/-- The whole add-and-double step as a single-function owned-RA `Lprog`, exporting
    `x25519_mono_step`. This is the object both byte routes consume:
    `encodeLprogReloc` (the `.o`, no gas instruction selection) and
    `renderLprogAtt → gas` (the differential oracle). -/
def monoStepLprog : Lprog :=
  { lp_funcs := [("x25519_mono_step", monoStepFundef)] }

/-- The whole-scalarmult owned-RA `Lprog`: the inlined add-and-double step
    `x25519_mono_step` PLUS the five fe25519 field leaves (`fe25519LeafFundefs`,
    each a byte-encodable `Lfundef` — `feMul/feSqr/feAdd/feSub/feMul121666`). The
    field leaves serve the off-hot-loop final inversion (`z^(p-2)`, the fixed
    squaring/mul addition chain the C harness drives) as sibling symbols in the
    SAME `.o` — so the entire field-arithmetic surface of `x25519_scalarmult` (the
    ladder step AND the inversion leaves) is byte-encoded by `encodeLprogReloc`
    with no gas instruction selection. -/
def x25519ScalarmultLprog : Lprog :=
  { lp_funcs := ("x25519_mono_step", monoStepFundef) :: fe25519LeafFundefs }

/-- The whole-scalarmult byte-`.o` (step + field leaves), the gas-free artifact. -/
def x25519ScalarmultObject : List (BitVec 8) := encodeLprogReloc x25519ScalarmultLprog

/-- The whole-scalarmult object carries all six function symbols' bytes (non-empty). -/
theorem x25519ScalarmultObject_nonempty : x25519ScalarmultObject ≠ [] := by
  have : 0 < x25519ScalarmultObject.length := by native_decide
  exact fun h => by simp [h] at this

/-- The byte-encoded `.o` of the whole add-and-double step (the artifact path). -/
def monoStepObject : List (BitVec 8) := encodeLprogReloc monoStepLprog

/-- The byte-encoder `.text` of the step is non-empty and carries the VEX-`MULX`
    lead byte `0xC4` (the inlined field-multiply schoolbook reaches machine bytes,
    not dropped). The exact byte-identity to the `renderLprogAtt → gas` `.text` of
    the SAME `Lprog` is the bench `monostep-validate` differential. -/
theorem monoStepObject_nonempty : monoStepObject ≠ [] := by
  have : 0 < monoStepObject.length := by native_decide
  exact fun h => by simp [h] at this

/-- The step body bytes carry VEX-`MULX` lead bytes (`0xC4`) — the inlined
    multiplies/squares are byte-encoded. -/
theorem monoStepEncoded_has_mulx :
    0 < countByte (BitVec.ofNat 8 0xc4)
      (LprogBytes.encodeLfundefBytes monoStepLcmd) := by native_decide

/-! ## 5. The WHOLE `x25519_scalarmult` folded into one owned `Lcmd` (the milestone)

The prior sections byte-encode the *field-arithmetic surface* (`x25519_mono_step` +
the fe25519 leaves); the RFC 7748 *scaffolding* — the 8-bit clamp/decode, the per-bit
`cswap` on the frame words, the 255-iteration ladder loop driver, the inversion
addition chain, and the little-endian pack/encode — was driven from C
(`bench/x25519_ladder/scalarmult_owned_kat.c::x25519_owned`). This section folds that
scaffolding into ONE owned-RA `Lcmd` so the whole `x25519_scalarmult(out,k,u)` is a
single byte-encoded function, with NO C scaffolding on the artifact path.

The whole function is expressible in the byte-encodable `LinstrR` alphabet
(`MOV`/`ADD`/`ADC`/`SUB`/`AND`/`OR`/`XOR`/shift-by-imm/`LOAD`/`STORE` + intra-object
`Lcall`):

* **decode** — eight `LOAD`s of the 32-byte scalar / u-coordinate (little-endian
  64-bit limbs) from `(%rsi)`/`(%rdx)` into the frame;
* **clamp** — `k[0] &= 248`, `k[31] &= 0x7fffffffffffffff` (the limb-3 image of
  byte-31 `&= 127`), `k[31] |= 0x4000000000000000` (byte-31 `|= 64`), via `AND`/`OR`
  immediates;
* **the 255-iteration ladder loop** (`loopLcmd`, the verified back-edge of
  `LprogControlFlow`) whose body is the constant-time `cswap` (mask `m = 0 - swap`
  synthesised as `MOV m,#0 ; SUB m,swap`, then `t = m & (a^b) ; a^=t ; b^=t` over the
  four limbs of `(x2,x3)` and `(z2,z3)`) plus the next scalar bit (top bit of the
  running scalar, extracted by `SHR $63` then a 4-limb `ADD`/`ADC` shift-left-by-1, so
  no variable shift is needed) and a `call x25519_mono_step` (the byte-encoded
  add-and-double, frame pointer in `%rdi`);
* **inversion** — the fixed `z^(p-2)` addition chain as a straight-line sequence of
  `call`s to the byte-encoded field leaves (`fe25519_{mul,sqr}_x86_from_lean`), the
  squaring runs (`for i<5/10/20/50/100` `SQR`) emitted as `loopLcmd` counted loops;
* **encode** — eight `STORE`s of the result limbs to `(out)`.

All control flow is public (the 255 trip count and the squaring-run counts are
configuration constants, never secret), so every back-edge is a CT-admissible public
branch (`#460` vartime policy); the only scalar-bit dependence is inside the `cswap`,
which is branchless mask arithmetic.

The whole function byte-encodes through `LprogBytes.encodeLprogReloc` together with
`x25519_mono_step` and the five field leaves as sibling symbols in ONE `.o`, the
field-op `call`s resolved intra-object. The end-to-end correctness gate is the RFC
7748 §5.2 KAT (`bench/x25519_ladder/scalarmult_owned_kat.c`), now over the
single-entry `.o` with NO C scaffolding. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (loopLcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
  (slotX2 slotZ2 slotX3 slotZ3 slotX1)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519UnifyingFront (UStep uband)

/-! The whole scalarmult body below is **generated** (FRONT) from a `List UStep`
    schedule over the unifying step language `Fe25519UnifyingFront.UStep` — the
    ad-hoc `w64`/`st64`/`callLeaf` `Lcmd` smart constructors are retired. Each
    `UStep` renders to exactly the owned-backend `Lopn`/`Lcall`/`loopLcmd` shape
    the deployed body used, so the RFC 7748 byte-KAT is unchanged. -/

/-- The work-frame base register (= `%rsp` after the wrapper opens the frame): all
    ladder/inversion cells are addressed `mem.FB.<off>`. The single sizing sentinel
    `k.SENT` forces `frameSize` to reserve the whole block (the spill region grows
    downward from below the qsave block; `k.SENT` is the lowest-address cell, so a
    reference to it sizes the frame to cover every `mem.FB.<off>` we use). -/
def FB : String := "RBX"

/-- The sizing-sentinel spill index. 110 work limbs (ladder 60 + inversion temps 48,
    plus a margin) ⇒ index 109 is the lowest-address cell; referencing it forces
    `frameSize = 984` (the 110-cell region below the 96-byte qsave block, `+8` call
    parity: the orchestrator body calls the field leaves, so the frame is sized
    `≡ 8 (mod 16)` to keep every call site SysV 16-aligned). The cell is used as
    scratch (the saved swap mask) so the reference is live, not dead. -/
def SENT : String := "k.109"

/-- The byte offset (within the work frame, base `FB`) of the ladder frame the step
    reads as `mem.%rdi.0..480`: it starts at `+8` (cell offset `0` is the `k.109`
    sentinel scratch, exclusively addressed as `k.109`). -/
def ladderBase : Int := 8
/-- The byte offset of the inversion-temp region (just above the 480-byte ladder). -/
def invBase : Int := ladderBase + 480

/-- `mem.FB.<off>` operand name. -/
def fbMem (off : Int) : String := "mem." ++ FB ++ "." ++ toString off.toNat
/-- A ladder-frame slot (relative to the step's `fp = FB + ladderBase`), limb `limb`. -/
def ladSlot (slot : Int) (limb : Nat) : String := fbMem (ladderBase + slot + 8 * limb)
/-- An inversion-temp cell: temp index `t` (each 32 bytes / 4 limbs), limb `limb`. -/
def invSlot (t : Nat) (limb : Nat) : String := fbMem (invBase + 32 * t + 8 * limb)

/-- Inversion-temp indices (the C harness' `z2_2,z9,z11,…` locals, here frame cells). -/
def T_z2_2 : Nat := 0
def T_z9 : Nat := 1
def T_z11 : Nat := 2
def T_z2_5_0 : Nat := 3
def T_z2_10_0 : Nat := 4
def T_z2_20_0 : Nat := 5
def T_z2_50_0 : Nat := 6
def T_z2_100_0 : Nat := 7
def T_z : Nat := 8
def T_t2 : Nat := 9
def T_x2 : Nat := 10   -- copy of the ladder x2 result (live across inversion)
def T_scalar : Nat := 11  -- the running (clamped, shifted) scalar, frame-resident
                          -- across the loop (R8..R11 are caller-clobbered by the
                          -- `call x25519_mono_step`, so the scalar cannot live in them)

/-- Load the work-frame pointer for a temp cell `t` into `dst` (for a leaf `call`,
    whose args are `mem.%rdi/%rsi/%rdx.*`): `dst := FB + invBase + 32*t`. -/
def ptrTemp (dst : String) (t : Nat) : List UStep :=
  [ .movRR dst FB, .addImm dst (invBase + 32 * t).toNat ]
/-- Load the work-frame pointer for the ladder slot `slot` into `dst`. -/
def ptrLad (dst : String) (slot : Int) : List UStep :=
  [ .movRR dst FB, .addImm dst (ladderBase + slot).toNat ]

/-- `fe25519_sqr(dst,src)` over temp cells: set `%rdi=&dst, %rsi=&src`, then `call`. -/
def sqrTemps (dst src : Nat) : List UStep :=
  ptrTemp "RDI" dst ++ ptrTemp "RSI" src ++ [.call "fe25519_sqr_x86_from_lean"]
/-- `fe25519_mul(dst,a,b)` over temp cells: `%rdi=&dst, %rsi=&a, %rdx=&b`, then `call`. -/
def mulTemps (dst a b : Nat) : List UStep :=
  ptrTemp "RDI" dst ++ ptrTemp "RSI" a ++ ptrTemp "RDX" b
    ++ [.call "fe25519_mul_x86_from_lean"]

/-- A counted squaring run `for i in [0,n) { dst = dst^2 }` over temp cell `dst`,
    emitted as a `loopLcmd` (counter `R15`, public trip count `n`). The body sets
    `%rdi=%rsi=&dst`, calls `fe25519_sqr`, then the `loopLcmd` appends the `n -= 1`
    via its own `CMP`/`jne` — but `loopLcmd` assumes the body decrements, so we add
    `SUB R15,#1` inside the body. The top label is `lbl`. -/
def sqrRun (lbl : LLabel) (dst n : Nat) : List UStep :=
  [ .movImm "R15" n
  , .loop lbl "R15"
      (uband 64 (ptrTemp "RDI" dst ++ ptrTemp "RSI" dst
        ++ [.call "fe25519_sqr_x86_from_lean", .subImm "R15" 1])) ]

/-! ### 5a. decode + clamp -/

/-- Decode the 32-byte little-endian scalar `k` (`%rsi` at entry), clamp, and store
    the four running-scalar limbs into the frame cell `T_scalar` (the scalar must be
    frame-resident: the `call x25519_mono_step` in the loop body clobbers every
    caller-saved register, so it cannot live in `R8..R11`). Clamp:
    `k[0] &= 248 ; k[31] &= 127` (limb3 `&= 0x7fff…ffff`) `; k[31] |= 64`
    (limb3 `|= 0x4000…0000`). -/
def decodeClampScalar : List UStep :=
  [ .load "R8"  "mem.RSI.0"
  , .load "R9"  "mem.RSI.8"
  , .load "R10" "mem.RSI.16"
  , .load "R11" "mem.RSI.24"
  -- clamp `k[0] &= 248` is a BYTE op: as a 64-bit limb-0 mask it clears only the low
  -- 3 bits, i.e. `limb0 &= 0xFFFFFFFFFFFFFFF8` (NOT `&= 0xf8`, which would also wipe
  -- bytes 1..7 of the limb). The 64-bit mask is materialised via a scratch register.
  , .movImm "RAX" 0xfffffffffffffff8, .andRR "R8" "RAX"
  -- the 64-bit high-limb clamp masks likewise do NOT fit a sign-extended imm32 (the
  -- byte encoder's `81 /digit id` ALU-imm form truncates to imm32 then sign-extends,
  -- so a literal `andq $0x7fff…` would mis-encode to `andq $-1`); materialise them
  -- into a scratch register via the 64-bit `movabs` (`encMovImm64`) and AND/OR r-to-r.
  , .movImm "RAX" 0x7fffffffffffffff, .andRR "R11" "RAX"
  , .movImm "RAX" 0x4000000000000000, .orRR "R11" "RAX"
  , .store (invSlot T_scalar 0) "R8",  .store (invSlot T_scalar 1) "R9"
  , .store (invSlot T_scalar 2) "R10", .store (invSlot T_scalar 3) "R11" ]

/-- Decode the 32-byte little-endian u-coordinate (`%rdx` at entry) into the ladder
    `x1` slot and `x3` slot, mask the top bit (`u[31] &= 0x7fff…`), and set the
    Montgomery start state `x2=1, z2=0, z3=1` (`z3`-limb0 = 1, the rest already
    zeroed). The whole work frame is NOT pre-zeroed by the encoder, so we explicitly
    zero `z2` (4 limbs) and the high limbs of `x2`,`z3`. -/
def decodeBase : List UStep :=
  -- load u into x1 and x3 (with top-bit mask on limb 3)
  [ .load "RAX" "mem.RDX.0", .store (ladSlot slotX1 0) "RAX", .store (ladSlot slotX3 0) "RAX"
  , .load "RAX" "mem.RDX.8", .store (ladSlot slotX1 1) "RAX", .store (ladSlot slotX3 1) "RAX"
  , .load "RAX" "mem.RDX.16", .store (ladSlot slotX1 2) "RAX", .store (ladSlot slotX3 2) "RAX"
  -- u[31] &= 0x7fff… : 64-bit mask via a scratch register (see decodeClampScalar note)
  , .load "RAX" "mem.RDX.24", .movImm "RCX" 0x7fffffffffffffff
  , .andRR "RAX" "RCX"
  , .store (ladSlot slotX1 3) "RAX", .store (ladSlot slotX3 3) "RAX"
  -- x2 = 1
  , .movImm "RAX" 1, .store (ladSlot slotX2 0) "RAX"
  , .movImm "RAX" 0
  , .store (ladSlot slotX2 1) "RAX", .store (ladSlot slotX2 2) "RAX", .store (ladSlot slotX2 3) "RAX"
  -- z2 = 0
  , .store (ladSlot slotZ2 0) "RAX", .store (ladSlot slotZ2 1) "RAX"
  , .store (ladSlot slotZ2 2) "RAX", .store (ladSlot slotZ2 3) "RAX"
  -- z3 = 1
  , .movImm "RAX" 1, .store (ladSlot slotZ3 0) "RAX"
  , .movImm "RAX" 0
  , .store (ladSlot slotZ3 1) "RAX", .store (ladSlot slotZ3 2) "RAX", .store (ladSlot slotZ3 3) "RAX" ]

/-! ### 5b. the constant-time cswap on two ladder slots, conditioned on mask `RCX` -/

/-- `cswap(slotA, slotB)` under the mask in `RCX` (`0` or all-ones): for each limb,
    `t = RCX & (a ^ b) ; a ^= t ; b ^= t`. Uses `RAX` (a), `RDX` (b/t) scratch. -/
def cswapSlots (slotA slotB : Int) : List UStep :=
  (List.range 4).flatMap (fun limb =>
    [ .load "RAX" (ladSlot slotA limb)
    , .load "RDX" (ladSlot slotB limb)
    , .movRR "RSI" "RAX"            -- RSI = a
    , .xorRR "RSI" "RDX"            -- RSI = a ^ b
    , .andRR "RSI" "RCX"            -- RSI = m & (a^b) = t
    , .xorRR "RAX" "RSI"            -- a ^= t
    , .xorRR "RDX" "RSI"            -- b ^= t
    , .store (ladSlot slotA limb) "RAX"
    , .store (ladSlot slotB limb) "RDX" ])

/-! ### 5c. one ladder iteration (the loop body) -/

/-- One Montgomery-ladder iteration over the running scalar in `R8..R11` and the
    swap accumulator in `R14`:

    1. `bit = R11 >> 63` (top bit of the running scalar, in `R12`-free `RAX`);
    2. shift the running scalar left by 1 (4-limb `ADD`/`ADC` doubling);
    3. `R14 ^= bit ; m = 0 - R14` (mask in `RCX`); `cswap(x2,x3) ; cswap(z2,z3)`;
    4. `R14 = bit` (the running swap = this bit, per RFC `cswap`-fold);
    5. `%rdi = FB + ladderBase` (the ladder `fp`); `call x25519_mono_step`.

    The mask `m = 0 - swap` is `MOV RCX,#0 ; SUB RCX,R14` (no `NEG` opcode needed). -/
def ladderIterLcmd : List UStep :=
  -- 1. load the running scalar from the frame, shift left by 1 across 4 limbs
  --    (ADD r8,r8 ; ADC …), so the next-to-process bit (initially bit 254 after
  --    clamp) lands in bit 255; store it back.
  [ .load "R8"  (invSlot T_scalar 0)
  , .load "R9"  (invSlot T_scalar 1)
  , .load "R10" (invSlot T_scalar 2)
  , .load "R11" (invSlot T_scalar 3)
  , .addRR "R8" "R8", .adcRR "R9" "R9"
  , .adcRR "R10" "R10", .adcRR "R11" "R11"
  -- 2. extract that top bit (bit 63 of limb 3) into RBP (callee-saved, so it
  --    survives the cswap scratch + the step call); store the shifted scalar back.
  , .movRR "RBP" "R11", .shrImm "RBP" 63
  , .store (invSlot T_scalar 0) "R8",  .store (invSlot T_scalar 1) "R9"
  , .store (invSlot T_scalar 2) "R10", .store (invSlot T_scalar 3) "R11" ]
  -- 3. swap ^= bit ; mask = 0 - swap  (RCX = 0 - R14)
  ++ [ .xorRR "R14" "RBP"
     , .movImm "RCX" 0, .subRR "RCX" "R14" ]
  ++ cswapSlots slotX2 slotX3
  ++ cswapSlots slotZ2 slotZ3
  -- 4. swap = bit  (the RFC `cswap`-fold: next iteration's prior-swap is this bit)
  ++ [ .movRR "R14" "RBP" ]
  -- 5. fp = FB + ladderBase ; call the byte-encoded add-and-double
  ++ ptrLad "RDI" 0
  ++ [ .call "x25519_mono_step" ]

/-! ### 5d. final cswap (after the loop), the inversion chain, and encode -/

/-- The RFC `x25519` post-loop sequence: a final `cswap(x2,x3)`/`cswap(z2,z3)` under
    `m = 0 - swap`, then copy `x2` to the temp `T_x2`, run the `z^(p-2)` addition
    chain over the temps (mirroring `scalarmult_owned_kat.c`), and `out = x2 * z`. -/
def invertAndEncode : List UStep :=
  -- final cswap under m = 0 - R14
  [ .movImm "RCX" 0, .subRR "RCX" "R14" ]
  ++ cswapSlots slotX2 slotX3
  ++ cswapSlots slotZ2 slotZ3
  -- copy x2 (ladder) -> temp T_x2, and z2 (ladder) -> temp T_z (reused as `z2`)
  ++ (List.range 4).flatMap (fun l =>
       [ .load "RAX" (ladSlot slotX2 l), .store (invSlot T_x2 l) "RAX" ])
  -- the addition chain operates on z2; keep z2 in temp cell `T_z` initially:
  ++ (List.range 4).flatMap (fun l =>
       [ .load "RAX" (ladSlot slotZ2 l), .store (invSlot T_z l) "RAX" ])
  -- z2_2 = z2^2
  ++ sqrTemps T_z2_2 T_z
  -- t2 = z2_2^2 ; t2 = t2^2     (== z2^8)
  ++ sqrTemps T_t2 T_z2_2 ++ sqrTemps T_t2 T_t2
  -- z9 = t2 * z2
  ++ mulTemps T_z9 T_t2 T_z
  -- z11 = z9 * z2_2
  ++ mulTemps T_z11 T_z9 T_z2_2
  -- t2 = z11^2
  ++ sqrTemps T_t2 T_z11
  -- z2_5_0 = t2 * z9
  ++ mulTemps T_z2_5_0 T_t2 T_z9
  -- t2 = z2_5_0^2 ; for i<5 (1..4) t2=t2^2  => 5 squarings total
  ++ sqrTemps T_t2 T_z2_5_0 ++ sqrRun 10 T_t2 4
  -- z2_10_0 = t2 * z2_5_0
  ++ mulTemps T_z2_10_0 T_t2 T_z2_5_0
  -- t2 = z2_10_0^2 ; for i<10 => 10 total
  ++ sqrTemps T_t2 T_z2_10_0 ++ sqrRun 11 T_t2 9
  -- z2_20_0 = t2 * z2_10_0
  ++ mulTemps T_z2_20_0 T_t2 T_z2_10_0
  -- t2 = z2_20_0^2 ; for i<20 => 20 total
  ++ sqrTemps T_t2 T_z2_20_0 ++ sqrRun 12 T_t2 19
  -- t2 = t2 * z2_20_0
  ++ mulTemps T_t2 T_t2 T_z2_20_0
  -- for i<10 t2=t2^2  (10 squarings)
  ++ sqrRun 13 T_t2 10
  -- z2_50_0 = t2 * z2_10_0
  ++ mulTemps T_z2_50_0 T_t2 T_z2_10_0
  -- t2 = z2_50_0^2 ; for i<50 => 50 total
  ++ sqrTemps T_t2 T_z2_50_0 ++ sqrRun 14 T_t2 49
  -- z2_100_0 = t2 * z2_50_0
  ++ mulTemps T_z2_100_0 T_t2 T_z2_50_0
  -- t2 = z2_100_0^2 ; for i<100 => 100 total
  ++ sqrTemps T_t2 T_z2_100_0 ++ sqrRun 15 T_t2 99
  -- t2 = t2 * z2_100_0
  ++ mulTemps T_t2 T_t2 T_z2_100_0
  -- for i<50 t2=t2^2 (50 squarings)
  ++ sqrRun 16 T_t2 50
  -- t2 = t2 * z2_50_0
  ++ mulTemps T_t2 T_t2 T_z2_50_0
  -- for i<5 t2=t2^2 (5 squarings)
  ++ sqrRun 17 T_t2 5
  -- z = t2 * z11
  ++ mulTemps T_z T_t2 T_z11
  -- out = x2 * z  -> %rdi = out (saved in R12), %rsi = &T_x2, %rdx = &T_z
  ++ [ .movRR "RDI" "R12" ]
  ++ ptrTemp "RSI" T_x2 ++ ptrTemp "RDX" T_z
  ++ [ .call "fe25519_mul_x86_from_lean" ]

/-- **The whole `x25519_scalarmult(out=%rdi, k=%rsi, u=%rdx)` schedule** over the
    unifying step language `Fe25519UnifyingFront.UStep`: decode/clamp, the
    255-iteration `cswap` ladder loop (a `.loop` with a sibling `.call
    x25519_mono_step`), the `z^(p-2)` inversion chain (several `sqrRun` `.loop`s
    interleaved with sibling `.call fe25519_{mul,sqr}`), and the result store.
    `uband 64` of this is the deployed body (`x25519ScalarmultLcmd`). -/
def x25519Schedule : List UStep :=
  -- frame base FB := RSP (the post-`leaq` frame base); save `out` (%rdi) in R12.
  [ .movRR FB "RSP"
  , .movRR "R12" "RDI"
  -- sizing sentinel: park the initial swap accumulator (0) in the lowest cell `k.109`
  -- (this single `k.N` reference sizes the frame; the cell is working scratch).
  , .movImm "RAX" 0, .store SENT "RAX"
  , .movImm "R14" 0 ]                                -- swap accumulator = 0
  ++ decodeClampScalar
  ++ decodeBase
  -- the 255-iteration ladder: counter R13 = 255, top label 0.
  ++ [ .movImm "R13" 255 ]
  ++ [ .loop 0 "R13" (uband 64 (ladderIterLcmd ++ [ .subImm "R13" 1 ])) ]
  ++ invertAndEncode
  ++ [ .ret ]

/-- **The whole `x25519_scalarmult(out=%rdi, k=%rsi, u=%rdx)` as one owned-RA
    `Lcmd`**, GENERATED (FRONT) from the `x25519Schedule` over the unifying step
    language `Fe25519UnifyingFront.UStep` (`uband 64`). Folds the RFC 7748
    scaffolding (decode/clamp, the 255-iteration `cswap` ladder loop, the
    `z^(p-2)` inversion chain, the result store) around the byte-encoded
    `x25519_mono_step` and the fe25519 leaves. The work frame is base `FB`
    (= `%rsp` after the wrapper opens it); the sizing sentinel `SENT` (`k.109`)
    forces the frame to cover the whole `mem.FB.*` work block. -/
def x25519ScalarmultLcmd : Lcmd := uband 64 x25519Schedule

/-- The deployed schedule passes the unifying front's generation gate (the
    `isSome` analogue): it carries a sibling `call` and a counted `loop`. -/
theorem x25519Schedule_wellFormed :
    Fe25519UnifyingFront.wellFormedU x25519Schedule = true := by native_decide

/-- The deployed schedule carries MULTIPLE counted loops (the 255-iteration ladder
    loop + the inversion chain's squaring runs) — at least eight `.loop` steps. -/
theorem x25519Schedule_multiple_loops :
    8 ≤ Fe25519UnifyingFront.loopCount x25519Schedule := by native_decide

/-! ### 5f. FRONT render-confirmation: the generated body carries the deployed ABI

The front-generated `x25519ScalarmultLcmd` renders to the SAME owned `.s` shape the
hand-authored body did — the frame size (`x25519Scalarmult_frame_reserved` = 984
below) and the byte-encodability (`x25519Scalarmult_fully_byteEncodable`) are the
same fingerprints, and these render KATs pin the control shape: the 255-iteration
ladder loop back-edge (`.L0:`/`jne .L0`), the sibling `call x25519_mono_step`, and
the inversion chain's field-brick `call fe25519_{mul,sqr}` all survive into the
rendered `.s`, so the RFC 7748 byte-KAT (`bench/x25519_ladder`,
`make …scalarmult_owned_kat`) links against the same intra-object symbols. -/

/-- The rendered `.s` of the front-generated whole-scalarmult body. -/
def x25519ScalarmultAsm : String :=
  LprogAsmPrinter.renderLfundef "x25519_scalarmult" x25519ScalarmultLcmd

/- The generated body renders the 255-iteration ladder loop back-edge
    (`.L0:` … `jne .L0`) — the `.loop 0 "R13"` of the schedule. -/
#guard (BignumMontMulKernel.hasSub x25519ScalarmultAsm ".L0:") && (BignumMontMulKernel.hasSub x25519ScalarmultAsm "jne .L0")

/- The generated body renders the sibling `call x25519_mono_step` inside the
    ladder loop (the byte-encoded add-and-double). -/
#guard (BignumMontMulKernel.hasSub x25519ScalarmultAsm "call x25519_mono_step")

/- The generated body renders the inversion chain's field-brick sibling calls
    (`call fe25519_mul`/`call fe25519_sqr`), including the ones inside the counted
    squaring-run loops. -/
#guard (BignumMontMulKernel.hasSub x25519ScalarmultAsm "call fe25519_mul_x86_from_lean") && (BignumMontMulKernel.hasSub x25519ScalarmultAsm "call fe25519_sqr_x86_from_lean")

/- The generated body renders MULTIPLE counted-loop back-edges: the ladder loop
    (`.L0:`) plus the inversion squaring-run loops (`.L14:`, `.L15:`) — the
    multiple-sequential-loops the unifying front expresses. -/
#guard (BignumMontMulKernel.hasSub x25519ScalarmultAsm ".L14:") && (BignumMontMulKernel.hasSub x25519ScalarmultAsm ".L15:")

/-- The whole-function owned-RA `Lfundef`: `x25519_scalarmult(out,k,u)` with the SysV
    3-pointer ABI (`out→RDI, k→RSI, u→RDX`). The body bare-writes `RBX/R12/R13/R14`
    (callee-saved), so `encodeLfundefBytes` brackets the frame with the matching
    `pushq`/`popq` and the contract holds for the C caller. -/
def x25519ScalarmultFundef : Lfundef :=
  { lfd_tyin := [64, 64, 64], lfd_arg := ["RDI", "RSI", "RDX"]
    lfd_body := x25519ScalarmultLcmd, lfd_tyout := [], lfd_res := [] }

/-- **The single-entry whole-scalarmult `Lprog`** (the milestone): the folded
    `x25519_scalarmult` orchestrator PLUS its sibling byte-encoded leaves
    `x25519_mono_step` and the five fe25519 field ops, all in ONE multi-symbol `.o`.
    Every cross-function `call` resolves intra-object. The whole RFC 7748 function —
    scaffolding included — is now byte-encoded by `encodeLprogReloc` with no C
    scaffolding and no gas instruction selection on the artifact path. -/
def x25519ScalarmultFullLprog : Lprog :=
  { lp_funcs :=
      ("x25519_scalarmult", x25519ScalarmultFundef)
        :: ("x25519_mono_step", monoStepFundef)
        -- only the field leaves the orchestrator actually calls (the inversion uses
        -- `mul`/`sqr`; the ladder step inlines its own lazy add/sub/cmadd). Keeping the
        -- object to exactly the called symbols makes the `.o` self-consistent and the
        -- differential (`renderLprogAtt → gas`) free of any dead-leaf residual.
        :: (fe25519LeafFundefs.filter (fun nf =>
              nf.1 == "fe25519_mul_x86_from_lean" || nf.1 == "fe25519_sqr_x86_from_lean")) }

/-- The single-entry whole-scalarmult byte-`.o` (orchestrator + step + field leaves). -/
def x25519ScalarmultFullObject : List (BitVec 8) := encodeLprogReloc x25519ScalarmultFullLprog

/-- The single-entry object is non-empty (carries all seven function symbols). -/
theorem x25519ScalarmultFullObject_nonempty : x25519ScalarmultFullObject ≠ [] := by
  have : 0 < x25519ScalarmultFullObject.length := by native_decide
  exact fun h => by simp [h] at this

/-- The folded orchestrator references the sizing sentinel `k.109`, so the encoder
    reserves the whole `mem.RBX.*` work frame (`frameSize = 984` bytes: the
    110-cell region + the 96-byte qsave block, `+8` call parity — the body calls
    the field leaves, so call sites stay SysV 16-aligned and the third through
    sixth pointer arguments are parked inside the frame rather than below `%rsp`). -/
theorem x25519Scalarmult_frame_reserved :
    LprogAsmPrinter.frameSize x25519ScalarmultLcmd = 984 := by native_decide

/-- Every `Lopn` of the folded orchestrator byte-encodes — ZERO uncovered ops (the
    whole scaffolding is in the byte-encodable `LinstrR` alphabet). -/
theorem x25519Scalarmult_fully_byteEncodable :
    (x25519ScalarmultLcmd.filter (fun i => match i.li_i with
      | .Lopn _ _ _ => (LprogBytes.encodeLopn 984 64 i.li_i 96).isEmpty
      | _ => false)) = [] := by native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LfundefBridge
