/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
import CatCrypt.Crypto.SecureCompilation.X86Backend.Mul48ProvenEmit

/-!
# Phase 1 — the generic emit driver

Every proven kernel's `emitMain` repeats the same chain: spill-allocate the
straight-line block, render each instruction through its `SpillView`, and wrap
the body in a System-V leaf (callee-saved saves, a frame-base `leaq`, argument
marshalling, restore + `ret`). This module factors that chain into ONE function

    genericLeafAsm sym args pins prologueClears frameBytes block : String

that emits **any** straight-line `List (JInstr 64)` to a `.s` leaf — no
per-kernel boilerplate. It is the connective piece between `cargo hax into lean`
(which lowers to a `Com`/straight-line block) and the backend `.s`, so the
`catcrypt-emit` CLI can run on extracted code rather than hand-written drivers.

`genericLeafAsmCT` gates emit on the Phase-0 `CompilableCT` contract: a block
outside the constant-time subset is rejected (`Except`) rather than emitted, so
the CLI never ships unverified-for-CT assembly.

The chain is the exact factoring of `Curve4MontMulProvenEmit.provenAsm` /
`Mul48ProvenEmit.mul48ProvenAsm`; the §3 self-test re-emits `bignum_mul_4_8`
through it and the GMP KAT confirms byte-correctness.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GenericEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. The factored spill-allocate + render chain -/

/-- The dedicated frame-base register name, pinned to `%rbp` (the spill window). -/
def frameBaseName : String := "fp"

/-- The frame-base pin shared by every emitted leaf. -/
def framePins : GpAlloc := [(frameBaseName, "%rbp")]

/-- The register-resident allocation: the caller's `pins` plus every name the
    pin-aware linear scan keeps in a register. -/
def residentOf (pins : GpAlloc) (block : List (JInstr 64)) : GpAlloc :=
  pins ++ (blockNames block).filterMap (fun n =>
    match (spillAllocPinned pins 0 block).lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- The spill-slot offset of a non-pinned name (`none` if pinned/resident). -/
def spilledOf (pins : GpAlloc) (block : List (JInstr 64)) (n : String) : Option Int :=
  if (pins.map Prod.fst).contains n then none
  else spillSlotOf (spillAllocPinned pins 0 block) n

/-- The `SpillView` for one instruction: the resident map (frame pin + caller
    pins + linear-scan residents) plus this instruction's spilled read/write
    operands. -/
def viewOf (pins : GpAlloc) (block : List (JInstr 64)) (i : JInstr 64) : SpillView where
  resident := framePins ++ residentOf pins block
  frameBase := frameBaseName
  spilledReads := (readNames i).filterMap (fun n =>
    (spilledOf pins block n).map (fun off => (n, off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (spilledOf pins block n).map (fun off => (n, off)))

/-- The spill-materialised body lines for the whole block. -/
def bodyLinesOf (pins : GpAlloc) (block : List (JInstr 64)) : List String :=
  block.flatMap (fun i => renderJInstrSpilled (viewOf pins block i) i)

/-! ## 2. The generic leaf emitter -/

/-- The standard System-V callee-saved prologue saves, in order. -/
def calleeSaves : List String :=
  [ "\tpushq %rbp", "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13"
  , "\tpushq %r14", "\tpushq %r15" ]

/-- The matching epilogue restores + `ret`. -/
def calleeRestores : List String :=
  [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
  , "\tpopq %rbx", "\tpopq %rbp", "\tret" ]

/-- **The generic emit driver.** Emit a straight-line block to a System-V `.s`
    leaf `sym`:

    * `args` — the pointer/integer arguments (their home registers are marshalled
      into the body's register names);
    * `pins` — the caller's fixed register assignments (ABI arg homes, the MULX
      `%rdx` funnel, the ADX zero register, scratch destinations, …);
    * `prologueClears` — extra prologue instructions (e.g. `xorq %rbx, %rbx` to
      zero the ADX zero register), run after the frame `leaq`, before marshalling;
    * `frameBytes` — the spill-window size below `%rsp` (`leaq -frameBytes(%rsp)`);
    * `block` — the straight-line `List (JInstr 64)` body.

    Factors `Mul48ProvenEmit`/`Curve4MontMulProvenEmit`'s per-kernel asm. -/
def genericLeafAsm (sym : String) (args : List AbiArg) (pins : GpAlloc)
    (prologueClears : List String) (frameBytes : Nat)
    (block : List (JInstr 64)) : String :=
  let resident := framePins ++ residentOf pins block
  let argMoves := argMarshalMoves resident args
  let prologue :=
    calleeSaves
      ++ [ "\tleaq -" ++ toString frameBytes ++ "(%rsp), %rbp" ]
      ++ prologueClears
      ++ argMoves
  renderLeafFn sym prologue (bodyLinesOf pins block) calleeRestores

/-- **CT-gated generic emit (Phase 0 + Phase 1).** Emit only if `block` is in the
    `CompilableCT` constant-time subset; otherwise reject with the violation
    message. The CLI calls this so out-of-subset blocks are never shipped. -/
def genericLeafAsmCT (sym : String) (args : List AbiArg) (pins : GpAlloc)
    (prologueClears : List String) (frameBytes : Nat)
    (block : List (JInstr 64)) : Except String String :=
  match checkCompilableCT block with
  | .ok b => .ok (genericLeafAsm sym args pins prologueClears frameBytes b)
  | .error e => .error e

/-! ## 3. Self-test: re-emit `bignum_mul_4_8` through the generic driver

`Mul48ProvenEmit` ships `bignum_mul_4_8` via a hand-written `emitMain`. Here the
SAME block/pins/args go through `genericLeafAsm`; the emit driver below writes it
and the existing GMP KAT (`bench/s2n_montmul_compare/mul48_proven_kat.c`)
confirms the generic path is byte-correct. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Mul48ProvenEmit in
/-- `bignum_mul_4_8` re-emitted through the generic driver (same symbol as the
    hand-written kernel, so the existing KAT links). -/
def bignum_mul_4_8_generic : String :=
  genericLeafAsm "bignum_mul_4_8_proven" mul48ProvenArgs mul48ProvenPins
    [ "\txorq %rbx, %rbx" ] 1024 mul48ProvenBlockLegal

/-- Emit driver for the generic-path `bignum_mul_4_8`. Run via
    `lake env lean --run` (or `catcrypt-emit emit`). -/
def emitMainGenericMul48 : IO Unit := do
  IO.FS.createDirAll "bench/s2n_montmul_compare/gen_com"
  IO.FS.writeFile
    "bench/s2n_montmul_compare/gen_com/bignum_mul_4_8_generic.s" bignum_mul_4_8_generic
  IO.println "wrote gen_com/bignum_mul_4_8_generic.s (via the generic emit driver)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.GenericEmit
