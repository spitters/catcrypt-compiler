/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-!
# Physical-path acceptance witness: data-dependent `while` export (`ComL.whileNz`)

This module is the acceptance witness for the physical byte-deployment path of a
**data-dependent `while`**, the control-flow shape handled by the front's
`translateDialectControl` `RWhileNz` arm. The abstract arm provides the
`whileNz` node; `JasminLprogExport` provides:

* the `ComL.whileNz` export node (the countdown loop `while (n != 0) { body; n -= 1 }`),
* its `ComL.denote` fold (the run-halting trip count = the countdown seed),
* the per-node lowering through the runtime counted loop `forLoopLcmdNRt`
  (`MOV`-seed the counter from the guard, zero-trip top guard
  `CMP Lctr,0 ; Lcond Z → end`, one body copy, bottom-test back-edge
  `CMP Lctr,0 ; Lcond NZ → top`, end label),
* the `comLToBody` / `comLRetReg` / `ComL.loopArgBaseNames` arms, so the full
  `ComL.toLprog{Phys,PhysAbi}` export reaches bytes through the node.

This file exercises a concrete countdown `while (n != 0) { acc := acc·acc; n -= 1 }`
end-to-end: it denotes to the expected fold (the empty fold at `n = 0`), its
lowered body carries the zero-trip skip and the back-edge, the trip counter is
seeded from a runtime register (not an immediate), the body is emitted **once**
(rolled, not unrolled), and the physical two-address export produces a single
function.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.WhileExportValidate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-- The countdown-while body `acc := acc · acc` over the `JLoopBodyN`-shaped
    context `[accTy = reg 64, idx = reg 64]` (invTys = `[]`; the loop index is
    unused by this scalar body). The `MUL:64` op is distinct from the loop
    scaffolding's `ADD Lidx` / `SUB Lctr`, so the one-body-copy check reads
    cleanly. -/
def whileNzBody : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil))) (.ret .here)

/-- A **data-dependent countdown loop** `while (n != 0) { acc := acc·acc; n -= 1 }`:
    seed `acc` from arg `.here`, run `whileNzBody` a **runtime** number of times
    read from the in-scope countdown seed `.there .here`, return the accumulator.
    invTys = `[]`. Structurally identical to `loopSmokeRtProg` with `.forLoopNRt`
    replaced by `.whileNz`. -/
def loopSmokeNzProg : ComL [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .whileNz whileNzBody (.there .here) .here .nil (.ret .here)

/-- **Denote = spec:** seed `3`, countdown `2` → `whileNzBody` (squaring) runs
    twice, `3 → 9 → 81`. The fold runs `(guard.lookup V).toNat = 2` times. -/
theorem loopSmokeNzProg_denote :
    ComL.denote loopSmokeNzProg (.cons (3 : BitVec 64) (.cons (2 : BitVec 64) .nil))
      = (81 : BitVec 64) := by rfl

/-- **Denote = spec (different countdown):** seed `2`, countdown `3` →
    `2 → 4 → 16 → 256`. The trip count is read from the valuation. -/
theorem loopSmokeNzProg_denote_count3 :
    ComL.denote loopSmokeNzProg (.cons (2 : BitVec 64) (.cons (3 : BitVec 64) .nil))
      = (256 : BitVec 64) := by rfl

/-- The lowered SSA body of `loopSmokeNzProg` (top-level, `nArgs = 2`). -/
def loopSmokeNzBody : Lcmd := comLToBody 2 argName (fun _ => none) loopSmokeNzProg 2

/-- **Real back-edge:** the data-dependent while lowers to a conditional jump
    (`Lcond`, rendered `jne .L<d>`) — a rolled loop, not an unrolled chain. -/
theorem loopSmokeNzBody_has_backedge :
    loopSmokeNzBody.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)
      = true := by decide

/-- **Zero-trip guard and back-edge.** Exactly two conditional jumps: the
    `Lcond Z` skip of the zero-trip top guard and the `Lcond NZ` bottom-test
    back-edge, the runtime counted loop's frame. -/
theorem loopSmokeNzBody_two_lcond :
    (loopSmokeNzBody.filter
      (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)).length = 2 := by decide

/-- The conditional jumps are, in order, the `Z` skip and the `NZ` back-edge. -/
theorem loopSmokeNzBody_lcond_codes :
    loopSmokeNzBody.filterMap (fun i => match i.li_i with
      | .Lcond (.reg cc) _ => some cc | _ => none) = ["Z", "NZ"] := by decide

/-- **Runtime countdown seed:** the trip counter `Lctr2` is initialised from a
    **register** (the resolved guard argument `a0`), i.e. `MOV Lctr2, a0` — NOT
    `MOV Lctr2, #n`. The trip count is data-dependent, fixed only at run time. -/
theorem loopSmokeNzBody_runtime_guard_seed :
    loopSmokeNzBody.any (fun i => match i.li_i with
      | .Lopn dsts mnem srcs =>
          mnem == withWidthTag 64 "MOV" &&
          (dsts.filterMap LOperand.regName?).contains (loopCtr 2) &&
          (srcs.filterMap LOperand.regName?).contains (argName 0)
      | _ => false) = true := by decide

/-- **One body copy, not `count`:** the squaring op `MUL:64` appears exactly once
    — the loop is rolled (one copy + back-edge), independent of the trip count. -/
theorem loopSmokeNzBody_one_body_copy :
    (loopSmokeNzBody.filter
      (fun i => match i.li_i with | .Lopn _ m _ => m == "MUL:64" | _ => false)).length
      = 1 := by decide

/-- The lowered body still ends with `Lret`. -/
theorem loopSmokeNzBody_ends_Lret :
    loopSmokeNzBody.getLast?.map Linstr.li_i = some .Lret := rfl

/-! ### The per-node emission is the runtime counted-loop frame

`comLToBody`'s `whileNz` arm splices `forLoopLcmdNRt` with the counter seeded from
the guard: a 3-instruction seed prefix (`MOV acc,init ; MOV idx,0 ; MOV ctr,guard`),
the zero-trip guard `CMP ctr,0 ; Lcond Z → end`, `Llabel top ; body ;
guard-advance ; CMP ctr,0 ; Lcond NZ → top`, and the end label. -/

/-- The raw per-node emission for this program's node (depth 2, accumulator
    `regName 2`, init operand `a1`, runtime guard `a0`, invTys = `[]`). This is
    the exact `Lcmd` `comLToBody`'s `whileNz` arm splices. -/
def whileNzRaw : Lcmd :=
  forLoopLcmdNRt 2 (regName 2) (.reg (argName 1)) (.reg (argName 0)) whileNzBody []
    (fun _ => none)

/-- **Zero-trip guard:** after the 3-instruction seed, the emission tests the
    counter and jumps to the end label when it is zero, then opens the loop
    region with `Llabel internal top`. -/
theorem whileNzRaw_zero_trip_guard :
    (whileNzRaw.drop 3).take 3 =
      [ ⟨0, .Lopn [.reg (loopCtr 2)] (withWidthTag 64 "CMP") [.reg (loopCtr 2), .imm 0]⟩
      , ⟨0, .Lcond (.reg "Z") (2 + 0x40000000)⟩
      , ⟨0, .Llabel .internal 2⟩ ] := rfl

/-- **Back-edge and end label:** the last three instructions are
    `CMP Lctr2, 0 ; Lcond NZ → top ; Llabel end`. -/
theorem whileNzRaw_control_tail :
    whileNzRaw.drop (whileNzRaw.length - 3) =
      [ ⟨0, .Lopn [.reg (loopCtr 2)] (withWidthTag 64 "CMP") [.reg (loopCtr 2), .imm 0]⟩
      , ⟨0, .Lcond (.reg "NZ") 2⟩
      , ⟨0, .Llabel .internal (2 + 0x40000000)⟩ ] := rfl

/-! ### Physical two-address export (the byte-deployment gate) -/

/-- **Physical export builds (acceptance gate):** the data-dependent-while program
    exports to a single physical-register two-address `Lprog` function through the
    new node — the loop-aware backend reaches bytes. -/
theorem loopSmokeNz_export_one_func :
    (ComL.toLprogPhys loopSmokeNzProg "count_while").lp_funcs.length = 1 := by rfl

/-- The exported program has a function (the `head?` acceptance gate). -/
theorem loopSmokeNz_export_head_isSome :
    (ComL.toLprogPhys loopSmokeNzProg "count_while").lp_funcs.head?.isSome = true := by rfl

/-- The physically-allocated do-while body (real x86 registers, one body copy, a
    real `jne .L2` back-edge). Defined here for downstream `.s`-render / byte-KAT
    use; the deep register-file / byte checks (physical RA + native-decide KAT)
    are out of the LSP-safe scope and left ORCHESTRATOR-VERIFY. -/
def loopSmokeNzPhysBody : Lcmd := (ComL.toLfundefPhys loopSmokeNzProg).lfd_body

end CatCrypt.Crypto.SecureCompilation.VIR.WhileExportValidate
