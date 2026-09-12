/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline

/-!
# The owned x86 optimizer wired onto the gather, on one kernel body

`X86ComPipeline.optimizeX86Block` is the composed owned-x86 optimizer
(store-to-load forwarding, identity-move drop, redundant-reload elimination,
guarded MUL→MULX fusion) and carries the unconditional translation-validation
certificate `optimizeX86Block_runBlock`. `GatherImmForms.gatherJBlock6` maps an
`Lcmd = List Linstr` body onto the `List (JInstr 64)` the optimizer runs on, and
`GatherLsemTie.gatherJBlock6_optimized_lsem_agree` certifies that on a body whose
every instruction is `tiedInstr`, the optimized gathered block's `runBlock`
register file is the one the source body's `lsemStraight` reaches.

This module composes those on a concrete body, so the optimizer runs on the emit
object with the full source-to-optimized-block certificate, and measures the
instruction-count change the optimizer produces.

## Main results

* `selfMoveTiedBody_optimized_lsem_agree` — the source-to-optimized-block tie on
  `selfMoveTiedBody`, a fully-`tiedInstr` body containing one redundant register
  self-move. The optimized gathered block register-corresponds to the body's
  `lsemStraight` final state.
* `demoBody_optimized_lsem_agree` — the same tie on `GatherLsemTie.demoBody`, the
  exporter-shape register-resident body, restated at this module.
* `gatherOptReduction` — the gathered-then-optimized instruction-count drop of a
  body, with `#guard` measurements: `0` on the register-resident `demoBody`, `1`
  on `selfMoveTiedBody`.

## What the measurement shows and what it does not

The `tiedInstr` fragment is register-only: two-address `ADD/SUB/MUL/AND/OR/XOR:64`
and `MOV:64` over registers and immediates, with no spill-slot `MOVQ` and no
`LOAD`/`STORE`. A body all of whose instructions are tied is therefore
register-resident, and store-to-load forwarding and redundant-reload elimination
find nothing to remove on it — the reduction is `0` on `demoBody`. The one drop
the optimizer makes inside the tied fragment is the identity-move drop, which
removes a `mov r, r`; `selfMoveTiedBody` carries such a move and the optimizer
deletes it, so its reduction is `1`, with the tie preserved.

The reload pairs the roadmap measures (adjacent `movq %R, N(%rsp)` /
`movq N(%rsp), %R`, 8–19% of instructions on the register-pressured kernels) are
spill-slot `MOVQ` / `LOAD` / `STORE` forms, which `tiedInstr` excludes. On those
bodies `gatherJBlock6` still succeeds and `optimizeX86Block_runBlock` still
certifies the optimizer at the block level, but the gather-faithfulness arm that
carries the block result back to the source `Lcmd` (`LJCorr` over
`gatherJBlock6_lsem_agree`) is stated only over the tied fragment. Realizing the
measured reload reduction with the full source-to-optimized certificate needs the
`LOAD`/`STORE`/`MOVQ` gather-and-tie arms (each with its `LprogBytes.encodeLopn`
byte-agreement), not a change here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedEmitWiring

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline (optimizeX86Block)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie
  (LJCorr tiedBody tiedBody_mem gatherJBlock6_optimized_lsem_agree demoBody demoBody_tied)

/-! ## 1. The chosen body

`secp256k1_femul` gathers whole per the census, but it carries `ADC`/`MULX` and
spill-slot `MOVQ` instructions, so it is not `tiedInstr`. The tie applies to the
register-resident exporter-shape body `GatherLsemTie.demoBody` and to
`selfMoveTiedBody` below, which adds one redundant register self-move to the same
shape so the optimizer has an instruction to remove while every instruction stays
tied. -/

/-- A `tiedInstr` body in the exporter's destructive two-address shape with one
    redundant register self-move: `RAX := RDI`, `RCX := RSI`, `RAX ^= RCX`,
    `RAX := RAX`, `RAX += RCX`. The self-move is the identity-move-drop's target. -/
def selfMoveTiedBody : List Linstr :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RDI"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "MOV:64" [.reg "RSI"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "XOR:64" [.reg "RAX", .reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .reg "RCX"]⟩ ]

/-- Every instruction of `selfMoveTiedBody` is tied. -/
theorem selfMoveTiedBody_tied : tiedBody selfMoveTiedBody = true := by decide

/-! ## 2. The optimizer runs on the emit object with the source certificate -/

/-- **The tie on `selfMoveTiedBody`.** The gather succeeds, the body's
    `lsemStraight` runs to completion from any corresponding `Lstate`, and the
    register file of the optimized gathered block corresponds to it. Composing the
    gather-faithfulness tie with the optimizer's translation validation, this is
    the certificate that running `optimizeX86Block` on the emit object preserves
    the source body's meaning. -/
theorem selfMoveTiedBody_optimized_lsem_agree {ls : Lstate 64} {s : JState 64}
    (hc : LJCorr ls s) :
    ∃ g ls', gatherJBlock6 selfMoveTiedBody = some g ∧
      lsemStraight (selfMoveTiedBody.map (·.li_i)) ls = some ls' ∧
      LJCorr ls' (runBlock s (optimizeX86Block g)) :=
  gatherJBlock6_optimized_lsem_agree selfMoveTiedBody
    (tiedBody_mem selfMoveTiedBody_tied) hc

/-- **The tie on the register-resident `demoBody`**, restated at this module as
    the register-resident representative alongside `selfMoveTiedBody`. -/
theorem demoBody_optimized_lsem_agree {ls : Lstate 64} {s : JState 64}
    (hc : LJCorr ls s) :
    ∃ g ls', gatherJBlock6 demoBody = some g ∧
      lsemStraight (demoBody.map (·.li_i)) ls = some ls' ∧
      LJCorr ls' (runBlock s (optimizeX86Block g)) :=
  gatherJBlock6_optimized_lsem_agree demoBody (tiedBody_mem demoBody_tied) hc

/-! ## 3. The instruction-count payoff -/

/-- The number of instructions the optimizer removes from the gathered block of a
    body, or `none` when the body does not gather. -/
def gatherOptReduction (body : List Linstr) : Option Nat :=
  (gatherJBlock6 body).map (fun g => g.length - (optimizeX86Block g).length)

/-- The gathered length of a body, for reading the block size alongside the drop. -/
def gatheredLength (body : List Linstr) : Option Nat :=
  (gatherJBlock6 body).map (·.length)

-- The register-resident body: five instructions gather, and the optimizer is
-- inert on the register-resident tied fragment.
#guard gatheredLength demoBody = some 5
#guard gatherOptReduction demoBody = some 0

-- The self-move body: five instructions gather, and the identity-move drop
-- removes one, so the optimized block is four instructions long.
#guard gatheredLength selfMoveTiedBody = some 5
#guard gatherOptReduction selfMoveTiedBody = some 1

end CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedEmitWiring
