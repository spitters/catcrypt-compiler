/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTMachine
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow

/-!
# Direct addressing and speculative constant time for compile-from-hax kernels

`ComToLfundefDirect.comToLfundef_lcmdDirect` shows that the virtual body
`comToLfundef` emits for a `Com` in the index-free fragment
`JasminCTByConstruction.ComJasminCTByConstruction` carries no register-indexed
(`LOperand.arrIdx`) operand, the class `AllocCTPreservation.lcmdDirect`.

Composing it with `CompileFromHaxScope.compileFromHax_ct` discharges the `lcmdDirect`
hypothesis of the deployed export for every kernel the compile-from-hax front
produces, which makes the speculative results unconditional on that front's output:
`compileFromHax_speculative_ct` (store bypass, Spectre-v4) and
`compileFromHax_cfSpec_state_independent` / `compileFromHax_cfSpec_mem_addr_in_program`
(branch misprediction, Spectre-v1).

## Scope

`ComToLfundefDirect.comToLfundef_lcmdDirect` is about the `Com` walk `comToBody`. A body built by one
of the loop exporters (`forLoopLcmdN` and its relatives) is outside it, as is a
`Com` binding `stackLoad` / `stackStore` — the fragment excludes exactly those two
ops, and the export does turn them into `arrIdx`.

The end-to-end statements keep the gather hypothesis `gatherJBlock6 … = some g`:
they are about the block the gather produces, and a body carrying a control
transfer does not gather.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FrontCTBridge

open _root_.Hax (ImpExpr)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (MLeak OwnedCF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTMachine
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect (comToLfundef_lcmdDirect)

/-! ## 1. The `lcmdDirect` hypothesis on front-compiled kernels -/

/-- The `lcmdDirect` hypothesis for a `Com` the compile-from-hax front emits. -/
theorem compileFromHax_lcmdDirect {w nIn : Nat} {params : List String} {e : ImpExpr}
    {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (hc : compileFromHax (w := w) (nIn := nIn) params e = some c)
    (immSlotMap : ImmSlotMap) :
    lcmdDirect (comToLfundef c immSlotMap).lfd_body = true :=
  comToLfundef_lcmdDirect c immSlotMap (compileFromHax_ct hc)

/-! ## 2. The deployed export on front-compiled kernels -/

/-- **The store-bypass (Spectre-v4) statement for the compile-from-hax front.**
    For every kernel the front compiles, the block the deployed allocator emits
    has the same speculative leakage trace from any two speculative states, for
    every window and every store-bypass predictor. -/
theorem compileFromHax_speculative_ct {w nIn : Nat} {params : List String}
    {e : ImpExpr} {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (hc : compileFromHax (w := w) (nIn := nIn) params e = some c)
    (fname : String) (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap) (abiArgs : List String)
    (abiTyin : List Nat) (residence : Option (Array Nat)) (abiW : Nat)
    (forceLivePin : Bool) {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi c fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (O : BypassOracle 64) (σ₁ σ₂ : SpecState 64) :
    specBlockLeak O σ₁ g = specBlockLeak O σ₂ g :=
  toLprogPhysAbi_gather_speculative_ct c fname shiftImm immSlotMap inLoadMap
    outStoreMap abiArgs abiTyin residence abiW forceLivePin
    (compileFromHax_lcmdDirect hc immSlotMap) hf hg O σ₁ σ₂

/-- **The branch-misprediction (Spectre-v1) leakage-equality statement for the
    compile-from-hax front.** For every kernel the front compiles, the gathered
    straight-line block the deployed allocator emits has the same speculative
    leakage trace from any two machine states, for every branch predictor and
    every speculation window. -/
theorem compileFromHax_cfSpec_state_independent {w nIn : Nat} {params : List String}
    {e : ImpExpr} {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (hc : compileFromHax (w := w) (nIn := nIn) params e = some c)
    (fname : String) (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap) (abiArgs : List String)
    (abiTyin : List Nat) (residence : Option (Array Nat)) (abiW : Nat)
    (forceLivePin : Bool) {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi c fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (window : Nat) (P : CFPredictor 64) (s₁ s₂ : JState 64) :
    (cfSpecExec window P s₁ (.straight g)).1
      = (cfSpecExec window P s₂ (.straight g)).1 :=
  toLprogPhysAbi_gather_cfSpec_state_independent c fname shiftImm immSlotMap
    inLoadMap outStoreMap abiArgs abiTyin residence abiW forceLivePin
    (compileFromHax_lcmdDirect hc immSlotMap) hf hg window P s₁ s₂

/-- **The predictor-free (Spectre-v1) containment statement for the
    compile-from-hax front.** For every kernel the front compiles, every memory
    event of the speculative trace of the gathered block — transient events
    included — names an address that occurs in the program text, for every branch
    predictor, every window and every state. -/
theorem compileFromHax_cfSpec_mem_addr_in_program {w nIn : Nat}
    {params : List String} {e : ImpExpr}
    {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (hc : compileFromHax (w := w) (nIn := nIn) params e = some c)
    (fname : String) (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap) (abiArgs : List String)
    (abiTyin : List Nat) (residence : Option (Array Nat)) (abiW : Nat)
    (forceLivePin : Bool) {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi c fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (window : Nat) (P : CFPredictor 64) (s : JState 64) (base : String) (off : Int)
    (hmem : SLeak.arch (MLeak.mem base off)
      ∈ (cfSpecExec window P s (.straight g)).1) :
    MLeak.mem base off ∈ cfAddrs (OwnedCF.straight g) :=
  cfSpecExec_mem_addr_in_program window P (.straight g)
    (toLprogPhysAbi_gather_cfAllDirect c fname shiftImm immSlotMap inLoadMap
      outStoreMap abiArgs abiTyin residence abiW forceLivePin
      (compileFromHax_lcmdDirect hc immSlotMap) hf hg) s base off hmem

end CatCrypt.Crypto.SecureCompilation.X86Backend.FrontCTBridge
