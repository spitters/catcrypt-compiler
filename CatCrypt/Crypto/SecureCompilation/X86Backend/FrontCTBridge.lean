/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTMachine
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow

/-!
# From the index-free `Com` fragment to direct addressing in the exported `Lprog`

`JasminCTByConstruction.ComJasminCTByConstruction` is the index-free fragment of
`Com jasminDialect`: no binding uses `stackLoad` / `stackStore`.
`AllocCTPreservation.lcmdDirect` is the corresponding class one level down: no
operand of the exported `Lcmd` is the register-indexed (SIB) form
`LOperand.arrIdx`.

`comToLfundef_lcmdDirect` connects them: the virtual body `comToLfundef` emits for
an index-free `Com` carries no `arrIdx` operand. The two sources of an operand in
that body are `resolveVar` — which returns a register or an immediate for every
argument slot and every let binding, whatever the `ImmSlotMap` says — and the
`opToLinstrR` arms for `stackLoad` / `stackStore`, which are the only arms that
build an `arrIdx` and are exactly the ops the fragment excludes.

Composing with `CompileFromHaxScope.compileFromHax_ct` discharges the `lcmdDirect`
hypothesis of the deployed export for every kernel the compile-from-hax front
produces, which makes the speculative results unconditional on that front's output:
`compileFromHax_speculative_ct` (store bypass, Spectre-v4) and
`compileFromHax_cfSpec_state_independent` / `compileFromHax_cfSpec_mem_addr_in_program`
(branch misprediction, Spectre-v1).

## Scope

`comToLfundef_lcmdDirect` is about the `Com` walk `comToBody`. A body built by one
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

/-! ## 1. Every operand the `Com` walk resolves is a register or an immediate -/

/-- A variable resolves to a register or an immediate, never to an indexed
    element. -/
theorem resolveVar_not_indexed (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    isIndexed (resolveVar curDepth nArgs argNames immSlotMap v) = false := by
  unfold resolveVar
  dsimp only
  split
  · split <;> rfl
  · rfl

/-- Every operand of a resolved variable vector is a register or an immediate. -/
theorem exprArgs_go_not_indexed (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ exprArgs.go curDepth nArgs argNames immSlotMap hv, isIndexed o = false
  | [], _ => by intro o ho; simp [exprArgs.go] at ho
  | _ :: _, .cons v rest => by
      intro o ho
      rw [exprArgs.go, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact resolveVar_not_indexed _ _ _ _ v
      · exact exprArgs_go_not_indexed curDepth nArgs argNames immSlotMap rest o ho

/-- Every source operand of a binding is a register or an immediate. -/
theorem exprArgs_not_indexed (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) :
    ∀ o ∈ exprArgs curDepth nArgs argNames immSlotMap e, isIndexed o = false :=
  exprArgs_go_not_indexed curDepth nArgs argNames immSlotMap e.args

/-! ## 2. The op-level bridge -/

/-- An op that is not an addressing surface exports to an instruction with no
    register-indexed operand, given sources that have none. `stackLoad` and
    `stackStore` are the only arms of `opToLinstrR` that build an `arrIdx`. -/
theorem opToLinstrR_direct {op : JasminOp} {dst : String} {srcs : List LOperand}
    (hop : jasminOpAddrSurface op = false)
    (hs : ∀ o ∈ srcs, isIndexed o = false) :
    linstrRDirect (opToLinstrR op dst srcs) = true := by
  cases op with
  | stackLoad w n => simp [jasminOpAddrSurface] at hop
  | stackStore w n => simp [jasminOpAddrSurface] at hop
  | extCall name argTys retTy =>
      unfold opToLinstrR
      dsimp only
      split
      · exact linstrRDirect_Lopn_mk (by simp) (by simp)
      · split <;> exact linstrRDirect_Lopn_mk (by simp) hs
  | callN name argTys retTys =>
      unfold opToLinstrR
      dsimp only
      split <;> exact linstrRDirect_Lopn_mk (by simp) hs
  | castW w w' =>
      unfold opToLinstrR
      dsimp only
      split <;> exact linstrRDirect_Lopn_mk (by simp) hs
  | regConst w n => exact linstrRDirect_Lopn_mk (by simp) (by simp)
  | stackZero w n => exact linstrRDirect_Lopn_mk (by simp) (by simp)
  | stackStoreImm w n i =>
      refine linstrRDirect_Lopn_mk (by simp) (fun o ho => ?_)
      rcases List.mem_append.mp ho with h | h
      · exact hs o h
      · rw [List.mem_singleton.mp h]; rfl
  | cmpImm c w n =>
      refine linstrRDirect_Lopn_mk (by simp) (fun o ho => ?_)
      rcases List.mem_append.mp ho with h | h
      · exact hs o h
      · rw [List.mem_singleton.mp h]; rfl
  | _ => exact linstrRDirect_Lopn_mk (by simp) hs

/-! ## 3. The body walk -/

/-- The body `comToBody` emits for an index-free `Com` uses no register-indexed
    operand. -/
theorem comToBody_lcmdDirect (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
      (curDepth : Nat), ComJasminCTByConstruction c →
      lcmdDirect (comToBody nArgs argNames immSlotMap c curDepth) = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, curDepth, h => by
      rw [comToBody]
      refine lcmdDirect_of_mem ?_
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact opToLinstrR_direct h.1 (exprArgs_not_indexed _ _ _ _ e)
      · exact (lcmdDirect_iff _).mp
          (comToBody_lcmdDirect nArgs argNames immSlotMap body (curDepth + 1) h.2) z hz

/-- **The index-free fragment exports to direct addressing.** The virtual body of
    the `Lfundef` a `Com` in the index-free fragment lowers to carries no
    register-indexed (SIB) operand, which is the hypothesis the deployed
    register allocator's preservation theorem takes. -/
theorem comToLfundef_lcmdDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (immSlotMap : ImmSlotMap)
    (h : ComJasminCTByConstruction com) :
    lcmdDirect (comToLfundef com immSlotMap).lfd_body = true :=
  comToBody_lcmdDirect _ _ _ com _ h

/-- The `lcmdDirect` hypothesis for a `Com` the compile-from-hax front emits. -/
theorem compileFromHax_lcmdDirect {w nIn : Nat} {params : List String} {e : ImpExpr}
    {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (hc : compileFromHax (w := w) (nIn := nIn) params e = some c)
    (immSlotMap : ImmSlotMap) :
    lcmdDirect (comToLfundef c immSlotMap).lfd_body = true :=
  comToLfundef_lcmdDirect c immSlotMap (compileFromHax_ct hc)

/-! ## 4. The deployed export on front-compiled kernels -/

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
