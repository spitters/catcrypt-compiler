/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-!
# Direct addressing in the bodies the loop exporters emit

`ComToLfundefDirect.comToLfundef_lcmdDirect` covers the straight-line walk `comToBody`.
This module covers the loop exporters of `VIR.JasminLprogExport` — `forLoopLcmd`,
`forLoopLcmdN`, `forLoopLcmdNCall`, `forLoopLcmdNRt`, `forLoopLcmdNRtNested`,
`whileLcmdNz`, `blockLoopFrame`, `forLoopBlockLcmd` — together with
`LprogControlFlow.loopLcmd`, the loop-aware body walk `comLToBody`, and the
deployed looped export `ComL.toLfundefPhysAbi` / `ComL.toLprogPhysAbi`.

Each exporter emits a back-edge frame around one copy of a walked body. The frame
instructions — accumulator seed, index init, counter seed, zero-trip guard, label,
index advance, counter decrement, invariant-base touches, compare, conditional
back-edge — take register and immediate operands only, so the frame is
`AllocCTPreservation.lcmdDirect` whatever the body is, given seed and trip-count
operands that are themselves registers or immediates. The body copy is direct
exactly when the `Com` it walks is in
`JasminCTByConstruction.ComJasminCTByConstruction`: the loop-body variable
resolvers (`loopResolveVar`, `loopResolveVarN`, `nestCountResolveVar`) return a
register or an immediate for every binder role — accumulator, loop index,
invariant base, body temporary — and the `stackLoad` / `stackStore` arms of
`opToLinstrR` remain the only ones that build an `LOperand.arrIdx`.

`ComLIndexFree` lifts the fragment to `ComL`: straight-line binders are index-free
and every loop node's body `Com` is in `ComJasminCTByConstruction`. It carries
through `comLToBody`, `ComL.toLfundef` and the ABI wrapping of
`ComL.toLfundefPhysAbi`, giving `ComL_toLprogPhysAbi_lcmdDirect`.

## Scope

A loop body that indexes an array at the loop index binds `stackLoad` /
`stackStore` and so lies outside the fragment; `stackLoad_export_not_direct` and
`stackStore_export_not_direct` record that the export of those two ops is indeed
register-indexed.

The statements here stop at `lcmdDirect` of the exported body. The speculative
results of `FrontCTBridge` are phrased over the straight-line block
`gatherJBlock6` produces, and `gatherJBlock6` lowers through `lowerCov6`, which
has no arm for `LinstrR.Llabel`, `LinstrR.Lcond` or `LinstrR.Lcall`. Every loop
frame emits a label and a conditional back-edge, so that gather returns `none` on
a loop-exported body and the block-shaped speculative statements do not apply to
it. Carrying them across a back-edge needs a control-flow-aware gather into
`MachineConstantTime.OwnedCF`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoopExporterCTBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect
open _root_.Hax (ImpExpr)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope
open CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-- The accumulator-feedback move a loop frame appends after the body copy uses
    register operands only. -/
theorem feedback_lcmdDirect (accReg retReg : String) :
    lcmdDirect (if retReg == accReg then []
      else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]) = true := by
  split <;> rfl

/-- The invariant-base touches a loop frame appends at the loop tail use register
    operands only. -/
theorem invTouch_lcmdDirect (ctr : String) (invRegs : List String) :
    lcmdDirect (invRegs.map (fun r =>
      ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)) = true := by
  refine lcmdDirect_of_mem ?_
  intro z hz
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hz
  rfl

/-- A single-source move into a register is direct when its source operand is. -/
theorem movOperand_direct (dst mnem : String) (op : LOperand)
    (h : isIndexed op = false) :
    linstrRDirect (.Lopn [.reg dst] mnem [op]) = true :=
  linstrRDirect_Lopn_mk (by simp [isIndexed]) (by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact h)

/-- The bottom-tested multi-binder back-edge frame around a body copy `w.1` with
    result register `w.2`: seed, index init, counter seed, label, body, feedback,
    index advance, counter decrement, invariant touches, compare and back-edge. -/
theorem frameN_lcmdDirect (accReg idxReg ctr : String) (initOp countOp : LOperand)
    (top : LLabel) (invRegs : List String) (w : Lcmd × String)
    (hinit : isIndexed initOp = false) (hcount : isIndexed countOp = false)
    (hbody : lcmdDirect w.1 = true) :
    lcmdDirect
      ([ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
       , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
       , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [countOp]⟩
       , ⟨0, .Llabel .internal top⟩ ]
       ++ w.1
       ++ (if w.2 == accReg then []
           else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg w.2]⟩])
       ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
          , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
       ++ invRegs.map (fun r =>
            ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
       ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
          , ⟨0, .Lcond (.reg "NZ") top⟩ ]) = true := by
  simp only [lcmdDirect_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, hbody⟩, feedback_lcmdDirect _ _⟩, rfl⟩, invTouch_lcmdDirect _ _⟩, rfl⟩
  refine lcmdDirect_of_mem ?_
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact movOperand_direct _ _ _ hinit
  · rfl
  · exact movOperand_direct _ _ _ hcount
  · rfl

/-! ## 2. Loop-body variables resolve to registers and immediates -/

/-- A single-binder loop-body variable resolves to a register or an immediate. -/
theorem loopResolveVar_not_indexed (d : Nat) (accReg : String) (curDepth : Nat)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    isIndexed (loopResolveVar d accReg curDepth immSlotMap v) = false := by
  unfold loopResolveVar
  dsimp only
  split
  · split <;> rfl
  · rfl

theorem loopExprArgs_go_not_indexed (d : Nat) (accReg : String) (curDepth : Nat)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ loopExprArgs.go d accReg curDepth immSlotMap hv, isIndexed o = false
  | [], _ => by intro o ho; simp [loopExprArgs.go] at ho
  | _ :: _, .cons v rest => by
      intro o ho
      rw [loopExprArgs.go, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact loopResolveVar_not_indexed _ _ _ _ v
      · exact loopExprArgs_go_not_indexed d accReg curDepth immSlotMap rest o ho

/-- Every operand of a single-binder loop-body expression is a register or an
    immediate. -/
theorem loopExprArgs_not_indexed (d : Nat) (accReg : String) (curDepth : Nat)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) :
    ∀ o ∈ loopExprArgs d accReg curDepth immSlotMap e, isIndexed o = false :=
  loopExprArgs_go_not_indexed d accReg curDepth immSlotMap e.args

/-- A multi-binder loop-body variable resolves to a register or an immediate:
    accumulator, loop index, invariant base and body temporary are all `.reg`. -/
theorem loopResolveVarN_not_indexed (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (curDepth : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    isIndexed (loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v) = false := by
  unfold loopResolveVarN
  dsimp only
  split
  · split <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem loopExprArgsN_go_not_indexed (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (curDepth : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ loopExprArgsN.go d accReg idxReg invRegs curDepth immSlotMap hv,
        isIndexed o = false
  | [], _ => by intro o ho; simp [loopExprArgsN.go] at ho
  | _ :: _, .cons v rest => by
      intro o ho
      rw [loopExprArgsN.go, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact loopResolveVarN_not_indexed _ _ _ _ _ _ v
      · exact loopExprArgsN_go_not_indexed d accReg idxReg invRegs curDepth immSlotMap
          rest o ho

/-- Every operand of a multi-binder loop-body expression is a register or an
    immediate. -/
theorem loopExprArgsN_not_indexed (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (curDepth : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    ∀ o ∈ loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e,
      isIndexed o = false :=
  loopExprArgsN_go_not_indexed d accReg idxReg invRegs curDepth immSlotMap e.args

/-- Every operand of a resolved invariant-seed vector is a register or an
    immediate. -/
theorem loopExprArgsHVN_not_indexed (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (curDepth : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} :
    ∀ {tys : Ctxt jasminDialect} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap hv,
        isIndexed o = false
  | [], _ => by intro o ho; simp [loopExprArgsHVN] at ho
  | _ :: _, .cons v rest => by
      intro o ho
      rw [loopExprArgsHVN, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact loopResolveVarN_not_indexed _ _ _ _ _ _ v
      · exact loopExprArgsHVN_not_indexed d accReg idxReg invRegs curDepth immSlotMap
          rest o ho

/-- An inner-count-body variable resolves to a register. -/
theorem nestCountResolveVar_not_indexed (d : Nat) (outerIdxReg : String)
    (invRegs : List String) (curDepth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    isIndexed (nestCountResolveVar d outerIdxReg invRegs curDepth v) = false := by
  unfold nestCountResolveVar
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem nestCountExprArgs_go_not_indexed (d : Nat) (outerIdxReg : String)
    (invRegs : List String) (curDepth : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ nestCountExprArgs.go d outerIdxReg invRegs curDepth hv, isIndexed o = false
  | [], _ => by intro o ho; simp [nestCountExprArgs.go] at ho
  | _ :: _, .cons v rest => by
      intro o ho
      rw [nestCountExprArgs.go, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact nestCountResolveVar_not_indexed _ _ _ _ v
      · exact nestCountExprArgs_go_not_indexed d outerIdxReg invRegs curDepth rest o ho

/-- Every operand of an inner-count-body expression is a register. -/
theorem nestCountExprArgs_not_indexed (d : Nat) (outerIdxReg : String)
    (invRegs : List String) (curDepth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) :
    ∀ o ∈ nestCountExprArgs d outerIdxReg invRegs curDepth e, isIndexed o = false :=
  nestCountExprArgs_go_not_indexed d outerIdxReg invRegs curDepth e.args

/-! ## 3. The loop-body walks -/

theorem lcmdDirect_append_of {a b : Lcmd} (ha : lcmdDirect a = true)
    (hb : lcmdDirect b = true) : lcmdDirect (a ++ b) = true := by
  simp [ha, hb]

/-- The single-binder loop-body walk of an index-free `Com` uses no
    register-indexed operand. -/
theorem loopBodyWalk_lcmdDirect (d : Nat) (accReg : String) (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
      (curDepth : Nat), ComJasminCTByConstruction c →
      lcmdDirect (loopBodyWalk d accReg immSlotMap c curDepth).1 = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, curDepth, h => by
      rw [loopBodyWalk]
      refine lcmdDirect_of_mem ?_
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact opToLinstrR_direct h.1 (loopExprArgs_not_indexed _ _ _ _ e)
      · exact (lcmdDirect_iff _).mp
          (loopBodyWalk_lcmdDirect d accReg immSlotMap body (curDepth + 1) h.2) z hz

/-- The multi-binder loop-body walk of an index-free `Com` uses no
    register-indexed operand. -/
theorem loopBodyWalkN_lcmdDirect (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
      (curDepth : Nat), ComJasminCTByConstruction c →
      lcmdDirect (loopBodyWalkN d accReg idxReg invRegs immSlotMap c curDepth).1 = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, curDepth, h => by
      rw [loopBodyWalkN]
      refine lcmdDirect_of_mem ?_
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact opToLinstrR_direct h.1 (loopExprArgsN_not_indexed _ _ _ _ _ _ e)
      · exact (lcmdDirect_iff _).mp
          (loopBodyWalkN_lcmdDirect d accReg idxReg invRegs immSlotMap body (curDepth + 1)
            h.2) z hz

/-- The inner-count-body walk of an index-free `Com` uses no register-indexed
    operand. -/
theorem nestCountWalk_lcmdDirect (d : Nat) (outerIdxReg : String)
    (invRegs : List String) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
      (curDepth : Nat), ComJasminCTByConstruction c →
      lcmdDirect (nestCountWalk d outerIdxReg invRegs c curDepth).1 = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, curDepth, h => by
      rw [nestCountWalk]
      refine lcmdDirect_of_mem ?_
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact opToLinstrR_direct h.1 (nestCountExprArgs_not_indexed _ _ _ _ e)
      · exact (lcmdDirect_iff _).mp
          (nestCountWalk_lcmdDirect d outerIdxReg invRegs body (curDepth + 1) h.2) z hz

/-- The System V marshalling sequence of an in-body leaf call is direct when its
    argument operands are. -/
theorem callMarshalHere_lcmdDirect (dst name : String) (argTys : List JasminTy)
    (retTy : JasminTy) (srcs : List LOperand)
    (h : ∀ o ∈ srcs, isIndexed o = false) :
    lcmdDirect (callMarshalHere dst name argTys retTy srcs) = true := by
  unfold callMarshalHere
  dsimp only
  split
  · exact loopBodyCallLcmdClassed_direct _ _ _ _ (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact h _ (List.of_mem_zip hq).1)
  · exact loopBodyCallLcmd_direct _ _ _ h

/-- The call-aware multi-binder loop-body walk of an index-free `Com` uses no
    register-indexed operand. -/
theorem loopBodyWalkNCall_lcmdDirect (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
      (curDepth : Nat), ComJasminCTByConstruction c →
      lcmdDirect (loopBodyWalkNCall d accReg idxReg invRegs immSlotMap c curDepth).1 = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, curDepth, h => by
      refine lcmdDirect_append_of ?_
        (loopBodyWalkNCall_lcmdDirect d accReg idxReg invRegs immSlotMap body
          (curDepth + 1) h.2)
      split
      · exact callMarshalHere_lcmdDirect _ _ _ _ _
          (loopExprArgsN_not_indexed _ _ _ _ _ _ e)
      · exact callMarshalHere_lcmdDirect _ _ _ _ _
          (loopExprArgsN_not_indexed _ _ _ _ _ _ e)
      · refine lcmdDirect_of_mem ?_
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        subst hz
        exact opToLinstrR_direct h.1 (loopExprArgsN_not_indexed _ _ _ _ _ _ e)

/-- A multi-binder loop-body variable resolved with the buffer bindings in scope
    is a register or an immediate: the in-place accumulator resolves to the
    accumulator register, a scratch buffer binding to its frame slot name, and
    every other reference exactly as `loopResolveVarN` resolves it. -/
theorem loopResolveVarNBuf_not_indexed (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (bufs : List (Nat × Nat)) (ipSlot : Option Nat)
    (curDepth : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    isIndexed (loopResolveVarNBuf d accReg idxReg invRegs bufs ipSlot curDepth
      immSlotMap v) = false := by
  unfold loopResolveVarNBuf
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact loopResolveVarN_not_indexed _ _ _ _ _ _ v

theorem loopExprArgsNBuf_go_not_indexed (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (bufs : List (Nat × Nat)) (ipSlot : Option Nat)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ loopExprArgsNBuf.go d accReg idxReg invRegs bufs ipSlot curDepth
        immSlotMap hv, isIndexed o = false
  | [], _ => by intro o ho; simp [loopExprArgsNBuf.go] at ho
  | _ :: _, .cons v rest => by
      intro o ho
      rw [loopExprArgsNBuf.go, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact loopResolveVarNBuf_not_indexed _ _ _ _ _ _ _ _ v
      · exact loopExprArgsNBuf_go_not_indexed d accReg idxReg invRegs bufs ipSlot
          curDepth immSlotMap rest o ho

/-- Every operand of a multi-binder loop-body expression resolved with the buffer
    bindings in scope is a register or an immediate. -/
theorem loopExprArgsNBuf_not_indexed (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (bufs : List (Nat × Nat)) (ipSlot : Option Nat)
    (curDepth : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    ∀ o ∈ loopExprArgsNBuf d accReg idxReg invRegs bufs ipSlot curDepth immSlotMap e,
      isIndexed o = false :=
  loopExprArgsNBuf_go_not_indexed d accReg idxReg invRegs bufs ipSlot curDepth
    immSlotMap e.args

/-- Marshalling one loop-body call operand into an argument register is direct
    when the operand is: a memory operand is taken by address (`LEA`) and every
    other operand by value (`MOV`), both with the operand as a source. -/
theorem loopBufMarshalArg_direct (areg : String) (op : LOperand)
    (h : isIndexed op = false) :
    linstrRDirect (loopBufMarshalArg areg op).li_i = true := by
  cases op with
  | reg n =>
      unfold loopBufMarshalArg
      dsimp only
      split
      · exact linstrRDirect_Lopn_mk (by simp [isIndexed]) (by
          intro o ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          subst ho
          rfl)
      · exact movOperand_direct _ _ _ rfl
  | imm m => exact movOperand_direct _ _ _ rfl
  | arr b i => exact movOperand_direct _ _ _ rfl
  | arrIdx b i s => simp [isIndexed] at h

/-- The out-pointer marshalling sequence of a buffer-returning loop-body leaf
    call is direct when its argument operands are. -/
theorem loopBodyCallLcmdBuf_direct (dstMem sym : String) (argOps : List LOperand)
    (h : ∀ o ∈ argOps, isIndexed o = false) :
    lcmdDirect (loopBodyCallLcmdBuf dstMem sym argOps) = true := by
  unfold loopBodyCallLcmdBuf
  refine lcmdDirect_of_mem ?_
  intro z hz
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hz
  rcases hz with ⟨p, hp, rfl⟩ | rfl | rfl
  · exact loopBufMarshalArg_direct _ _ (h _ (List.of_mem_zip hp).1)
  · exact linstrRDirect_Lopn_mk (by simp [isIndexed]) (by
      intro o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      subst ho
      rfl)
  · rfl

/-- The in-place marshalling sequence of a buffer-returning loop-body leaf call
    that writes the accumulator is direct when the accumulator operand and the
    argument operands are. -/
theorem loopBodyCallLcmdBufInPlace_direct (accOp : LOperand) (sym : String)
    (argOps : List LOperand) (hacc : isIndexed accOp = false)
    (h : ∀ o ∈ argOps, isIndexed o = false) :
    lcmdDirect (loopBodyCallLcmdBufInPlace accOp sym argOps) = true := by
  unfold loopBodyCallLcmdBufInPlace
  refine lcmdDirect_of_mem ?_
  intro z hz
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hz
  rcases hz with ⟨p, hp, rfl⟩ | rfl | rfl
  · exact loopBufMarshalArg_direct _ _ (h _ (List.of_mem_zip hp).1)
  · exact loopBufMarshalArg_direct _ _ hacc
  · rfl

/-- The buffer-aware multi-binder loop-body walk of an index-free `Com` uses no
    register-indexed operand. -/
theorem loopBodyWalkNBuf_lcmdDirect (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (bufs : List (Nat × Nat)) (ipSlot : Option Nat)
    (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
      (curDepth : Nat), ComJasminCTByConstruction c →
      lcmdDirect (loopBodyWalkNBuf d accReg idxReg invRegs bufs ipSlot immSlotMap c
        curDepth).1 = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, curDepth, h => by
      have hs := loopExprArgsNBuf_not_indexed d accReg idxReg invRegs bufs ipSlot
        curDepth immSlotMap e
      refine lcmdDirect_append_of ?_
        (loopBodyWalkNBuf_lcmdDirect d accReg idxReg invRegs bufs ipSlot immSlotMap
          body (curDepth + 1) h.2)
      split
      · split
        · exact loopBodyCallLcmdBufInPlace_direct _ _ _ rfl hs
        · split
          · exact loopBodyCallLcmdBuf_direct _ _ _ hs
          · exact callMarshalHere_lcmdDirect _ _ _ _ _ hs
      · split
        · exact loopBodyCallLcmdBufInPlace_direct _ _ _ rfl hs
        · split
          · exact loopBodyCallLcmdBuf_direct _ _ _ hs
          · exact callMarshalHere_lcmdDirect _ _ _ _ _ hs
      · refine lcmdDirect_of_mem ?_
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        subst hz
        exact opToLinstrR_direct h.1 hs

/-- The single-binder back-edge frame around a body copy `w.1` with result
    register `w.2`. -/
theorem frame1_lcmdDirect (accReg ctr : String) (initOp : LOperand) (n : Nat)
    (top : LLabel) (w : Lcmd × String) (hinit : isIndexed initOp = false)
    (hbody : lcmdDirect w.1 = true) :
    lcmdDirect
      ([ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
       , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm n]⟩
       , ⟨0, .Llabel .internal top⟩ ]
       ++ w.1
       ++ (if w.2 == accReg then []
           else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg w.2]⟩])
       ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩
          , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
          , ⟨0, .Lcond (.reg "NZ") top⟩ ]) = true := by
  simp only [lcmdDirect_append, Bool.and_eq_true]
  refine ⟨⟨⟨?_, hbody⟩, feedback_lcmdDirect _ _⟩, rfl⟩
  refine lcmdDirect_of_mem ?_
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact movOperand_direct _ _ _ hinit
  · rfl
  · rfl

/-- The runtime back-edge frame `blockLoopFrame` around a pre-walked body copy is
    direct when the seed, the runtime trip count and the body are. -/
theorem blockLoopFrame_lcmdDirect (d : Nat) (accReg idxReg ctr : String)
    (initOp countOp : LOperand) (invRegs : List String) (bodyW : Lcmd) (retReg : String)
    (hinit : isIndexed initOp = false) (hcount : isIndexed countOp = false)
    (hbody : lcmdDirect bodyW = true) :
    lcmdDirect (blockLoopFrame d accReg idxReg ctr initOp countOp invRegs bodyW retReg)
      = true := by
  unfold blockLoopFrame
  simp only [lcmdDirect_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, rfl⟩, rfl⟩, hbody⟩, feedback_lcmdDirect _ _⟩, rfl⟩,
    invTouch_lcmdDirect _ _⟩, rfl, rfl⟩
  refine lcmdDirect_of_mem ?_
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact movOperand_direct _ _ _ hinit
  · rfl
  · exact movOperand_direct _ _ _ hcount

/-- The nested runtime back-edge frame around the inner-count copy `cw.1` and the
    inner body copy `w.1`. -/
theorem frameNested_lcmdDirect (accReg outerIdxReg outerCtr innerIdxReg innerCtr : String)
    (initOp outerCountOp : LOperand) (outerTop outerEnd innerTop innerEnd : LLabel)
    (invRegs : List String) (cw w : Lcmd × String)
    (hinit : isIndexed initOp = false) (hcount : isIndexed outerCountOp = false)
    (hcnt : lcmdDirect cw.1 = true) (hbody : lcmdDirect w.1 = true) :
    lcmdDirect
      ([ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
       , ⟨0, .Lopn [.reg outerIdxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
       , ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "MOV") [outerCountOp]⟩
       , ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "CMP") [.reg outerCtr, .imm 0]⟩
       , ⟨0, .Lcond (.reg "Z") outerEnd⟩
       , ⟨0, .Llabel .internal outerTop⟩ ]
       ++ cw.1
       ++ [ ⟨0, .Lopn [.reg innerIdxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
          , ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "MOV") [.reg cw.2]⟩
          , ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "CMP") [.reg innerCtr, .imm 0]⟩
          , ⟨0, .Lcond (.reg "Z") innerEnd⟩
          , ⟨0, .Llabel .internal innerTop⟩ ]
       ++ w.1
       ++ (if w.2 == accReg then []
           else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg w.2]⟩])
       ++ [ ⟨0, .Lopn [.reg innerIdxReg] (withWidthTag 64 "ADD") [.reg innerIdxReg, .imm 1]⟩
          , ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "SUB") [.reg innerCtr, .imm 1]⟩
          , ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "CMP") [.reg innerCtr, .imm 0]⟩
          , ⟨0, .Lcond (.reg "NZ") innerTop⟩
          , ⟨0, .Llabel .internal innerEnd⟩ ]
       ++ [ ⟨0, .Lopn [.reg outerIdxReg] (withWidthTag 64 "ADD") [.reg outerIdxReg, .imm 1]⟩
          , ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "SUB") [.reg outerCtr, .imm 1]⟩ ]
       ++ invRegs.map (fun r =>
            ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "CMP") [.reg outerCtr, .reg r]⟩)
       ++ [ ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "CMP") [.reg outerCtr, .imm 0]⟩
          , ⟨0, .Lcond (.reg "NZ") outerTop⟩
          , ⟨0, .Llabel .internal outerEnd⟩ ]) = true := by
  simp only [lcmdDirect_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, hcnt⟩, rfl⟩, hbody⟩, feedback_lcmdDirect _ _⟩, rfl⟩, rfl⟩,
    invTouch_lcmdDirect _ _⟩, rfl⟩
  refine lcmdDirect_of_mem ?_
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · exact movOperand_direct _ _ _ hinit
  · rfl
  · exact movOperand_direct _ _ _ hcount
  · rfl
  · rfl
  · rfl

/-! ## 4. The exporters -/

/-- `forLoopLcmdN` emits no register-indexed operand when its accumulator seed is
    a register or an immediate and its loop body is index-free. -/
theorem forLoopLcmdN_lcmdDirect (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect} (p : JLoopBodyN accTy invTys)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hinit : isIndexed initOp = false)
    (hp : ComJasminCTByConstruction p.update) :
    lcmdDirect (forLoopLcmdN d accReg initOp p invOps immSlotMap) = true :=
  frameN_lcmdDirect accReg (loopIdx d) (loopCtr d) initOp (.imm p.n) d
    (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
    (loopBodyWalkN d accReg (loopIdx d)
      (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
      immSlotMap p.update (2 + invTys.length))
    hinit rfl
    (loopBodyWalkN_lcmdDirect d accReg (loopIdx d) _ immSlotMap p.update _ hp)

/-- `forLoopLcmd` emits no register-indexed operand when its accumulator seed is a
    register or an immediate and its loop body is index-free. -/
theorem forLoopLcmd_lcmdDirect (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} (p : JLoopBody accTy) (immSlotMap : ImmSlotMap)
    (hinit : isIndexed initOp = false)
    (hp : ComJasminCTByConstruction p.update) :
    lcmdDirect (forLoopLcmd d accReg initOp p immSlotMap) = true :=
  frame1_lcmdDirect accReg (loopCtr d) initOp p.n d
    (loopBodyWalk d accReg immSlotMap p.update 1) hinit
    (loopBodyWalk_lcmdDirect d accReg immSlotMap p.update 1 hp)

/-- `forLoopLcmdNCall` emits no register-indexed operand when its accumulator seed
    is a register or an immediate and its loop body is index-free. -/
theorem forLoopLcmdNCall_lcmdDirect (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect} (p : JLoopBodyN accTy invTys)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hinit : isIndexed initOp = false)
    (hp : ComJasminCTByConstruction p.update) :
    lcmdDirect (forLoopLcmdNCall d accReg initOp p invOps immSlotMap) = true := by
  unfold forLoopLcmdNCall
  refine lcmdDirect_append_of (lcmdDirect_append_of (lcmdDirect_append_of
    (lcmdDirect_append_of (lcmdDirect_append_of (lcmdDirect_append_of
      ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · split <;> rfl
  · refine lcmdDirect_of_mem ?_
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact movOperand_direct _ _ _ hinit
    · rfl
    · rfl
    · rfl
  · cases hc : ((loopScratchBufBindings p.update (2 + invTys.length)).isEmpty &&
        (loopInPlaceBufSlot p.update (2 + invTys.length)).isNone) with
    | false => exact loopBodyWalkNBuf_lcmdDirect _ _ _ _ _ _ _ _ _ hp
    | true => exact loopBodyWalkNCall_lcmdDirect _ _ _ _ _ _ _ hp
  · split <;> rfl
  · rfl
  · exact invTouch_lcmdDirect _ _
  · rfl

/-- `forLoopLcmdNRt` emits no register-indexed operand when its accumulator seed
    and runtime trip count are registers or immediates and its loop body is
    index-free. -/
theorem forLoopLcmdNRt_lcmdDirect (d : Nat) (accReg : String)
    (initOp countOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hinit : isIndexed initOp = false) (hcount : isIndexed countOp = false)
    (hup : ComJasminCTByConstruction update) :
    lcmdDirect (forLoopLcmdNRt d accReg initOp countOp update invOps immSlotMap)
      = true :=
  blockLoopFrame_lcmdDirect d accReg (loopIdx d) (loopCtr d) initOp countOp
    (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
    (loopBodyWalkN d accReg (loopIdx d)
      (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
      immSlotMap update (2 + invTys.length)).1
    (loopBodyWalkN d accReg (loopIdx d)
      (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
      immSlotMap update (2 + invTys.length)).2
    hinit hcount
    (loopBodyWalkN_lcmdDirect d accReg (loopIdx d) _ immSlotMap update _ hup)

/-- `whileLcmdNz` emits no register-indexed operand when its accumulator seed and
    countdown guard are registers or immediates and its loop body is
    index-free. -/
theorem whileLcmdNz_lcmdDirect (d : Nat) (accReg : String)
    (initOp guardOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hinit : isIndexed initOp = false) (hguard : isIndexed guardOp = false)
    (hup : ComJasminCTByConstruction update) :
    lcmdDirect (whileLcmdNz d accReg initOp guardOp update invOps immSlotMap)
      = true :=
  frameN_lcmdDirect accReg (loopIdx d) (loopCtr d) initOp guardOp d
    (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
    (loopBodyWalkN d accReg (loopIdx d)
      (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
      immSlotMap update (2 + invTys.length))
    hinit hguard
    (loopBodyWalkN_lcmdDirect d accReg (loopIdx d) _ immSlotMap update _ hup)

/-- `forLoopLcmdNRtNested` emits no register-indexed operand when its accumulator
    seed and outer runtime trip count are registers or immediates and both the
    inner-count body and the inner loop body are index-free. -/
theorem forLoopLcmdNRtNested_lcmdDirect (d : Nat) (accReg : String)
    (initOp outerCountOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hinit : isIndexed initOp = false) (hcount : isIndexed outerCountOp = false)
    (hcnt : ComJasminCTByConstruction innerCount)
    (hup : ComJasminCTByConstruction innerUpdate) :
    lcmdDirect (forLoopLcmdNRtNested d accReg initOp outerCountOp innerCount
      innerUpdate invOps immSlotMap) = true :=
  frameNested_lcmdDirect accReg (loopIdx d) (loopCtr d) (loopIdx (d + 1))
    (loopCtr (d + 1)) initOp outerCountOp d (d + 0x40000000) (d + 1)
    (d + 1 + 0x40000000)
    (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
    (nestCountWalk d (loopIdx d)
      (invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
      innerCount (1 + invTys.length))
    (loopBodyWalkN (d + 1) accReg (loopIdx (d + 1))
      (loopIdx d :: invOps.filterMap (fun o => match o with | .reg n => some n | _ => none))
      immSlotMap innerUpdate (2 + (invTys.length + 1)))
    hinit hcount
    (nestCountWalk_lcmdDirect d (loopIdx d) _ innerCount _ hcnt)
    (loopBodyWalkN_lcmdDirect (d + 1) accReg (loopIdx (d + 1)) _ immSlotMap
      innerUpdate _ hup)

/-- The generic bounded-counter back-edge wrapper `loopLcmd` adds a label, a
    compare against the counter register and a conditional back-edge, so it is
    direct whenever the body it wraps is. -/
theorem loopLcmd_lcmdDirect (w : Nat) (top : LLabel) (nReg : String) (body : Lcmd)
    (hbody : lcmdDirect body = true) :
    lcmdDirect (LprogControlFlow.loopLcmd w top nReg body) = true := by
  unfold LprogControlFlow.loopLcmd
  simp only [lcmdDirect_append, Bool.and_eq_true]
  refine ⟨?_, rfl⟩
  refine lcmdDirect_of_mem ?_
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · rfl
  · exact (lcmdDirect_iff _).mp hbody z hz

/-! ### The boundary of the fragment

The exporters' own instructions — seed, index init, counter seed, index advance,
counter decrement, invariant touch, compare, label and back-edge — carry register
and immediate operands only, so they are direct unconditionally. The only source
of a register-indexed operand is the body copy, through the `stackLoad` /
`stackStore` arms of `opToLinstrR` that `ComJasminCTByConstruction` excludes: a
loop body binding either op leaves the fragment. -/

/-- A `stackLoad` at a register index exports to the register-indexed `LOADIDX`,
    which is not direct. -/
theorem stackLoad_export_not_direct (w n : Nat) (dst base idx : String) :
    linstrRDirect (opToLinstrR (.stackLoad w n) dst [.reg base, .reg idx]) = false :=
  rfl

/-- A `stackStore` at a register index exports to the register-indexed `STOREIDX`,
    which is not direct. -/
theorem stackStore_export_not_direct (w n : Nat) (dst base idx : String)
    (val : LOperand) :
    linstrRDirect (opToLinstrR (.stackStore w n) dst [.reg base, .reg idx, val])
      = false := rfl

/-! ## 5. The loop-aware `ComL` walk -/

/-- A `ComL` is index-free when every straight-line binder it holds is index-free
    and the body `Com` of every loop node it holds is in
    `ComJasminCTByConstruction`. The `ComL` counterpart of that fragment. -/
def ComLIndexFree {Γ : Ctxt jasminDialect} {t : JasminTy} : ComL Γ t → Prop
  | .ret _ => True
  | .var e body => jasminOpAddrSurface e.op = false ∧ ComLIndexFree body
  | .forLoop loop _ body =>
      ComJasminCTByConstruction loop.update ∧ ComLIndexFree body
  | .forLoopN loop _ _ body =>
      ComJasminCTByConstruction loop.update ∧ ComLIndexFree body
  | .forLoopNRt update _ _ _ body =>
      ComJasminCTByConstruction update ∧ ComLIndexFree body
  | .forLoopNRtNested innerCount innerUpdate _ _ _ body =>
      ComJasminCTByConstruction innerCount ∧ ComJasminCTByConstruction innerUpdate
        ∧ ComLIndexFree body
  | .whileNz update _ _ _ body =>
      ComJasminCTByConstruction update ∧ ComLIndexFree body
  | .forLoopBlock loopBody _ _ _ body =>
      ComLIndexFree loopBody ∧ ComLIndexFree body

/-- The `forLoopBlock` body walk of an index-free `ComL` uses no register-indexed
    operand. -/
theorem comLLoopBodyWalk_lcmdDirect (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) (d : Nat)
      (accReg idxReg : String) (invRegs : List String) (curDepth : Nat),
      ComLIndexFree c →
      lcmdDirect (comLLoopBodyWalk immSlotMap c d accReg idxReg invRegs curDepth).1
        = true
  | _, _, .ret _, _, _, _, _, _, _ => rfl
  | _, _, .var e body, d, accReg, idxReg, invRegs, curDepth, h => by
      rw [comLLoopBodyWalk]
      refine lcmdDirect_of_mem ?_
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact opToLinstrR_direct h.1 (loopExprArgsN_not_indexed _ _ _ _ _ _ e)
      · exact (lcmdDirect_iff _).mp
          (comLLoopBodyWalk_lcmdDirect immSlotMap body d accReg idxReg invRegs
            (curDepth + 1) h.2) z hz
  | _, _, .forLoop loop init body, d, accReg, idxReg, invRegs, curDepth, h =>
      lcmdDirect_append_of
        (forLoopLcmd_lcmdDirect _ _ _ loop immSlotMap
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap init)
          h.1)
        (comLLoopBodyWalk_lcmdDirect immSlotMap body d accReg idxReg invRegs
          (curDepth + 1) h.2)
  | _, _, .forLoopN loop init invs body, d, accReg, idxReg, invRegs, curDepth, h =>
      lcmdDirect_append_of
        (forLoopLcmdN_lcmdDirect _ _ _ loop _ immSlotMap
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap init)
          h.1)
        (comLLoopBodyWalk_lcmdDirect immSlotMap body d accReg idxReg invRegs
          (curDepth + 1) h.2)
  | _, _, .forLoopNRt update count init invs body, d, accReg, idxReg, invRegs,
      curDepth, h =>
      lcmdDirect_append_of
        (forLoopLcmdNRt_lcmdDirect _ _ _ _ update _ immSlotMap
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap init)
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap count)
          h.1)
        (comLLoopBodyWalk_lcmdDirect immSlotMap body d accReg idxReg invRegs
          (curDepth + 1) h.2)
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body, d,
      accReg, idxReg, invRegs, curDepth, h =>
      lcmdDirect_append_of
        (forLoopLcmdNRtNested_lcmdDirect _ _ _ _ innerCount innerUpdate _ immSlotMap
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap init)
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap
            outerCount)
          h.1 h.2.1)
        (comLLoopBodyWalk_lcmdDirect immSlotMap body d accReg idxReg invRegs
          (curDepth + 1) h.2.2)
  | _, _, .whileNz update guard init invs body, d, accReg, idxReg, invRegs,
      curDepth, h =>
      lcmdDirect_append_of
        (whileLcmdNz_lcmdDirect _ _ _ _ update _ immSlotMap
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap init)
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap guard)
          h.1)
        (comLLoopBodyWalk_lcmdDirect immSlotMap body d accReg idxReg invRegs
          (curDepth + 1) h.2)
  | _, _, .forLoopBlock loopBody count init invs body, d, accReg, idxReg, invRegs,
      curDepth, h =>
      lcmdDirect_append_of
        (blockLoopFrame_lcmdDirect _ _ _ _ _ _ _ _ _
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap init)
          (loopResolveVarN_not_indexed d accReg idxReg invRegs curDepth immSlotMap count)
          (comLLoopBodyWalk_lcmdDirect immSlotMap loopBody _ _ _ _ _ h.1))
        (comLLoopBodyWalk_lcmdDirect immSlotMap body d accReg idxReg invRegs
          (curDepth + 1) h.2)

/-- `forLoopBlockLcmd` emits no register-indexed operand when its accumulator seed
    and runtime trip count are registers or immediates and its recursive loop body
    is index-free. -/
theorem forLoopBlockLcmd_lcmdDirect (d : Nat) (accReg : String)
    (initOp countOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (loopBody : ComL (accTy :: .reg 64 :: invTys) accTy) (invOps : List LOperand)
    (immSlotMap : ImmSlotMap) (hinit : isIndexed initOp = false)
    (hcount : isIndexed countOp = false) (hbody : ComLIndexFree loopBody) :
    lcmdDirect (forLoopBlockLcmd d accReg initOp countOp loopBody invOps immSlotMap)
      = true :=
  blockLoopFrame_lcmdDirect _ _ _ _ _ _ _ _ _ hinit hcount
    (comLLoopBodyWalk_lcmdDirect immSlotMap loopBody d accReg (loopIdx d) _ _ hbody)

theorem lcmdDirect_ite {c : Bool} {a b : Lcmd} (ha : lcmdDirect a = true)
    (hb : lcmdDirect b = true) : lcmdDirect (if c = true then a else b) = true := by
  split <;> assumption

/-- **The index-free `ComL` fragment exports to direct addressing.** The virtual
    body the loop-aware walk emits carries no register-indexed (SIB) operand. -/
theorem comLToBody_lcmdDirect (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) (curDepth : Nat),
      ComLIndexFree c →
      lcmdDirect (comLToBody nArgs argNames immSlotMap c curDepth) = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, curDepth, h => by
      rw [comLToBody]
      refine lcmdDirect_of_mem ?_
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact opToLinstrR_direct h.1 (exprArgs_not_indexed _ _ _ _ e)
      · exact (lcmdDirect_iff _).mp
          (comLToBody_lcmdDirect nArgs argNames immSlotMap body (curDepth + 1) h.2) z hz
  | _, _, .forLoop loop init body, curDepth, h =>
      lcmdDirect_append_of
        (forLoopLcmd_lcmdDirect _ _ _ loop immSlotMap
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap init) h.1)
        (comLToBody_lcmdDirect nArgs argNames immSlotMap body (curDepth + 1) h.2)
  | _, _, .forLoopN loop init invs body, curDepth, h =>
      lcmdDirect_append_of
        (lcmdDirect_ite
          (forLoopLcmdNCall_lcmdDirect _ _ _ loop _ immSlotMap
            (resolveVar_not_indexed curDepth nArgs argNames immSlotMap init) h.1)
          (forLoopLcmdN_lcmdDirect _ _ _ loop _ immSlotMap
            (resolveVar_not_indexed curDepth nArgs argNames immSlotMap init) h.1))
        (comLToBody_lcmdDirect nArgs argNames immSlotMap body (curDepth + 1) h.2)
  | _, _, .forLoopNRt update count init invs body, curDepth, h =>
      lcmdDirect_append_of
        (forLoopLcmdNRt_lcmdDirect _ _ _ _ update _ immSlotMap
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap init)
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap count) h.1)
        (comLToBody_lcmdDirect nArgs argNames immSlotMap body (curDepth + 1) h.2)
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body,
      curDepth, h =>
      lcmdDirect_append_of
        (forLoopLcmdNRtNested_lcmdDirect _ _ _ _ innerCount innerUpdate _ immSlotMap
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap init)
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap outerCount)
          h.1 h.2.1)
        (comLToBody_lcmdDirect nArgs argNames immSlotMap body (curDepth + 1) h.2.2)
  | _, _, .whileNz update guard init invs body, curDepth, h =>
      lcmdDirect_append_of
        (whileLcmdNz_lcmdDirect _ _ _ _ update _ immSlotMap
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap init)
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap guard) h.1)
        (comLToBody_lcmdDirect nArgs argNames immSlotMap body (curDepth + 1) h.2)
  | _, _, .forLoopBlock loopBody count init invs body, curDepth, h =>
      lcmdDirect_append_of
        (forLoopBlockLcmd_lcmdDirect _ _ _ _ loopBody _ immSlotMap
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap init)
          (resolveVar_not_indexed curDepth nArgs argNames immSlotMap count) h.1)
        (comLToBody_lcmdDirect nArgs argNames immSlotMap body (curDepth + 1) h.2)

/-- The virtual `Lfundef` of an index-free `ComL` carries no register-indexed
    (SIB) operand. -/
theorem ComL_toLfundef_lcmdDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (immSlotMap : ImmSlotMap) (h : ComLIndexFree c) :
    lcmdDirect (ComL.toLfundef c immSlotMap).lfd_body = true :=
  comLToBody_lcmdDirect _ _ _ c _ h

/-! ## 6. The deployed looped export -/

theorem aliasRegOperand_isIndexed (from_ to_ : String) (o : LOperand) :
    isIndexed (aliasRegOperand from_ to_ o) = isIndexed o := by
  cases o <;> rfl

/-- Renaming a register label across a body leaves every operand's addressing
    form unchanged. -/
theorem aliasRegBody_lcmdDirect (from_ to_ : String) {body : Lcmd}
    (h : lcmdDirect body = true) :
    lcmdDirect (aliasRegBody from_ to_ body) = true :=
  lcmdDirect_mapOperands (aliasRegOperand_isIndexed from_ to_) h

/-- The saves of a list of argument registers to their save slots, which the multi-input
    prologue appends, use register operands only. -/
theorem extraInputSaves_lcmdDirect (regs : List String) :
    lcmdDirect (regs.filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none)) = true := by
  refine lcmdDirect_of_mem ?_
  intro z hz
  rw [List.mem_filterMap] at hz
  obtain ⟨a, _, ha⟩ := hz
  split at ha <;> simp only [Option.some.injEq, reduceCtorEq] at ha
  subst ha
  rfl

/-- The synthetic argument-liveness pin uses register operands only. -/
theorem livePin_lcmdDirect (abiArgs : List String) :
    lcmdDirect (if abiArgs.length ≥ 4 then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
        ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
      else []) = true := by
  split
  · refine lcmdDirect_of_mem ?_
    intro z hz
    rw [List.mem_singleton] at hz
    subst hz
    refine linstrRDirect_Lopn_mk (by simp [isIndexed]) ?_
    intro o ho
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ho
    rfl
  · rfl

/-- The ABI wrapping of the looped export around a register-allocated body keeps
    every memory operand direct. -/
theorem physAbiLoopWrap_lcmdDirect (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (extra : Lcmd) (shiftImm : ShiftImmOracle)
    (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (p : Linstr → Bool)
    (hextra : lcmdDirect extra = true) (hv : lcmdDirect virt.lfd_body = true) :
    lcmdDirect (buildPrologue virt tbl (fun _ => none) ++ extra
      ++ buildArgPtrMaterialize virt tbl abiArgs (fun _ => none)
      ++ insertEpilogue
          ((physBodyWithStores shiftImm virt.lfd_body (fun _ => none) reloadScratch2 []
              reloadScratch2 0 memrefBaseReload callArgBaseReload).filter p)
          calleeSaveRestoreEpilogue) = true := by
  simp only [lcmdDirect_append, Bool.and_eq_true]
  refine ⟨⟨⟨buildPrologue_lcmdDirect _ _ _, hextra⟩,
    buildArgPtrMaterialize_lcmdDirect _ _ _ _⟩, ?_⟩
  exact insertEpilogue_lcmdDirect
    (lcmdDirect_filter (physBodyWithStores_lcmdDirect _ _ _ _ _ _ _ _ _ hv))
    calleeSaveRestoreEpilogue_lcmdDirect

/-- A left fold of body transformations that each preserve direct addressing
    preserves direct addressing. -/
theorem foldl_lcmdDirect_of {α : Type} (g : Lcmd → α → Lcmd)
    (hg : ∀ b a, lcmdDirect b = true → lcmdDirect (g b a) = true) :
    ∀ (l : List α) (b : Lcmd), lcmdDirect b = true → lcmdDirect (l.foldl g b) = true
  | [], _, h => h
  | a :: l, b, h => foldl_lcmdDirect_of g hg l (g b a) (hg b a h)

/-- **The deployed looped export preserves direct addressing.** For an index-free
    `ComL`, the body of the ABI-wrapped, register-allocated function the looped
    2-pointer export emits carries no register-indexed (SIB) operand. -/
theorem ComL_toLfundefPhysAbi_lcmdDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap) (abiArgs : List String)
    (abiTyin : List Nat) (h : ComLIndexFree c) :
    lcmdDirect (ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs
      abiTyin).lfd_body = true := by
  refine physAbiLoopWrap_lcmdDirect _ _ _ _ _ _ _ _
    (extraInputSaves_lcmdDirect (extraSaveRegs abiArgs)) ?_
  exact lcmdDirect_append_of (livePin_lcmdDirect abiArgs)
    (canonicalizeMemrefThread_lcmdDirect
      (foldl_lcmdDirect_of _ (fun _ _ hb => aliasRegBody_lcmdDirect _ _ hb) _ _
        (ComL_toLfundef_lcmdDirect c immSlotMap h)))

/-- **The shipped looped `Lprog` export preserves direct addressing.** Every
    function of the looped 2-pointer export of an index-free `ComL` has a body
    free of register-indexed (SIB) operands. -/
theorem ComL_toLprogPhysAbi_lcmdDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap) (abiArgs : List String)
    (abiTyin : List Nat) (h : ComLIndexFree c) :
    ∀ f ∈ (ComL.toLprogPhysAbi c fname outArg inArgs shiftImm immSlotMap abiArgs
      abiTyin).lp_funcs, lcmdDirect f.2.lfd_body = true := by
  intro f hf
  simp only [ComL.toLprogPhysAbi, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact ComL_toLfundefPhysAbi_lcmdDirect c outArg inArgs shiftImm immSlotMap abiArgs
    abiTyin h

/-! ## 7. Loop bodies the compile-from-hax front produces

A `compileFromHax` output at word width 64 over `k + 2` inputs lives in the
context `List.replicate (k + 2) (.reg 64)`, which is definitionally the
`JLoopBodyN` body context `.reg 64 :: .reg 64 :: List.replicate k (.reg 64)`
(accumulator, loop index, `k` invariant bases). So a front-compiled `Com` is a
loop body for the multi-binder exporters, and `compileFromHax_ct` discharges
their index-freeness hypothesis. -/

/-- The fixed-trip multi-binder loop over a front-compiled body emits no
    register-indexed operand. -/
theorem compileFromHax_forLoopLcmdN_lcmdDirect {k : Nat} {params : List String}
    {e : ImpExpr} {update : Com jasminDialect (frontCtxt 64 (k + 2) []) (rW 64)}
    (hc : compileFromHax (w := 64) (nIn := k + 2) params e = some update)
    (N d : Nat) (accReg : String) (initOp : LOperand) (invOps : List LOperand)
    (immSlotMap : ImmSlotMap) (hinit : isIndexed initOp = false) :
    lcmdDirect (forLoopLcmdN d accReg initOp
      (accTy := rW 64) (invTys := List.replicate k (rW 64)) ⟨N, update⟩ invOps
      immSlotMap) = true :=
  forLoopLcmdN_lcmdDirect d accReg initOp ⟨N, update⟩ invOps immSlotMap hinit
    (compileFromHax_ct hc)

/-- The runtime-trip multi-binder loop over a front-compiled body emits no
    register-indexed operand. -/
theorem compileFromHax_forLoopLcmdNRt_lcmdDirect {k : Nat} {params : List String}
    {e : ImpExpr} {update : Com jasminDialect (frontCtxt 64 (k + 2) []) (rW 64)}
    (hc : compileFromHax (w := 64) (nIn := k + 2) params e = some update)
    (d : Nat) (accReg : String) (initOp countOp : LOperand) (invOps : List LOperand)
    (immSlotMap : ImmSlotMap) (hinit : isIndexed initOp = false)
    (hcount : isIndexed countOp = false) :
    lcmdDirect (forLoopLcmdNRt d accReg initOp countOp
      (accTy := rW 64) (invTys := List.replicate k (rW 64)) update invOps immSlotMap)
      = true :=
  forLoopLcmdNRt_lcmdDirect d accReg initOp countOp update invOps immSlotMap hinit
    hcount (compileFromHax_ct hc)

/-- The countdown do-while over a front-compiled body emits no register-indexed
    operand. -/
theorem compileFromHax_whileLcmdNz_lcmdDirect {k : Nat} {params : List String}
    {e : ImpExpr} {update : Com jasminDialect (frontCtxt 64 (k + 2) []) (rW 64)}
    (hc : compileFromHax (w := 64) (nIn := k + 2) params e = some update)
    (d : Nat) (accReg : String) (initOp guardOp : LOperand) (invOps : List LOperand)
    (immSlotMap : ImmSlotMap) (hinit : isIndexed initOp = false)
    (hguard : isIndexed guardOp = false) :
    lcmdDirect (whileLcmdNz d accReg initOp guardOp
      (accTy := rW 64) (invTys := List.replicate k (rW 64)) update invOps immSlotMap)
      = true :=
  whileLcmdNz_lcmdDirect d accReg initOp guardOp update invOps immSlotMap hinit
    hguard (compileFromHax_ct hc)

/-- **The looped export of a front-compiled loop body uses direct addressing.**
    A `ComL.forLoopN` whose body is a `compileFromHax` output exports, through the
    deployed looped 2-pointer ABI path, to a function body with no register-indexed
    (SIB) operand — no `lcmdDirect` hypothesis is left for the caller. -/
theorem compileFromHax_rolledLoop_toLprogPhysAbi_lcmdDirect {k : Nat}
    {params : List String} {e : ImpExpr} {Γ : Ctxt jasminDialect}
    {update : Com jasminDialect (frontCtxt 64 (k + 2) []) (rW 64)}
    (hc : compileFromHax (w := 64) (nIn := k + 2) params e = some update)
    (N : Nat) (init : Ctxt.Var Γ (rW 64))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) (List.replicate k (rW 64)))
    (fname outArg : String) (inArgs : List String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (abiArgs : List String) (abiTyin : List Nat) :
    ∀ f ∈ (ComL.toLprogPhysAbi (ComL.forLoopN ⟨N, update⟩ init invs (.ret .here))
      fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin).lp_funcs,
      lcmdDirect f.2.lfd_body = true :=
  ComL_toLprogPhysAbi_lcmdDirect _ fname outArg inArgs shiftImm immSlotMap abiArgs
    abiTyin ⟨compileFromHax_ct hc, trivial⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoopExporterCTBridge
