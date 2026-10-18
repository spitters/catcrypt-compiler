/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

/-!
# The index-free `Com` fragment exports to direct addressing

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

The statements concern the `Com` walk `comToBody`. A body built by one of the loop
exporters (`forLoopLcmdN` and its relatives) is outside it, as is a `Com` binding
`stackLoad` / `stackStore`.

## Main results

* `opToLinstrR_direct`: an op that is not an addressing surface exports to an
  instruction with no register-indexed operand, given direct sources.
* `comToLfundef_lcmdDirect`: the virtual body of the `Lfundef` an index-free `Com`
  lowers to satisfies `lcmdDirect`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

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

end CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect
