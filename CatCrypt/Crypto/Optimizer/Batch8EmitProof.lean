/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Batch8Emit
public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeirCorrect

/-!
# Correctness anchor for the fused `batch8` emit lowering

`Batch8Emit.batch8Body` walks a scalar `Com jasminDialect` once and emits the
flat two-address body that `comToBody (batch8 com)` produces, without
materialising the widened `Com`. This module relates the fused body to the
composition `comToBody ∘ batch8`.

The registers `comToBody` emits are integer-depth names, so the whole identity
is slot arithmetic over the block-splice `spliceCom`: each scalar op expands to a
block of `blockSize e` widened bindings, and the continuation's variables must
resolve to the same absolute slots whether reached through the fused
`endSlot` table or through the De Bruijn transport `spliceCom` inserts.

## Main results

* `bodyNoRet` / `comToBody_eq_bodyNoRet`: the terminal law splitting `comToBody`
  into its instruction prefix and the trailing `Lret`.
* `size_lowerExprBlock`: each scalar op's widened block has `blockSize e`
  bindings, matching `Com.size (lowering.lowerExprBlock e)`.
* `varIndex_weakenOne` / `varIndex_lift_*`: the De Bruijn index shifts the
  block-splice renaming `Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ _)` applies.
* `comToBody_rename_of_varIndex`: `comToBody` is invariant under a renaming that
  preserves `varIndex`.
* `batch8Body_eq` / `batch8RetReg_eq` / `batch8Virt_eq`: the fused body, its return
  register, and the virtual `Lfundef` equal the flat lowering of the widened
  program `batch8 com`. `batch8Virt_eq` reduces to the other two.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Batch8EmitProof

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.Optimizer.Batch8
open CatCrypt.Crypto.Optimizer.Batch8Emit

/-! ## 1. The terminal law: `comToBody` is a prefix followed by `Lret` -/

/-- The instruction prefix `comToBody` emits, without the trailing `.Lret`. At a
    `.ret` it is empty; at a `.var` it emits the op's flat `Linstr` and recurses.
    The per-op shape of `comToBody`, factored out so the trailing terminal can be
    reasoned about separately. -/
def bodyNoRet (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Lcmd
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let srcs := exprArgs curDepth nArgs argNames immSlotMap e
      let instr : Linstr := ⟨0, opToLinstrR e.op (regName curDepth) srcs⟩
      instr :: bodyNoRet nArgs argNames immSlotMap body (curDepth + 1)

/-- `comToBody` is its instruction prefix followed by the single terminal `Lret`. -/
theorem comToBody_eq_bodyNoRet (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    (curDepth : Nat) →
    comToBody nArgs argNames immSlotMap c curDepth
      = bodyNoRet nArgs argNames immSlotMap c curDepth ++ [⟨0, .Lret⟩]
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, curDepth => by
      simp only [comToBody, bodyNoRet, List.cons_append]
      rw [comToBody_eq_bodyNoRet nArgs argNames immSlotMap body (curDepth + 1)]

/-! ## 2. Block sizes: each covered op expands to `blockSize e` bindings -/

/-- On a covered op the widened block has exactly `blockSize e` bindings — one for
    every op but the rotate `rorImm 32 n`, which expands to three. -/
theorem size_lowerExprBlock {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hcov : CoveredExpr e) :
    Com.size (lowering.lowerExprBlock e) = blockSize e := by
  obtain ⟨op, rfl, args⟩ := e
  cases op
  case regArith bop w =>
    cases args with
    | cons a rest => cases rest with
      | cons b rest2 => cases rest2 with
        | nil =>
          cases bop <;>
            first
            | (simp only [CoveredExpr] at hcov; subst hcov; rfl)
            | (simp only [CoveredExpr] at hcov)
  case shlImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _⟩ : w = 32 ∧ n < 32 := hcov
        subst hw; rfl
  case shrImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _⟩ : w = 32 ∧ n < 32 := hcov
        subst hw; rfl
  case sarImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil => simp only [CoveredExpr] at hcov; subst hcov; rfl
  case rorImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _, _⟩ : w = 32 ∧ 0 < n ∧ n < 32 := hcov
        subst hw; rfl
  case regConst w kk =>
    cases args
    simp only [CoveredExpr] at hcov; subst hcov; rfl
  case stackLoad w n =>
    cases args with
    | cons arr rest => cases rest with
      | cons idx rest2 => cases rest2 with
        | nil => simp only [CoveredExpr] at hcov; subst hcov; rfl
  all_goals (simp only [CoveredExpr] at hcov)

/-! ## 3. De Bruijn index shifts under the splice renaming -/

/-- Weakening by one binder increments the De Bruijn index. -/
theorem varIndex_weakenOne {Γ : Ctxt jasminDialect} {s τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    varIndex (Ctxt.Hom.weakenOne Γ s v) = varIndex v + 1 := rfl

/-- The lifted renaming fixes the head variable's De Bruijn index at zero. -/
theorem varIndex_lift_here {Γ Γ' : Ctxt jasminDialect} {s : JasminTy}
    (h : Ctxt.Hom Γ Γ') :
    varIndex (Ctxt.Hom.lift (s := s) h (Ctxt.Var.here)) = 0 := rfl

/-- The lifted renaming shifts a non-head variable by its image under `h`. -/
theorem varIndex_lift_there {Γ Γ' : Ctxt jasminDialect} {s τ : JasminTy}
    (h : Ctxt.Hom Γ Γ') (v : Ctxt.Var Γ τ) :
    varIndex (Ctxt.Hom.lift (s := s) h (Ctxt.Var.there v)) = varIndex (h v) + 1 := rfl

/-- A De Bruijn index is bounded by the context length. -/
theorem varIndex_lt {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    varIndex v < Γ.length := by
  induction v with
  | here => simp only [varIndex, List.length_cons]; omega
  | there w ih => simp only [varIndex, List.length_cons]; omega

/-- The context transport `mapVar` preserves the De Bruijn index. -/
theorem varIndex_mapVar {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    varIndex (mapVar v) = varIndex v := by
  induction v with
  | here => rfl
  | there w ih => exact congrArg (· + 1) ih

/-! ## 4. `comToBody` is invariant under a `varIndex`-preserving renaming -/

/-- A renaming that preserves the De Bruijn index of every variable. Under such a
    renaming `resolveVar` — hence the whole emitted body — is unchanged, because
    the resolved slot `curDepth - 1 - varIndex v` depends on the variable only
    through `varIndex`. -/
def PreservesVarIndex {Γ Γ' : Ctxt jasminDialect} (h : Ctxt.Hom Γ Γ') : Prop :=
  ∀ {τ : JasminTy} (v : Ctxt.Var Γ τ), varIndex (h v) = varIndex v

/-- `lift` preserves the `varIndex`-preserving property. -/
theorem PreservesVarIndex.lift {Γ Γ' : Ctxt jasminDialect} {s : JasminTy}
    {h : Ctxt.Hom Γ Γ'} (hh : PreservesVarIndex h) :
    PreservesVarIndex (Ctxt.Hom.lift (s := s) h) := by
  intro τ v
  cases v with
  | here => rfl
  | there w => simp only [varIndex_lift_there, hh w, varIndex]

/-- `resolveVar` depends on a variable only through its De Bruijn index, so it is
    unchanged by a `varIndex`-preserving renaming. -/
theorem resolveVar_of_varIndex (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ Γ' : Ctxt jasminDialect}
    {h : Ctxt.Hom Γ Γ'} (hh : PreservesVarIndex h) {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    resolveVar curDepth nArgs argNames immSlotMap (h v)
      = resolveVar curDepth nArgs argNames immSlotMap v := by
  simp only [resolveVar, hh v]

/-- The `resolveVar`-map underlying `exprArgs`, over an explicit `HVector` of
    variables. Definitionally equal to `exprArgs.go`. -/
def mapResolve (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → List LOperand
  | [], _ => []
  | _ :: _, .cons v rest =>
      resolveVar curDepth nArgs argNames immSlotMap v ::
        mapResolve curDepth nArgs argNames immSlotMap rest

/-- `exprArgs.go` is the `resolveVar`-map over its argument vector. -/
theorem go_eq_mapResolve (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} → (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    exprArgs.go curDepth nArgs argNames immSlotMap hv
      = mapResolve curDepth nArgs argNames immSlotMap hv
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show resolveVar curDepth nArgs argNames immSlotMap v ::
          exprArgs.go curDepth nArgs argNames immSlotMap rest
        = resolveVar curDepth nArgs argNames immSlotMap v ::
          mapResolve curDepth nArgs argNames immSlotMap rest
      rw [go_eq_mapResolve curDepth nArgs argNames immSlotMap rest]

/-- `exprArgs` is the `resolveVar`-map over the `Expr`'s argument vector. -/
theorem exprArgs_eq_mapResolve (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) :
    exprArgs curDepth nArgs argNames immSlotMap e
      = mapResolve curDepth nArgs argNames immSlotMap e.args :=
  go_eq_mapResolve curDepth nArgs argNames immSlotMap e.args

/-- The `resolveVar`-map is invariant under a `varIndex`-preserving renaming. -/
theorem mapResolve_rename (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ Γ' : Ctxt jasminDialect}
    {h : Ctxt.Hom Γ Γ'} (hh : PreservesVarIndex h) :
    {tys : List JasminTy} → (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    mapResolve curDepth nArgs argNames immSlotMap (HVector.renameVars h hv)
      = mapResolve curDepth nArgs argNames immSlotMap hv
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show resolveVar curDepth nArgs argNames immSlotMap (h v) ::
          mapResolve curDepth nArgs argNames immSlotMap (HVector.renameVars h rest)
        = resolveVar curDepth nArgs argNames immSlotMap v ::
          mapResolve curDepth nArgs argNames immSlotMap rest
      rw [resolveVar_of_varIndex curDepth nArgs argNames immSlotMap hh v,
          mapResolve_rename curDepth nArgs argNames immSlotMap hh rest]

/-- `exprArgs` is invariant under a `varIndex`-preserving renaming. -/
theorem exprArgs_rename (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ Γ' : Ctxt jasminDialect}
    {h : Ctxt.Hom Γ Γ'} (hh : PreservesVarIndex h) {t : JasminTy}
    (e : Expr jasminDialect Γ t) :
    exprArgs curDepth nArgs argNames immSlotMap (e.rename h)
      = exprArgs curDepth nArgs argNames immSlotMap e := by
  rw [exprArgs_eq_mapResolve, exprArgs_eq_mapResolve]
  show mapResolve curDepth nArgs argNames immSlotMap (HVector.renameVars h e.args)
      = mapResolve curDepth nArgs argNames immSlotMap e.args
  exact mapResolve_rename curDepth nArgs argNames immSlotMap hh e.args

/-- `comToBody` is invariant under a `varIndex`-preserving renaming: the renamed
    program emits the same flat body, because every variable resolves to the same
    slot and every destination register is fixed by the shared depth counter. -/
theorem comToBody_rename_of_varIndex (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) :
    {Γ Γ' : Ctxt jasminDialect} → {h : Ctxt.Hom Γ Γ'} → PreservesVarIndex h →
    {t : JasminTy} → (c : Com jasminDialect Γ t) → (curDepth : Nat) →
    comToBody nArgs argNames immSlotMap (Com.rename h c) curDepth
      = comToBody nArgs argNames immSlotMap c curDepth
  | _, _, _, _, _, .ret _, _ => rfl
  | _, _, h, hh, _, .var e body, curDepth => by
      simp only [Com.rename, comToBody]
      rw [show (e.rename h).op = e.op from rfl,
          exprArgs_rename curDepth nArgs argNames immSlotMap hh e,
          comToBody_rename_of_varIndex nArgs argNames immSlotMap hh.lift body (curDepth + 1)]

/-! ## 4b. Renaming algebra -/

/-- `renameVars` respects pointwise-equal renamings. -/
theorem HVector.renameVars_congr {Γ Γ' : Ctxt jasminDialect} {h h' : Ctxt.Hom Γ Γ'}
    (hyp : ∀ {τ : JasminTy} (v : Ctxt.Var Γ τ), h v = h' v) :
    {tys : List JasminTy} → (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    HVector.renameVars h hv = HVector.renameVars h' hv
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show HVector.cons (h v) (HVector.renameVars h rest)
        = HVector.cons (h' v) (HVector.renameVars h' rest)
      rw [hyp v, HVector.renameVars_congr hyp rest]

/-- `renameVars` composes. -/
theorem HVector.renameVars_comp {Γ Γ' Γ'' : Ctxt jasminDialect}
    (h₂ : Ctxt.Hom Γ' Γ'') (h₁ : Ctxt.Hom Γ Γ') :
    {tys : List JasminTy} → (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    HVector.renameVars h₂ (HVector.renameVars h₁ hv)
      = HVector.renameVars (Ctxt.Hom.comp h₂ h₁) hv
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show HVector.cons (h₂ (h₁ v)) (HVector.renameVars h₂ (HVector.renameVars h₁ rest))
        = HVector.cons (h₂ (h₁ v)) (HVector.renameVars (Ctxt.Hom.comp h₂ h₁) rest)
      rw [HVector.renameVars_comp h₂ h₁ rest]

/-- `lift` commutes with composition, pointwise. -/
theorem lift_comp_apply {Γ Γ' Γ'' : Ctxt jasminDialect} {s τ : JasminTy}
    (h₂ : Ctxt.Hom Γ' Γ'') (h₁ : Ctxt.Hom Γ Γ') (v : Ctxt.Var (s :: Γ) τ) :
    Ctxt.Hom.lift (s := s) (Ctxt.Hom.comp h₂ h₁) v
      = Ctxt.Hom.comp (Ctxt.Hom.lift h₂) (Ctxt.Hom.lift h₁) v := by
  cases v <;> rfl

/-- `Com.size` is invariant under renaming. -/
theorem Com.size_rename : {Γ Γ' : Ctxt jasminDialect} → {t : JasminTy} →
    (ρ : Ctxt.Hom Γ Γ') → (c : Com jasminDialect Γ t) →
    Com.size (Com.rename ρ c) = Com.size c
  | _, _, _, _, .ret _ => rfl
  | _, _, _, ρ, .var e body => by
      show Com.size (Com.var (Expr.rename ρ e) (Com.rename ρ.lift body)) = Com.size (Com.var e body)
      simp only [Com.size]
      rw [Com.size_rename ρ.lift body]

/-- `Com.rename` respects pointwise-equal renamings. -/
theorem Com.rename_congr {Γ Γ' : Ctxt jasminDialect} {h h' : Ctxt.Hom Γ Γ'}
    (hyp : ∀ {τ : JasminTy} (v : Ctxt.Var Γ τ), h v = h' v) :
    {t : JasminTy} → (c : Com jasminDialect Γ t) → Com.rename h c = Com.rename h' c
  | _, .ret v => by show Com.ret (h v) = Com.ret (h' v); rw [hyp v]
  | _, .var (t := bs) e body => by
      show Com.var (Expr.rename h e) (Com.rename (Ctxt.Hom.lift h) body)
        = Com.var (Expr.rename h' e) (Com.rename (Ctxt.Hom.lift h') body)
      have hl : ∀ {τ : JasminTy} (w : Ctxt.Var (bs :: Γ) τ),
          Ctxt.Hom.lift (s := bs) h w = Ctxt.Hom.lift (s := bs) h' w := by
        intro τ w; cases w with | here => rfl | there u => exact congrArg _ (hyp u)
      rw [Com.rename_congr hl body]
      congr 1
      show Expr.rename h e = Expr.rename h' e
      simp only [Expr.rename]
      rw [HVector.renameVars_congr hyp e.args]

/-- Renaming composes. -/
theorem Com.rename_comp : {Γ Γ' Γ'' : Ctxt jasminDialect} → {t : JasminTy} →
    (h₂ : Ctxt.Hom Γ' Γ'') → (h₁ : Ctxt.Hom Γ Γ') → (c : Com jasminDialect Γ t) →
    Com.rename h₂ (Com.rename h₁ c) = Com.rename (Ctxt.Hom.comp h₂ h₁) c
  | _, _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, h₂, h₁, .var (t := bs) e body => by
      show Com.var (Expr.rename h₂ (Expr.rename h₁ e))
          (Com.rename (Ctxt.Hom.lift h₂) (Com.rename (Ctxt.Hom.lift h₁) body))
        = Com.var (Expr.rename (Ctxt.Hom.comp h₂ h₁) e)
          (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.comp h₂ h₁)) body)
      rw [Com.rename_comp (Ctxt.Hom.lift h₂) (Ctxt.Hom.lift h₁) body,
          Com.rename_congr (fun {_} v => (lift_comp_apply h₂ h₁ v).symm) body]
      congr 1
      show Expr.rename h₂ (Expr.rename h₁ e) = Expr.rename (Ctxt.Hom.comp h₂ h₁) e
      simp only [Expr.rename]
      rw [HVector.renameVars_comp h₂ h₁ e.args]

/-- Renaming distributes over the block-splice. -/
theorem rename_spliceCom : {Γ Δ : Ctxt jasminDialect} → {t s : JasminTy} →
    (ρ : Ctxt.Hom Γ Δ) → (c : Com jasminDialect Γ t) → (k : Com jasminDialect (t :: Γ) s) →
    Com.rename ρ (spliceCom c k)
      = spliceCom (Com.rename ρ c) (Com.rename (Ctxt.Hom.lift ρ) k)
  | _, _, _, _, ρ, .ret v, k => by
      show Com.rename ρ (Com.rename (substHeadHom v) k)
        = Com.rename (substHeadHom (ρ v)) (Com.rename (Ctxt.Hom.lift ρ) k)
      rw [Com.rename_comp, Com.rename_comp]
      exact Com.rename_congr (fun {_} w => by cases w <;> rfl) k
  | _, _, _, _, ρ, .var (t := bs) e body, k => by
      show Com.var (Expr.rename ρ e)
          (Com.rename (Ctxt.Hom.lift ρ)
            (spliceCom body (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs)) k)))
        = Com.var (Expr.rename ρ e)
          (spliceCom (Com.rename (Ctxt.Hom.lift ρ) body)
            (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs)) (Com.rename (Ctxt.Hom.lift ρ) k)))
      congr 1
      rw [rename_spliceCom (Ctxt.Hom.lift ρ) body
            (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs)) k)]
      congr 1
      rw [Com.rename_comp, Com.rename_comp]
      exact Com.rename_congr (fun {_} w => by cases w <;> rfl) k

/-- The context the continuation `k` is renamed into by `spliceCom c k`. -/
def spliceCtx : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Ctxt jasminDialect
  | Γ, _, .ret _ => Γ
  | _, _, .var _ body => spliceCtx body

/-- The renaming `spliceCom c k` applies to its continuation `k`. -/
def spliceHom : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → Ctxt.Hom (t :: Γ) (spliceCtx c)
  | _, _, .ret v => substHeadHom v
  | Γ, _, .var (t := bs) _ body =>
      Ctxt.Hom.comp (spliceHom body) (Ctxt.Hom.lift (Ctxt.Hom.weakenOne Γ bs))

/-- Splice fusion for `comRetReg`: the return register of `spliceCom c k` is that of
    the renamed continuation, read at the depth past `c`'s bindings. -/
theorem comRetReg_spliceCom (nA : Nat) (an : Nat → String) :
    {Γ : Ctxt jasminDialect} → {t s : JasminTy} → (c : Com jasminDialect Γ t) →
    (k : Com jasminDialect (t :: Γ) s) → (D : Nat) →
    comRetReg nA an (spliceCom c k) D
      = comRetReg nA an (Com.rename (spliceHom c) k) (D + Com.size c)
  | _, _, _, .ret v, k, D => rfl
  | _, _, _, .var (t := bs) e body, k, D => by
      show comRetReg nA an (spliceCom body
          (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs)) k)) (D + 1)
        = comRetReg nA an (Com.rename (spliceHom (.var e body)) k) (D + Com.size (.var e body))
      rw [comRetReg_spliceCom nA an body _ (D + 1), Com.rename_comp,
          show D + 1 + Com.size body = D + Com.size (.var e body) from by
            simp only [Com.size_var]; omega]
      rfl

/-- Splice fusion for `comToBody`: the flat body of `spliceCom c k` is `c`'s block
    prefix followed by the renamed continuation, emitted past `c`'s bindings. -/
theorem comToBody_spliceCom (nA : Nat) (an : Nat → String) (im : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t s : JasminTy} → (c : Com jasminDialect Γ t) →
    (k : Com jasminDialect (t :: Γ) s) → (D : Nat) →
    comToBody nA an im (spliceCom c k) D
      = bodyNoRet nA an im c D
        ++ comToBody nA an im (Com.rename (spliceHom c) k) (D + Com.size c)
  | _, _, _, .ret v, k, D => rfl
  | _, _, _, .var (t := bs) e body, k, D => by
      show ⟨0, opToLinstrR e.op (regName D)
            (exprArgs D nA an im e)⟩ :: comToBody nA an im (spliceCom body
              (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs)) k)) (D + 1)
        = (⟨0, opToLinstrR e.op (regName D) (exprArgs D nA an im e)⟩
            :: bodyNoRet nA an im body (D + 1))
          ++ comToBody nA an im (Com.rename (spliceHom (.var e body)) k)
              (D + Com.size (.var e body))
      rw [comToBody_spliceCom nA an im body _ (D + 1), Com.rename_comp, List.cons_append,
          show D + 1 + Com.size body = D + Com.size (.var e body) from by
            simp only [Com.size_var]; omega]
      rfl

/-- Under `spliceHom c`, a non-head variable shifts its De Bruijn index by the
    block size. -/
theorem varIndex_spliceHom_there : {Γ : Ctxt jasminDialect} → {t s : JasminTy} →
    (c : Com jasminDialect Γ t) → (X : Ctxt.Var Γ s) →
    varIndex (spliceHom c (Ctxt.Var.there X)) = varIndex X + Com.size c
  | _, _, _, .ret v, X => rfl
  | _, _, _, .var (t := bs) e body, X => by
      show varIndex (spliceHom body (Ctxt.Var.there (Ctxt.Var.there X)))
        = varIndex X + Com.size (.var e body)
      rw [varIndex_spliceHom_there body (Ctxt.Var.there X)]
      simp only [varIndex, Com.size_var]; omega

/-- `comRetReg` is invariant under a `varIndex`-preserving renaming. -/
theorem comRetReg_rename_of_varIndex (nA : Nat) (an : Nat → String) :
    {Γ Γ' : Ctxt jasminDialect} → {h : Ctxt.Hom Γ Γ'} → PreservesVarIndex h →
    {t : JasminTy} → (c : Com jasminDialect Γ t) → (D : Nat) →
    comRetReg nA an (Com.rename h c) D = comRetReg nA an c D
  | _, _, h, hh, _, .ret v, D => by
      show (match resolveVar D nA an (fun _ => none) (h v) with
            | .reg n => n | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .imm n => toString n | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
        = comRetReg nA an (Com.ret v) D
      rw [resolveVar_of_varIndex D nA an (fun _ => none) hh v]
      rfl
  | _, _, h, hh, _, .var e body, D => by
      show comRetReg nA an (Com.rename (Ctxt.Hom.lift h) body) (D + 1)
        = comRetReg nA an body (D + 1)
      exact comRetReg_rename_of_varIndex nA an hh.lift body (D + 1)

/-- Each covered op's widened block returns its last binding, so `spliceHom`
    sends the block-result variable to De Bruijn index zero. -/
theorem spliceHom_lowerExprBlock_here {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom (widen8Ctxt Γ) Δ) (e : Expr jasminDialect Γ t) (hcov : CoveredExpr e) :
    varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e)) Ctxt.Var.here) = 0 := by
  obtain ⟨op, rfl, args⟩ := e
  cases op
  case regArith bop w =>
    cases args with
    | cons a rest => cases rest with
      | cons b rest2 => cases rest2 with
        | nil =>
          cases bop <;>
            first
            | (simp only [CoveredExpr] at hcov; subst hcov; rfl)
            | (simp only [CoveredExpr] at hcov)
  case shlImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _⟩ : w = 32 ∧ n < 32 := hcov
        subst hw; rfl
  case shrImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _⟩ : w = 32 ∧ n < 32 := hcov
        subst hw; rfl
  case sarImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil => simp only [CoveredExpr] at hcov; subst hcov; rfl
  case rorImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _, _⟩ : w = 32 ∧ 0 < n ∧ n < 32 := hcov
        subst hw; rfl
  case regConst w kk =>
    cases args
    simp only [CoveredExpr] at hcov; subst hcov; rfl
  case stackLoad w n =>
    cases args with
    | cons arr rest => cases rest with
      | cons idx rest2 => cases rest2 with
        | nil => simp only [CoveredExpr] at hcov; subst hcov; rfl
  all_goals (simp only [CoveredExpr] at hcov)

/-! ## 5. The fused-body anchor equalities

The block-splice `blockLowerCom` inlines each op's block at the same integer
depth `comToBody` would emit it, and rebases the continuation's variables by the
De Bruijn transport `spliceCom` inserts. For a multi-binder block (the rotate,
`blockSize = 3`) that transport shifts the continuation's non-head De Bruijn
indices, so the naive factorisation
`comToBody (spliceCom c k) D = bodyNoRet c D ++ comToBody k (D + Com.size c)`
with the *unrenamed* `k` fails; the continuation resolves against the renamed
program, which the fused `endSlot` table also encodes. Relating the two is the
remaining content of the generalized invariant `batch8Body_eq`. -/

/-- Reading the just-pushed slot. -/
theorem getD_push_of_size (a : Array Nat) (x d : Nat) {n : Nat} (h : a.size = n) :
    (a.push x).getD n d = x := by
  subst h; simp [Array.getD]

/-- Reading an earlier slot is unaffected by a push. -/
theorem getD_push_of_lt (a : Array Nat) (x d : Nat) {i : Nat} (h : i < a.size) :
    (a.push x).getD i d = a.getD i d := by
  have : i < a.size + 1 := by omega
  simp [Array.getD, h, this, Array.getElem_push_lt]

/-- An in-range read of `Array.range` returns the index. -/
theorem getD_range (n i d : Nat) (h : i < n) : (Array.range n).getD i d = i := by
  simp [Array.getD, Array.size_range, h, Array.getElem_range]

/-- The fused operand resolution of a scalar variable coincides with `resolveVar`
    on its widened transport, whenever the slot equality of `RetInv` holds. -/
theorem operand_eq (nA sDepth wDepth : Nat) (immSlotMap : ImmSlotMap) (endSlot : Array Nat)
    {Γ Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom (widen8Ctxt Γ) Δ) {τ : JasminTy}
    (v : Ctxt.Var Γ τ)
    (h : wDepth - 1 - varIndex (ρ (mapVar v))
        = endSlot.getD (sDepth - 1 - varIndex v) (sDepth - 1 - varIndex v)) :
    operandOfVar nA sDepth immSlotMap endSlot v
      = resolveVar wDepth nA argName immSlotMap (ρ (mapVar v)) := by
  simp only [operandOfVar, resolveVar]
  rw [h]
  split_ifs <;> rfl

/-- The invariant tying the fused `endSlot` table to the widened program's variable
    resolution: every in-scope scalar slot resolves, through the threaded renaming
    `ρ`, to the widened slot `endSlot` records for it. -/
def RetInv {Γ Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom (widen8Ctxt Γ) Δ)
    (sDepth wDepth : Nat) (endSlot : Array Nat) : Prop :=
  endSlot.size = sDepth ∧ (∀ {τ : JasminTy} (v : Ctxt.Var Γ τ), varIndex v < sDepth) ∧
    ∀ {τ : JasminTy} (v : Ctxt.Var Γ τ),
      wDepth - 1 - varIndex (ρ (mapVar v))
        = endSlot.getD (sDepth - 1 - varIndex v) (sDepth - 1 - varIndex v)

/-- **Generalized return-register invariant.** For a covered program, under a
    renaming `ρ` and `endSlot` table meeting `RetInv`, the fused return register
    equals the widened program's. -/
theorem batch8RetReg_gen (nA : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (com : Com jasminDialect Γ t) →
    Batch8Covered com → {Δ : Ctxt jasminDialect} → (ρ : Ctxt.Hom (widen8Ctxt Γ) Δ) →
    (sDepth wDepth : Nat) → (endSlot : Array Nat) → RetInv ρ sDepth wDepth endSlot →
    comRetReg nA argName (Com.rename ρ (lowering.blockLowerCom com)) wDepth
      = batch8RetReg nA com sDepth wDepth endSlot
  | _, _, .ret v, _, _, ρ, sDepth, wDepth, endSlot, hinv => by
      show comRetReg nA argName (Com.ret (ρ (mapVar v))) wDepth
        = batch8RetReg nA (Com.ret v) sDepth wDepth endSlot
      simp only [comRetReg, resolveVar, batch8RetReg]
      rw [hinv.2.2 v]
      split_ifs <;> rfl
  | _, _, .var e body, hcov, _, ρ, sDepth, wDepth, endSlot, hinv => by
      obtain ⟨hsize, hbnd, hinvv⟩ := hinv
      have hcov1 := hcov.1
      have hcov2 := hcov.2
      have hsz := size_lowerExprBlock e hcov1
      show comRetReg nA argName (Com.rename ρ (spliceCom (lowering.lowerExprBlock e)
          (lowering.blockLowerCom body))) wDepth
        = batch8RetReg nA (Com.var e body) sDepth wDepth endSlot
      erw [rename_spliceCom, comRetReg_spliceCom, Com.rename_comp]
      refine (batch8RetReg_gen nA body hcov2 _ (sDepth + 1)
        (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)))
        (endSlot.push (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1))
        ⟨by simp [Array.size_push, hsize],
         fun w => by cases w with
           | here => simp only [varIndex]; omega
           | there u => simp only [varIndex]; have := hbnd u; omega, ?_⟩).trans ?_
      · intro τ w
        cases w with
        | here =>
            have h0 : varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))
                (Ctxt.Hom.lift ρ Ctxt.Var.here)) = 0 := spliceHom_lowerExprBlock_here ρ e hcov1
            show wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1
                - varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))
                    (Ctxt.Hom.lift ρ Ctxt.Var.here))
              = (endSlot.push (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1)).getD
                  sDepth sDepth
            rw [h0, getD_push_of_size _ _ _ hsize, Nat.sub_zero]
        | there u =>
            have hthere : varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))
                (Ctxt.Hom.lift ρ (Ctxt.Var.there (mapVar u))))
              = varIndex (ρ (mapVar u)) + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) :=
              varIndex_spliceHom_there (Com.rename ρ (lowering.lowerExprBlock e)) (ρ (mapVar u))
            show wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1
                - varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))
                    (Ctxt.Hom.lift ρ (Ctxt.Var.there (mapVar u))))
              = (endSlot.push (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1)).getD
                  (sDepth + 1 - 1 - varIndex (Ctxt.Var.there u))
                  (sDepth + 1 - 1 - varIndex (Ctxt.Var.there u))
            have hu := hbnd u
            rw [hthere,
                show sDepth + 1 - 1 - varIndex (Ctxt.Var.there u) = sDepth - 1 - varIndex u from by
                  simp only [varIndex]; omega,
                getD_push_of_lt _ _ _ (by simp only [hsize]; omega), ← hinvv u]
            show wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1
                - (varIndex (ρ (mapVar u)) + Com.size (Com.rename ρ (lowering.lowerExprBlock e)))
              = wDepth - 1 - varIndex (ρ (mapVar u))
            omega
      · show batch8RetReg nA body (sDepth + 1) (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)))
              (endSlot.push (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1))
            = batch8RetReg nA body (sDepth + 1) (wDepth + blockSize e)
              (endSlot.push (wDepth + blockSize e - 1))
        rw [show Com.size (Com.rename ρ (lowering.lowerExprBlock e)) = blockSize e from
              (Com.size_rename ρ (lowering.lowerExprBlock e)).trans hsz]

/-- The fused body's return register equals the widened program's. The return
    slot is rendered as a real register, so no `immSlotMap` enters. -/
theorem batch8RetReg_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (hcov : Batch8Covered com) (_immSlotMap : ImmSlotMap) :
    batch8RetReg Γ.length com Γ.length Γ.length (Array.range Γ.length)
      = comRetReg Γ.length argName (batch8 com) Γ.length := by
  have hpid : PreservesVarIndex (Ctxt.Hom.id (widen8Ctxt Γ)) := fun v => rfl
  have key := batch8RetReg_gen Γ.length com hcov (Ctxt.Hom.id (widen8Ctxt Γ))
    Γ.length Γ.length (Array.range Γ.length)
    ⟨by simp [Array.size_range], fun v => varIndex_lt v, fun v => by
      have hlt := varIndex_lt v
      show Γ.length - 1 - varIndex (mapVar v)
        = (Array.range Γ.length).getD (Γ.length - 1 - varIndex v) (Γ.length - 1 - varIndex v)
      rw [varIndex_mapVar, getD_range _ _ _ (by omega)]⟩
  erw [comRetReg_rename_of_varIndex Γ.length argName hpid] at key
  exact key.symm

/-- The `resolveVar` slot is invariant under lifting the depth and the variable
    together: reading a `there`-shifted variable one depth deeper is the same
    operand. -/
theorem resolveVar_there_succ (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {s τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    resolveVar (curDepth + 1) nArgs argNames immSlotMap (Ctxt.Var.there (s := s) v)
      = resolveVar curDepth nArgs argNames immSlotMap v := by
  simp only [resolveVar, varIndex,
    show curDepth + 1 - 1 - (varIndex v + 1) = curDepth - 1 - varIndex v from by omega]

/-- **Per-op block equality.** Each covered op's flat `blockBody` equals the
    `bodyNoRet` of its widened block under the threaded renaming, using the operand
    correspondence `hop`; the rotate's intra-block registers need `nA ≤ wDepth`. -/
theorem blockBody_eq (nA sDepth wDepth : Nat) (immSlotMap : ImmSlotMap) (endSlot : Array Nat)
    {Γ Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom (widen8Ctxt Γ) Δ) (hnA : nA ≤ wDepth)
    (hop : ∀ {τ' : JasminTy} (a : Ctxt.Var Γ τ'),
      operandOfVar nA sDepth immSlotMap endSlot a
        = resolveVar wDepth nA argName immSlotMap (ρ (mapVar a)))
    {τ : JasminTy} (e : Expr jasminDialect Γ τ) (hcov : CoveredExpr e) :
    blockBody nA sDepth wDepth immSlotMap endSlot e
      = bodyNoRet nA argName immSlotMap (Com.rename ρ (lowering.lowerExprBlock e)) wDepth := by
  obtain ⟨op, rfl, args⟩ := e
  -- The binary widened op for a covered `regArith`, unary for the shifts.
  cases op
  case regArith bop w =>
    cases args with
    | cons a rest => cases rest with
      | cons b rest2 => cases rest2 with
        | nil =>
          have close : ∀ wop : YmmDialect.YmmOp,
              [(⟨0, opToLinstrR (.vymm wop) (regName wDepth)
                  [operandOfVar nA sDepth immSlotMap endSlot a,
                   operandOfVar nA sDepth immSlotMap endSlot b]⟩ : Linstr)]
                = [(⟨0, opToLinstrR (.vymm wop) (regName wDepth)
                    [resolveVar wDepth nA argName immSlotMap (ρ (mapVar a)),
                     resolveVar wDepth nA argName immSlotMap (ρ (mapVar b))]⟩ : Linstr)] := by
            intro wop; rw [hop a, hop b]
          cases bop
          case add => simp only [CoveredExpr] at hcov; subst hcov; exact close .vpaddd
          case xor => simp only [CoveredExpr] at hcov; subst hcov; exact close .vpxor
          case or => simp only [CoveredExpr] at hcov; subst hcov; exact close .vpor
          case and => simp only [CoveredExpr] at hcov; subst hcov; exact close .vpand
          case sub => simp only [CoveredExpr] at hcov; subst hcov; exact close .vpsubd
          case mul => simp only [CoveredExpr] at hcov; subst hcov; exact close .vpmulld
          case andn => simp only [CoveredExpr] at hcov; subst hcov; exact close .vpandn
          all_goals (simp only [CoveredExpr] at hcov)
  case shlImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _⟩ : w = 32 ∧ n < 32 := hcov
        subst hw
        show [(⟨0, opToLinstrR (.vymm (.vpslld n)) (regName wDepth)
                [operandOfVar nA sDepth immSlotMap endSlot a]⟩ : Linstr)]
          = [(⟨0, opToLinstrR (.vymm (.vpslld n)) (regName wDepth)
                [resolveVar wDepth nA argName immSlotMap (ρ (mapVar a))]⟩ : Linstr)]
        rw [hop a]
  case shrImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _⟩ : w = 32 ∧ n < 32 := hcov
        subst hw
        show [(⟨0, opToLinstrR (.vymm (.vpsrld n)) (regName wDepth)
                [operandOfVar nA sDepth immSlotMap endSlot a]⟩ : Linstr)]
          = [(⟨0, opToLinstrR (.vymm (.vpsrld n)) (regName wDepth)
                [resolveVar wDepth nA argName immSlotMap (ρ (mapVar a))]⟩ : Linstr)]
        rw [hop a]
  case sarImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        simp only [CoveredExpr] at hcov; subst hcov
        show [(⟨0, opToLinstrR (.vymm (.vpsrad n)) (regName wDepth)
                [operandOfVar nA sDepth immSlotMap endSlot a]⟩ : Linstr)]
          = [(⟨0, opToLinstrR (.vymm (.vpsrad n)) (regName wDepth)
                [resolveVar wDepth nA argName immSlotMap (ρ (mapVar a))]⟩ : Linstr)]
        rw [hop a]
  case rorImm w n =>
    cases args with
    | cons a rest => cases rest with
      | nil =>
        obtain ⟨hw, _, _⟩ : w = 32 ∧ 0 < n ∧ n < 32 := hcov
        subst hw
        have e3 : resolveVar (wDepth + 2) nA argName immSlotMap
              (Ctxt.Var.there (s := widen8Ty (.reg 32))
                (Ctxt.Var.here : Ctxt.Var (widen8Ty (.reg 32) :: widen8Ctxt Γ)
                (widen8Ty (.reg 32)))) = .reg (regName wDepth) := by
          simp only [resolveVar, varIndex,
            show wDepth + 2 - 1 - (0 + 1) = wDepth from by omega, ite_eq_right (by omega : ¬ wDepth < nA)]
        have e4 : resolveVar (wDepth + 2) nA argName immSlotMap
              (Ctxt.Var.here : Ctxt.Var (widen8Ty (.reg 32) :: widen8Ty (.reg 32) :: widen8Ctxt Γ)
                (widen8Ty (.reg 32))) = .reg (regName (wDepth + 1)) := by
          simp only [resolveVar, varIndex,
            show wDepth + 2 - 1 - 0 = wDepth + 1 from by omega,
            ite_eq_right (by omega : ¬ wDepth + 1 < nA)]
        show [(⟨0, opToLinstrR (.vymm (.vpslld (32 - n))) (regName wDepth)
                [operandOfVar nA sDepth immSlotMap endSlot a]⟩ : Linstr),
              ⟨0, opToLinstrR (.vymm (.vpsrld n)) (regName (wDepth + 1))
                [operandOfVar nA sDepth immSlotMap endSlot a]⟩,
              ⟨0, opToLinstrR (.vymm .vpor) (regName (wDepth + 2))
                [.reg (regName wDepth), .reg (regName (wDepth + 1))]⟩]
          = [(⟨0, opToLinstrR (.vymm (.vpslld (32 - n))) (regName wDepth)
                [resolveVar wDepth nA argName immSlotMap (ρ (mapVar a))]⟩ : Linstr),
             ⟨0, opToLinstrR (.vymm (.vpsrld n)) (regName (wDepth + 1))
                [resolveVar (wDepth + 1) nA argName immSlotMap (Ctxt.Var.there (ρ (mapVar a)))]⟩,
             ⟨0, opToLinstrR (.vymm .vpor) (regName (wDepth + 2))
                [resolveVar (wDepth + 2) nA argName immSlotMap
                   (Ctxt.Var.there (s := widen8Ty (.reg 32))
                     (Ctxt.Var.here : Ctxt.Var (widen8Ty (.reg 32) :: widen8Ctxt Γ)
                     (widen8Ty (.reg 32)))),
                 resolveVar (wDepth + 2) nA argName immSlotMap
                   (Ctxt.Var.here : Ctxt.Var (widen8Ty (.reg 32) :: widen8Ty (.reg 32) :: widen8Ctxt Γ)
                     (widen8Ty (.reg 32)))]⟩]
        rw [hop a, resolveVar_there_succ, e3, e4]
  case regConst w kk =>
    cases args
    simp only [CoveredExpr] at hcov; subst hcov
    rfl
  case stackLoad w n =>
    cases args with
    | cons arr rest => cases rest with
      | cons idx rest2 => cases rest2 with
        | nil =>
          simp only [CoveredExpr] at hcov; subst hcov
          show [(⟨0, opToLinstrR (.stackLoad 256 n) (regName wDepth)
                  [operandOfVar nA sDepth immSlotMap endSlot arr,
                   operandOfVar nA sDepth immSlotMap endSlot idx]⟩ : Linstr)]
            = [(⟨0, opToLinstrR (.stackLoad 256 n) (regName wDepth)
                  [resolveVar wDepth nA argName immSlotMap (ρ (mapVar arr)),
                   resolveVar wDepth nA argName immSlotMap (ρ (mapVar idx))]⟩ : Linstr)]
          rw [hop arr, hop idx]
  all_goals (simp only [CoveredExpr] at hcov)

/-- **Generalized fused-body invariant.** The body analogue of `batch8RetReg_gen`,
    over the same `RetInv`; the head fuses through `blockBody_eq`, the continuation
    through the identical `endSlot` re-establishment. -/
theorem batch8Body_gen (nA : Nat) (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (com : Com jasminDialect Γ t) →
    Batch8Covered com → {Δ : Ctxt jasminDialect} → (ρ : Ctxt.Hom (widen8Ctxt Γ) Δ) →
    (sDepth wDepth : Nat) → (endSlot : Array Nat) → nA ≤ wDepth →
    RetInv ρ sDepth wDepth endSlot →
    batch8Body nA immSlotMap com sDepth wDepth endSlot
      = comToBody nA argName immSlotMap (Com.rename ρ (lowering.blockLowerCom com)) wDepth
  | _, _, .ret v, _, _, ρ, _, _, _, _, _ => rfl
  | _, _, .var e body, hcov, _, ρ, sDepth, wDepth, endSlot, hnA, hinv => by
      obtain ⟨hsize, hbnd, hinvv⟩ := hinv
      have hcov1 := hcov.1
      have hcov2 := hcov.2
      have hsz := size_lowerExprBlock e hcov1
      have hop : ∀ {τ' : JasminTy} (a : Ctxt.Var _ τ'),
          operandOfVar nA sDepth immSlotMap endSlot a
            = resolveVar wDepth nA argName immSlotMap (ρ (mapVar a)) :=
        fun a => operand_eq nA sDepth wDepth immSlotMap endSlot ρ a (hinvv a)
      show blockBody nA sDepth wDepth immSlotMap endSlot e
          ++ batch8Body nA immSlotMap body (sDepth + 1) (wDepth + blockSize e)
              (endSlot.push (wDepth + blockSize e - 1))
        = comToBody nA argName immSlotMap
            (Com.rename ρ (spliceCom (lowering.lowerExprBlock e)
              (lowering.blockLowerCom body))) wDepth
      erw [rename_spliceCom, comToBody_spliceCom, Com.rename_comp]
      refine congrArg₂ (· ++ ·)
        (blockBody_eq nA sDepth wDepth immSlotMap endSlot ρ hnA hop e hcov1) ?_
      have hsz2 : Com.size (Com.rename ρ (lowering.lowerExprBlock e)) = blockSize e :=
        (Com.size_rename ρ (lowering.lowerExprBlock e)).trans hsz
      rw [← hsz2]
      refine batch8Body_gen nA immSlotMap body hcov2
        (Ctxt.Hom.comp (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))) (Ctxt.Hom.lift ρ))
        (sDepth + 1) (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)))
        (endSlot.push (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1))
        (by omega)
        ⟨by simp [Array.size_push, hsize],
         fun w => by cases w with
           | here => simp only [varIndex]; omega
           | there u => simp only [varIndex]; have := hbnd u; omega, ?_⟩
      intro τ w
      cases w with
      | here =>
          have h0 : varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))
              (Ctxt.Hom.lift ρ Ctxt.Var.here)) = 0 := spliceHom_lowerExprBlock_here ρ e hcov1
          show wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1
              - varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))
                  (Ctxt.Hom.lift ρ Ctxt.Var.here))
            = (endSlot.push (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1)).getD
                sDepth sDepth
          rw [h0, getD_push_of_size _ _ _ hsize, Nat.sub_zero]
      | there u =>
          have hthere : varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))
              (Ctxt.Hom.lift ρ (Ctxt.Var.there (mapVar u))))
            = varIndex (ρ (mapVar u)) + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) :=
            varIndex_spliceHom_there (Com.rename ρ (lowering.lowerExprBlock e)) (ρ (mapVar u))
          have hu := hbnd u
          show wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1
              - varIndex (spliceHom (Com.rename ρ (lowering.lowerExprBlock e))
                  (Ctxt.Hom.lift ρ (Ctxt.Var.there (mapVar u))))
            = (endSlot.push (wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1)).getD
                (sDepth + 1 - 1 - varIndex (Ctxt.Var.there u))
                (sDepth + 1 - 1 - varIndex (Ctxt.Var.there u))
          rw [hthere,
              show sDepth + 1 - 1 - varIndex (Ctxt.Var.there u) = sDepth - 1 - varIndex u from by
                simp only [varIndex]; omega,
              getD_push_of_lt _ _ _ (by simp only [hsize]; omega), ← hinvv u]
          show wDepth + Com.size (Com.rename ρ (lowering.lowerExprBlock e)) - 1
              - (varIndex (ρ (mapVar u)) + Com.size (Com.rename ρ (lowering.lowerExprBlock e)))
            = wDepth - 1 - varIndex (ρ (mapVar u))
          omega

/-- **Fused-body anchor.** The one-pass fused body equals the flat lowering of the
    widened program `batch8 com = lowering.blockLowerCom com`, at the initial
    depth `Γ.length` with the identity argument table `Array.range Γ.length`. -/
theorem batch8Body_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (hcov : Batch8Covered com) (immSlotMap : ImmSlotMap) :
    batch8Body Γ.length immSlotMap com Γ.length Γ.length (Array.range Γ.length)
      = comToBody Γ.length argName immSlotMap (batch8 com) Γ.length := by
  have hpid : PreservesVarIndex (Ctxt.Hom.id (widen8Ctxt Γ)) := fun v => rfl
  have key := batch8Body_gen Γ.length immSlotMap com hcov (Ctxt.Hom.id (widen8Ctxt Γ))
    Γ.length Γ.length (Array.range Γ.length) (le_refl _)
    ⟨by simp [Array.size_range], fun v => varIndex_lt v, fun v => by
      have hlt := varIndex_lt v
      show Γ.length - 1 - varIndex (mapVar v)
        = (Array.range Γ.length).getD (Γ.length - 1 - varIndex v) (Γ.length - 1 - varIndex v)
      rw [varIndex_mapVar, getD_range _ _ _ (by omega)]⟩
  erw [comToBody_rename_of_varIndex Γ.length argName immSlotMap hpid] at key
  exact key

/-- **Virtual-`Lfundef` anchor.** The fused `batch8Virt` equals the `Lfundef` that
    lowering the materialised widened program would produce. Reduces field by field
    to `batch8Body_eq` (body) and `batch8RetReg_eq` (result register); the argument
    names, widths and output width match because `widen8Ctxt Γ = Γ.map widen8Ty`
    preserves length and the argument prefix. -/
theorem batch8Virt_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (hcov : Batch8Covered com) (immSlotMap : ImmSlotMap) :
    batch8Virt com immSlotMap = comToLfundef (batch8 com) immSlotMap := by
  have hlen : (widen8Ctxt Γ).length = Γ.length := by
    simp only [widen8Ctxt, List.length_map]
  simp only [batch8Virt, comToLfundef, hlen]
  rw [batch8Body_eq com hcov immSlotMap, batch8RetReg_eq com hcov immSlotMap]

end CatCrypt.Crypto.Optimizer.Batch8EmitProof
