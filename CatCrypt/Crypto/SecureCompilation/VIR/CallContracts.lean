/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgModule
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall

/-!
# Leaf agreements of `jasminDialect` as call-environment contracts

A single-result external-leaf semantics `LeafSem` (the shape of `jasminExtSem`) is a total
call environment of `jasminDialect` whose callees return one value (`CallEnv.ofLeafSem`).
The leaf agreements stated against `jasminExtSem` are then equations of call
environments.

* `JasminPrintSemCorrect.LeafAgrees leafSem` (the printed-code evaluator's leaf equals
  `jasminExtSem` on every agreeing store) is the equation
  `CallEnv.ofLeafSem leafSem = CallEnv.ofLeafSem jasminExtSem`.
* `ComInlineCall.CalleeConsistent name fb` (the callee body computes the leaf `name`) is
  the agreement at `name` of the environment binding `name` to the body with the
  environment of `jasminExtSem`; by `NFProg.denoteAt_congr`, binding `name` to the body
  leaves the denotation of every `NFProg jasminDialect` program unchanged.

## Main definitions

* `CallEnv.ofLeafSem` — the call environment of a single-result leaf semantics.
* `CallEnv.funBodyCallee` — the callee of a statically known function body.

## Main results

* `CallEnv.ofLeafSem_eq_iff` — two leaf environments are equal exactly when the leaf
  semantics agree pointwise.
* `CallContracts.leafAgrees_iff_pointwise` — `LeafAgrees leafSem` is the pointwise
  equality of `leafSem` and `jasminExtSem`.
* `CallContracts.leafAgrees_iff_tableEq` — `LeafAgrees leafSem` is the equation of the two
  leaf environments.
* `CallContracts.calleeConsistent_iff` — `CalleeConsistent name fb` is the agreement of
  the body callee with the `jasminExtSem` environment at `name`.
* `CallContracts.denoteAt_extend_of_calleeConsistent` — binding a consistent callee body at
  `name` in an environment that calls `jasminExtSem` there leaves every program's
  denotation unchanged; `denoteAt_extend_ofLeafSem_of_calleeConsistent` is the instance at
  `CallEnv.ofLeafSem jasminExtSem`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open JasminDialect
open JasminPrint (VarMap paramsAndMap)
open JasminPrintSemCorrect (LeafSem LeafAgrees StoreAgrees lookupArgsStore lookupArgsStore_eq
  seedStore seedStore_agrees)
open ComInlineCall (FunBodyN CalleeConsistent)

/-! ## 1. Leaf environments -/

namespace CallEnv

/-- The call environment of a single-result leaf semantics: the symbol `f` at the
    signature `as → [r]` returns the one value `leafSem f as r`; every signature with a
    result list of another length refuses. -/
def ofLeafSem (leafSem : LeafSem) : CallEnv jasminDialect where
  call f as rs x := match rs with
    | [r] => some (.cons (leafSem f as r x) .nil)
    | _ => none

/-- A leaf environment at a single-result signature returns the leaf value. -/
@[simp] theorem ofLeafSem_call_single (leafSem : LeafSem) (f : String)
    (as : List JasminTy) (r : JasminTy) (x : Valuation (d := jasminDialect) as) :
    (ofLeafSem leafSem).call f as [r] x = some (.cons (leafSem f as r x) .nil) := rfl

/-- Two leaf environments are equal exactly when the leaf semantics agree pointwise. -/
theorem ofLeafSem_eq_iff (l₁ l₂ : LeafSem) :
    ofLeafSem l₁ = ofLeafSem l₂ ↔ ∀ f as r x, l₁ f as r x = l₂ f as r x := by
  constructor
  · intro h f as r x
    have : some (HVector.cons (l₁ f as r x) .nil) = some (.cons (l₂ f as r x) .nil) :=
      congrArg (fun E : CallEnv jasminDialect => E.call f as [r] x) h
    simp only [Option.some.injEq, HVector.cons.injEq] at this
    exact this.1
  · intro h
    have hl : l₁ = l₂ := funext fun f => funext fun as => funext fun r => funext fun x =>
      h f as r x
    rw [hl]

/-- The callee of a statically known function body: one result, the body's denotation. -/
def funBodyCallee (fb : FunBodyN) :
    Valuation (d := jasminDialect) fb.argTys → Option (Valuation (d := jasminDialect) [fb.retTy]) :=
  fun V => some (.cons (fb.body.denote V) .nil)

end CallEnv

namespace CallContracts

/-! ## 2. `LeafAgrees` as a table equation -/

/-- `LeafAgrees leafSem` is the pointwise equality of `leafSem` and `jasminExtSem`. The
    forward direction evaluates the agreement at the seed store of the canonical parameter
    resolver, which agrees with every valuation. -/
theorem leafAgrees_iff_pointwise (leafSem : LeafSem) :
    LeafAgrees leafSem ↔ ∀ f as r x, leafSem f as r x = jasminExtSem f as r x := by
  constructor
  · intro h f as r x
    have hS : StoreAgrees (paramsAndMap as).2 x (seedStore (paramsAndMap as).2 x) :=
      seedStore_agrees WholeFnLowering.paramsAndMap_injective
    have := h (paramsAndMap as).2 x (seedStore (paramsAndMap as).2 x) f as r
      (allVars (d := jasminDialect) as) hS
    rwa [lookupArgsStore_eq hS, lookupArgs_allVars] at this
  · intro h Γ vm V s f as r args hS
    rw [lookupArgsStore_eq hS]
    exact h f as r _

/-- **`LeafAgrees` as a table contract.** `LeafAgrees leafSem` holds exactly when the
    call environment of `leafSem` equals the call environment of `jasminExtSem`. -/
theorem leafAgrees_iff_tableEq (leafSem : LeafSem) :
    LeafAgrees leafSem ↔ CallEnv.ofLeafSem leafSem = CallEnv.ofLeafSem jasminExtSem :=
  (leafAgrees_iff_pointwise leafSem).trans (CallEnv.ofLeafSem_eq_iff _ _).symm

/-! ## 3. `CalleeConsistent` and the congruence theorem -/

/-- `CalleeConsistent name fb` is the agreement at `name` and the signature of `fb` of the
    body callee with the environment of `jasminExtSem`. -/
theorem calleeConsistent_iff (name : String) (fb : FunBodyN) :
    CalleeConsistent name fb ↔ ∀ x, CallEnv.funBodyCallee fb x =
      (CallEnv.ofLeafSem jasminExtSem).call name fb.argTys [fb.retTy] x := by
  show (∀ V, _ = _) ↔ ∀ x, some (HVector.cons (fb.body.denote x) .nil) =
    some (.cons (jasminExtSem name fb.argTys fb.retTy x) .nil)
  simp only [Option.some.injEq, HVector.cons.injEq, and_true]

/-- **Congruence at a consistent callee.** In an environment `E` that calls
    `jasminExtSem` at `name` and the signature of `fb`, binding `name` to the body of a
    callee consistent with the leaf `name` leaves the denotation of every program
    unchanged. -/
theorem denoteAt_extend_of_calleeConsistent (name : String) (fb : FunBodyN)
    (hcon : CalleeConsistent name fb) (E : CallEnv jasminDialect)
    (hE : ∀ x, E.call name fb.argTys [fb.retTy] x =
      (CallEnv.ofLeafSem jasminExtSem).call name fb.argTys [fb.retTy] x)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (fuel : Nat)
    (V : Valuation Γ) :
    p.denoteAt (CallEnv.extend (d := jasminDialect) E name fb.argTys [fb.retTy]
        (CallEnv.funBodyCallee fb)) fuel V =
      p.denoteAt E fuel V := by
  refine NFProg.denoteAt_congr p _ _ (fun f as rs x _ => ?_) fuel V
  by_cases h : f = name ∧ as = fb.argTys ∧ rs = [fb.retTy]
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [CallEnv.extend_call_self (d := jasminDialect), hE]
    exact (calleeConsistent_iff f fb).1 hcon x
  · exact CallEnv.extend_call_of_ne _ _ h x

/-- The instance of `denoteAt_extend_of_calleeConsistent` at the environment of
    `jasminExtSem`. -/
theorem denoteAt_extend_ofLeafSem_of_calleeConsistent (name : String) (fb : FunBodyN)
    (hcon : CalleeConsistent name fb) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (fuel : Nat) (V : Valuation Γ) :
    p.denoteAt (CallEnv.extend (d := jasminDialect) (CallEnv.ofLeafSem jasminExtSem) name
        fb.argTys [fb.retTy] (CallEnv.funBodyCallee fb)) fuel V =
      p.denoteAt (CallEnv.ofLeafSem jasminExtSem) fuel V :=
  denoteAt_extend_of_calleeConsistent name fb hcon _ (fun _ => rfl) p fuel V

end CallContracts

end CatCrypt.Crypto.SecureCompilation.VIR
