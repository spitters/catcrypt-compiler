/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.LegalizeBy

@[expose] public section

set_option autoImplicit false

/-!
# The rotate legalisation of a structured program

The stage `legalizeRor` of the region back half rewrites every binding of a rotate by an
immediate `rorImm w k` with `0 < k < w` into the shift-or block
`(x >>> k) ||| (x <<< (w - k))` of `shrImm w k`, `shlImm w (w - k)` and `regArith .or w`
(`rorBlock`), in every region: it is the legalisation `legalizeBy isRorB rorBlock`. A program
with no `rorImm` binding is returned unchanged (`legalizeRor_eq_of_noRor`).

## Main definitions

* `isRorB` — the test of a rotate by an immediate.
* `shiftOrBlock`, `rorBlock` — the shift-or block of a rotate, and the block of a binding.
* `legalizeRor` — the stage on a program with one result.

## Main results

* `rorBlock_denote` — the block of a binding denotes the value of the binding.
* `legalizeRor_eq_of_noRor` — the stage is the identity on a program with no `rorImm`.
* `legalizeRor_denoteAt`, `legalizeRor_denote` — the stage keeps the denotation, at every
  call environment and fuel.
* `legalizeRor_leakRun` — at leakage parameters with no variable-time operation the stage
  keeps the leakage run, and `nfct_legalizeRor` constant time at the source events.
* `legalizeRor_callTest`, `legalizeRor_callFree_eq`, `legalizeRor_callFree` — the stage keeps
  every test that reads only the calls, among them the absence of `call`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Expr.ctLeak Com.ctLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open Ctxt (Var Valuation)

/-! ## 1. The block of a binding -/

/-- The test of a rotate by an immediate. -/
def isRorB : JasminOp → Bool
  | .rorImm _ _ => true
  | _ => false

/-- **The shift-or block of a rotate** of the register `x` of width `w` by `k`: the bindings
    `a := x >>> k` (`shrImm w k`), `b := x <<< (w - k)` (`shlImm w (w - k)`) and
    `a ||| b` (`regArith .or w`), returning the last. -/
def shiftOrBlock {Γ : Ctxt jasminDialect} (w k : Nat) (x : Var Γ (JasminTy.reg w)) :
    Com jasminDialect Γ (JasminTy.reg w) :=
  .var ⟨JasminOp.shrImm w k, rfl, .cons x .nil⟩ <|
  .var ⟨JasminOp.shlImm w (w - k), rfl, .cons (.there x) .nil⟩ <|
  .var ⟨JasminOp.regArith .or w, rfl, .cons (.there .here) (.cons .here .nil)⟩ <|
  .ret Var.here

/-- **The block of a binding**: the shift-or block `shiftOrBlock w k x` of a rotate
    `rorImm w k` of `x` with `0 < k < w`, and the binding followed by the return of its value
    on every other binding. -/
def rorBlock {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Expr jasminDialect Γ t → Com jasminDialect Γ t
  | ⟨.rorImm w k, heq, args⟩ =>
      if 0 < k ∧ k < w then heq ▸ shiftOrBlock w k args.head
      else .var ⟨.rorImm w k, heq, args⟩ (.ret Var.here)
  | e => .var e (.ret Var.here)

/-- The shift-or block of a rotate of `x` by `0 < k < w` denotes the rotate of the value of
    `x`. -/
theorem shiftOrBlock_denote {Γ : Ctxt jasminDialect} (w k : Nat) (hk : 0 < k ∧ k < w)
    (x : Var Γ (JasminTy.reg w)) (V : Valuation Γ) :
    (shiftOrBlock w k x).denote V
      = (show BitVec w from x.lookup V).rotateRight k := by
  rw [rorImm_denote_eq_shiftOr k hk.2]
  show (show BitVec w from x.lookup V) >>> shiftMask w k
    ||| (show BitVec w from x.lookup V) <<< shiftMask w (w - k) = _
  rw [shiftMask_of_lt hk.2, shiftMask_of_lt (by omega : w - k < w)]

/-- **The block of a binding denotes the value of the binding.** -/
theorem rorBlock_denote {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (V : Valuation Γ) : (rorBlock e).denote V = e.denote V := by
  obtain ⟨op, heq, args⟩ := e
  cases op with
  | rorImm w k =>
      cases heq
      cases args with
      | cons x xs =>
          cases xs
          by_cases h : 0 < k ∧ k < w
          · rw [rorBlock, ite_eq_left h]
            exact shiftOrBlock_denote w k h x V
          · rw [rorBlock, ite_eq_right h]
            rfl
  | _ => rfl

/-- **The block of a binding emits the events of the binding** at leakage parameters with no
    variable-time operation. -/
theorem rorBlock_ctLeak {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) (V : Valuation Γ) :
    Com.ctLeak (jLeakModel Pj) (rorBlock e) V = Expr.ctLeak (jLeakModel Pj) e V := by
  obtain ⟨op, heq, args⟩ := e
  cases op with
  | rorImm w k =>
      cases heq
      cases args with
      | cons x xs =>
          cases xs
          by_cases h : 0 < k ∧ k < w
          · rw [rorBlock, ite_eq_left h]
            simp [shiftOrBlock, Com.ctLeak, Expr.ctLeak, ComLevelCheck.opLeak, jLeakModel,
              Dialects.JasminComLLeak.jKind, hV]
          · rw [rorBlock, ite_eq_right h]
            simp [Com.ctLeak]
  | _ => simp [rorBlock, Com.ctLeak]

/-! ## 2. The stage -/

/-- **The rotate legalisation** of a program with one result: the legalisation by the block
    `rorBlock` at the test `isRorB`. -/
def legalizeRor {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    NFProg jasminDialect Γ [t] :=
  legalizeBy isRorB rorBlock p

/-- **On a program with no rotate the stage is the identity.** -/
theorem legalizeRor_eq_of_noRor {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : p.allOps (fun op => !isRorB op) = true) :
    legalizeRor p = p :=
  legalizeBy_eq_of_none h

/-- **The stage keeps the denotation** at every call environment and fuel. -/
theorem legalizeRor_denoteAt (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) (V : Valuation Γ) :
    (legalizeRor p).denoteAt E fuel V = p.denoteAt E fuel V :=
  legalizeBy_denoteAt rorBlock_denote E fuel p V

/-- **The stage keeps the denotation**, at every fuel. -/
theorem legalizeRor_denote [CallDenote jasminDialect] (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    (legalizeRor p).denote fuel = p.denote fuel :=
  legalizeBy_denote rorBlock_denote fuel p

/-- **The stage keeps the leakage run** at leakage parameters with no variable-time
    operation, at every fuel. -/
theorem legalizeRor_leakRun {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (legalizeRor p) V
      = Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V :=
  legalizeBy_leakRun rorBlock_denote (rorBlock_ctLeak hV) fuel p V

/-- **The stage keeps constant time at the source events** at leakage parameters with no
    variable-time operation. -/
theorem nfct_legalizeRor {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {L : ComLevelCheck.Labels Γ} {fuel : Nat}
    (h : Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel p) :
    Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel (legalizeRor p) :=
  nfct_legalizeBy rorBlock_denote (rorBlock_ctLeak hV) h

/-- **The stage keeps the value of every test that reads only the calls.** -/
theorem legalizeRor_callTest {c : String → Bool}
    {F : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool}
    (hF : CallTest c F) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : F (legalizeRor p) = F p :=
  legalizeBy_callTest hF p

/-- **The stage keeps the absence of `call` and its presence.** -/
theorem legalizeRor_callFree_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : (legalizeRor p).callFree = p.callFree :=
  legalizeBy_callFree_eq p

/-- **The stage keeps the absence of `call`.** -/
theorem legalizeRor_callFree {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : p.callFree = true) :
    (legalizeRor p).callFree = true := by
  rw [legalizeRor_callFree_eq, h]

end CatCrypt.Crypto.SecureCompilation.Haxc
