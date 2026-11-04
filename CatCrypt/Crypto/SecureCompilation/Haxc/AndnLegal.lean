/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RorLegal

@[expose] public section

set_option autoImplicit false

/-!
# The and-not legalisation and the region legalisation of a structured program

The stage `legalizeAndn` rewrites every binding of the BMI1 and-not `regArith .andn w` of
`a` and `b`, which denotes `(~~~a) &&& b`, into the block `(a &&& b) ^^^ b` of
`regArith .and w` and `regArith .xor w` (`andXorBlock`), in every region: it is the
legalisation `legalizeBy isAndnB andnBlock`. A program with no and-not binding is returned
unchanged (`legalizeAndn_eq_of_noAndn`). The region legalisation `legalizeRegion` of the
region back half is the identity: a rotate by an immediate and the and-not are compiled
natively (`ROR`, and the BMI1 `ANDN` of the encoder and the decoder), so no operation of the
fragment is rewritten before the export.

## Main definitions

* `isAndnB` — the test of an and-not.
* `andXorBlock`, `andnBlock` — the and-xor block of an and-not, and the block of a binding.
* `legalizeAndn` — the stage on a program with one result.
* `legalizeRegion` — the region legalisation, the identity.

## Main results

* `andnBlock_denote` — the block of a binding denotes the value of the binding.
* `legalizeAndn_eq_of_noAndn` — the stage is the identity on a program with no and-not.
* `legalizeAndn_denoteAt`, `legalizeAndn_denote` — the stage keeps the denotation, at every
  call environment and fuel.
* `legalizeAndn_leakRun` — at leakage parameters with no variable-time operation the stage
  keeps the leakage run, and `nfct_legalizeAndn` constant time at the source events.
* `legalizeAndn_callTest` — the stage keeps the value of every `CallTest`, and
  `legalizeAndn_callFree_eq`, `legalizeAndn_callFree` the absence of `call`.
* `legalizeRegion_denoteAt`, `legalizeRegion_denote`, `legalizeRegion_leakRun`,
  `nfct_legalizeRegion`, `legalizeRegion_callTest`, `legalizeRegion_callFree_eq`,
  `legalizeRegion_callFree` — the same facts for the region legalisation.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Expr.ctLeak Com.ctLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open Ctxt (Var Valuation)

/-! ## 1. The block of a binding -/

/-- The test of an and-not. -/
def isAndnB : JasminOp → Bool
  | .regArith .andn _ => true
  | _ => false

/-- **The and-xor block of an and-not** of the registers `a` and `b` of width `w`: the
    bindings `c := a &&& b` (`regArith .and w`) and `c ^^^ b` (`regArith .xor w`), returning
    the last. -/
def andXorBlock {Γ : Ctxt jasminDialect} (w : Nat) (a b : Var Γ (JasminTy.reg w)) :
    Com jasminDialect Γ (JasminTy.reg w) :=
  .var ⟨JasminOp.regArith .and w, rfl, .cons a (.cons b .nil)⟩ <|
  .var ⟨JasminOp.regArith .xor w, rfl, .cons .here (.cons (.there b) .nil)⟩ <|
  .ret Var.here

/-- **The block of a binding**: the and-xor block `andXorBlock w a b` of an and-not
    `regArith .andn w` of `a` and `b`, and the binding followed by the return of its value on
    every other binding. -/
def andnBlock {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Expr jasminDialect Γ t → Com jasminDialect Γ t
  | ⟨.regArith .andn w, heq, args⟩ => heq ▸ andXorBlock w args.head args.tail.head
  | e => .var e (.ret Var.here)

/-- The and-xor block of `a` and `b` denotes the and-not of their values. -/
theorem andXorBlock_denote {Γ : Ctxt jasminDialect} (w : Nat) (a b : Var Γ (JasminTy.reg w))
    (V : Valuation Γ) :
    (andXorBlock w a b).denote V
      = (~~~(show BitVec w from a.lookup V)) &&& (show BitVec w from b.lookup V) := by
  have hxy : ∀ x y : BitVec w, (x &&& y) ^^^ y = ~~~x &&& y := by
    grind only [= BitVec.getElem_xor, = BitVec.getElem_and, = BitVec.getElem_not]
  exact hxy _ _

/-- **The block of a binding denotes the value of the binding.** -/
theorem andnBlock_denote {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (V : Valuation Γ) : (andnBlock e).denote V = e.denote V := by
  obtain ⟨op, heq, args⟩ := e
  cases op with
  | regArith bop w =>
      cases heq
      cases bop with
      | andn =>
          cases args with
          | cons a xs =>
              cases xs with
              | cons b ys =>
                  cases ys
                  rw [andnBlock]
                  exact andXorBlock_denote w a b V
      | _ => rfl
  | _ => rfl

/-- **The block of a binding emits the events of the binding** at leakage parameters with no
    variable-time operation. -/
theorem andnBlock_ctLeak {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) (V : Valuation Γ) :
    Com.ctLeak (jLeakModel Pj) (andnBlock e) V = Expr.ctLeak (jLeakModel Pj) e V := by
  obtain ⟨op, heq, args⟩ := e
  cases op with
  | regArith bop w =>
      cases heq
      cases bop with
      | andn =>
          cases args with
          | cons a xs =>
              cases xs with
              | cons b ys =>
                  cases ys
                  rw [andnBlock]
                  simp [andXorBlock, Com.ctLeak, Expr.ctLeak, ComLevelCheck.opLeak, jLeakModel,
                    Dialects.JasminComLLeak.jKind, hV]
      | _ => simp [andnBlock, Com.ctLeak]
  | _ => simp [andnBlock, Com.ctLeak]

/-! ## 2. The stage -/

/-- **The and-not legalisation** of a program with one result: the legalisation by the block
    `andnBlock` at the test `isAndnB`. -/
def legalizeAndn {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    NFProg jasminDialect Γ [t] :=
  legalizeBy isAndnB andnBlock p

/-- **On a program with no and-not the stage is the identity.** -/
theorem legalizeAndn_eq_of_noAndn {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : p.allOps (fun op => !isAndnB op) = true) :
    legalizeAndn p = p :=
  legalizeBy_eq_of_none h

/-- **The stage keeps the denotation** at every call environment and fuel. -/
theorem legalizeAndn_denoteAt (E : CallEnv jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (V : Valuation Γ) :
    (legalizeAndn p).denoteAt E fuel V = p.denoteAt E fuel V :=
  legalizeBy_denoteAt andnBlock_denote E fuel p V

/-- **The stage keeps the denotation**, at every fuel. -/
theorem legalizeAndn_denote [CallDenote jasminDialect] (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    (legalizeAndn p).denote fuel = p.denote fuel :=
  legalizeBy_denote andnBlock_denote fuel p

/-- **The stage keeps the leakage run** at leakage parameters with no variable-time
    operation, at every fuel. -/
theorem legalizeAndn_leakRun {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (legalizeAndn p) V
      = Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V :=
  legalizeBy_leakRun andnBlock_denote (andnBlock_ctLeak hV) fuel p V

/-- **The stage keeps constant time at the source events** at leakage parameters with no
    variable-time operation. -/
theorem nfct_legalizeAndn {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {L : ComLevelCheck.Labels Γ} {fuel : Nat}
    (h : Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel p) :
    Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel (legalizeAndn p) :=
  nfct_legalizeBy andnBlock_denote (andnBlock_ctLeak hV) h

/-- **The stage keeps the value of every test that reads only the calls.** -/
theorem legalizeAndn_callTest {c : String → Bool}
    {F : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool}
    (hF : CallTest c F) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : F (legalizeAndn p) = F p :=
  legalizeBy_callTest hF p

/-- **The stage keeps the absence of `call` and its presence.** -/
theorem legalizeAndn_callFree_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : (legalizeAndn p).callFree = p.callFree :=
  legalizeBy_callFree_eq p

/-- **The stage keeps the absence of `call`.** -/
theorem legalizeAndn_callFree {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : p.callFree = true) :
    (legalizeAndn p).callFree = true := by
  rw [legalizeAndn_callFree_eq, h]

/-! ## 3. The region legalisation -/

/-- **The region legalisation** of a program with one result: the identity. A rotate by an
    immediate and the and-not are compiled natively, so neither the rotate legalisation
    `legalizeRor` nor the and-not legalisation `legalizeAndn` is a stage. -/
def legalizeRegion {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    NFProg jasminDialect Γ [t] :=
  p

/-- **The region legalisation keeps the denotation** at every call environment and fuel. -/
theorem legalizeRegion_denoteAt (E : CallEnv jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (V : Valuation Γ) :
    (legalizeRegion p).denoteAt E fuel V = p.denoteAt E fuel V :=
  rfl

/-- **The region legalisation keeps the denotation**, at every fuel. -/
theorem legalizeRegion_denote [CallDenote jasminDialect] (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    (legalizeRegion p).denote fuel = p.denote fuel :=
  rfl

/-- **The region legalisation keeps the leakage run** at leakage parameters with no
    variable-time operation, at every fuel. -/
theorem legalizeRegion_leakRun {Pj : JLeakParams} (_hV : ∀ op, Pj.opVT op = none) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (legalizeRegion p) V
      = Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V :=
  rfl

/-- **The region legalisation keeps constant time at the source events** at leakage
    parameters with no variable-time operation. -/
theorem nfct_legalizeRegion {Pj : JLeakParams} (_hV : ∀ op, Pj.opVT op = none)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {L : ComLevelCheck.Labels Γ} {fuel : Nat}
    (h : Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel p) :
    Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel (legalizeRegion p) :=
  h

/-- **The region legalisation keeps the value of every test that reads only the calls.** -/
theorem legalizeRegion_callTest {c : String → Bool}
    {F : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool}
    (_hF : CallTest c F) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : F (legalizeRegion p) = F p :=
  rfl

/-- **The region legalisation keeps the absence of `call` and its presence.** -/
theorem legalizeRegion_callFree_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : (legalizeRegion p).callFree = p.callFree :=
  legalizeRegion_callTest callTest_callFree p

/-- **The region legalisation keeps the absence of `call`.** -/
theorem legalizeRegion_callFree {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : p.callFree = true) :
    (legalizeRegion p).callFree = true := by
  rw [legalizeRegion_callFree_eq, h]

end CatCrypt.Crypto.SecureCompilation.Haxc
