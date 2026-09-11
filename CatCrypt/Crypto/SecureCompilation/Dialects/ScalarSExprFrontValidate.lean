/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom


@[expose] public section
set_option autoImplicit false

/-!
# End-to-end validation of the scalar-`SExpr` front arm (`RScalarSetExpr`)

A small GF(16)-style scalar body — bitwise `and`/`xor` plus a shift over the
`u64` slots `a`, `b` — is assigned via `RScalarSetExpr` and pushed through the
`CProg`-free front (`lowerSExpr` ⊂ `translateDialectFull` ⊂
`translateDialectControl`). This file confirms, computationally:

1. the body **translates** (`translateDialectControlTop … = some`);
2. the body **lowers** to a `Com jasminDialect` (`lowCTToJasminComD … = some`),
   i.e. it reaches owned `.s` through `cryptoDialectToJasminCom`;
3. the front's emitted dialect program **denotes to the same value** as the
   `SExpr`'s pure-Lean wrapping-`u64` evaluator `SExpr.evalBV` on sample inputs
   (`denote = spec`), which is the front-arm correctness gate.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprFrontValidate

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- Input context with two `u64` scalar slots `a` (`.here`) and `b`
    (`.there .here`). -/
def testΓ : Ctx := [.sword 64, .sword 64]

/-- `VarMap` binding `a`, `b` to the two slots. -/
def testVM : VarMap testΓ := (VarMap.empty.bind "b").bind "a"

/-- A GF(16)-style scalar body: `(a & b) ^ (a << 1)`. -/
def testE : SExpr := .SXor (.SAnd (.SVar "a") (.SVar "b")) (.SShl (.SVar "a") (.SLit 1))

/-- The whole `LowCT` leaf: `out := (a & b) ^ (a << 1)`. -/
def testC : LowCT := .RScalarSetExpr "out" testE

/-- The pure-Lean `u64`-faithful spec value of `testE` on inputs `av`, `bv`. -/
def specVal (av bv : BitVec 64) : BitVec 64 :=
  testE.evalBV (fun n => if n = "a" then av else if n = "b" then bv else 0)

/-- The front-emitted dialect program for `testE` that *returns the result word*
    (the front's `…Top` wrappers return `unit`; here we keep the result var so we
    can denote the computed value). `none` if the front declines. -/
def frontResultProg : Option (Com catCryptDialect testΓ (.sword 64)) :=
  match lowerSExpr testVM 0 testE with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword 64, v⟩ => r.1.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- Denote `frontResultProg` at inputs `av` (slot `a`) and `bv` (slot `b`). -/
def frontDenote (av bv : BitVec 64) : Option (BitVec 64) :=
  frontResultProg.map (fun com => com.denote (.cons av (.cons bv .nil)))

/-! ## 1. The body translates and lowers -/

/-- The `RScalarSetExpr` body translates through the `CProg`-free control front. -/
theorem testC_translates : (translateDialectControlTop testVM testC).isSome := by
  native_decide

/-- The front-emitted SExpr chain (`bvConst`/`bvAnd`/`bvXor`/`bvShiftLV` plus the
    `bvShiftL 0` result copy) lowers end-to-end to a `Com jasminDialect` — i.e. it
    reaches owned `.s` through `cryptoDialectToJasminCom`. -/
theorem testC_lowers :
    (frontResultProg.bind DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  native_decide

/-! ## 2. `denote = spec` on sample inputs (front-arm correctness gate) -/

/-- The front actually emits a result program. -/
theorem frontResultProg_isSome : frontResultProg.isSome := by native_decide

example : frontDenote 0x1234 0xABCD = some (specVal 0x1234 0xABCD) := by native_decide
example : frontDenote 0xFFFFFFFFFFFFFFFF 1 = some (specVal 0xFFFFFFFFFFFFFFFF 1) := by
  native_decide
example : frontDenote 0 0 = some (specVal 0 0) := by native_decide
example : frontDenote 0xDEADBEEF12345678 0x0F0F0F0F0F0F0F0F
    = some (specVal 0xDEADBEEF12345678 0x0F0F0F0F0F0F0F0F) := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprFrontValidate
