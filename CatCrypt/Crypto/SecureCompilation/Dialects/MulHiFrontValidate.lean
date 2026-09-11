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
# End-to-end validation of the scalar high-multiply front arm (`SMulHiU`)

The scalar `SExpr` front (`lowerSExpr`) covers the widening high-multiply
`SMulHiU a b` — the high 64 bits of the full unsigned `64×64 → 128` product,
the `hi` output of `MULX`. It lowers to the dialect `bvMulHi 64` op (denotation
`mulHiC`, the unsigned high word), which `DialectToJasminCom` lowers to jasmin
`mulhi`/x86 `MULX`. This is the field-arithmetic prerequisite for Barrett /
Montgomery folds `fMul = (a·b) mod p` (low word `SMul` + high word `SMulHiU`),
needed for the BabyBear-field rolled loop bodies.

A Barrett-style body combining the high word and the low word,
`(a *hi b) ^ (a * b)`, is assigned via `RScalarSetExpr` and pushed through the
`CProg`-free front. This file confirms, computationally:

1. the body **translates** (`translateDialectControlTop … = some`);
2. the body **lowers** to a `Com jasminDialect` (via `cryptoDialectToJasminCom`),
   i.e. it reaches owned `.s`;
3. the front's emitted dialect program **denotes to the same value** as the
   `SExpr`'s pure-Lean wrapping-`u64` evaluator `SExpr.evalBV` on sample inputs
   (`denote = spec`) — the front-arm correctness gate — including inputs whose
   high word is non-zero, so the `mulhi` leg is genuinely exercised.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.MulHiFrontValidate

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

/-- A Barrett-style scalar body exercising the high-multiply: `(a *hi b) ^ (a * b)`.
    The `SMulHiU` leg is the high 64 bits of the unsigned product; the `SMul` leg
    is the low 64 bits. -/
def testE : SExpr :=
  .SXor (.SMulHiU (.SVar "a") (.SVar "b")) (.SMul (.SVar "a") (.SVar "b"))

/-- A pure high-multiply body `a *hi b` (isolates the new arm). -/
def testHi : SExpr := .SMulHiU (.SVar "a") (.SVar "b")

/-- The whole `LowCT` leaf: `out := (a *hi b) ^ (a * b)`. -/
def testC : LowCT := .RScalarSetExpr "out" testE

/-- The pure-Lean `u64`-faithful spec value of an `SExpr` on inputs `av`, `bv`. -/
def specVal (e : SExpr) (av bv : BitVec 64) : BitVec 64 :=
  e.evalBV (fun n => if n = "a" then av else if n = "b" then bv else 0)

/-- The front-emitted dialect program for `e` that *returns the result word*
    (the `…Top` wrappers return `unit`; here we keep the result var so we can
    denote the computed value). `none` if the front declines. -/
def frontResultProg (e : SExpr) : Option (Com catCryptDialect testΓ (.sword 64)) :=
  match lowerSExpr testVM 0 e with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword 64, v⟩ => r.1.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- Denote `frontResultProg e` at inputs `av` (slot `a`) and `bv` (slot `b`). -/
def frontDenote (e : SExpr) (av bv : BitVec 64) : Option (BitVec 64) :=
  (frontResultProg e).map (fun com => com.denote (.cons av (.cons bv .nil)))

/-! ## 1. The body translates and lowers -/

/-- The `RScalarSetExpr` body (with the `SMulHiU` leg) translates through the
    `CProg`-free control front. -/
theorem testC_translates : (translateDialectControlTop testVM testC).isSome := by
  native_decide

/-- The front-emitted SExpr chain (`bvMulHi`/`bvMul`/`bvXor` plus the `bvShiftL 0`
    result copy) lowers end-to-end to a `Com jasminDialect` — i.e. the high-mul
    leg reaches owned `.s` through `cryptoDialectToJasminCom`. -/
theorem testC_lowers :
    ((frontResultProg testE).bind DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  native_decide

/-- The isolated high-multiply body also lowers (`bvMulHi` ↦ jasmin `mulhi`). -/
theorem testHi_lowers :
    ((frontResultProg testHi).bind DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  native_decide

/-! ## 2. `denote = spec` on sample inputs (front-arm correctness gate) -/

/-- The front actually emits a result program for the combined body. -/
theorem frontResultProg_isSome : (frontResultProg testE).isSome := by native_decide

-- Combined body `(a *hi b) ^ (a * b)`. The first two inputs have a non-zero
-- high word (the product exceeds 2^64), so the `mulhi` leg is exercised.
example : frontDenote testE 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
    = some (specVal testE 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF) := by native_decide
example : frontDenote testE 0xDEADBEEF12345678 0x0F0F0F0FF0F0F0F0
    = some (specVal testE 0xDEADBEEF12345678 0x0F0F0F0FF0F0F0F0) := by native_decide
example : frontDenote testE 0x100000000 0x100000000
    = some (specVal testE 0x100000000 0x100000000) := by native_decide
example : frontDenote testE 0 0 = some (specVal testE 0 0) := by native_decide

-- Isolated high word `a *hi b`: directly checks the `bvMulHi` denotation equals
-- the unsigned high word `sexprMulHiU`.
example : frontDenote testHi 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
    = some (specVal testHi 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF) := by native_decide
example : frontDenote testHi 0x78000001 0x78000001
    = some (specVal testHi 0x78000001 0x78000001) := by native_decide
example : frontDenote testHi 0x123456789ABCDEF0 0x0FEDCBA987654321
    = some (specVal testHi 0x123456789ABCDEF0 0x0FEDCBA987654321) := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.MulHiFrontValidate
