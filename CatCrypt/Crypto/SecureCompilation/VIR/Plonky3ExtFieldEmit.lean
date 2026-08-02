/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit

/-!
# Plonky3 degree-4 extension-field kernels FRONT-COMPILED as `Com jasminDialect`

The `BinomialExtensionField<BabyBear, 4>` arithmetic (binomial `x^4 = 11`) that
the p3 accept-prover (`bench/plonky3_compare/p3_accept_prove.c`) performs,
sourced through the verified front: each field op is a single `RScalarSetExpr`
over named scalar slots, the statement list is pushed through
`translateDialectControl` and lowered by `cryptoDialectToJasminCom` to a
`Com jasminDialect`.  The `Plonky3FriFoldEmit` field vocabulary
(`sBBMul`/`sBBAdd`/`sBBSub`/`seqAll`) and its 16-word source context are reused.

## The reference (`p3_accept_prove.c`)

```
E = { c[0..3] }              // BinomialExtensionField<BabyBear,4>, x^4 = 11
emul(a,b):                   // ext4 multiply, schoolbook + x^4=11 reduction
  c0 = a0·b0 + 11·(a1·b3 + a2·b2 + a3·b1)
  c1 = a0·b1 + a1·b0 + 11·(a2·b3 + a3·b2)
  c2 = a0·b2 + a1·b1 + a2·b0 + 11·(a3·b3)
  c3 = a0·b3 + a1·b2 + a2·b1 + a3·b0
escale(a,s) = { a_i · s }    // base-field scale (Frobenius coeff multiply)
efrob(a):  c_i = a_i · f1^i,  f1 = 11^((p-1)/4)   // x -> x^p
einv(a):                     // Frobenius / norm inverse
  t = efrob(a)·efrob²(a)·efrob³(a);  n = (a·t).c[0]  (norm, in base field)
  return escale(t, finv(n))
eadd/esub(a,b) = { a_i ± b_i }                     // coordinate-wise
```

`emul`, `escale`, `eadd` and `esub` are pure base-field `bbMul`/`bbAdd`/`bbSub`
on canonical operands (the `W = 11` reduction factor is a `bbMul` by the input
constant `11`).  `einv` decomposes into `emul` + `escale` + the base-field
`bbInv` leaf (`Plonky3FriFoldEmit.bbInvCom`, the Fermat `a^(p−2)` chain) for
`finv(n)`.

## The 16-input ABI

Every kernel keeps the 16-word input context of `Plonky3FriFoldEmit.inCtxt` and
the type `Com jasminDialect inCtxt r64`, so the `Plonky3EmitMain` renderers that
do `Com.toLprogPhysAbi … (abiMaps 16 extConstAt)` address the same words:

* `a0..a3` → `0,1,2,3`; `b0,b1` → `4,5`; `b2,b3` → `13,14`; `W = 11` → `15`;
* Barrett `mu, p, 0, 30, 32, 63` → `7..12`; word `6` unused.

`extConstAt` bakes words `7..12` and `15` as immediates; `0..5`, `13`, `14` are
runtime loads.  The scale / add / sub leaves read only words `0` and `1`.

The field constants are read as **`SVar` input words**, not `SLit` immediates, so
the shift amounts `30/32/63` lower to the variable `bvShiftRV` (jasmin
`regArith .shr`) rather than `shrImm`.

## leaf.denote = spec by construction

Each lowered `Com` is confined to `regArith`/`regConst`/`shlImm`/`shrImm`
bindings (`ext4*_is_purearith`), so the owned backend renders no
`# UNHANDLED-OP` and the emitted `.s`'s denotation IS the Barrett word
arithmetic.  Numeric equality of that arithmetic to `emul`/`escale`/`eadd`/`esub`
is KAT-witnessed against the p3 reference
(`bench/plonky3_compare/ext4_from_rustcmd_kat.c`,
`ext_fri_fold_from_rustcmd_kat.c`); Barrett reduction-correctness is not
re-proved in Lean.

## Scope

The deg-4 ext multiply (all four coordinates), the base-field scale, and the
coordinate-wise add / sub are emitted here — the core ext arithmetic and the
multiplicative pieces of the Frobenius/norm inverse.  The `ExtensionMmcs` fold's
row flatten (16×2-ext → 16×8 base lane interleave) and Merkle commit are
structural marshalling over these leaves plus the existing base-field
`Plonky3CompressEmit`/`Plonky3HashLeafEmit` leaves, and carry no field op.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ExtFieldEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit
  (r64 nInputs inCtxt srcCtx sBBMul sBBAdd sBBSub seqAll allPureArith)

set_option autoImplicit false

/-! ## 1. Source context and the ext-field slot names

The source `Ctx` is `Plonky3FriFoldEmit.srcCtx` (16 `sword 64` words).  Word `0`
is the head of the context list and word `15` the innermost binding. -/

/-- The source `VarMap` naming the 16 input words at the ext-field ABI:
    `a0..a3` at `0..3`, `b0,b1` at `4,5`, `b2,b3` at `13,14`, `W` at `15`, the
    Barrett constants `mu,p,zero,sh30,sh32,sh63` at `7..12`, word `6` unused. -/
def extVM : VarMap srcCtx :=
  ((((((((((((((((VarMap.empty.bind "wW").bind "b3").bind "b2").bind
    "sh63").bind "sh32").bind "sh30").bind "zero").bind "p").bind "mu").bind
    "u6").bind "b1").bind "b0").bind "a3").bind "a2").bind "a1").bind "a0")

/-- Translate a LowCT body over `extVM` and return the `Com` whose result is the
    slot `name`. -/
def extComAt (body : LowCT) (name : String) :
    Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl extVM body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- Front-lower a leaf's statement list to a `Com jasminDialect` (result slot
    `acc`). -/
def frontLeafOpt (stmts : List LowCT) : Option (Com jasminDialect inCtxt r64) :=
  (extComAt (seqAll stmts) "acc").bind DialectToJasminCom.cryptoDialectToJasminCom

/-! ## 2. The ext4-mul coordinate bodies

`acc` accumulates the coordinate, `s` the inner sum folded by `W`, `t` the
per-product scratch.  All Barrett `bbMul`/`bbAdd` on canonical operands. -/

/-- `c0 = a0·b0 + W·(a1·b3 + a2·b2 + a3·b1)`. -/
def c0Stmts : List LowCT :=
  sBBMul "acc" (.SVar "a0") (.SVar "b0") ++
  sBBMul "s" (.SVar "a1") (.SVar "b3") ++
  sBBMul "t" (.SVar "a2") (.SVar "b2") ++ sBBAdd "s" (.SVar "s") (.SVar "t") ++
  sBBMul "t" (.SVar "a3") (.SVar "b1") ++ sBBAdd "s" (.SVar "s") (.SVar "t") ++
  sBBMul "s" (.SVar "wW") (.SVar "s") ++
  sBBAdd "acc" (.SVar "acc") (.SVar "s")

/-- `c1 = a0·b1 + a1·b0 + W·(a2·b3 + a3·b2)`. -/
def c1Stmts : List LowCT :=
  sBBMul "acc" (.SVar "a0") (.SVar "b1") ++
  sBBMul "t" (.SVar "a1") (.SVar "b0") ++ sBBAdd "acc" (.SVar "acc") (.SVar "t") ++
  sBBMul "s" (.SVar "a2") (.SVar "b3") ++
  sBBMul "t" (.SVar "a3") (.SVar "b2") ++ sBBAdd "s" (.SVar "s") (.SVar "t") ++
  sBBMul "s" (.SVar "wW") (.SVar "s") ++
  sBBAdd "acc" (.SVar "acc") (.SVar "s")

/-- `c2 = a0·b2 + a1·b1 + a2·b0 + W·(a3·b3)`. -/
def c2Stmts : List LowCT :=
  sBBMul "acc" (.SVar "a0") (.SVar "b2") ++
  sBBMul "t" (.SVar "a1") (.SVar "b1") ++ sBBAdd "acc" (.SVar "acc") (.SVar "t") ++
  sBBMul "t" (.SVar "a2") (.SVar "b0") ++ sBBAdd "acc" (.SVar "acc") (.SVar "t") ++
  sBBMul "s" (.SVar "a3") (.SVar "b3") ++
  sBBMul "s" (.SVar "wW") (.SVar "s") ++
  sBBAdd "acc" (.SVar "acc") (.SVar "s")

/-- `c3 = a0·b3 + a1·b2 + a2·b1 + a3·b0`. -/
def c3Stmts : List LowCT :=
  sBBMul "acc" (.SVar "a0") (.SVar "b3") ++
  sBBMul "t" (.SVar "a1") (.SVar "b2") ++ sBBAdd "acc" (.SVar "acc") (.SVar "t") ++
  sBBMul "t" (.SVar "a2") (.SVar "b1") ++ sBBAdd "acc" (.SVar "acc") (.SVar "t") ++
  sBBMul "t" (.SVar "a3") (.SVar "b0") ++ sBBAdd "acc" (.SVar "acc") (.SVar "t")

/-! ## 3. Base-field scale and the coordinate-wise add / sub

`escale`/`efrob` per coordinate is `bbMul x s`; `eadd`/`esub` per coordinate is
`bbAdd x y` / `bbSub x y`.  Each reads input words `0` and `1`. -/

/-- `escale` coordinate: `bbMul x s`. -/
def scaleStmts : List LowCT := sBBMul "acc" (.SVar "a0") (.SVar "a1")

/-- `eadd` coordinate: `bbAdd x y`. -/
def addStmts : List LowCT := sBBAdd "acc" (.SVar "a0") (.SVar "a1")

/-- `esub` coordinate: `bbSub x y`. -/
def subStmts : List LowCT := sBBSub "acc" (.SVar "a0") (.SVar "a1")

/-! ## 4. The lowered `Com`s -/

def ext4MulC0Opt := frontLeafOpt c0Stmts
theorem ext4MulC0_isSome : ext4MulC0Opt.isSome := by native_decide
/-- The `emul` coordinate `c0` leaf (front-sourced, 16-word ABI). -/
def ext4MulC0Com : Com jasminDialect inCtxt r64 := ext4MulC0Opt.get ext4MulC0_isSome

def ext4MulC1Opt := frontLeafOpt c1Stmts
theorem ext4MulC1_isSome : ext4MulC1Opt.isSome := by native_decide
/-- The `emul` coordinate `c1` leaf (front-sourced, 16-word ABI). -/
def ext4MulC1Com : Com jasminDialect inCtxt r64 := ext4MulC1Opt.get ext4MulC1_isSome

def ext4MulC2Opt := frontLeafOpt c2Stmts
theorem ext4MulC2_isSome : ext4MulC2Opt.isSome := by native_decide
/-- The `emul` coordinate `c2` leaf (front-sourced, 16-word ABI). -/
def ext4MulC2Com : Com jasminDialect inCtxt r64 := ext4MulC2Opt.get ext4MulC2_isSome

def ext4MulC3Opt := frontLeafOpt c3Stmts
theorem ext4MulC3_isSome : ext4MulC3Opt.isSome := by native_decide
/-- The `emul` coordinate `c3` leaf (front-sourced, 16-word ABI). -/
def ext4MulC3Com : Com jasminDialect inCtxt r64 := ext4MulC3Opt.get ext4MulC3_isSome

def ext4ScaleOpt := frontLeafOpt scaleStmts
theorem ext4Scale_isSome : ext4ScaleOpt.isSome := by native_decide
/-- The `escale` coordinate leaf (front-sourced, 16-word ABI). -/
def ext4ScaleCom : Com jasminDialect inCtxt r64 := ext4ScaleOpt.get ext4Scale_isSome

def ext4AddOpt := frontLeafOpt addStmts
theorem ext4Add_isSome : ext4AddOpt.isSome := by native_decide
/-- The `eadd` coordinate leaf (front-sourced, 16-word ABI). -/
def ext4AddCom : Com jasminDialect inCtxt r64 := ext4AddOpt.get ext4Add_isSome

def ext4SubOpt := frontLeafOpt subStmts
theorem ext4Sub_isSome : ext4SubOpt.isSome := by native_decide
/-- The `esub` coordinate leaf (front-sourced, 16-word ABI). -/
def ext4SubCom : Com jasminDialect inCtxt r64 := ext4SubOpt.get ext4Sub_isSome

/-! ## 5. Front provenance

Each leaf `Com` IS the front lowering of its LowCT statement list: the
`translateDialectControl` translation over `extVM`, lowered by
`cryptoDialectToJasminCom`.  The equalities are definitional
(`Option.some_get`). -/

theorem ext4MulC0_front_sourced :
    (extComAt (seqAll c0Stmts) "acc").bind
      DialectToJasminCom.cryptoDialectToJasminCom = some ext4MulC0Com :=
  (Option.some_get ext4MulC0_isSome).symm

theorem ext4MulC1_front_sourced :
    (extComAt (seqAll c1Stmts) "acc").bind
      DialectToJasminCom.cryptoDialectToJasminCom = some ext4MulC1Com :=
  (Option.some_get ext4MulC1_isSome).symm

theorem ext4MulC2_front_sourced :
    (extComAt (seqAll c2Stmts) "acc").bind
      DialectToJasminCom.cryptoDialectToJasminCom = some ext4MulC2Com :=
  (Option.some_get ext4MulC2_isSome).symm

theorem ext4MulC3_front_sourced :
    (extComAt (seqAll c3Stmts) "acc").bind
      DialectToJasminCom.cryptoDialectToJasminCom = some ext4MulC3Com :=
  (Option.some_get ext4MulC3_isSome).symm

theorem ext4Scale_front_sourced :
    (extComAt (seqAll scaleStmts) "acc").bind
      DialectToJasminCom.cryptoDialectToJasminCom = some ext4ScaleCom :=
  (Option.some_get ext4Scale_isSome).symm

theorem ext4Add_front_sourced :
    (extComAt (seqAll addStmts) "acc").bind
      DialectToJasminCom.cryptoDialectToJasminCom = some ext4AddCom :=
  (Option.some_get ext4Add_isSome).symm

theorem ext4Sub_front_sourced :
    (extComAt (seqAll subStmts) "acc").bind
      DialectToJasminCom.cryptoDialectToJasminCom = some ext4SubCom :=
  (Option.some_get ext4Sub_isSome).symm

/-! ## 6. Pure-arith predicate — leaf.denote = spec by construction

Each lowered `Com` is `regArith`/`regConst`/`shlImm`/`shrImm`-only, so
`JasminLprogExport.opToLinstrR` renders every binding and the owned backend
emits no `# UNHANDLED-OP`. -/

theorem ext4MulC0_is_purearith : allPureArith ext4MulC0Com = true := by native_decide
theorem ext4MulC1_is_purearith : allPureArith ext4MulC1Com = true := by native_decide
theorem ext4MulC2_is_purearith : allPureArith ext4MulC2Com = true := by native_decide
theorem ext4MulC3_is_purearith : allPureArith ext4MulC3Com = true := by native_decide
theorem ext4Scale_is_purearith : allPureArith ext4ScaleCom = true := by native_decide
theorem ext4Add_is_purearith : allPureArith ext4AddCom = true := by native_decide
theorem ext4Sub_is_purearith : allPureArith ext4SubCom = true := by native_decide

/-- **All seven ext-field leaves are pure-arith.** Each `emul` coordinate, the
    base-field `escale`, and the coordinate-wise `eadd`/`esub` denote exactly the
    Barrett word arithmetic — the by-construction `leaf.denote = spec` for the
    deg-4 ext-field kernels. -/
theorem ext_field_all_purearith :
    allPureArith ext4MulC0Com = true ∧ allPureArith ext4MulC1Com = true
      ∧ allPureArith ext4MulC2Com = true ∧ allPureArith ext4MulC3Com = true
      ∧ allPureArith ext4ScaleCom = true ∧ allPureArith ext4AddCom = true
      ∧ allPureArith ext4SubCom = true :=
  ⟨ext4MulC0_is_purearith, ext4MulC1_is_purearith,
   ext4MulC2_is_purearith, ext4MulC3_is_purearith,
   ext4Scale_is_purearith, ext4Add_is_purearith,
   ext4Sub_is_purearith⟩

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ExtFieldEmit
