/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop

@[expose] public section

set_option autoImplicit false

/-!
# Carry-select front for the runtime-trip rolled loop (`ComL.forLoopNRt`)

`TranslateDialectRuntimeLoop.rolledForLoopNRt` front-compiles a loop body through
`translateDialectControl` and wraps it in a `ComL.forLoopNRt` whose trip count is
a runtime `.reg 64` register. `translateDialectControl` has no carry-flag
surface, so a multi-limb body's carry bit is synthesised branch-free through the
`bSltu` window — around 25 dialect ops per limb, and no `adcx` in the rendered
text.

This module wraps the same `ComL.forLoopNRt` node around the **carry-selecting**
body front `TranslateDialectRolledLoop.frontLoopBodyJC`
(`CarryChainSelect.translateDialectCarrySelect` +
`cryptoDialectToJasminCom`), which rewrites the recognised `bSltu` windows to
`bvAddCarryLo`/`bvAddCarryHi` pairs. It is to `rolledForLoopNRt` exactly what
`TranslateDialectRolledLoop.rolledForLoopNC` is to `rolledForLoopN`: the body
front changes, the export node, the `mapCtx` context reduction and the
`count`/`init`/`invs` threading do not.

```
  bodyLowCT  (RArrLoad / RScalarSetExpr / RArrStore, bSltu carry windows)
    --(translateDialectCarrySelect on Γbody = accCTy :: .sword 64 :: invCTys)--> Com catCryptDialect
    --(cryptoDialectToJasminCom)-------------------------------------------> Com jasminDialect = JLoopBodyN.update
    --(ComL.forLoopNRt update count init invs (ret acc))-------------------> ComL
    --(ComL.toLprogPhysAbi / renderLprogAtt)-------------------------------> .s  (adcx inside the back-edge)
```

## Main results

* `rolledForLoopNRtC` — the runtime-trip `ComL.forLoopNRt` over a carry-selected
  loop body.
* `rolledForLoopNRtC_denote` — its denotation is the `JLoopBodyN.denote` fold of
  the front body at the runtime trip count.
* `rolledForLoopNRtNestedC` / `rolledForLoopNRtNestedC_denote` — the nested twin,
  whose inner-count and inner-update bodies both run through the carry-selecting
  front.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-- Carry-select twin of `TranslateDialectRuntimeLoop.rolledForLoopNRt`: build a
    runtime-trip `ComL.forLoopNRt` whose body is front-compiled through the
    carry-selecting `frontLoopBodyJC`.

    * `Γouter` is the outer context (the kernel's argument slots, jasmin types);
    * `count` is the in-scope runtime trip-count variable (`.reg 64`), which the
      lowering reads to seed the loop counter;
    * `init` is the in-scope accumulator seed;
    * `invs` are the in-scope loop-invariant seeds (input array bases);
    * the body is `frontLoopBodyJC vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys`, so its jasmin image matches
      `accTy :: .reg 64 :: invTys`.

    Returns a `ComL Γouter (mapTy accCTy)` binding and returning the loop result
    (`.ret .here`). `none` if the carry-selecting front declines. -/
def rolledForLoopNRtC {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match frontLoopBodyJC (accCTy := accCTy) vmBody accName body with
  | some update =>
      -- `mapCtx (accCTy :: .sword 64 :: invCTys)` reduces to
      -- `mapTy accCTy :: .reg 64 :: invCTys.map mapTy` definitionally.
      some (ComL.forLoopNRt update count init invs (.ret .here))
  | none => none

/-- **Carry-select runtime-loop denotation = `JLoopBodyN.denote` fold at the
    runtime count.** When the carry-selecting body front-compiles to `update`,
    the `ComL.forLoopNRt`'s denotation at any valuation is the
    `(count.lookup V).toNat`-fold `JLoopBodyN.denote` of `update` over the loop
    index, seeded by `init` and threading the invariants `invs`. Structural
    (`ComL.denote` on `forLoopNRt`), no `sorry`. -/
theorem rolledForLoopNRtC_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJC (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNRtC (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmBody accName body count init invs).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩
                (Expr.lookupArgs invs V) (init.lookup V)) := by
  unfold rolledForLoopNRtC
  rw [hupd]
  rfl

/-! ## The nested runtime loop over carry-selected bodies

`TranslateDialectRuntimeLoop.rolledForLoopNRtNested` builds a
`ComL.forLoopNRtNested` from two bodies front-compiled by `frontLoopBodyJ` — an
inner-count body over `Γcount = .sword 64 :: invCTys` returning the per-outer
inner trip, and an inner-update body over
`Γbody = accCTy :: .sword 64 :: .sword 64 :: invCTys`. Both contexts' `mapCtx`
images reduce definitionally to the `forLoopNRtNested` field shapes, so the only
delta in the carry-select twin is the body front. -/

/-- Carry-select twin of `TranslateDialectRuntimeLoop.rolledForLoopNRtNested`:
    build a nested runtime-trip `ComL.forLoopNRtNested` whose inner-count and
    inner-update bodies are both front-compiled through the carry-selecting
    `frontLoopBodyJC`. The inner loop is first-class: its trip count is
    recomputed from the outer index each outer pass. `none` if either body's
    carry-selecting front declines. -/
def rolledForLoopNRtNestedC {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match frontLoopBodyJC (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
          vmCount countName countBody,
        frontLoopBodyJC (accCTy := accCTy)
          (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys)
          vmBody accName updateBody with
  | some innerCount, some innerUpdate =>
      some (ComL.forLoopNRtNested innerCount innerUpdate outerCount init invs (.ret .here))
  | _, _ => none

/-- **Carry-select nested-runtime-loop denotation = `JLoopBodyN.nestedDenote`
    double fold.** When both carry-selecting bodies front-compile, the
    `ComL.forLoopNRtNested`'s denotation at any valuation is the outer×inner
    double fold: the outer loop over `(outerCount.lookup V).toNat`, the inner
    trip recomputed per outer pass via `innerCount`, applying `innerUpdate`
    innermost. Structural (`ComL.denote` on `forLoopNRtNested`), no `sorry`. -/
theorem rolledForLoopNRtNestedC_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {innerCount : Com jasminDialect (mapCtx (.sword 64 :: invCTys)) (mapTy (.sword 64))}
    {innerUpdate : Com jasminDialect
      (mapCtx (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hcnt : frontLoopBodyJC (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
              vmCount countName countBody = some innerCount)
    (hupd : frontLoopBodyJC (accCTy := accCTy)
              (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys)
              vmBody accName updateBody = some innerUpdate)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNRtNestedC (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmCount countName countBody vmBody accName updateBody outerCount init invs).map
        (fun c => ComL.denote c V)
      = some (JLoopBodyN.nestedDenote innerCount innerUpdate (outerCount.lookup V).toNat
                (Expr.lookupArgs invs V) (init.lookup V)) := by
  unfold rolledForLoopNRtNestedC
  rw [hcnt, hupd]
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
