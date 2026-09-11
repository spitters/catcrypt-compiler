/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RecursiveForLoopBlockFront
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect

@[expose] public section

set_option autoImplicit false

/-!
# `RolledFront`: a rolled-loop front bundled with the denotation it realises

A `RolledFront Γouter s` carries the three things a consumer needs from a
rolled-loop front combinator, in one value:

* `build` — the `Option (ComL Γouter s)` the combinator produces;
* `spec` — the value that `ComL` denotes to, as a function of the outer
  valuation;
* `denote_eq` — the equation between them.

The front's own side condition (the body `LowCT` front-compiles through
`frontLoopBodyJ`) is an argument of each constructor, so `denote_eq` is
hypothesis-free once the record exists. A consumer that ranges over loop shapes
therefore reads `spec` and `denote_eq` off the record and needs no per-shape
lemma.

The record is indexed only by the outer context `Γouter` and the result type
`s`. Everything that varies between shapes — the trip-count expression, the body
context, the accumulator type, the loop invariants, the continuation — is an
argument of the shape's constructor and is absorbed into the `spec` closure.

## Main results

* `RolledFront` — a rolled-loop front bundled with its denotation.
* `RolledFront.denote_of_build` / `build_isSome` — reading the bundled equation
  back at a produced program.

## The instantiated shapes

| `ComL` node | constructor | `spec` at valuation `V` |
|---|---|---|
| `forLoopN` | `RolledFront.forLoopN` | `cont` on the `N`-fold `JLoopBodyN.denote` |
| `forLoopNRt` | `RolledFront.forLoopNRt` | `cont` on the `(count.lookup V).toNat`-fold |
| `whileNz` | `RolledFront.whileNz` | `cont` on the `(guard.lookup V).toNat`-fold |
| `forLoopNRtNested` | `RolledFront.forLoopNRtNested` | `cont` on `JLoopBodyN.nestedDenote` |
| `forLoopBlock` | `RolledFront.forLoopBlock` | outer fold of the inner node's `ComL.denote` |

The first four are built over the continuation-carrying combinators, which are
the primitives their continuation-free siblings instantiate at
`cont := .ret .here`; the `*_spec_ret_here` equations below give the `spec` each
takes at that continuation. `forLoopBlock` has no continuation-carrying
combinator, so its constructor is over `lowerNestedLoop` directly.

`forLoopNC`, `forLoopNRtC` and `forLoopNV` are the same `forLoopN` /
`forLoopNRt` nodes over the carry-selecting and vsimd body fronts. Those fronts
have no continuation-carrying combinator, so each is over the
continuation-free one and its `spec` is the bare fold.

Each `denote_eq` field is the shape's committed `_denote` lemma applied to the
constructor's arguments.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.RecursiveForLoopBlockFront
  (lowerNestedLoop lowerNestedLoop_denote rolledWhileNzComLCont
   rolledWhileNzComLCont_denote)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
  (frontLoopBodyJ frontLoopBodyJC frontLoopBodyJV
   rolledForLoopNC rolledForLoopNC_denote rolledForLoopNV rolledForLoopNV_denote)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
  (rolledForLoopNRtC rolledForLoopNRtC_denote)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileNode
  (rolledWhileNzComL)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
  (rolledForLoopNCont rolledForLoopNCont_denote
   rolledForLoopNRtCont rolledForLoopNRtCont_denote
   rolledForLoopNRtNestedCont rolledForLoopNRtNestedCont_denote)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The record -/

/-- A rolled-loop front paired with the denotation its output realises.

    `build` is what the front combinator returns; `spec V` is the value that
    output denotes to at the outer valuation `V`; `denote_eq` is the equation,
    which also witnesses that `build` is `some`. -/
structure RolledFront (Γouter : Ctxt jasminDialect) (s : JasminTy) where
  /-- The `ComL` the front combinator builds. -/
  build : Option (ComL Γouter s)
  /-- The value `build` denotes to, as a function of the outer valuation. -/
  spec : Ctxt.Valuation Γouter → ⟦s⟧
  /-- `build` denotes to `spec` at every outer valuation. -/
  denote_eq : ∀ V : Ctxt.Valuation Γouter,
    build.map (fun c => ComL.denote c V) = some (spec V)

namespace RolledFront

variable {Γouter : Ctxt jasminDialect}

/-- The front produced a `ComL`. -/
theorem build_isSome {s : JasminTy} (F : RolledFront Γouter s)
    (V : Ctxt.Valuation Γouter) :
    F.build.isSome := by
  have h := F.denote_eq V
  cases hb : F.build with
  | none => simp [hb] at h
  | some c => simp

/-- The built `ComL` denotes to `spec`. -/
theorem denote_of_build {s : JasminTy} (F : RolledFront Γouter s) {c : ComL Γouter s}
    (hc : F.build = some c) (V : Ctxt.Valuation Γouter) :
    ComL.denote c V = F.spec V := by
  have h := F.denote_eq V
  rw [hc] at h
  simpa using h

/-! ## 2. The fixed-trip loop (`ComL.forLoopN`) -/

/-- The fixed-trip rolled loop, over `rolledForLoopNCont`. `spec` is the
    continuation evaluated on the valuation extended by the `N`-fold
    `JLoopBodyN.denote` of the front-compiled body. -/
def forLoopN {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update) :
    RolledFront Γouter s where
  build := rolledForLoopNCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    N vmBody accName body init invs cont
  spec V := ComL.denote cont
    (V.extend (JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V) (init.lookup V)))
  denote_eq := rolledForLoopNCont_denote N vmBody accName body init invs cont hupd

/-- At `cont := .ret .here` the fixed-trip `spec` is the bare `N`-fold. -/
theorem forLoopN_spec_ret_here {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (forLoopN N vmBody accName body init invs (.ret .here) hupd).spec V
      = JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V) (init.lookup V) := rfl

/-! ## 3. The runtime-trip loop (`ComL.forLoopNRt`) -/

/-- The runtime-trip rolled loop, over `rolledForLoopNRtCont`. `spec` is the
    continuation evaluated on the valuation extended by the
    `(count.lookup V).toNat`-fold of the front-compiled body. -/
def forLoopNRt {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update) :
    RolledFront Γouter s where
  build := rolledForLoopNRtCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    vmBody accName body count init invs cont
  spec V := ComL.denote cont
    (V.extend (JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩
      (Expr.lookupArgs invs V) (init.lookup V)))
  denote_eq := rolledForLoopNRtCont_denote vmBody accName body count init invs cont hupd

/-- At `cont := .ret .here` the runtime-trip `spec` is the bare fold at the
    count register's value. -/
theorem forLoopNRt_spec_ret_here {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (forLoopNRt vmBody accName body count init invs (.ret .here) hupd).spec V
      = JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩
          (Expr.lookupArgs invs V) (init.lookup V) := rfl

/-! ## 4. The countdown do-while (`ComL.whileNz`) -/

/-- The countdown do-while sweep, over `rolledWhileNzComLCont`. `spec` is the
    continuation evaluated on the valuation extended by the
    `(guard.lookup V).toNat`-fold of the front-compiled body — the trip the
    countdown guard exit realises. -/
def whileNz {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (guard : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update) :
    RolledFront Γouter s where
  build := rolledWhileNzComLCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    vmBody accName body guard init invs cont
  spec V := ComL.denote cont
    (V.extend (JLoopBodyN.denote ⟨(guard.lookup V).toNat, update⟩
      (Expr.lookupArgs invs V) (init.lookup V)))
  denote_eq := rolledWhileNzComLCont_denote vmBody accName body guard init invs cont hupd

/-- At `cont := .ret .here` the do-while `spec` is the bare fold at the guard
    seed. -/
theorem whileNz_spec_ret_here {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (guard : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (whileNz vmBody accName body guard init invs (.ret .here) hupd).spec V
      = JLoopBodyN.denote ⟨(guard.lookup V).toNat, update⟩
          (Expr.lookupArgs invs V) (init.lookup V) := rfl

/-! ## 5. The nested runtime loop (`ComL.forLoopNRtNested`) -/

/-- The nested runtime loop, over `rolledForLoopNRtNestedCont`: a runtime outer
    trip whose inner trip is recomputed each outer pass by the front-compiled
    `countBody`. `spec` is the continuation evaluated on the valuation extended
    by the double fold `JLoopBodyN.nestedDenote`. -/
def forLoopNRtNested {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {innerCount : Com jasminDialect (mapCtx (.sword 64 :: invCTys)) (mapTy (.sword 64))}
    {innerUpdate : Com jasminDialect
      (mapCtx (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hcnt : frontLoopBodyJ (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
              vmCount countName countBody = some innerCount)
    (hupd : frontLoopBodyJ (accCTy := accCTy)
              (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys)
              vmBody accName updateBody = some innerUpdate) :
    RolledFront Γouter s where
  build := rolledForLoopNRtNestedCont (Γouter := Γouter) (accCTy := accCTy)
    (invCTys := invCTys) vmCount countName countBody vmBody accName updateBody
    outerCount init invs cont
  spec V := ComL.denote cont
    (V.extend (JLoopBodyN.nestedDenote innerCount innerUpdate
      (outerCount.lookup V).toNat (Expr.lookupArgs invs V) (init.lookup V)))
  denote_eq := rolledForLoopNRtNestedCont_denote vmCount countName countBody vmBody
    accName updateBody outerCount init invs cont hcnt hupd

/-- At `cont := .ret .here` the nested `spec` is the bare double fold. -/
theorem forLoopNRtNested_spec_ret_here {accCTy : CryptoTy} {invCTys : Ctx}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {innerCount : Com jasminDialect (mapCtx (.sword 64 :: invCTys)) (mapTy (.sword 64))}
    {innerUpdate : Com jasminDialect
      (mapCtx (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hcnt : frontLoopBodyJ (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
              vmCount countName countBody = some innerCount)
    (hupd : frontLoopBodyJ (accCTy := accCTy)
              (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys)
              vmBody accName updateBody = some innerUpdate)
    (V : Ctxt.Valuation Γouter) :
    (forLoopNRtNested vmCount countName countBody vmBody accName updateBody
        outerCount init invs (.ret .here) hcnt hupd).spec V
      = JLoopBodyN.nestedDenote innerCount innerUpdate (outerCount.lookup V).toNat
          (Expr.lookupArgs invs V) (init.lookup V) := rfl

/-! ## 6. The recursive block (`ComL.forLoopBlock`) -/

/-- The recursive block loop, over `lowerNestedLoop`: a runtime outer trip whose
    per-iteration body is the inner `ComL.whileNz` node the inner front built.
    `spec` is the outer fold of the inner node's own `ComL.denote`, with the
    accumulator threaded, the outer index at the `.reg 64` binder and the outer
    invariants after it. The combinator fixes the continuation at `.ret .here`,
    so the result type is `mapTy accCTy`. -/
def forLoopBlock {accCTy : CryptoTy} {outerInvCTys innerInvCTys : Ctx}
    (vmInner : VarMap (accCTy :: .sword 64 :: innerInvCTys)) (innerAccName : String)
    (innerBody : LowCT)
    (innerGuard : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (JasminTy.reg 64))
    (innerInit : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy))
    (innerInvs : HVector
      (fun ty => Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) ty)
      (innerInvCTys.map mapTy))
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (outerInit : Ctxt.Var Γouter (mapTy accCTy))
    (outerInvs : HVector (fun ty => Ctxt.Var Γouter ty) (outerInvCTys.map mapTy))
    {inner : ComL (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy)}
    (hinner : rolledWhileNzComL
                (Γouter := mapCtx (accCTy :: .sword 64 :: outerInvCTys))
                (accCTy := accCTy) (invCTys := innerInvCTys)
                vmInner innerAccName innerBody innerGuard innerInit innerInvs
              = some inner) :
    RolledFront Γouter (mapTy accCTy) where
  build := lowerNestedLoop vmInner innerAccName innerBody innerGuard innerInit
    innerInvs outerCount outerInit outerInvs
  spec V := (List.range (outerCount.lookup V).toNat).foldl
    (fun acc t => ComL.denote inner
      (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs outerInvs V))))
    (outerInit.lookup V)
  denote_eq := lowerNestedLoop_denote vmInner innerAccName innerBody innerGuard
    innerInit innerInvs outerCount outerInit outerInvs hinner

/-! ## 7. The carry-selecting and vsimd body fronts -/

/-- The fixed-trip rolled loop over the carry-selecting body front, via
    `rolledForLoopNC`. `spec` is the `N`-fold `JLoopBodyN.denote` of the body
    `frontLoopBodyJC` compiles. -/
def forLoopNC {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJC (accCTy := accCTy) vmBody accName body = some update) :
    RolledFront Γouter (mapTy accCTy) where
  build := rolledForLoopNC (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    N vmBody accName body init invs
  spec V := JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V) (init.lookup V)
  denote_eq := rolledForLoopNC_denote N vmBody accName body init invs hupd

/-- The runtime-trip rolled loop over the carry-selecting body front, via
    `rolledForLoopNRtC`. `spec` is the `(count.lookup V).toNat`-fold of the body
    `frontLoopBodyJC` compiles. -/
def forLoopNRtC {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJC (accCTy := accCTy) vmBody accName body = some update) :
    RolledFront Γouter (mapTy accCTy) where
  build := rolledForLoopNRtC (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    vmBody accName body count init invs
  spec V := JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩
    (Expr.lookupArgs invs V) (init.lookup V)
  denote_eq := rolledForLoopNRtC_denote vmBody accName body count init invs hupd

/-- The fixed-trip rolled loop over the vsimd body front, via `rolledForLoopNV`.
    `spec` is the `N`-fold `JLoopBodyN.denote` of the body `frontLoopBodyJV`
    compiles. -/
def forLoopNV {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJV (accCTy := accCTy) vmBody accName body = some update) :
    RolledFront Γouter (mapTy accCTy) where
  build := rolledForLoopNV (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    N vmBody accName body init invs
  spec V := JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V) (init.lookup V)
  denote_eq := rolledForLoopNV_denote N vmBody accName body init invs hupd

end RolledFront

end CatCrypt.Crypto.SecureCompilation.Dialects
