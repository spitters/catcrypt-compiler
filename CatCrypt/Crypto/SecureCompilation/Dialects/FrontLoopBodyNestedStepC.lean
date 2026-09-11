/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC

/-!
# The front-compiled nested loop as a `JLoopBodyN.nestedDenote` double fold

`FrontLoopBodyStepC.frontLoopBodyJ_denote_foldl` closes the single (inner) loop:
the `n`-trip `JLoopBodyN.denote` of a front-compiled body is the `ctTransTy`
transport of the word-model fold `(List.range n).foldl f init`. The nested
runtime-loop front (`Dialects.FrontRoutePlan.compileNested`) emits a
`ComL.forLoopNRtNested` whose denotation is a `JLoopBodyN.nestedDenote`: an outer
fold over the rows, each row an inner fold over a per-row recomputed trip count.
This module lifts the single-loop bridge over the outer fold.

At a fixed outer index `jd`, `JLoopBodyN.stepCNested innerUpdate invs jd t` is
definitionally `JLoopBodyN.stepC innerUpdate (.cons (BitVec.ofNat 64 jd) invs) t`
— the outer index prepended to the invariants — so the inner fold at `jd` is a
`JLoopBodyN.denote` over `invCTys` extended by `.sword 64` at the front, and
`frontLoopBodyJ_denote_foldl` (at `invCTys := .sword 64 :: invCTys`) discharges
it. The outer induction threads that per-row identity through the outer fold.

## Main results

* `nested_fold_bridge` — a generic outer fold whose per-row body carries the
  `ctTransTy` transport of a model row step is the transport of the model outer
  fold.
* `nestedDenote_foldl` — the composite: a per-row-per-trip source run of the
  update body, together with a per-row inner-count identification, makes the
  emitted nest's `JLoopBodyN.nestedDenote` the `ctTransTy` transport of the
  model double fold `(List.range outerN).foldl (fun a jd =>
  (List.range (cnt jd)).foldl (fj jd) a) init`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyNestedStepC

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar ConsistentS semScalar IsCoveredSCtl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC (frontLoopBodyJ_denote_foldl)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The generic outer fold -/

/-- **The outer fold transports.** When each row body `INN jd` carries the
    `ctTransTy` transport of a model row step `G · jd` (for rows below `outerN`),
    the outer fold of the row bodies from `ctTransTy init` is the transport of the
    model outer fold. Proved by induction on `outerN`, peeling the last row. -/
theorem nested_fold_bridge {accCTy : CryptoTy}
    (INN : Nat → ⟦mapTy accCTy⟧ → ⟦mapTy accCTy⟧)
    (G : ⟦accCTy⟧ → Nat → ⟦accCTy⟧) (outerN : Nat)
    (h : ∀ jd, jd < outerN → ∀ acc : ⟦accCTy⟧,
      INN jd (ctTransTy acc) = ctTransTy (G acc jd)) :
    ∀ init : ⟦accCTy⟧,
      (List.range outerN).foldl (fun acc jd => INN jd acc) (ctTransTy init)
        = ctTransTy ((List.range outerN).foldl G init) := by
  induction outerN with
  | zero => intro init; rfl
  | succ k ih =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (fun jd hjd acc => h jd (by omega) acc) init,
        h k (Nat.lt_succ_self k) _]

/-! ## 2. The nested composite -/

/-- **The front-compiled nest computes the model double fold.** For an
    `IsCoveredSCtl` update body over `accCTy :: .sword 64 :: .sword 64 :: invCTys`
    that the front compiles to `innerUpdate`, given

    * `hcnt` — at every outer row below `outerN`, the emitted inner-count body's
      recomputed trip count `innerTripAtC innerCount (ctMapValD invsC) jd` equals
      the model count `cnt jd`, and
    * `hstep` — every trip below `cnt jd` of row `jd` has a source `semScalar` run
      of the update body from a consistent entry state (the outer index prepended
      to the invariants) leaving the model step `fj jd acc t` in the accumulator,

    the nest's `JLoopBodyN.nestedDenote` is the `ctTransTy` transport of the model
    double fold. The inner fold at each row is `frontLoopBodyJ_denote_foldl` at
    `invCTys := .sword 64 :: invCTys`; the outer fold is `nested_fold_bridge`. -/
theorem nestedDenote_foldl {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT) (hcov : IsCoveredSCtl body)
    (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys)
    (innerCount : Com jasminDialect (mapCtx (.sword 64 :: invCTys)) (mapTy (.sword 64)))
    (cnt : Nat → Nat) (fj : Nat → ⟦accCTy⟧ → Nat → ⟦accCTy⟧) (outerN : Nat)
    (hcnt : ∀ jd, jd < outerN →
      JLoopBodyN.innerTripAtC innerCount (ctMapValD invsC) jd = cnt jd)
    (hstep : ∀ jd, jd < outerN → ∀ t (acc : ⟦accCTy⟧), t < cnt jd →
      ∃ env env',
        ConsistentS vmBody
          (.cons acc (.cons (BitVec.ofNat 64 t) (.cons (BitVec.ofNat 64 jd) invsC))) env ∧
        semScalar body env = some env' ∧ env' accName = some ⟨accCTy, fj jd acc t⟩)
    {innerUpdate : Com jasminDialect
      (mapCtx (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy)
      (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys) vmBody accName body
        = some innerUpdate)
    (init : ⟦accCTy⟧) :
    JLoopBodyN.nestedDenote innerCount innerUpdate outerN (ctMapValD invsC) (ctTransTy init)
      = ctTransTy ((List.range outerN).foldl
          (fun a jd => (List.range (cnt jd)).foldl (fj jd) a) init) := by
  refine nested_fold_bridge
    (fun jd acc =>
      (List.range (JLoopBodyN.innerTripAtC innerCount (ctMapValD invsC) jd)).foldl
        (fun acc2 t => JLoopBodyN.stepCNested innerUpdate (ctMapValD invsC) jd t acc2) acc)
    (fun a jd => (List.range (cnt jd)).foldl (fj jd) a) outerN ?_ init
  intro jd hjd acc
  beta_reduce
  rw [hcnt jd hjd]
  exact frontLoopBodyJ_denote_foldl (accCTy := accCTy) (invCTys := .sword 64 :: invCTys)
    vmBody accName body hcov (.cons (BitVec.ofNat 64 jd) invsC) (fj jd) (cnt jd)
    (fun t acc' ht => hstep jd hjd t acc' ht) hupd acc

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyNestedStepC
