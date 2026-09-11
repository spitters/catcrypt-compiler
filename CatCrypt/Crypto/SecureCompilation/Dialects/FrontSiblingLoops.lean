/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose

@[expose] public section

set_option autoImplicit false

/-!
# Front-compiling two sibling runtime loops into one `ComL`

A GMP-shape multi-limb kernel such as `mpn_mul_basecase` is two loop phases in
sequence: a first sweep (`mpn_mul_1`) that writes the initial rows, then a second
sweep (`mpn_addmul_1`, itself an outer loop over an inner accumulation loop) that
adds the remaining partial products. The two phases share a destination array but
each carries its own accumulator; the second phase reads the first phase's result
as an invariant.

`ComL`'s loop nodes carry a continuation that runs after the loop with the loop's
final accumulator bound at `.here`, so the sibling structure is the first phase's
loop with the second phase's loop as its continuation. This module packages that
seam as two named combinators over front-compiled loop bodies:

* `rolledSiblingLoops` — two plain runtime loops in sequence. The second loop's
  accumulator seed and invariants live in the extended context where the first
  loop's result is `.here`, so the first phase's output threads into the second.
* `rolledSiblingLoopsNested` — the same, with the second phase a nested runtime
  loop (`ComL.forLoopNRtNested`): the outer×inner sweep of `mpn_addmul_1` behind
  the initial `mpn_mul_1` sweep.

Both compose the committed continuation primitive
`TranslateDialectRuntimeLoop.rolledForLoopNRtCont` with a continuation-free
second loop; neither hand-authors a `Com`. The denotation of each is the second
phase's fold applied to the valuation extended by the first phase's fold — the
sequential composition `f₂ ∘ f₁` the phase seam realises, not a per-iteration
double fold.

## Main results

* `rolledSiblingLoops` / `rolledSiblingLoops_denote` — the two-plain-loop
  combinator and its fold-after-fold denotation.
* `rolledSiblingLoopsNested` / `rolledSiblingLoopsNested_denote` — the twin whose
  second phase is a nested runtime loop, and its denotation.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontSiblingLoops

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
  (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
  (rolledForLoopNRt rolledForLoopNRt_denote rolledForLoopNRtCont
   rolledForLoopNRtNested rolledForLoopNRtNested_denote)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
  (rolledForLoopNRtCont_denote)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. Two plain sibling runtime loops -/

/-- Front-compile two plain runtime loops in sequence into one `ComL`.

    The first loop runs over `Γouter` with accumulator `accCTy1`; the second runs
    over the extended context `mapTy accCTy1 :: Γouter`, where the first loop's
    result is bound at `.here`, so its `count2` / `init2` / `invs2` may read that
    result. The result type is the second loop's accumulator `mapTy accCTy2`.

    Built as `rolledForLoopNRtCont` (first loop) whose continuation is the
    continuation-free second loop; `none` if either front declines its body. -/
def rolledSiblingLoops {Γouter : Ctxt jasminDialect}
    {accCTy1 : CryptoTy} {invCTys1 : Ctx}
    {accCTy2 : CryptoTy} {invCTys2 : Ctx}
    (vm1 : VarMap (accCTy1 :: .sword 64 :: invCTys1)) (acc1Name : String) (body1 : LowCT)
    (count1 : Ctxt.Var Γouter (JasminTy.reg 64))
    (init1 : Ctxt.Var Γouter (mapTy accCTy1))
    (invs1 : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys1.map mapTy))
    (vm2 : VarMap (accCTy2 :: .sword 64 :: invCTys2)) (acc2Name : String) (body2 : LowCT)
    (count2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (JasminTy.reg 64))
    (init2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (mapTy accCTy2))
    (invs2 : HVector (fun ty => Ctxt.Var (mapTy accCTy1 :: Γouter) ty) (invCTys2.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy2)) :=
  match rolledForLoopNRt (Γouter := mapTy accCTy1 :: Γouter) (accCTy := accCTy2)
          (invCTys := invCTys2) vm2 acc2Name body2 count2 init2 invs2 with
  | some p2 =>
      rolledForLoopNRtCont (Γouter := Γouter) (accCTy := accCTy1) (invCTys := invCTys1)
        vm1 acc1Name body1 count1 init1 invs1 p2
  | none => none

/-- **The two-plain-sibling loop denotes the second fold after the first.** When
    both bodies front-compile, the program's denotation at any valuation is the
    second loop's `JLoopBodyN.denote` fold, run on the valuation extended by the
    first loop's fold result. -/
theorem rolledSiblingLoops_denote {Γouter : Ctxt jasminDialect}
    {accCTy1 : CryptoTy} {invCTys1 : Ctx}
    {accCTy2 : CryptoTy} {invCTys2 : Ctx}
    (vm1 : VarMap (accCTy1 :: .sword 64 :: invCTys1)) (acc1Name : String) (body1 : LowCT)
    (count1 : Ctxt.Var Γouter (JasminTy.reg 64))
    (init1 : Ctxt.Var Γouter (mapTy accCTy1))
    (invs1 : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys1.map mapTy))
    (vm2 : VarMap (accCTy2 :: .sword 64 :: invCTys2)) (acc2Name : String) (body2 : LowCT)
    (count2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (JasminTy.reg 64))
    (init2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (mapTy accCTy2))
    (invs2 : HVector (fun ty => Ctxt.Var (mapTy accCTy1 :: Γouter) ty) (invCTys2.map mapTy))
    {update1 : Com jasminDialect (mapCtx (accCTy1 :: .sword 64 :: invCTys1)) (mapTy accCTy1)}
    {update2 : Com jasminDialect (mapCtx (accCTy2 :: .sword 64 :: invCTys2)) (mapTy accCTy2)}
    (hupd1 : frontLoopBodyJ (accCTy := accCTy1) vm1 acc1Name body1 = some update1)
    (hupd2 : frontLoopBodyJ (accCTy := accCTy2) vm2 acc2Name body2 = some update2)
    (V : Ctxt.Valuation Γouter) :
    (rolledSiblingLoops vm1 acc1Name body1 count1 init1 invs1
        vm2 acc2Name body2 count2 init2 invs2).map (fun c => ComL.denote c V)
      = (let r1 : ⟦mapTy accCTy1⟧ :=
           JLoopBodyN.denote
             (⟨(count1.lookup V).toNat, update1⟩ : JLoopBodyN (mapTy accCTy1) (invCTys1.map mapTy))
             (Expr.lookupArgs invs1 V) (init1.lookup V)
         some
           (JLoopBodyN.denote ⟨(count2.lookup (V.extend r1)).toNat, update2⟩
             (Expr.lookupArgs invs2 (V.extend r1)) (init2.lookup (V.extend r1)))) := by
  have hp2 : rolledForLoopNRt (Γouter := mapTy accCTy1 :: Γouter) (accCTy := accCTy2)
      (invCTys := invCTys2) vm2 acc2Name body2 count2 init2 invs2
        = some (ComL.forLoopNRt update2 count2 init2 invs2 (.ret .here)) := by
    unfold rolledForLoopNRt rolledForLoopNRtCont
    rw [hupd2]
  simp only [rolledSiblingLoops, hp2]
  rw [rolledForLoopNRtCont_denote vm1 acc1Name body1 count1 init1 invs1 _ hupd1 V]
  rfl

/-! ## 2. A plain first phase with a nested second phase

The GMP `mpn_mul_basecase` shape: the first phase is the `mpn_mul_1` sweep and the
second phase is the `mpn_addmul_1` outer×inner nest. -/

/-- Front-compile a plain first runtime loop followed by a nested second runtime
    loop into one `ComL`. The first loop's result is bound at `.here` in the
    second phase's context, so the nested phase reads it. `none` if any of the
    three bodies (first update, second count, second update) declines. -/
def rolledSiblingLoopsNested {Γouter : Ctxt jasminDialect}
    {accCTy1 : CryptoTy} {invCTys1 : Ctx}
    {accCTy2 : CryptoTy} {invCTys2 : Ctx}
    (vm1 : VarMap (accCTy1 :: .sword 64 :: invCTys1)) (acc1Name : String) (body1 : LowCT)
    (count1 : Ctxt.Var Γouter (JasminTy.reg 64))
    (init1 : Ctxt.Var Γouter (mapTy accCTy1))
    (invs1 : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys1.map mapTy))
    (vmCount2 : VarMap (.sword 64 :: invCTys2)) (count2Name : String) (countBody2 : LowCT)
    (vm2 : VarMap (accCTy2 :: .sword 64 :: .sword 64 :: invCTys2)) (acc2Name : String)
    (updateBody2 : LowCT)
    (outerCount2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (JasminTy.reg 64))
    (init2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (mapTy accCTy2))
    (invs2 : HVector (fun ty => Ctxt.Var (mapTy accCTy1 :: Γouter) ty) (invCTys2.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy2)) :=
  match rolledForLoopNRtNested (Γouter := mapTy accCTy1 :: Γouter) (accCTy := accCTy2)
          (invCTys := invCTys2) vmCount2 count2Name countBody2 vm2 acc2Name updateBody2
          outerCount2 init2 invs2 with
  | some p2 =>
      rolledForLoopNRtCont (Γouter := Γouter) (accCTy := accCTy1) (invCTys := invCTys1)
        vm1 acc1Name body1 count1 init1 invs1 p2
  | none => none

/-- **The plain-then-nested sibling loop denotes the nested double fold after the
    first fold.** When all three bodies front-compile, the program's denotation is
    the second phase's `JLoopBodyN.nestedDenote` double fold, run on the valuation
    extended by the first phase's fold result. -/
theorem rolledSiblingLoopsNested_denote {Γouter : Ctxt jasminDialect}
    {accCTy1 : CryptoTy} {invCTys1 : Ctx}
    {accCTy2 : CryptoTy} {invCTys2 : Ctx}
    (vm1 : VarMap (accCTy1 :: .sword 64 :: invCTys1)) (acc1Name : String) (body1 : LowCT)
    (count1 : Ctxt.Var Γouter (JasminTy.reg 64))
    (init1 : Ctxt.Var Γouter (mapTy accCTy1))
    (invs1 : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys1.map mapTy))
    (vmCount2 : VarMap (.sword 64 :: invCTys2)) (count2Name : String) (countBody2 : LowCT)
    (vm2 : VarMap (accCTy2 :: .sword 64 :: .sword 64 :: invCTys2)) (acc2Name : String)
    (updateBody2 : LowCT)
    (outerCount2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (JasminTy.reg 64))
    (init2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (mapTy accCTy2))
    (invs2 : HVector (fun ty => Ctxt.Var (mapTy accCTy1 :: Γouter) ty) (invCTys2.map mapTy))
    {update1 : Com jasminDialect (mapCtx (accCTy1 :: .sword 64 :: invCTys1)) (mapTy accCTy1)}
    {innerCount2 : Com jasminDialect (mapCtx (.sword 64 :: invCTys2)) (mapTy (.sword 64))}
    {innerUpdate2 : Com jasminDialect
      (mapCtx (accCTy2 :: .sword 64 :: .sword 64 :: invCTys2)) (mapTy accCTy2)}
    (hupd1 : frontLoopBodyJ (accCTy := accCTy1) vm1 acc1Name body1 = some update1)
    (hcnt2 : frontLoopBodyJ (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys2)
              vmCount2 count2Name countBody2 = some innerCount2)
    (hupd2 : frontLoopBodyJ (accCTy := accCTy2)
              (Γbody := accCTy2 :: .sword 64 :: .sword 64 :: invCTys2)
              vm2 acc2Name updateBody2 = some innerUpdate2)
    (V : Ctxt.Valuation Γouter) :
    (rolledSiblingLoopsNested vm1 acc1Name body1 count1 init1 invs1
        vmCount2 count2Name countBody2 vm2 acc2Name updateBody2
        outerCount2 init2 invs2).map (fun c => ComL.denote c V)
      = (let r1 : ⟦mapTy accCTy1⟧ :=
           JLoopBodyN.denote
             (⟨(count1.lookup V).toNat, update1⟩ : JLoopBodyN (mapTy accCTy1) (invCTys1.map mapTy))
             (Expr.lookupArgs invs1 V) (init1.lookup V)
         some
           (JLoopBodyN.nestedDenote innerCount2 innerUpdate2
             (outerCount2.lookup (V.extend r1)).toNat
             (Expr.lookupArgs invs2 (V.extend r1)) (init2.lookup (V.extend r1)))) := by
  have hp2 : rolledForLoopNRtNested (Γouter := mapTy accCTy1 :: Γouter) (accCTy := accCTy2)
      (invCTys := invCTys2) vmCount2 count2Name countBody2 vm2 acc2Name updateBody2
      outerCount2 init2 invs2
        = some (ComL.forLoopNRtNested innerCount2 innerUpdate2 outerCount2 init2 invs2
            (.ret .here)) := by
    unfold rolledForLoopNRtNested
      TranslateDialectRuntimeLoop.rolledForLoopNRtNestedCont
    rw [hcnt2, hupd2]
  simp only [rolledSiblingLoopsNested, hp2]
  rw [rolledForLoopNRtCont_denote vm1 acc1Name body1 count1 init1 invs1 _ hupd1 V]
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontSiblingLoops
