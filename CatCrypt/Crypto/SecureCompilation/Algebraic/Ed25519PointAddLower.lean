/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAddCompile

/-!
# The extended-coordinate point addition over four 64-bit limbs per coordinate

`pointAddProg` of `Ed25519PointAddCompile` is covered by
`FieldToJasminLimbs25519.GoodL`, so `fieldToJasminLimbs_denote` applies to it: its
lowering `loweringL.lowerMulti` is a `MultiReturnCom jasminDialect` over the
thirty-two limb registers of the eight input coordinates, returning the four limbs
of the selected output coordinate.

The four output coordinates are obtained as the four programs
`pointAddProg dd 0 .. 3`, which share their bindings and differ in the returned
variable, so the sixteen output limbs are the limbs of `X₃`, `Y₃`, `Z₃`, `T₃`.

## Main definitions

* `pointAddJasmin`: the lowered program.
* `limbVal`: the thirty-two input limbs as a valuation of the flattened context.

## Main results

* `flatVal_inVal`: the flattened valuation of `inVal` is the appended limbs of the
  eight coordinates.
* `pointAddProg_lowered`: the lowered program maps the limbs of the inputs to the
  limbs of the source program's result.
* `pointAddProg_lowered_x3`, `_y3`, `_z3`, `_t3`: the four lowered programs return
  the limbs of the four entries of `addSpec`.
* `pointAddProg_lowered_m1add`: at extended-point inputs the four lowered programs
  return the limbs of the coordinates of `EdwardsPointExt.m1add`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs25519
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (p25519 enc)
open CatCrypt.Crypto.Jasmin.EdwardsCurve (EdwardsPointExt)
open CatCrypt.Util (ed25519D)

/-- The lowering of the addition program returning coordinate `i`, over four
    64-bit limbs per field element. -/
def pointAddJasmin (dd : ZMod p25519) (i : Fin 4) :
    MultiReturnCom jasminDialect (loweringL.mapCtx inCtxt) (loweringL.mapTys F25519) :=
  loweringL.lowerMulti (pointAddProg dd i)

/-- The thirty-two input limbs: the four limbs of each of the eight input
    coordinates, in input order. -/
def limbVal (x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    Valuation (loweringL.mapCtx inCtxt) :=
  hvAppend (enc x1) (hvAppend (enc y1) (hvAppend (enc z1) (hvAppend (enc t1)
    (hvAppend (enc x2) (hvAppend (enc y2) (hvAppend (enc z2)
      (hvAppend (enc t2) .nil)))))))

theorem flatVal_inVal (x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    flatVal (fun {t} x => encL (t := t) x) (inVal x1 y1 z1 t1 x2 y2 z2 t2)
      = limbVal x1 y1 z1 t1 x2 y2 z2 t2 := rfl

/-- **Denotation preservation of the lowered addition.** -/
theorem pointAddProg_lowered (dd : ZMod p25519) (i : Fin 4) (V : Valuation inCtxt) :
    (pointAddJasmin dd i).denote (flatVal (fun {t} x => encL (t := t) x) V)
      = encL ((pointAddProg dd i).denote V) :=
  fieldToJasminLimbs_denote (pointAddProg dd i) (pointAddProg_covered dd i) V

theorem pointAddProg_lowered_x3 (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    (pointAddJasmin dd 0).denote (limbVal x1 y1 z1 t1 x2 y2 z2 t2)
      = enc (addSpec dd x1 y1 z1 t1 x2 y2 z2 t2).1 := by
  have h := pointAddProg_lowered dd 0 (inVal x1 y1 z1 t1 x2 y2 z2 t2)
  rw [flatVal_inVal, pointAddProg_denote_x3, encL_fp] at h
  exact h

theorem pointAddProg_lowered_y3 (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    (pointAddJasmin dd 1).denote (limbVal x1 y1 z1 t1 x2 y2 z2 t2)
      = enc (addSpec dd x1 y1 z1 t1 x2 y2 z2 t2).2.1 := by
  have h := pointAddProg_lowered dd 1 (inVal x1 y1 z1 t1 x2 y2 z2 t2)
  rw [flatVal_inVal, pointAddProg_denote_y3, encL_fp] at h
  exact h

theorem pointAddProg_lowered_z3 (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    (pointAddJasmin dd 2).denote (limbVal x1 y1 z1 t1 x2 y2 z2 t2)
      = enc (addSpec dd x1 y1 z1 t1 x2 y2 z2 t2).2.2.1 := by
  have h := pointAddProg_lowered dd 2 (inVal x1 y1 z1 t1 x2 y2 z2 t2)
  rw [flatVal_inVal, pointAddProg_denote_z3, encL_fp] at h
  exact h

theorem pointAddProg_lowered_t3 (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    (pointAddJasmin dd 3).denote (limbVal x1 y1 z1 t1 x2 y2 z2 t2)
      = enc (addSpec dd x1 y1 z1 t1 x2 y2 z2 t2).2.2.2 := by
  have h := pointAddProg_lowered dd 3 (inVal x1 y1 z1 t1 x2 y2 z2 t2)
  rw [flatVal_inVal, pointAddProg_denote_t3, encL_fp] at h
  exact h

/-- **The sixteen output limbs are the coordinates of the sum.** At inputs that
    are extended points of the Ed25519 curve, the four lowered programs return the
    limbs of the four coordinates of `EdwardsPointExt.m1add`. -/
theorem pointAddProg_lowered_m1add (P Q : EdwardsPointExt ed25519Ext) :
    (pointAddJasmin ed25519D 0).denote (limbVal P.X P.Y P.Z P.T Q.X Q.Y Q.Z Q.T)
        = enc (EdwardsPointExt.m1add ed25519Ext_a P Q).X ∧
      (pointAddJasmin ed25519D 1).denote (limbVal P.X P.Y P.Z P.T Q.X Q.Y Q.Z Q.T)
        = enc (EdwardsPointExt.m1add ed25519Ext_a P Q).Y ∧
      (pointAddJasmin ed25519D 2).denote (limbVal P.X P.Y P.Z P.T Q.X Q.Y Q.Z Q.T)
        = enc (EdwardsPointExt.m1add ed25519Ext_a P Q).Z ∧
      (pointAddJasmin ed25519D 3).denote (limbVal P.X P.Y P.Z P.T Q.X Q.Y Q.Z Q.T)
        = enc (EdwardsPointExt.m1add ed25519Ext_a P Q).T := by
  have h := addSpec_m1add P Q
  rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pointAddProg_lowered_x3, h.1]
  · rw [pointAddProg_lowered_y3, h.2.1]
  · rw [pointAddProg_lowered_z3, h.2.2.1]
  · rw [pointAddProg_lowered_t3, h.2.2.2]

end CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd
