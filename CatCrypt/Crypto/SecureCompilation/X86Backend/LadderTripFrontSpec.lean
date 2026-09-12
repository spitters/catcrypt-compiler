/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedLadder
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedScheduleValue
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
public import CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric
public import CatCrypt.Crypto.SecureCompilation.EcProjectiveAddGeneric

/-!
# The secp256k1 point-op `Nat` specs as the generic Jacobian group law

`Secp256k1PointOpFront.jacDblSpec` / `jacAddSpec` are the `Nat`-valued
`dbl-2009-l` / `add-2007-bl` point-op specs the framed doubling/addition bodies
compute in their output slots
(`Secp256k1PointOpFramedScheduleValue.jacDblBodyFramed_spec`). This module ties
them, componentwise under the cast into `ZMod pNat` (`pNat` the secp256k1
base-field prime), to the generic group-law forms
`EcProjectiveGeneric.jacDoubleGen` / `jacAddGen`, and pins the type of the
framed ladder step pushed through the scalar rolled-loop front.

## Main results

* `fm_cast` / `fa_cast` / `fs_cast` — the base-field `Nat` operations cast into
  `ZMod pNat` as `*` / `+` / `-`.
* `jacDblSpec_cast_eq_jacDoubleGen` — `jacDblSpec` cast into `ZMod pNat` is
  `jacDoubleGen` at the cast coordinates.
* `jacAddSpec_cast_eq_jacAddGen` — `jacAddSpec` cast into `ZMod pNat` is
  `jacAddGen` at the cast coordinates.
* `ladderΓbody` / `ladderVMBody` / `mapCtx_ladderΓbody` — the framed ladder's
  loop-body context (256-cell frame accumulator, loop index, empty invariant
  tail) and its jasmin image.
* `ladderStepUpdateOf` / `ladderStepUpdate?` — a loop body over the ladder
  context, and `ladderStepFramed` in particular, pushed through the scalar
  rolled-loop front (`frontLoopBodyJ`), typed as the `JLoopBodyN.update` shape
  over the 256-cell ladder frame.
* `LadderStepFrontOk` — the front-success gate `ladderStepUpdate?.isSome`, as a
  named hypothesis for downstream statements.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LadderTripFrontSpec

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (pNat)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront (fm fa fs jacDblSpec jacAddSpec)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedLadder (ladderStepFramed)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedScheduleValue
  (fm_lt_pNat fa_lt_pNat fs_lt_pNat)
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric (jacDoubleGen jacAddGen)

/-! ## 1. The base-field `Nat` operations under the cast into `ZMod pNat` -/

/-- `fm` casts to multiplication in `ZMod pNat`. -/
theorem fm_cast (a b : Nat) :
    ((fm a b : Nat) : ZMod pNat) = (a : ZMod pNat) * (b : ZMod pNat) := by
  simp only [fm, ZMod.natCast_mod, Nat.cast_mul]

/-- `fa` casts to addition in `ZMod pNat`. -/
theorem fa_cast (a b : Nat) :
    ((fa a b : Nat) : ZMod pNat) = (a : ZMod pNat) + (b : ZMod pNat) := by
  simp only [fa, ZMod.natCast_mod, Nat.cast_add]

/-- `fs` casts to subtraction in `ZMod pNat` when the subtrahend is a canonical
    residue (`b < pNat`, so the `Nat` subtraction `a + pNat - b` never
    truncates). Every `fs` subtrahend in `jacDblSpec` / `jacAddSpec` is an
    `fm`/`fa`/`fs` output, hence canonical. -/
theorem fs_cast (a : Nat) {b : Nat} (hb : b < pNat) :
    ((fs a b : Nat) : ZMod pNat) = (a : ZMod pNat) - (b : ZMod pNat) := by
  have hble : b ≤ a + pNat := hb.le.trans (Nat.le_add_left _ _)
  simp only [fs, ZMod.natCast_mod, Nat.cast_sub hble, Nat.cast_add,
    ZMod.natCast_self, add_zero]

/-! ## 2. The `Nat` point-op specs are the generic group law in `ZMod pNat` -/

/-- **`jacDblSpec` is `jacDoubleGen` over `ZMod pNat`.** Casting the three
    components of the `Nat`-valued `dbl-2009-l` spec into the secp256k1 base
    field yields the generic group-law double at the cast coordinates. -/
theorem jacDblSpec_cast_eq_jacDoubleGen [Fact (Nat.Prime pNat)] (X Y Z : Nat) :
    (((jacDblSpec X Y Z).1 : ZMod pNat),
     ((jacDblSpec X Y Z).2.1 : ZMod pNat),
     ((jacDblSpec X Y Z).2.2 : ZMod pNat))
      = jacDoubleGen (X : ZMod pNat) (Y : ZMod pNat) (Z : ZMod pNat) := by
  simp only [jacDblSpec, jacDoubleGen, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [fm_cast, fa_cast, fs_cast, fa_lt_pNat, fs_lt_pNat]
      ring

/-- **`jacAddSpec` is `jacAddGen` over `ZMod pNat`.** Casting the three
    components of the `Nat`-valued `add-2007-bl` spec into the secp256k1 base
    field yields the generic group-law add at the cast coordinates. -/
theorem jacAddSpec_cast_eq_jacAddGen [Fact (Nat.Prime pNat)]
    (X1 Y1 Z1 X2 Y2 Z2 : Nat) :
    (((jacAddSpec X1 Y1 Z1 X2 Y2 Z2).1 : ZMod pNat),
     ((jacAddSpec X1 Y1 Z1 X2 Y2 Z2).2.1 : ZMod pNat),
     ((jacAddSpec X1 Y1 Z1 X2 Y2 Z2).2.2 : ZMod pNat))
      = jacAddGen (X1 : ZMod pNat) (Y1 : ZMod pNat) (Z1 : ZMod pNat)
          (X2 : ZMod pNat) (Y2 : ZMod pNat) (Z2 : ZMod pNat) := by
  simp only [jacAddSpec, jacAddGen, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [fm_cast, fa_cast, fs_cast, fm_lt_pNat, fa_lt_pNat, fs_lt_pNat]
      ring

/-! ## 3. The framed ladder step through the rolled-loop front -/

/-- Loop-body context of the framed ladder step: the 256-cell frame accumulator
    at the head, the loop index next, and an empty invariant tail — every value
    the step reads or writes lives in the frame. -/
def ladderΓbody : Ctx := [.memref 256, .sword 64]

/-- Loop-body `VarMap`: the frame bound as `F` at the accumulator slot, the
    loop index bound as `i`. -/
def ladderVMBody : VarMap ladderΓbody :=
  (VarMap.empty.bind (t := .sword 64) "i").bind (t := .memref 256) "F"

/-- The ladder body context lowers to the `JLoopBodyN.update` context shape:
    stack-array accumulator, `reg 64` loop index, no invariants. -/
theorem mapCtx_ladderΓbody :
    mapCtx ladderΓbody = [JasminTy.stackArr 64 256, JasminTy.reg 64] := rfl

/-- A loop body over the ladder context pushed through the scalar rolled-loop
    front, typed at the `JLoopBodyN.update` shape over the 256-cell ladder
    frame. `none` when the front declines the body. -/
def ladderStepUpdateOf (body : LowCT) :
    Option (Com jasminDialect
      (JasminTy.stackArr 64 256 :: JasminTy.reg 64 :: ([] : Ctxt jasminDialect))
      (JasminTy.stackArr 64 256)) :=
  frontLoopBodyJ (accCTy := .memref 256) ladderVMBody "F" body

/-- `ladderStepFramed` pushed through the scalar rolled-loop front: the
    `JLoopBodyN.update`-shaped `Com jasminDialect` carrying the 256-cell ladder
    frame as the loop accumulator. -/
def ladderStepUpdate? := ladderStepUpdateOf ladderStepFramed

/-- The front-success gate: the scalar rolled-loop front accepts the framed
    ladder step. -/
def LadderStepFrontOk : Prop := ladderStepUpdate?.isSome

end CatCrypt.Crypto.SecureCompilation.X86Backend.LadderTripFrontSpec
