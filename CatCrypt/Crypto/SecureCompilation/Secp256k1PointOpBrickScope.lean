/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickReduce
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickInv

/-!
# The doubling schedule's value tie, from the brick scope

`Secp256k1PointOpBrickInv.BrickStepInv` is the per-brick obligation in the form
the schedule fold can chain: parametric in an entry predicate each brick both
assumes and re-establishes. `Secp256k1FeMulBrickReduce.brickStep` proves exactly
that shape on all three arms, at the predicate
`Secp256k1FeAddSubBrick.BrickScope`.

Instantiating one at the other discharges `BrickStepInv` and, through
`jacDblSchedule_waist_value_inv`, gives the doubling schedule's waist value over
an entry environment in the brick scope, with no residual hypothesis.

## Main results

* `brickStepInv_brickScope` — `BrickStepInv BrickScope`, from `brickStep`.
* `jacDblSchedule_waist_value_brickScope`,
  `jacAddSchedule_waist_value_brickScope` — from an entry environment in the
  brick scope whose schedule readout is the operation's initial environment, the
  emitted schedule's waist holds `jacDblSpec` / `jacAddSpec`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickScope

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (runSchedule jacDblSchedule jacDblSpec jacAddSchedule jacAddSpec)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (feVal schedNameB)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional (dblEnv0 addEnv0)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick (BrickScope)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickReduce
  (brickStep genMulSpec_holds constsAt_of_brickScope)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickInv
  (BrickStepInv jacDblSchedule_waist_value_inv jacAddSchedule_waist_value_inv
   jacDblSchedule_scope_inv jacAddSchedule_scope_inv)

/-- **The per-brick obligation, at the brick scope.** `brickStep` already has the
    invariant-preserving shape; this names it as `BrickStepInv` so the schedule
    fold can consume it. -/
theorem brickStepInv_brickScope : BrickStepInv BrickScope := by
  intro i op env env' hop hsc hsem
  obtain ⟨hsc', hval⟩ :=
    brickStep genMulSpec_holds i op hop env env' hsc (constsAt_of_brickScope hsc) hsem
  exact ⟨hval, hsc'⟩

/-- **The doubling schedule's waist value, over the brick scope.** No residual
    hypothesis: the per-brick obligation is discharged, so an entry environment
    in the brick scope holding `dblEnv0 X Y Z` leaves the emitted schedule's
    waist at `jacDblSpec X Y Z`. -/
theorem jacDblSchedule_waist_value_brickScope
    (env env' : SEnvScalar) (X Y Z : Nat)
    (hsc : BrickScope env)
    (h0 : ∀ fe, schedNameB fe = true → feVal env fe = dblEnv0 X Y Z fe)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    (feVal env' "Xp", feVal env' "Yp", feVal env' "Zp") = jacDblSpec X Y Z :=
  jacDblSchedule_waist_value_inv brickStepInv_brickScope env env' X Y Z hsc h0 hSem

/-- **The brick scope survives the doubling schedule.** The store block that
    follows reads the half-limb slots, so it needs the scope at its entry and not
    only the value tie. -/
theorem jacDblSchedule_waist_scope
    (env env' : SEnvScalar) (hsc : BrickScope env)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    BrickScope env' :=
  jacDblSchedule_scope_inv brickStepInv_brickScope env env' hsc hSem

/-- **The brick scope survives the addition schedule.** -/
theorem jacAddSchedule_waist_scope
    (env env' : SEnvScalar) (hsc : BrickScope env)
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    BrickScope env' :=
  jacAddSchedule_scope_inv brickStepInv_brickScope env env' hsc hSem

/-- **The addition schedule's waist value, over the brick scope.** The
    `jacAddSchedule` counterpart of `jacDblSchedule_waist_value_brickScope`. -/
theorem jacAddSchedule_waist_value_brickScope
    (env env' : SEnvScalar) (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hsc : BrickScope env)
    (h0 : ∀ fe, schedNameB fe = true → feVal env fe = addEnv0 X1 Y1 Z1 X2 Y2 Z2 fe)
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    (feVal env' "Xp", feVal env' "Yp", feVal env' "Zp") = jacAddSpec X1 Y1 Z1 X2 Y2 Z2 :=
  jacAddSchedule_waist_value_inv brickStepInv_brickScope env env' X1 Y1 Z1 X2 Y2 Z2
    hsc h0 hSem

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickScope
