/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.LinearCombination
public import CatCrypt.Crypto.SecureCompilation.VIR.EdPointOnCurve

/-!
# The edwards25519 group

The on-curve affine points `EdwardsPointAff E` of a complete twisted-Edwards curve
`E` form an additive commutative group under the unified addition of
`Jasmin/EdwardsCurve.lean`, with identity `(0, 1)` and negation `(x, y) ↦ (−x, y)`.
The Ed25519 curve `ed25519Curve` is the record `⟨−1, ed25519D⟩` with the
completeness conditions of `EdPointOnCurve.isEdCurve_of_ed25519_constants`, and
`basePointAff` is the RFC 8032 §5.1 base point as an element of that group.

## Main results

* `instAddCommGroupEdwardsPointAff`: the on-curve affine points of a complete
  twisted-Edwards curve form an additive commutative group.
* `ed25519Curve`, `EdPt`: the Ed25519 curve and its group of on-curve points.
* `basePoint_onCurve`: the Ed25519 base point lies on the curve.
* `basePointAff`: the base point as an element of `EdPt`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519Group

open CatCrypt.Util (Fp25519 P25519 Ed25519Point ed25519D)
open CatCrypt.Crypto.Jasmin.EdwardsCurve (EdwardsParams EdwardsPointAff OnCurveAff)
open CatCrypt.Crypto.SecureCompilation.VIR.EdPointOnCurve (isEdCurve_of_ed25519_constants)

/-! ## 1. The on-curve affine points as an additive commutative group -/

section Group

variable {F : Type*} [Field F] {E : EdwardsParams F}

/-- Addition of on-curve affine points is the unified twisted-Edwards addition. -/
noncomputable instance instAddEdwardsPointAff : Add (EdwardsPointAff E) :=
  ⟨EdwardsPointAff.add⟩

/-- The zero of the on-curve affine points is the identity `(0, 1)`. -/
instance instZeroEdwardsPointAff : Zero (EdwardsPointAff E) := ⟨EdwardsPointAff.zero E⟩

/-- Negation of an on-curve affine point is `(x, y) ↦ (−x, y)`. -/
instance instNegEdwardsPointAff : Neg (EdwardsPointAff E) := ⟨EdwardsPointAff.neg⟩

/-- The on-curve affine points of a complete twisted-Edwards curve form an additive
    commutative group under the unified addition, with identity `(0, 1)` and
    negation `(x, y) ↦ (−x, y)`. -/
noncomputable instance instAddCommGroupEdwardsPointAff : AddCommGroup (EdwardsPointAff E) where
  add_assoc := EdwardsPointAff.add_assoc
  zero_add := EdwardsPointAff.zero_add
  add_zero := EdwardsPointAff.add_zero
  neg_add_cancel P := by
    show EdwardsPointAff.add (EdwardsPointAff.neg P) P = EdwardsPointAff.zero E
    rw [EdwardsPointAff.add_comm]
    exact EdwardsPointAff.add_neg_self P
  add_comm := EdwardsPointAff.add_comm
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem add_def (P Q : EdwardsPointAff E) : P + Q = EdwardsPointAff.add P Q := rfl

theorem zero_def : (0 : EdwardsPointAff E) = EdwardsPointAff.zero E := rfl

end Group

/-! ## 2. The Ed25519 curve and its base point -/

/-- The Ed25519 curve as the `Jasmin/EdwardsCurve.lean` record: the dialect pair
    `⟨−1, ed25519D⟩` with its completeness conditions. -/
def ed25519Curve : EdwardsParams Fp25519 :=
  (isEdCurve_of_ed25519_constants (C := ⟨-1, ed25519D⟩) rfl rfl).toCurve

/-- The on-curve affine points of Ed25519. -/
abbrev EdPt : Type := EdwardsPointAff ed25519Curve

/-- The `x`-coordinate of the RFC 8032 §5.1 base point. -/
def baseX : Fp25519 :=
  (15112221349535400772501151409588531511454012693041857206046113283949847762202 : ℕ)

/-- The `y`-coordinate of the RFC 8032 §5.1 base point (`4/5 mod p`). -/
def baseY : Fp25519 :=
  (46316835694926478169428394003475163141307993866256225615783033603165251855960 : ℕ)

/-- The RFC 8032 §5.1 base point as a computable affine point. -/
def basePoint : Ed25519Point := ⟨baseX, baseY⟩

/-- The base point satisfies the curve equation `−x² + y² = 1 + d·x²·y²`, checked on
    the canonical residues. -/
theorem basePoint_onCurve : OnCurveAff ed25519Curve baseX baseY := by
  have hd : ed25519D = ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : ℕ) : Fp25519) := rfl
  have ha : ed25519Curve.a = -1 := rfl
  have hdd : ed25519Curve.d = ed25519D := rfl
  unfold OnCurveAff
  rw [ha, hdd, hd, baseX, baseY]
  rw [show ∀ x y d : Fp25519, (-1 * x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2)
      ↔ (y ^ 2 = 1 + d * x ^ 2 * y ^ 2 + x ^ 2) from fun x y d => by
    constructor <;> intro h <;> linear_combination h]
  rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_one,
    ← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  decide

/-- The base point as an on-curve group element. -/
def basePointAff : EdPt := ⟨baseX, baseY, basePoint_onCurve⟩

end CatCrypt.Crypto.Jasmin.Ed25519Group
