/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

/-!
# Montgomery-domain transport for NTT arithmetic

The Montgomery representation stores a field element `a` as `a · R` (the
*Montgomery form*), where `R` is a fixed unit (the Montgomery radix). Products
in this representation are taken with `montMul x y = x · y · R⁻¹`, which absorbs
the extra `R` factor so that the representation map stays a ring homomorphism
*into the Montgomery-multiplication monoid*.

This file proves the algebraic transport, purely over a field `F` with a nonzero
radix `R` (no byte/limb representation layer): the representation map
`toMont a = a · R` is

* **additive**: `toMont (a + b) = toMont a + toMont b` (`toMont_add`);
* **multiplicative into `montMul`**: `toMont (a · b) = montMul (toMont a) (toMont b)`
  (`montMul_toMont`), the crux — ordinary product corresponds to Montgomery
  product under the representation; and
* **bijective**: multiplication by a unit, with inverse `fromMont x = x · R⁻¹`
  (`fromMont_toMont`, `toMont_fromMont`, `toMont_injective`, `toMont_bijective`).

The payoff is `montButterfly_eq_toMont`: a radix-2 Cooley–Tukey butterfly run on
Montgomery-form operands `(toMont a, toMont b)` with a Montgomery-form twiddle
`toMont ω`, using `montMul` for the twiddle multiply, equals the Montgomery form
of the ordinary `ctButterfly ω a b`. So a Montgomery-domain butterfly *reads as*
the ordinary butterfly under the representation map, closing the
`Montgomery ↔ ZMod` (field) transport gap.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryTransport

open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

variable {F : Type*} [Field F] {R : F}

/-- The Montgomery representation map: store `a` as `a · R`. -/
def toMont (R a : F) : F := a * R

/-- Recover an element from Montgomery form: `x · R⁻¹`. -/
def fromMont (R x : F) : F := x * R⁻¹

/-- Montgomery multiplication: `montMul R x y = x · y · R⁻¹`. The extra `R⁻¹`
cancels one of the two `R` factors carried by the Montgomery-form operands. -/
def montMul (R x y : F) : F := x * y * R⁻¹

/-! ## Representation-map laws -/

/-- `toMont` is additive (it is multiplication by `R`). -/
@[simp] theorem toMont_add (R a b : F) :
    toMont R (a + b) = toMont R a + toMont R b := by
  simp [toMont, add_mul]

/-- `toMont` sends subtraction to subtraction. -/
@[simp] theorem toMont_sub (R a b : F) :
    toMont R (a - b) = toMont R a - toMont R b := by
  simp [toMont, sub_mul]

/-- The crux: ordinary multiplication corresponds to Montgomery multiplication
under the representation map, `toMont (a · b) = montMul (toMont a) (toMont b)`.
Needs `R ≠ 0` so that `R · R⁻¹ = 1`. -/
theorem montMul_toMont (hR : R ≠ 0) (a b : F) :
    toMont R (a * b) = montMul R (toMont R a) (toMont R b) := by
  simp only [toMont, montMul]
  rw [show a * R * (b * R) * R⁻¹ = a * b * R * (R * R⁻¹) by ring,
    mul_inv_cancel₀ hR, mul_one]

/-- `fromMont` is a left inverse of `toMont` (when `R ≠ 0`). -/
@[simp] theorem fromMont_toMont (hR : R ≠ 0) (a : F) :
    fromMont R (toMont R a) = a := by
  simp only [fromMont, toMont, mul_assoc, mul_inv_cancel₀ hR, mul_one]

/-- `fromMont` is a right inverse of `toMont` (when `R ≠ 0`). -/
@[simp] theorem toMont_fromMont (hR : R ≠ 0) (x : F) :
    toMont R (fromMont R x) = x := by
  simp only [toMont, fromMont, mul_assoc, inv_mul_cancel₀ hR, mul_one]

/-- `toMont R` is injective (multiplication by the nonzero `R` in a field). -/
theorem toMont_injective (hR : R ≠ 0) :
    Function.Injective (toMont R) := by
  intro a b h
  have := congrArg (fromMont R) h
  simpa [fromMont_toMont hR] using this

/-- `toMont R` is surjective: `fromMont R x` is a preimage of `x`. -/
theorem toMont_surjective (hR : R ≠ 0) :
    Function.Surjective (toMont R) :=
  fun x => ⟨fromMont R x, toMont_fromMont hR x⟩

/-- `toMont R` is bijective (multiplication by a unit in a field). -/
theorem toMont_bijective (hR : R ≠ 0) :
    Function.Bijective (toMont R) :=
  ⟨toMont_injective hR, toMont_surjective hR⟩

/-- The representation map packaged as an equivalence `F ≃ F`. -/
@[simps] def toMontEquiv (hR : R ≠ 0) : F ≃ F where
  toFun := toMont R
  invFun := fromMont R
  left_inv := fromMont_toMont hR
  right_inv := toMont_fromMont hR

/-! ## Montgomery-domain butterfly transport -/

/-- The Montgomery-domain Cooley–Tukey butterfly. The twiddle `ωhat` and the
operands `x`, `y` are all in Montgomery form; the twiddle multiply uses
`montMul`, while the add/subtract lanes are ordinary field operations (Montgomery
form is additive, so no correction is needed there). -/
def montButterfly (R ωhat x y : F) : F × F :=
  (x + montMul R ωhat y, x - montMul R ωhat y)

@[simp] theorem montButterfly_fst (R ωhat x y : F) :
    (montButterfly R ωhat x y).1 = x + montMul R ωhat y := rfl

@[simp] theorem montButterfly_snd (R ωhat x y : F) :
    (montButterfly R ωhat x y).2 = x - montMul R ωhat y := rfl

/-- The Montgomery-form twiddle multiply transports to the ordinary product:
`montMul (toMont ω) (toMont b) = toMont (ω · b)`. -/
theorem montMul_toMont_twiddle (hR : R ≠ 0) (ω b : F) :
    montMul R (toMont R ω) (toMont R b) = toMont R (ω * b) :=
  (montMul_toMont hR ω b).symm

/-- **Montgomery butterfly transport.** Running the Montgomery-domain butterfly
on Montgomery-form operands `(toMont a, toMont b)` with Montgomery-form twiddle
`toMont ω` equals the Montgomery form of the ordinary `ctButterfly ω a b`:
componentwise `toMont` of `(a + ω·b, a − ω·b)`. So the Montgomery-domain
butterfly reads as the ordinary butterfly under the representation map. -/
theorem montButterfly_eq_toMont (hR : R ≠ 0) (ω a b : F) :
    montButterfly R (toMont R ω) (toMont R a) (toMont R b)
      = (toMont R (ctButterfly ω a b).1, toMont R (ctButterfly ω a b).2) := by
  simp only [montButterfly, ctButterfly_fst, ctButterfly_snd,
    montMul_toMont_twiddle hR, ← toMont_add, ← toMont_sub]

end CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryTransport
