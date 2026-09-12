/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Tactic.Ring


@[expose] public section
set_option autoImplicit false

/-!
# Curve-agnostic final-exponentiation correctness

This file proves the *generic* core of the optimal-ate final exponentiation used
in pairing-based cryptography, in a fully curve-agnostic setting.

For a pairing over an embedding-degree-12 curve (BLS12, BN, …), a Miller-loop
output `f` lives in the degree-12 extension field, and the pairing value is
obtained by raising `f` to the power `(q¹² − 1)/r`, where `q` is the base-field
size and `r` the group order. Implementations split this exponentiation into

* an **easy part** `m := f^(q⁶) · f⁻¹` followed by `m · Frob²(m)`
  (here `Frob²` is modeled as the literal integer power `·^(q²)`), and
* a **hard part**, raising the easy-part output to `(q⁴ − q² + 1)/r`.

The headline lemma `finalExp_correct` shows the composition of these two steps
equals the single power map `·^((q¹² − 1)/r)`, given only the cyclotomic
divisibility `r ∣ (q⁴ − q² + 1)`. Everything is stated in an abstract
`CommGroup G` with the Frobenius maps modeled as integer powers (`zpow`), so the
result is reusable: a concrete pairing field instantiates it by taking
`G = Kˣ` (the units of the degree-12 field), `Q = q` (the base-field size), with
the conjugation `·^(q⁶)` and Frobenius `·^(q²)` realized literally as the integer
powers appearing here (on a finite field these powers coincide with the
`q⁶`- and `q²`-iterated Frobenius endomorphism, but that identification is left
to the instantiation step and is **not** needed for the algebraic identity).

The whole development is curve-agnostic: it does not import any BLS/BN/Fp12
file.
-/

namespace CatCrypt.Pairing.FinalExpGeneric

variable {G : Type*} [CommGroup G]

/-- The cyclotomic factorization of the final exponent at embedding degree 12:
`(Q⁶ − 1)(Q² + 1)(Q⁴ − Q² + 1) = Q¹² − 1`. Concretely this packages
`Q¹² − 1 = (Q⁶ − 1)(Q⁶ + 1)` together with `Q⁶ + 1 = (Q² + 1)(Q⁴ − Q² + 1)`. -/
theorem exp_factor (Q : ℤ) :
    (Q ^ 6 - 1) * (Q ^ 2 + 1) * (Q ^ 4 - Q ^ 2 + 1) = Q ^ 12 - 1 := by
  ring

/-- The **easy part** of the final exponentiation as a single power map.
With `m := f^(Q⁶) · f⁻¹`, the easy-part output `m · m^(Q²)` equals
`f^((Q⁶ − 1)(Q² + 1))`. -/
theorem finalExpEasy_eq (Q : ℤ) (f : G) :
    (f ^ (Q ^ 6) * f⁻¹) * (f ^ (Q ^ 6) * f⁻¹) ^ (Q ^ 2)
      = f ^ ((Q ^ 6 - 1) * (Q ^ 2 + 1)) := by
  have hm : f ^ (Q ^ 6) * f⁻¹ = f ^ (Q ^ 6 - 1) := (zpow_sub_one f (Q ^ 6)).symm
  rw [hm, ← zpow_mul, ← zpow_add]
  congr 1
  ring

/-- The **headline** curve-agnostic final-exponentiation correctness lemma.

Given the cyclotomic divisibility `r ∣ (Q⁴ − Q² + 1)`, composing the easy part
`m · m^(Q²)` (with `m = f^(Q⁶) · f⁻¹`) with the hard part `·^((Q⁴ − Q² + 1)/r)`
equals the full final exponentiation `·^((Q¹² − 1)/r)`. -/
theorem finalExp_correct {Q r : ℤ} (hr : r ∣ (Q ^ 4 - Q ^ 2 + 1)) (f : G) :
    ((f ^ (Q ^ 6) * f⁻¹) * (f ^ (Q ^ 6) * f⁻¹) ^ (Q ^ 2)) ^ ((Q ^ 4 - Q ^ 2 + 1) / r)
      = f ^ ((Q ^ 12 - 1) / r) := by
  rw [finalExpEasy_eq, ← zpow_mul]
  congr 1
  rw [← Int.mul_ediv_assoc _ hr, exp_factor]

/-- Smoke check: at `r = 1` the hard part is the full cyclotomic power and the
composition is exactly `·^(Q¹² − 1)`. -/
example (Q : ℤ) (f : G) :
    ((f ^ (Q ^ 6) * f⁻¹) * (f ^ (Q ^ 6) * f⁻¹) ^ (Q ^ 2)) ^ ((Q ^ 4 - Q ^ 2 + 1) / 1)
      = f ^ ((Q ^ 12 - 1) / 1) :=
  finalExp_correct (one_dvd _) f

end CatCrypt.Pairing.FinalExpGeneric
