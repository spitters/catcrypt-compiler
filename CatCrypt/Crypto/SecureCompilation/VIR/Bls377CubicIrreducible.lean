/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Bls377NonResidueTower
public import CatCrypt.Crypto.SecureCompilation.VIR.Bls377NonResidueTower

/-!
# BLS12-377 cubic irreducibility bridge

The `Fp6` non-residue leaf of `Bls377NonResidueTower` reduces to `u = ⟨0,1⟩` being
a non-cube in `Fp2_377` and, from there, to `x³ − u` having no root over `Fp2_377`,
hence being irreducible. This module supplies that irreducibility step by wiring the
Kummer-polynomial theory in mathlib (`X_pow_sub_C_irreducible_of_prime`) to the
hand-rolled tower field.

## What is proved

* `cube_nonRoot_irreducible` — over any field `K`, if `a : K` is not a cube then
  `X³ − C a` is irreducible. Instance of `X_pow_sub_C_irreducible_of_prime` at the
  prime `3`.

* `cube_nonRoot_irreducible_iff` — the two-way form
  `(¬ ∃ z, z³ = a) ↔ Irreducible (X³ − C a)` from
  `X_pow_sub_C_irreducible_iff_of_prime`.

* `fp2_xcubed_sub_u_irreducible` — the concrete instantiation at `K = Fp2_377`
  (a field via `Fp2_377.fieldOfNonsquare (-5) bls377_neg_five_nonsquare`): `u`
  non-cube in `Fp2_377` gives `X³ − C u` irreducible over `Fp2_377`.

* `fp2_xcubed_sub_u_irreducible_of_five_nonCube` — the same conclusion driven from
  the base cubic leaf `FpFiveNonCube` through `fp2_u_nonCube_of_fp_five_nonCube`.

## The remaining cubic-residue gap

The one hypothesis these lemmas still consume is `FpFiveNonCube` — that `5` has no
cube root modulo `bls377Q`. This is not closed here, for two independent reasons.

* A cube root of `5` exists iff `5^((q−1)/3) = 1` in `ZMod bls377Q`. Since
  `bls377Q ≡ 1 [MOD 3]` (so `3 ∣ q − 1`), the cubes form a proper index-`3`
  subgroup of `(ZMod bls377Q)ˣ` and the criterion is non-degenerate, but evaluating
  it is a modular exponentiation on the 377-bit prime — i.e. `native_decide`, which
  is excluded here.

* Mathlib provides `legendreSym`, quadratic reciprocity, and `ZMod.euler_criterion`
  for the quadratic (square) character, but no cubic residue character / cubic
  reciprocity (Eisenstein-integer) analogue that would give a symbolic
  `5^((q−1)/3) ≠ 1`. So the symbolic route available for the square leaf
  (`bls377_five_nonsquare`, via the Legendre symbol) has no cubic counterpart.

Everything downstream of `FpFiveNonCube` — the non-cube of `u`, the irreducibility
of `X³ − u`, and hence the field structure route for `Fp6_377` — is symbolic and
`native_decide`-free.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. The generic field-level irreducibility bridge -/

/-- Over any field, a non-cube `a` gives an irreducible cubic `X³ − C a`. This is
    `X_pow_sub_C_irreducible_of_prime` specialized to the prime `3`. -/
theorem cube_nonRoot_irreducible {K : Type*} [Field K] {a : K}
    (h : ¬ ∃ z : K, z ^ 3 = a) : Irreducible (X ^ 3 - C a) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three (fun b hb => h ⟨b, hb⟩)

/-- The two-way form: over a field, `X³ − C a` is irreducible iff `a` is not a cube.
    From `X_pow_sub_C_irreducible_iff_of_prime` at the prime `3`. -/
theorem cube_nonRoot_irreducible_iff {K : Type*} [Field K] {a : K} :
    (¬ ∃ z : K, z ^ 3 = a) ↔ Irreducible (X ^ 3 - C a) := by
  rw [X_pow_sub_C_irreducible_iff_of_prime Nat.prime_three]
  constructor
  · intro h b hb; exact h ⟨b, hb⟩
  · rintro h ⟨z, hz⟩; exact h z hz

/-! ## 2. The concrete cubic over `Fp2_377` -/

/-- At the concrete parameters `ξ₂ = -5`, with `Fp2_377` a field (via
    `fieldOfNonsquare` and `bls377_neg_five_nonsquare`): if `u = ⟨0,1⟩` is a non-cube
    in `Fp2_377`, then `X³ − C u` is irreducible over `Fp2_377`. This is the
    polynomial-side statement of the `Fp6` non-residue leaf. -/
theorem fp2_xcubed_sub_u_irreducible [Fact (Nat.Prime bls377Q)]
    (h : letI := Fp2_377.commRing (-5 : FpBLS377)
         ¬ ∃ z : Fp2_377, z ^ 3 = (⟨0, 1⟩ : Fp2_377)) :
    letI := Fp2_377.commRing (-5 : FpBLS377)
    letI : Field Fp2_377 := Fp2_377.fieldOfNonsquare (-5) bls377_neg_five_nonsquare
    Irreducible (X ^ 3 - C (⟨0, 1⟩ : Fp2_377)) := by
  letI := Fp2_377.commRing (-5 : FpBLS377)
  letI : Field Fp2_377 := Fp2_377.fieldOfNonsquare (-5) bls377_neg_five_nonsquare
  exact cube_nonRoot_irreducible h

/-- The same irreducibility driven from the base cubic leaf `FpFiveNonCube`
    (`5` a non-cube mod `bls377Q`) through `fp2_u_nonCube_of_fp_five_nonCube`. The
    hypothesis `FpFiveNonCube` is the remaining number-theoretic input; see the
    module docstring for why it is not closed symbolically. -/
theorem fp2_xcubed_sub_u_irreducible_of_five_nonCube [Fact (Nat.Prime bls377Q)]
    (h : FpFiveNonCube) :
    letI := Fp2_377.commRing (-5 : FpBLS377)
    letI : Field Fp2_377 := Fp2_377.fieldOfNonsquare (-5) bls377_neg_five_nonsquare
    Irreducible (X ^ 3 - C (⟨0, 1⟩ : Fp2_377)) :=
  fp2_xcubed_sub_u_irreducible (fp2_u_nonCube_of_fp_five_nonCube h)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
