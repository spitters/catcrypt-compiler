/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Generic single-level Karatsuba multiplication identity

This file isolates the **abstract algebraic core** behind two-way Karatsuba
multiplication: with only **three** multiplications instead of the schoolbook
four, one can compute the product of two "two-limb" values
`a1 * B + a0` and `b1 * B + b0` over an arbitrary commutative ring `R`, with a
base element `B : R`.

The schoolbook product expands as
```
(a1 * B + a0) * (b1 * B + b0)
  = a1 * b1 * B^2 + (a1 * b0 + a0 * b1) * B + a0 * b0.
```
The Karatsuba trick computes the three products
```
z2 = a1 * b1            -- high
z0 = a0 * b0            -- low
zm = (a1 + a0) * (b1 + b0)   -- middle, the third (and only extra) product
```
and recovers the cross term as `z1 = zm - z2 - z0 = a1 * b0 + a0 * b1`, so that
```
z2 * B^2 + z1 * B + z0 = (a1 * B + a0) * (b1 * B + b0).
```

This is the generic identity that the concrete Karatsuba multiplies all
instantiate: the `Fp2` / `Fp6` tower-field `mulKaratsuba` (with `B` the
non-residue), the multi-limb bignum Karatsuba (with `B` a power of the radix),
and any e-graph / peephole rewrite that replaces a four-multiply schoolbook
expansion with the three-multiply form. Being parametric over `[CommRing R]`
and the base `B`, it is proved once here by `ring`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.KaratsubaGeneric

variable {R : Type*} [CommRing R]

set_option linter.unusedVariables false in
/-- Schoolbook product of two two-limb values `(a1, a0)` and `(b1, b0)`
representing `a1 * B + a0` and `b1 * B + b0`, returned as the three-coefficient
result `(a1*b1, a1*b0 + a0*b1, a0*b0)` so that the value is
`hi * B^2 + mid * B + lo`. Uses the full **four** multiplications. The base `B`
is carried for signature uniformity with `karatsubaMul`/`evalLimbs`. -/
def schoolbookMul (B a1 a0 b1 b0 : R) : R × R × R :=
  (a1 * b1, a1 * b0 + a0 * b1, a0 * b0)

set_option linter.unusedVariables false in
/-- Karatsuba product of two two-limb values, using only **three**
multiplications (`a1*b1`, `a0*b0`, and the middle `(a1+a0)*(b1+b0)`). The
cross/middle coefficient is recovered by subtraction:
`z1 = (a1+a0)*(b1+b0) - a1*b1 - a0*b0`. The base `B` is carried for signature
uniformity with `schoolbookMul`/`evalLimbs`. -/
def karatsubaMul (B a1 a0 b1 b0 : R) : R × R × R :=
  let z2 := a1 * b1
  let z0 := a0 * b0
  let zm := (a1 + a0) * (b1 + b0)
  (z2, zm - z2 - z0, z0)

/-- The value `hi * B^2 + mid * B + lo` carried by a three-coefficient result. -/
def evalLimbs (B : R) (p : R × R × R) : R :=
  p.1 * B ^ 2 + p.2.1 * B + p.2.2

/-- **Karatsuba = schoolbook (coefficientwise).** The three Karatsuba
coefficients agree with the schoolbook ones; in particular the recovered middle
coefficient `(a1+a0)*(b1+b0) - a1*b1 - a0*b0` equals `a1*b0 + a0*b1`. -/
theorem karatsubaMul_eq_schoolbook (B a1 a0 b1 b0 : R) :
    karatsubaMul B a1 a0 b1 b0 = schoolbookMul B a1 a0 b1 b0 := by
  simp only [karatsubaMul, schoolbookMul, Prod.mk.injEq, true_and, and_true]
  ring

/-- **The core Karatsuba identity.** Reassembling the three Karatsuba
coefficients at base `B` yields exactly the product `(a1*B+a0)*(b1*B+b0)` — the
single-level Karatsuba (three multiplications) equals the schoolbook product. -/
theorem karatsuba_eq_schoolbook (B a1 a0 b1 b0 : R) :
    let z2 := a1 * b1
    let z0 := a0 * b0
    let z1 := (a1 + a0) * (b1 + b0) - z2 - z0
    z2 * B ^ 2 + z1 * B + z0 = (a1 * B + a0) * (b1 * B + b0) := by
  ring

/-- Evaluated form: the Karatsuba assembly equals the schoolbook assembly, both
equal to the genuine ring product `(a1*B+a0)*(b1*B+b0)`. -/
theorem evalLimbs_karatsubaMul (B a1 a0 b1 b0 : R) :
    evalLimbs B (karatsubaMul B a1 a0 b1 b0) = (a1 * B + a0) * (b1 * B + b0) := by
  simp only [evalLimbs, karatsubaMul]
  ring

/-- The schoolbook assembly also equals the genuine ring product. -/
theorem evalLimbs_schoolbookMul (B a1 a0 b1 b0 : R) :
    evalLimbs B (schoolbookMul B a1 a0 b1 b0) = (a1 * B + a0) * (b1 * B + b0) := by
  simp only [evalLimbs, schoolbookMul]
  ring

/-- The two assemblies agree as evaluated ring elements (corollary of
`karatsubaMul_eq_schoolbook`). -/
theorem evalLimbs_karatsuba_eq_schoolbook (B a1 a0 b1 b0 : R) :
    evalLimbs B (karatsubaMul B a1 a0 b1 b0)
      = evalLimbs B (schoolbookMul B a1 a0 b1 b0) := by
  rw [karatsubaMul_eq_schoolbook]

/-! ## Worked example over `ℤ` with base `B = 10`

`a = a1*10 + a0`, `b = b1*10 + b0`; e.g. `a = 12`, `b = 34`. -/

/-- `12 * 34 = 408` recovered through the generic Karatsuba assembly over `ℤ`
with base `10` (`a1 = 1, a0 = 2, b1 = 3, b0 = 4`). -/
example : evalLimbs (R := ℤ) 10 (karatsubaMul 10 1 2 3 4) = 408 := by
  decide

/-- The three Karatsuba multiplications for `12 * 34`:
`z2 = 1*3 = 3`, `z0 = 2*4 = 8`, middle `(1+2)*(3+4) = 21`, so
`z1 = 21 - 3 - 8 = 10` — matching the schoolbook cross term `1*4 + 2*3 = 10`. -/
example : karatsubaMul (R := ℤ) 10 1 2 3 4 = (3, 10, 8) := by
  decide

/-- The Karatsuba and schoolbook coefficient triples coincide on the example. -/
example :
    karatsubaMul (R := ℤ) 10 1 2 3 4 = schoolbookMul (R := ℤ) 10 1 2 3 4 := by
  decide

end CatCrypt.Crypto.Optimizer.Rewrite.KaratsubaGeneric
