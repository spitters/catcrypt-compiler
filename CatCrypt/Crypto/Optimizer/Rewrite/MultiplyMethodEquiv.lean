/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.KaratsubaGenericPass
public import CatCrypt.Crypto.Optimizer.Rewrite.Toom3GenericPass

/-!
# Tying the verified multiplication methods: method-selection is sound

The optimizer has three verified ways to compute the product of two
multi-limb integers split at a base element `B` of a commutative ring `R`:

* **schoolbook** — the naive expansion (four multiplications for two limbs,
  nine for three);
* **Karatsuba** (`KaratsubaGenericPass.lean`) — two limbs, three
  multiplications;
* **Toom-3** (`Toom3GenericPass.lean`) — three limbs, five multiplications.

Each method `M` comes with its own assembly: a tuple of coefficients and an
`evalLimbs` (resp. `evalLimbs5`) function that reads the tuple back as a ring
element `hi·B^k + … + lo`. Each is proved equal to its schoolbook
reference. This module **ties the hierarchy together**: it proves that, on the
same inputs, every method evaluates to the *same ring product*
```
(a1·B + a0)·(b1·B + b0)        -- two-limb / Karatsuba
(a2·B^2 + a1·B + a0)·(b2·B^2 + b1·B + b0)   -- three-limb / Toom-3
```
and hence that *any two methods agree* on the assembled value. That equality is
exactly the justification a compiler needs to perform **method selection**:
replacing a schoolbook multiply by Karatsuba (or Toom-3) on the same inputs is a
sound rewrite — `mulMethod_substitution_sound`.

The point is generic: the theorems are parametric over `[CommRing R]` (and, for
the division form of Toom-3, `[Field R]`), so they apply uniformly to the
tower-field multiplies (`Fp2`/`Fp6`), the multi-limb bignum multiplies, and any
e-graph / peephole rewrite that selects a multiplication algorithm.

## Method names

We expose the two arities as small `inductive` selectors and a dispatch
`evalMethod*` so the substitution theorem can be stated once, quantified over
the chosen method, rather than as a matrix of pairwise equalities.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodEquiv

open CatCrypt.Crypto.Optimizer.Rewrite.KaratsubaGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.Toom3Generic

/-! ## Two-limb arity: schoolbook ↔ Karatsuba

Both Karatsuba and the two-limb schoolbook evaluate to the product
`(a1·B + a0)·(b1·B + b0)`. The per-method facts `evalLimbs_karatsubaMul` and
`evalLimbs_schoolbookMul` are imported from `KaratsubaGenericPass.lean`; here we
phrase them as a *value*-level statement and a dispatch over a method selector.
-/

section TwoLimb

variable {R : Type*} [CommRing R]

/-- A selector for the two verified two-limb multiplication methods. -/
inductive Mul2Method
  | schoolbook
  | karatsuba
  deriving DecidableEq, Repr

/-- Dispatch: evaluate two-limb operands `(a1,a0)`, `(b1,b0)` at base `B` by the
chosen method, reading the result back as a ring element via `evalLimbs`. -/
def evalMethod2 : Mul2Method → R → R → R → R → R → R
  | .schoolbook, B, a1, a0, b1, b0 => evalLimbs B (schoolbookMul B a1 a0 b1 b0)
  | .karatsuba,  B, a1, a0, b1, b0 => evalLimbs B (karatsubaMul  B a1 a0 b1 b0)

/-- **Every two-limb method computes the ring product.** Whatever method
the optimizer picks, the assembled value is `(a1·B + a0)·(b1·B + b0)`. -/
theorem evalMethod2_eq_product (m : Mul2Method) (B a1 a0 b1 b0 : R) :
    evalMethod2 m B a1 a0 b1 b0 = (a1 * B + a0) * (b1 * B + b0) := by
  cases m with
  | schoolbook => simpa [evalMethod2] using evalLimbs_schoolbookMul B a1 a0 b1 b0
  | karatsuba  => simpa [evalMethod2] using evalLimbs_karatsubaMul  B a1 a0 b1 b0

/-- **The Karatsuba value equals the ring product.** (Re-exported from
`evalLimbs_karatsubaMul` under the method-selection naming so the tie reads
uniformly.) -/
theorem karatsuba_value_eq_product (B a1 a0 b1 b0 : R) :
    evalLimbs B (karatsubaMul B a1 a0 b1 b0) = (a1 * B + a0) * (b1 * B + b0) :=
  evalLimbs_karatsubaMul B a1 a0 b1 b0

/-- **The schoolbook value equals the ring product** (two-limb). -/
theorem schoolbook2_value_eq_product (B a1 a0 b1 b0 : R) :
    evalLimbs B (schoolbookMul B a1 a0 b1 b0) = (a1 * B + a0) * (b1 * B + b0) :=
  evalLimbs_schoolbookMul B a1 a0 b1 b0

/-- **Any two two-limb methods agree on the assembled value.** This is the core
soundness fact for method selection at the two-limb arity: the value does not
depend on which multiplication algorithm the compiler chose. -/
theorem evalMethod2_agree (m m' : Mul2Method) (B a1 a0 b1 b0 : R) :
    evalMethod2 m B a1 a0 b1 b0 = evalMethod2 m' B a1 a0 b1 b0 := by
  rw [evalMethod2_eq_product, evalMethod2_eq_product]

end TwoLimb

/-! ## Three-limb arity: schoolbook ↔ Toom-3

The three-limb schoolbook evaluates (via `evalLimbs5_schoolbookMul3`) to the
product. The Toom-3 field form `toom3Coeffs` evaluates to the same
product whenever `6` is invertible (`toom3_eq_schoolbook`); the
denominator-cleared form `toom3Coeffs6` evaluates to `6 ×` the product over a
bare ring (`toom3_eq_schoolbook6`).
-/

section ThreeLimbField

variable {R : Type*} [Field R]

/-- A selector for the two verified three-limb multiplication methods (the
field-form Toom-3, which needs `6 ≠ 0`). -/
inductive Mul3Method
  | schoolbook
  | toom3
  deriving DecidableEq, Repr

/-- Dispatch for three-limb operands `(a2,a1,a0)`, `(b2,b1,b0)` at base `B`. -/
def evalMethod3 : Mul3Method → R → R → R → R → R → R → R → R
  | .schoolbook, B, a2, a1, a0, b2, b1, b0 =>
      evalLimbs5 B (schoolbookMul3 B a2 a1 a0 b2 b1 b0)
  | .toom3, B, a2, a1, a0, b2, b1, b0 =>
      evalLimbs5 B (toom3Coeffs B a2 a1 a0 b2 b1 b0)

/-- **The Toom-3 (field-form) value equals the ring product**, given
`6 ≠ 0`. (Re-exported from `toom3_eq_schoolbook` under the method-selection
naming.) -/
theorem toom3_value_eq_product (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    evalLimbs5 B (toom3Coeffs B a2 a1 a0 b2 b1 b0)
      = (a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0) :=
  toom3_eq_schoolbook h6 B a2 a1 a0 b2 b1 b0

/-- **The schoolbook value equals the ring product** (three-limb). -/
theorem schoolbook3_value_eq_product (B a2 a1 a0 b2 b1 b0 : R) :
    evalLimbs5 B (schoolbookMul3 B a2 a1 a0 b2 b1 b0)
      = (a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0) :=
  evalLimbs5_schoolbookMul3 B a2 a1 a0 b2 b1 b0

/-- **Every three-limb method computes the ring product** (given
`6 ≠ 0`, required by the Toom-3 interpolation). -/
theorem evalMethod3_eq_product (h6 : (6 : R) ≠ 0)
    (m : Mul3Method) (B a2 a1 a0 b2 b1 b0 : R) :
    evalMethod3 m B a2 a1 a0 b2 b1 b0
      = (a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0) := by
  cases m with
  | schoolbook =>
      simpa [evalMethod3] using evalLimbs5_schoolbookMul3 B a2 a1 a0 b2 b1 b0
  | toom3 =>
      simpa [evalMethod3] using toom3_eq_schoolbook h6 B a2 a1 a0 b2 b1 b0

/-- **Any two three-limb methods agree on the assembled value** (given
`6 ≠ 0`). The three-limb arity analogue of `evalMethod2_agree`. -/
theorem evalMethod3_agree (h6 : (6 : R) ≠ 0)
    (m m' : Mul3Method) (B a2 a1 a0 b2 b1 b0 : R) :
    evalMethod3 m B a2 a1 a0 b2 b1 b0 = evalMethod3 m' B a2 a1 a0 b2 b1 b0 := by
  rw [evalMethod3_eq_product h6, evalMethod3_eq_product h6]

end ThreeLimbField

/-! ## Cleared-ring Toom-3: agreement up to the factor `6`

Over a bare commutative ring (no invertibility of `6`), the cleared Toom-3 form
agrees with `6 ×` the schoolbook product. This is the form a bignum rewrite uses
when `6` is coprime to the modulus, recovering the true product by multiplying
through by `6⁻¹`.
-/

section ThreeLimbCleared

variable {R : Type*} [CommRing R]

/-- **The cleared Toom-3 value equals `6 ×` the ring product**, over any
commutative ring (no invertibility needed). -/
theorem toom3_cleared_value_eq_six_product (B a2 a1 a0 b2 b1 b0 : R) :
    evalLimbs5 B (toom3Coeffs6 B a2 a1 a0 b2 b1 b0)
      = 6 * ((a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0)) :=
  toom3_eq_schoolbook6 B a2 a1 a0 b2 b1 b0

/-- **Cleared Toom-3 agrees with `6 ×` schoolbook** on the assembled value over
a bare ring. -/
theorem toom3_cleared_agree_schoolbook (B a2 a1 a0 b2 b1 b0 : R) :
    evalLimbs5 B (toom3Coeffs6 B a2 a1 a0 b2 b1 b0)
      = 6 * evalLimbs5 B (schoolbookMul3 B a2 a1 a0 b2 b1 b0) := by
  rw [toom3_eq_schoolbook6, evalLimbs5_schoolbookMul3]

end ThreeLimbCleared

/-! ## The optimizer-pass justification

The substitution soundness statement a method-selection rewrite appeals to:
replacing one verified method by another on the same inputs preserves the
computed value. We package both arities.
-/

section Substitution

variable {R : Type*}

/-- **Method-selection soundness, two-limb arity.** If the optimizer rewrites a
multiplication from method `src` to method `dst` (over `[CommRing R]`), the
assembled value is unchanged. This is what licenses choosing Karatsuba over
schoolbook (or vice versa). -/
theorem mulMethod_substitution_sound [CommRing R]
    (src dst : Mul2Method) (B a1 a0 b1 b0 : R) :
    evalMethod2 src B a1 a0 b1 b0 = evalMethod2 dst B a1 a0 b1 b0 :=
  evalMethod2_agree src dst B a1 a0 b1 b0

/-- **Method-selection soundness, three-limb arity** (given `6 ≠ 0`). Replacing
method `src` by `dst` — e.g. schoolbook by field-form Toom-3 — preserves the
assembled value. -/
theorem mulMethod3_substitution_sound [Field R] (h6 : (6 : R) ≠ 0)
    (src dst : Mul3Method) (B a2 a1 a0 b2 b1 b0 : R) :
    evalMethod3 src B a2 a1 a0 b2 b1 b0 = evalMethod3 dst B a2 a1 a0 b2 b1 b0 :=
  evalMethod3_agree h6 src dst B a2 a1 a0 b2 b1 b0

end Substitution

/-! ## Worked example over `ℤ` (two-limb) and `ℚ` (three-limb)

`12 * 34 = 408` with base `10` (`a1=1, a0=2, b1=3, b0=4`), and
`123 * 456 = 56088` with base `10` (`a2=1, a1=2, a0=3, b2=4, b1=5, b0=6`). -/

/-- Over `ℤ`, schoolbook and Karatsuba both yield `12 * 34 = 408`. -/
example :
    evalMethod2 (R := ℤ) .schoolbook 10 1 2 3 4 = 408 ∧
    evalMethod2 (R := ℤ) .karatsuba 10 1 2 3 4 = 408 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Over `ℤ`, schoolbook and Karatsuba agree on `12 * 34` — the concrete instance
of `mulMethod_substitution_sound`. -/
example :
    evalMethod2 (R := ℤ) .schoolbook 10 1 2 3 4
      = evalMethod2 (R := ℤ) .karatsuba 10 1 2 3 4 :=
  mulMethod_substitution_sound .schoolbook .karatsuba 10 1 2 3 4

/-- Over `ℚ`, schoolbook and Toom-3 both yield `123 * 456 = 56088`. -/
example :
    evalMethod3 (R := ℚ) .schoolbook 10 1 2 3 4 5 6 = 56088 ∧
    evalMethod3 (R := ℚ) .toom3 10 1 2 3 4 5 6 = 56088 := by
  refine ⟨?_, ?_⟩ <;> norm_num [evalMethod3, evalLimbs5, schoolbookMul3, toom3Coeffs]

/-- Over `ℚ`, schoolbook and Toom-3 agree on `123 * 456` — the concrete instance
of `mulMethod3_substitution_sound` (`6 ≠ 0` in `ℚ`). -/
example :
    evalMethod3 (R := ℚ) .schoolbook 10 1 2 3 4 5 6
      = evalMethod3 (R := ℚ) .toom3 10 1 2 3 4 5 6 :=
  mulMethod3_substitution_sound (by norm_num) .schoolbook .toom3 10 1 2 3 4 5 6

end CatCrypt.Crypto.Optimizer.Rewrite.MultiplyMethodEquiv
