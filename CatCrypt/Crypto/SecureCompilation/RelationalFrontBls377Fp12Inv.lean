/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp12Conj
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp6Inv

/-!
# The `bls12_377` dodecic-extension `Fp12` inversion — the top of the pairing tower is a field

`RelationalFrontBls377Fp6` builds the `bls12_377` dodecic extension
`Fp12_377 = Fp6_377[w]/(w² − v)` (`c0 + c1·w`, two `Fp6_377` coordinates,
schoolbook / Karatsuba multiply with the `w² = v` fold via `Fp6_377.mulByV`)
and its `CommRing`. `RelationalFrontBls377Fp12Conj` exposes the cyclotomic
conjugation `conj12 (c0 + c1·w) = c0 − c1·w` and the `Fp12 → Fp6` field norm
`norm12 x = (x · conj12 x).c0`, with `mul_conj12_eq : x · conj12 x = ⟨norm12 x, 0⟩`
(the product of an element with its conjugate lands in the `Fp6_377` subfield).
`RelationalFrontBls377Fp6Inv` makes the *intermediate* tower rung `Fp6_377`
operationally a field: `inv6` with `Fp6_377.mul_inv6 : x · inv6 x = 1` (whenever
the `Fp6` norm's `Fp2`-norm is nonzero).

This module closes the tower: with `Fp6_377` a field, the quadratic dodecic
extension `Fp12_377 = Fp6_377[w]/(w² − v)` is inverted by the standard
conjugate-over-norm formula `x⁻¹ = x̄ / N(x)`, exactly mirroring the `Fp2` and
`Fp6` rungs one level up. It builds that inverse and proves `x · x⁻¹ = 1`
(whenever the norm is invertible in `Fp6_377`).

## What this module proves

For `x = c0 + c1·w` with `w² = v`, the conjugate is `x̄ = c0 − c1·w` and the
norm `N = norm12 x = (x · x̄).c0 = c0² − v·c1² ∈ Fp6_377`. The **`Fp6_377`
embedding** `ofFp6 n = n + 0·w` injects the norm's `Fp6_377` inverse back into
`Fp12_377`. The inverse scales the conjugate by that embedded inverse:

```
   inv12 ξ₂ ξ₆ x := conj12 x  *  ofFp6 (inv6 (norm12 x))
   x · inv12 ξ₂ ξ₆ x = 1        (when N(x) is invertible in Fp6_377)
```

The crux is the **embedding-product identity** (`ofFp6_mul`):

```
   ofFp6 a · ofFp6 b = ofFp6 (a · b)
```

(the `w`-slot is `0` on both factors, so the `mulByV (a₁·b₁)` fold vanishes).
The cancellation (`mul_inv12`) associates `x · (x̄ · ofFp6 N⁻¹)` as
`(x · x̄) · ofFp6 N⁻¹`, rewrites `x · x̄ = ⟨N, 0, …⟩ = ofFp6 N` via
`mul_conj12_eq`, then `ofFp6 N · ofFp6 N⁻¹ = ofFp6 (N · N⁻¹) = ofFp6 1 = 1` by
`Fp6_377.mul_inv6` in the subfield. This makes `Fp12_377` **operationally a
field** over the relational `bls12_377` carrier — the dodecic field operation
the pairing's final exponentiation is built on, completing the `Fp2 → Fp6 →
Fp12` tower as a chain of operational fields.

## Honesty boundary

This is the abstract `Fp12` inversion over the relational `bls12_377` carrier.
As at the `Fp2` / `Fp6` rungs, the cancellation law is conditioned on the norm
being invertible (here: the `Fp2`-norm of the `Fp6`-norm of `norm12 x` is
nonzero, the `inv6` precondition); equivalence of that condition with `x ≠ 0`
needs the tower nonresidue facts (`ξ₂`, `ξ₆`, `v` non-residuosity) about the
concrete `bls12_377` parameters, which we do **not** prove. Both base
nonresidues `ξ₂, ξ₆` stay parametric, and every `Fp6_377` multiply is kept
opaque (`mul₆ … = (· * ·)` into the `Fp6_377` `CommRing`). We do not wire
inversion to emitted base kernels.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

namespace Fp12_377

/-! ## 1. The `Fp6_377` embedding `Fp6_377 → Fp12_377`

`ofFp6 n = n + 0·w` injects an `Fp6_377` element into the `w⁰` slot of
`Fp12_377`. The `Fp12 → Fp6` norm's `Fp6_377` inverse is injected back into the
extension this way. -/

/-- The **`Fp6_377` embedding** `Fp6_377 → Fp12_377`, `n ↦ n + 0·w`. The
    `Fp6_377` inverse of the `Fp12` norm is injected into the dodecic extension
    this way. -/
def ofFp6 (n : Fp6_377) : Fp12_377 := ⟨n, 0⟩

@[simp] theorem ofFp6_c0 (n : Fp6_377) : (ofFp6 n).c0 = n := rfl
@[simp] theorem ofFp6_c1 (n : Fp6_377) : (ofFp6 n).c1 = 0 := rfl

/-- **`ofFp6` sends the `Fp6_377` one to the `Fp12_377` one** (`ofFp6 1 = 1`). -/
@[simp] theorem ofFp6_one : ofFp6 (1 : Fp6_377) = 1 := rfl

/-! ## 2. The embedding-product identity `ofFp6 a · ofFp6 b = ofFp6 (a · b)`

Both factors have a zero `w`-component, so the `w² = v` fold `mulByV (a₁·b₁)`
vanishes and the schoolbook dodecic product collapses to the base `Fp6_377`
product on the `w⁰` slot. The base `Fp6_377` multiply is kept opaque (`hm`); the
`mulByV` of the `0·0` cross term is killed by `mulByV_zero`. -/

/-- The **product of two `Fp6_377` embeddings** stays in the subfield and is the
    base product on the `w⁰` slot (`ofFp6 a · ofFp6 b = ofFp6 (a · b)`): the
    `w`-slots are `0`, so the `mulByV (a₁·b₁)` nonresidue fold vanishes. -/
theorem ofFp6_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (a b : Fp6_377) :
    letI := Fp6_377.commRing ξ₂ ξ₆
    letI := commRing ξ₂ ξ₆
    ofFp6 a * ofFp6 b = ofFp6 (a * b) := by
  letI := Fp6_377.commRing ξ₂ ξ₆
  letI := commRing ξ₂ ξ₆
  show mulSchoolbook ξ₂ ξ₆ (ofFp6 a) (ofFp6 b) = ofFp6 (a * b)
  have hm : ∀ a b : Fp6_377, mul₆ ξ₂ ξ₆ a b = a * b := fun _ _ => rfl
  refine Fp12_377.ext ?_ ?_
  · show mul₆ ξ₂ ξ₆ a b + Fp6_377.mulByV ξ₂ ξ₆ (mul₆ ξ₂ ξ₆ 0 0) = a * b
    simp only [hm, mul_zero, Fp6_377.mulByV_zero, add_zero]
  · show mul₆ ξ₂ ξ₆ a 0 + mul₆ ξ₂ ξ₆ 0 b = 0
    simp only [hm, mul_zero, zero_mul, add_zero]

/-! ## 3. The conjugate-over-norm inverse and the cancellation law

`inv12` scales the cyclotomic conjugate `conj12 x` by the `Fp6_377` inverse of
the norm `norm12 x`, embedded into the `w⁰` slot. We work under
`[Fact (Nat.Prime bls377Q)]` so the `Fp6_377` subfield inverse `inv6` and its
cancellation `Fp6_377.mul_inv6` are available. -/

/-- The **`Fp12_377` inverse** `inv12 ξ₂ ξ₆ x = conj12 x · ofFp6 (inv6 (norm12 x))` —
    the cyclotomic conjugate scaled by the `Fp6_377` inverse of the `Fp12 → Fp6`
    norm (`x⁻¹ = x̄ / N(x)`). Requires `[Fact (Nat.Prime bls377Q)]` so the
    `Fp6_377` subfield is invertible; the cancellation law (`mul_inv12`)
    additionally needs the `inv6` precondition on the norm. -/
noncomputable def inv12 [Fact (Nat.Prime bls377Q)] (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (x : Fp12_377) : Fp12_377 :=
  letI := Fp6_377.commRing ξ₂ ξ₆
  letI := commRing ξ₂ ξ₆
  conj12 x * ofFp6 (Fp6_377.inv6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x))

/-- **`Fp12_377` field cancellation** (`x · inv12 ξ₂ ξ₆ x = 1`) whenever the
    `Fp12 → Fp6` norm `norm12 x` is invertible in `Fp6_377` (the `inv6`
    precondition: the `Fp2`-norm of the `Fp6`-norm of `norm12 x` is nonzero).
    Associating `x · (conj12 x · ofFp6 N⁻¹)` as `(x · conj12 x) · ofFp6 N⁻¹`, the
    inner factor is the subfield-valued `⟨N, 0⟩ = ofFp6 N` (`mul_conj12_eq`), so
    the whole product is the embedded base product `ofFp6 (N · N⁻¹) = ofFp6 1 = 1`
    by `Fp6_377.mul_inv6` in the `Fp6_377` subfield. This is the operation that
    makes `Fp12_377` operationally a field, completing the `Fp2 → Fp6 → Fp12`
    pairing tower as a chain of operational fields. -/
theorem mul_inv12 [Fact (Nat.Prime bls377Q)] (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (x : Fp12_377)
    (hN : Fp2_377.norm ξ₂ (Fp6_377.normFp6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x)) ≠ 0) :
    letI := commRing ξ₂ ξ₆
    x * inv12 ξ₂ ξ₆ x = 1 := by
  letI := Fp6_377.commRing ξ₂ ξ₆
  letI := commRing ξ₂ ξ₆
  -- Associate: x * (conj12 x * ofFp6 N⁻¹) = (x * conj12 x) * ofFp6 N⁻¹.
  have hassoc : x * inv12 ξ₂ ξ₆ x
      = (x * conj12 x) * ofFp6 (Fp6_377.inv6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x)) := by
    show x * (conj12 x * ofFp6 (Fp6_377.inv6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x)))
      = (x * conj12 x) * ofFp6 (Fp6_377.inv6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x))
    rw [mul_assoc]
  rw [hassoc]
  -- x * conj12 x = ⟨norm12 x, 0⟩ = ofFp6 (norm12 x).
  rw [mul_conj12_eq ξ₂ ξ₆ x]
  show ofFp6 (norm12 ξ₂ ξ₆ x) * ofFp6 (Fp6_377.inv6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x)) = 1
  -- ofFp6 N · ofFp6 N⁻¹ = ofFp6 (N · N⁻¹) = ofFp6 1 = 1 in the Fp6_377 subfield.
  rw [ofFp6_mul ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x) (Fp6_377.inv6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x))]
  rw [Fp6_377.mul_inv6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x) hN]
  exact ofFp6_one

/-- **`Fp12_377` field cancellation, other side** (`inv12 ξ₂ ξ₆ x · x = 1`) —
    immediate from `mul_inv12` and commutativity of the `commRing ξ₂ ξ₆` multiply.
    -/
theorem inv12_mul [Fact (Nat.Prime bls377Q)] (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (x : Fp12_377)
    (hN : Fp2_377.norm ξ₂ (Fp6_377.normFp6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x)) ≠ 0) :
    letI := commRing ξ₂ ξ₆
    inv12 ξ₂ ξ₆ x * x = 1 := by
  letI := commRing ξ₂ ξ₆
  rw [mul_comm]
  exact mul_inv12 ξ₂ ξ₆ x hN

end Fp12_377

end CatCrypt.Crypto.SecureCompilation.RelationalFront
