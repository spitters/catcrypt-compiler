/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp6
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp2Inv

/-!
# The `bls12_377` cubic-extension `Fp6` inversion — `Fp6_377` is operationally a field

`RelationalFrontBls377Fp6` builds the `bls12_377` cubic tower
`Fp6_377 = Fp2_377[v]/(v³ − ξ₆)` (`c0 + c1·v + c2·v²`) with its schoolbook /
Karatsuba multiplies and a `CommRing` structure over the relational `Fp2_377`
base. `RelationalFrontBls377Fp2Inv` makes that base `Fp2_377` **operationally a
field**: it exposes `Fp2_377.inv ξ₂` with the cancellation law `x · x⁻¹ = 1`
(under `[Fact (Nat.Prime bls377Q)]` and a nonzero norm). The *next* tower rung
toward the `bls12_377` pairing's final exponentiation is **`Fp6` inversion**:
with the base `Fp2_377` a field, the cubic extension is inverted by the standard
cubic-extension cofactor (adjugate-over-determinant) formula. This module builds
that inverse and proves `x · x⁻¹ = 1` (whenever the `Fp6` norm is nonzero).

## What this module proves

For `x = c0 + c1·v + c2·v²` with `v³ = ξ₆` (`ξ₆ : Fp2_377`), the cubic-extension
**cofactor** coordinates (all in `Fp2_377`) are

```
   t0 = c0² − ξ₆·c1·c2,   t1 = ξ₆·c2² − c0·c1,   t2 = c1² − c0·c2
```

and the **norm** (the determinant-like quantity, a base-`Fp2_377` element) is

```
   N = c0·t0 + ξ₆·c2·t1 + ξ₆·c1·t2 ∈ Fp2_377.
```

The crux is the **cofactor identity** (`mul_cofactor_eq`):

```
   x · (t0 + t1·v + t2·v²) = ⟨N, 0, 0⟩       (the scalar N in the v⁰ slot)
```

i.e. multiplying `x` by its cofactor lands in the base field `Fp2_377` (the `v¹`
and `v²` slots vanish). Then the inverse scales the cofactor by the base-field
inverse of the norm:

```
   inv6 ξ₂ ξ₆ x := cofactor x  *  ⟨Fp2.inv ξ₂ N, 0, 0⟩
   x · inv6 ξ₂ ξ₆ x = 1        (when N ≠ 0)
```

The cancellation (`mul_inv6`) associates `x · (cofactor · ⟨N⁻¹,0,0⟩)` as
`(x · cofactor) · ⟨N⁻¹,0,0⟩ = ⟨N,0,0⟩ · ⟨N⁻¹,0,0⟩ = ⟨N·N⁻¹,0,0⟩ = ⟨1,0,0⟩ = 1`,
the last `Fp2`-step by `Fp2_377.mul_inv` in the base field. This makes
`Fp6_377` **operationally a field** over the relational `bls12_377` carrier — the
cubic-extension field operation the pairing's `Fp12` inversion and final
exponentiation are built on.

## Honesty boundary

This is the abstract `Fp6` inversion over the relational `bls12_377` base
carrier. As with the `Fp2` layer, the cancellation law is conditioned on the
`Fp6` norm being nonzero; equivalence of that condition with `x ≠ 0` needs the
`ξ₆`-non-residue (number-theoretic) fact about the concrete `bls12_377` tower
parameters, which we do **not** prove. We keep both nonresidues `ξ₂, ξ₆`
parametric (generic over the tower, not hand-inlined), and keep every base
`Fp2_377` multiply opaque (`mul₂ … = (· * ·)` rewriting into the `Fp2_377`
`CommRing`, so `ring` normalizes the cubic expansion). We do not wire inversion
to emitted base kernels.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

namespace Fp6_377

/-! ## 1. The base-`Fp2_377` embedding and the cofactor / norm

`ofBase6 n = ⟨n, 0, 0⟩` injects a base-`Fp2_377` element into the `v⁰` slot of
`Fp6_377`. The cofactor and norm are the standard cubic-extension
adjugate / determinant data, all computed with the opaque base `mul₂`. -/

/-- The **base-`Fp2_377` embedding** `Fp2_377 → Fp6_377`, `n ↦ n + 0·v + 0·v²`.
    The `Fp6` norm (a base-`Fp2_377` element) is injected into the extension this
    way. -/
def ofBase6 (n : Fp2_377) : Fp6_377 := ⟨n, 0, 0⟩

@[simp] theorem ofBase6_c0 (n : Fp2_377) : (ofBase6 n).c0 = n := rfl
@[simp] theorem ofBase6_c1 (n : Fp2_377) : (ofBase6 n).c1 = 0 := rfl
@[simp] theorem ofBase6_c2 (n : Fp2_377) : (ofBase6 n).c2 = 0 := rfl

/-- The **cofactor `t0` coordinate**, `t0 = c0² − ξ₆·c1·c2` (in `Fp2_377`). -/
def cof0 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) : Fp2_377 :=
  mul₂ ξ₂ x.c0 x.c0 - mul₂ ξ₂ ξ₆ (mul₂ ξ₂ x.c1 x.c2)

/-- The **cofactor `t1` coordinate**, `t1 = ξ₆·c2² − c0·c1` (in `Fp2_377`). -/
def cof1 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) : Fp2_377 :=
  mul₂ ξ₂ ξ₆ (mul₂ ξ₂ x.c2 x.c2) - mul₂ ξ₂ x.c0 x.c1

/-- The **cofactor `t2` coordinate**, `t2 = c1² − c0·c2` (in `Fp2_377`). The cubic
    nonresidue `ξ₆` does not enter this coordinate; the parameter is kept for a
    uniform `cof0`/`cof1`/`cof2 ξ₂ ξ₆ x` calling convention in `cofactor`. -/
def cof2 (ξ₂ : FpBLS377) (_ξ₆ : Fp2_377) (x : Fp6_377) : Fp2_377 :=
  mul₂ ξ₂ x.c1 x.c1 - mul₂ ξ₂ x.c0 x.c2

/-- The **`Fp6_377` cofactor** `t0 + t1·v + t2·v²` (the adjugate of `x`). Its
    product with `x` lands in the base field as the scalar `normFp6 x`
    (`mul_cofactor_eq`). -/
def cofactor (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) : Fp6_377 :=
  ⟨cof0 ξ₂ ξ₆ x, cof1 ξ₂ ξ₆ x, cof2 ξ₂ ξ₆ x⟩

/-- The **`Fp6_377` norm** `N = c0·t0 + ξ₆·c2·t1 + ξ₆·c1·t2 ∈ Fp2_377` (the
    determinant-like quantity); `x · cofactor x = ⟨N, 0, 0⟩` (`mul_cofactor_eq`).
    -/
def normFp6 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) : Fp2_377 :=
  mul₂ ξ₂ x.c0 (cof0 ξ₂ ξ₆ x)
    + mul₂ ξ₂ ξ₆ (mul₂ ξ₂ x.c2 (cof1 ξ₂ ξ₆ x))
    + mul₂ ξ₂ ξ₆ (mul₂ ξ₂ x.c1 (cof2 ξ₂ ξ₆ x))

/-! ## 2. The cofactor identity `x · cofactor x = ⟨N, 0, 0⟩`

The load-bearing determinant identity: multiplying `x` by its adjugate lands in
the base `Fp2_377` as the scalar norm `N` (the `v¹` and `v²` slots vanish). The
base `Fp2_377` multiply is kept opaque (`hm`) so `ring` normalizes over the
`Fp2_377` `CommRing`. -/

/-- **The cubic-extension cofactor identity** — `x · cofactor x = ⟨N, 0, 0⟩`.
    Multiplying `x = c0 + c1·v + c2·v²` by its adjugate `t0 + t1·v + t2·v²` (with
    `v³ = ξ₆`) lands in the base field `Fp2_377`: the `v⁰` coordinate is the norm
    `N = c0·t0 + ξ₆·c2·t1 + ξ₆·c1·t2`, and both higher coordinates cancel. Closed
    by `ext` then `ring` over the `Fp2_377` `CommRing` with the base multiply
    opaque. This is the determinant identity behind `Fp6` inversion. -/
theorem mul_cofactor_eq (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) :
    mulSchoolbook ξ₂ ξ₆ x (cofactor ξ₂ ξ₆ x) = ofBase6 (normFp6 ξ₂ ξ₆ x) := by
  letI := Fp2_377.commRing ξ₂
  have hm : ∀ a b : Fp2_377, mul₂ ξ₂ a b = a * b := fun _ _ => rfl
  refine Fp6_377.ext ?_ ?_ ?_ <;>
    · simp only [mulSchoolbook, cofactor, cof0, cof1, cof2, normFp6, ofBase6, hm]
      ring

/-! ## 3. The cofactor-over-norm inverse and the cancellation law

`inv6` scales the cofactor by the base-`Fp2_377` inverse of the norm, injected
into the `v⁰` slot. We work under `[Fact (Nat.Prime bls377Q)]` so the base
`Fp2_377` is a field via `Fp2_377.inv` and `Fp2_377.mul_inv`. -/

/-- The **`Fp6_377` inverse** `inv6 ξ₂ ξ₆ x = cofactor x · ⟨Fp2.inv ξ₂ N, 0, 0⟩` —
    the adjugate scaled by the base-`Fp2_377` inverse of the norm
    (`x⁻¹ = adj x / norm x`). Requires `[Fact (Nat.Prime bls377Q)]` so the base
    `Fp2_377` is a field; the cancellation law (`mul_inv6`) additionally needs
    the `Fp2_377`-norm `Fp2_377.norm ξ₂ (normFp6 …) ≠ 0`. -/
noncomputable def inv6 [Fact (Nat.Prime bls377Q)] (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (x : Fp6_377) : Fp6_377 :=
  letI := Fp2_377.commRing ξ₂
  letI := commRing ξ₂ ξ₆
  cofactor ξ₂ ξ₆ x * ofBase6 (Fp2_377.inv ξ₂ (normFp6 ξ₂ ξ₆ x))

/-- The **product of two base-`Fp2_377` embeddings** stays in the base field and
    is the base product on the `v⁰` slot (`⟨a,0,0⟩ · ⟨b,0,0⟩ = ⟨a·b,0,0⟩`): the
    `ξ₆`-folded cross terms all vanish because the `v¹`/`v²` slots are `0`. -/
theorem ofBase6_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (a b : Fp2_377) :
    letI := Fp2_377.commRing ξ₂
    letI := commRing ξ₂ ξ₆
    ofBase6 a * ofBase6 b = ofBase6 (a * b) := by
  letI := Fp2_377.commRing ξ₂
  letI := commRing ξ₂ ξ₆
  show mulSchoolbook ξ₂ ξ₆ (ofBase6 a) (ofBase6 b) = ofBase6 (a * b)
  have hm : ∀ a b : Fp2_377, mul₂ ξ₂ a b = a * b := fun _ _ => rfl
  refine Fp6_377.ext ?_ ?_ ?_ <;>
    · simp only [mulSchoolbook, ofBase6, hm]
      ring

/-- **`Fp6_377` field cancellation** (`x · inv6 ξ₂ ξ₆ x = 1`) whenever the
    `Fp2_377`-norm of the `Fp6` norm is nonzero. Associating
    `x · (cofactor · ⟨N⁻¹,0,0⟩)` as `(x · cofactor) · ⟨N⁻¹,0,0⟩`, the inner factor
    is the base-`Fp2_377`-valued `⟨N, 0, 0⟩` (`mul_cofactor_eq`), so the whole
    product is the base product `⟨N · N⁻¹, 0, 0⟩ = ⟨1, 0, 0⟩ = 1` by
    `Fp2_377.mul_inv` in the base field. This is the operation that makes
    `Fp6_377` operationally a field. -/
theorem mul_inv6 [Fact (Nat.Prime bls377Q)] (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (x : Fp6_377) (hN : Fp2_377.norm ξ₂ (normFp6 ξ₂ ξ₆ x) ≠ 0) :
    letI := commRing ξ₂ ξ₆
    x * inv6 ξ₂ ξ₆ x = 1 := by
  letI := Fp2_377.commRing ξ₂
  letI := commRing ξ₂ ξ₆
  -- Associate: x * (cofactor * ⟨N⁻¹,0,0⟩) = (x * cofactor) * ⟨N⁻¹,0,0⟩.
  have hassoc : x * inv6 ξ₂ ξ₆ x
      = (x * cofactor ξ₂ ξ₆ x) * ofBase6 (Fp2_377.inv ξ₂ (normFp6 ξ₂ ξ₆ x)) := by
    show x * (cofactor ξ₂ ξ₆ x * ofBase6 (Fp2_377.inv ξ₂ (normFp6 ξ₂ ξ₆ x)))
      = (x * cofactor ξ₂ ξ₆ x) * ofBase6 (Fp2_377.inv ξ₂ (normFp6 ξ₂ ξ₆ x))
    rw [mul_assoc]
  rw [hassoc]
  -- x * cofactor x = ⟨N, 0, 0⟩.
  have hcof : x * cofactor ξ₂ ξ₆ x = ofBase6 (normFp6 ξ₂ ξ₆ x) := by
    show mulSchoolbook ξ₂ ξ₆ x (cofactor ξ₂ ξ₆ x) = ofBase6 (normFp6 ξ₂ ξ₆ x)
    exact mul_cofactor_eq ξ₂ ξ₆ x
  rw [hcof, ofBase6_mul ξ₂ ξ₆ (normFp6 ξ₂ ξ₆ x) (Fp2_377.inv ξ₂ (normFp6 ξ₂ ξ₆ x))]
  -- ⟨N · Fp2.inv N, 0, 0⟩ = ⟨1, 0, 0⟩ = 1 by the base-field cancellation.
  rw [Fp2_377.mul_inv ξ₂ (normFp6 ξ₂ ξ₆ x) hN]
  rfl

/-- **`Fp6_377` field cancellation, other side** (`inv6 ξ₂ ξ₆ x · x = 1`) —
    immediate from `mul_inv6` and commutativity of the `commRing ξ₂ ξ₆` multiply.
    -/
theorem inv6_mul [Fact (Nat.Prime bls377Q)] (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (x : Fp6_377) (hN : Fp2_377.norm ξ₂ (normFp6 ξ₂ ξ₆ x) ≠ 0) :
    letI := commRing ξ₂ ξ₆
    inv6 ξ₂ ξ₆ x * x = 1 := by
  letI := commRing ξ₂ ξ₆
  rw [mul_comm]
  exact mul_inv6 ξ₂ ξ₆ x hN

end Fp6_377

end CatCrypt.Crypto.SecureCompilation.RelationalFront
