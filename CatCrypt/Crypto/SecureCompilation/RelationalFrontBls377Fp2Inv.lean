/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp2Conj
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# The `bls12_377` `Fp2` inversion — `Fp2_377` is operationally a field

`RelationalFrontBls377Fp2Conj` builds the `bls12_377` `Fp2` Galois conjugation
`conj (a + b·u) = a − b·u`, proves it is a base-field-fixing ring endomorphism,
and forms the field norm `norm ξ x = (x · conj x).c0 = a² − ξ·b²` together with
`mul_conj_eq : x · conj x = ⟨norm ξ x, 0⟩` (the product of an element with its
conjugate lands in the base field). The *next* gateway toward `bls12_377`
pairings is **inversion**: with the norm in hand, `x⁻¹ = conj x / norm x`, the
operation that makes `Fp2_377` a genuine field. This module builds that inverse
and proves the cancellation law `x · x⁻¹ = 1` (whenever `norm ξ x ≠ 0`).

## What this module proves

The headline is the **field cancellation** law:

```
   inv ξ x := conj x * ⟨(norm ξ x)⁻¹, 0⟩
   x * inv ξ x = 1        (when norm ξ x ≠ 0)
   inv ξ x * x = 1        (by commutativity)
```

The construction is the classical "conjugate over norm": multiplying `x` by
`conj x` lands in the base field (`x · conj x = ⟨norm ξ x, 0⟩`, by `mul_conj_eq`),
and a base-field element `⟨n, 0⟩` is inverted by `⟨n⁻¹, 0⟩` (the `Fp2_377`
embedding of the base field commutes with multiplication on `c0`, and the cross
terms vanish because both `c1`-components are `0`). So

```
   x * (conj x * ⟨(norm x)⁻¹, 0⟩) = (x · conj x) * ⟨(norm x)⁻¹, 0⟩
                                  = ⟨norm x, 0⟩ * ⟨(norm x)⁻¹, 0⟩
                                  = ⟨norm x · (norm x)⁻¹, 0⟩ = ⟨1, 0⟩ = 1
```

the last step by `mul_inv_cancel₀` in the base field `FpBLS377`. We work under
`[Fact (Nat.Prime bls377Q)]` so `FpBLS377 = ZMod bls377Q` is a `Field` and the
norm is invertible in the base field. This makes `Fp2_377` **operationally a
field** over the relational `bls12_377` carrier — the final field-tower operation
needed for pairing arithmetic and the pairing's final exponentiation.

## Honesty boundary

This is the abstract `Fp2` inversion over the relational `bls12_377` base
carrier. The cancellation law is conditioned on `norm ξ x ≠ 0`; that condition
is equivalent to `x ≠ 0` **iff** `ξ` is a non-residue (so `a² − ξ·b² = 0`
forces `a = b = 0`) — a number-theoretic fact about the concrete `bls12_377`
twist nonresidue, stated here as the remark `norm_ne_zero_iff_of_nonresidue`'s
hypothesis, **not** proved. We also do not wire inversion down to the emitted
6-limb base kernels (the `BaseSubstrate` lift, one further step, deliberately
not attempted here to keep the pass focused and sorry-free). The conjugate-over-
norm inverse and its cancellation law are the deliverables.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

namespace Fp2_377

/-! ## 1. The base-field embedding and the conjugate-over-norm inverse

We invert via the classical formula `x⁻¹ = conj x / norm x`: scale the conjugate
`conj x` by the base-field inverse of the norm, injected into `Fp2_377` on the
`c0` component (the embedding `n ↦ ⟨n, 0⟩` of the base field into the extension).
We work under `[Fact (Nat.Prime bls377Q)]` so that `FpBLS377 = ZMod bls377Q` is a
`Field` and `(norm ξ x)⁻¹` is a base-field inverse. -/

/-- The **base-field embedding** `FpBLS377 → Fp2_377`, `n ↦ n + 0·u`. The norm
    (a base-field element) is injected back into the extension this way. -/
def ofBase (n : FpBLS377) : Fp2_377 := ⟨n, 0⟩

@[simp] theorem ofBase_c0 (n : FpBLS377) : (ofBase n).c0 = n := rfl
@[simp] theorem ofBase_c1 (n : FpBLS377) : (ofBase n).c1 = 0 := rfl

/-- The **product of two base-field elements** stays in the base field and is the
    base-field product on `c0` (`⟨a, 0⟩ · ⟨b, 0⟩ = ⟨a·b, 0⟩`): the cross terms
    `a·0`, `0·b` and the `ξ`-reduced term `0·0·ξ` all vanish. -/
theorem ofBase_mul (ξ : FpBLS377) (a b : FpBLS377) :
    letI := commRing ξ
    ofBase a * ofBase b = ofBase (a * b) := by
  letI := commRing ξ
  show mulSchoolbook ξ (ofBase a) (ofBase b) = ofBase (a * b)
  ext <;> simp [mulSchoolbook, ofBase]

/-- The **`Fp2_377` inverse** `inv ξ x = conj x · ⟨(norm ξ x)⁻¹, 0⟩` — the
    conjugate scaled by the base-field inverse of the norm (`x⁻¹ = conj x /
    norm x`). Requires `FpBLS377` to be a field (`[Fact (Nat.Prime bls377Q)]`) so
    the norm is invertible in the base field; the cancellation law
    (`mul_inv`) additionally needs `norm ξ x ≠ 0`. -/
noncomputable def inv [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377) (x : Fp2_377) :
    Fp2_377 :=
  letI := commRing ξ
  conj x * ofBase (norm ξ x)⁻¹

/-! ## 2. The field cancellation law `x · x⁻¹ = 1` -/

/-- **`Fp2_377` field cancellation** (`x · inv ξ x = 1`) whenever the norm is
    nonzero. The conjugate-over-norm inverse cancels `x`: associating the product
    as `(x · conj x) · ⟨(norm x)⁻¹, 0⟩`, the inner factor is the base-field-valued
    `⟨norm ξ x, 0⟩` (`mul_conj_eq`), so the whole product is the base-field
    product `⟨norm x · (norm x)⁻¹, 0⟩ = ⟨1, 0⟩ = 1` by `mul_inv_cancel₀`. This is
    the operation that makes `Fp2_377` a genuine field. -/
theorem mul_inv [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377) (x : Fp2_377)
    (hx : norm ξ x ≠ 0) :
    letI := commRing ξ
    x * inv ξ x = 1 := by
  letI := commRing ξ
  -- Associate: x * (conj x * ⟨(norm x)⁻¹,0⟩) = (x * conj x) * ⟨(norm x)⁻¹,0⟩.
  have hassoc : x * inv ξ x = (x * conj x) * ofBase (norm ξ x)⁻¹ := by
    show x * (conj x * ofBase (norm ξ x)⁻¹) = (x * conj x) * ofBase (norm ξ x)⁻¹
    rw [mul_assoc]
  rw [hassoc, mul_conj_eq ξ x]
  -- Now ⟨norm x, 0⟩ * ⟨(norm x)⁻¹, 0⟩ = ⟨norm x * (norm x)⁻¹, 0⟩ = ⟨1, 0⟩ = 1.
  have hbase : (⟨norm ξ x, 0⟩ : Fp2_377) = ofBase (norm ξ x) := rfl
  rw [hbase, ofBase_mul ξ (norm ξ x) (norm ξ x)⁻¹, mul_inv_cancel₀ hx]
  rfl

/-- **`Fp2_377` field cancellation, other side** (`inv ξ x · x = 1`) — immediate
    from `mul_inv` and commutativity of the `commRing ξ` multiply. -/
theorem inv_mul [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377) (x : Fp2_377)
    (hx : norm ξ x ≠ 0) :
    letI := commRing ξ
    inv ξ x * x = 1 := by
  letI := commRing ξ
  rw [mul_comm]
  exact mul_inv ξ x hx

/-! ## 3. Remark — when is the norm nonzero?

The cancellation law is conditioned on `norm ξ x ≠ 0`. For `Fp2_377` to be a
field (every nonzero element invertible) one needs `norm ξ x = 0 ↔ x = 0`, which
holds **iff** `ξ` is a non-residue: `norm ξ x = a² − ξ·b²`, so `norm ξ x = 0`
forces `a² = ξ·b²`; if `ξ` is a non-square this is impossible unless `a = b = 0`.
Non-squareness of the concrete `bls12_377` twist nonresidue is a number-theoretic
fact about the concrete `ξ`, **not** proved here — we record the equivalence as a
statement parameterized by that non-residue hypothesis. -/

/-- **The norm vanishes only at `0`, given `ξ` is a non-residue** (stated as the
    hypothesis `hξ`). Under that number-theoretic assumption — which we do **not**
    prove, it is a fact about the concrete `bls12_377` twist nonresidue —
    `norm ξ x = 0 ↔ x = 0`, so every nonzero `Fp2_377` element is invertible by
    `mul_inv` and `Fp2_377` is a field. -/
theorem norm_ne_zero_iff_of_nonresidue [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (hξ : ∀ x : Fp2_377, norm ξ x = 0 → x = 0) (x : Fp2_377) :
    norm ξ x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro hn hx0
    apply hn
    subst hx0
    show norm ξ 0 = 0
    rw [norm_eq]
    simp
  · intro hx0 hn
    exact hx0 (hξ x hn)

end Fp2_377

end CatCrypt.Crypto.SecureCompilation.RelationalFront
