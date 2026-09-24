/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp2
public import Mathlib.Data.ZMod.Basic

/-!
# The `bls12_377` `Fp2` Galois conjugation and field norm

`RelationalFrontBls377Fp2` builds the `bls12_377` quadratic extension
`Fp2_377 = FpBLS377[u]/(u² − ξ)` (with `c0 + c1·u`, schoolbook/Karatsuba multiply,
componentwise add/neg/sub, and the `commRing ξ` instance). The *next* gateway
toward `bls12_377` pairings is the **nontrivial Galois automorphism** of `Fp2`
over its base field `FpBLS377` — the Frobenius / conjugation
`a + b·u ↦ a − b·u`. This module builds that conjugation and its field-norm
companion.

## What this module proves

The headline facts about `conj (a + b·u) = a − b·u`:

```
   conj (x + y) = conj x + conj y         -- additive
   conj (x * y) = conj x * conj y         -- multiplicative (the ring-hom fact)
   conj (conj x) = x                       -- involution (order-2 automorphism)
   conj 1 = 1,  conj 0 = 0                 -- units
```

The multiplicative fact is the key one: both `conj (x*y)` and
`conj x * conj y` equal `(c0·c0' + ξ·c1·c1') − (c0·c1' + c1·c0')·u`, i.e. the
sign flip on the `u`-component commutes with the schoolbook product (the `ξ`
reduction is invariant under it because `(−b)(−d)ξ = bdξ`). Together these say
`conj` is a **ring endomorphism of `Fp2_377` that fixes the base field
pointwise** — the nontrivial element of `Gal(Fp2 / Fp)`.

We then form the **field norm** `norm x = (x · conj x).c0`, the product of an
element with its conjugate. Because `x · conj x = (a + b·u)(a − b·u) =
(a² − ξ·b²) + 0·u`, the norm **lands in the base field** — the `u`-component of
`x · conj x` vanishes (`norm_c1_zero`). This `Fp2 → Fp` norm is the building
block for `Fp2` inversion (`x⁻¹ = conj x / norm x`) and for the pairing's final
exponentiation.

## Scope

This is the abstract `Fp2` conjugation and norm over the relational `bls12_377`
base carrier. It does **not** wire conjugation/norm down to the emitted 6-limb
base kernels (that is the `BaseSubstrate` lift, one further step, deliberately
not attempted here to keep the pass focused and sorry-free), nor does it use the
norm to construct an inverse (which requires `norm x ≠ 0`, i.e. `ξ` a
non-square — a number-theoretic fact about the concrete twist nonresidue, not
proved here). The conjugation ring-hom facts and the norm's base-field landing
are the deliverables.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

namespace Fp2_377

/-! ## 1. The `Fp2` Galois conjugation `a + b·u ↦ a − b·u`

The conjugation flips the sign of the `u`-component. It is `ξ`-independent at the
definition level (it is just a componentwise negation on `c1`); its
multiplicativity does interact with `ξ`, but invariantly so. We work over the
`commRing ξ` instance (so `*` is `mulSchoolbook ξ`) for the multiplicative
facts. -/

/-- The **`Fp2_377` Galois conjugate** `conj (a + b·u) = a − b·u` — the
    nontrivial automorphism of `Fp2_377` over the base field `FpBLS377`. -/
def conj (x : Fp2_377) : Fp2_377 := ⟨x.c0, -x.c1⟩

@[simp] theorem conj_c0 (x : Fp2_377) : (conj x).c0 = x.c0 := rfl
@[simp] theorem conj_c1 (x : Fp2_377) : (conj x).c1 = -x.c1 := rfl

/-! ## 2. `conj` is additive, an involution, and unit-preserving -/

/-- **`conj` is additive** (`conj (x + y) = conj x + conj y`). -/
theorem conj_add (x y : Fp2_377) : conj (x + y) = conj x + conj y := by
  ext <;> simp [add_comm]

/-- **`conj` is an involution** (`conj (conj x) = x`) — it is the order-2 element
    of `Gal(Fp2 / Fp)`. -/
theorem conj_conj (x : Fp2_377) : conj (conj x) = x := by
  ext <;> simp

/-- **`conj` fixes `1`** (`conj 1 = 1`). -/
theorem conj_one : conj (1 : Fp2_377) = 1 := by
  ext <;> simp

/-- **`conj` fixes `0`** (`conj 0 = 0`). -/
theorem conj_zero : conj (0 : Fp2_377) = 0 := by
  ext <;> simp

/-- **`conj` negates** (`conj (-x) = -conj x`). -/
theorem conj_neg (x : Fp2_377) : conj (-x) = -conj x := by
  ext <;> simp

/-! ## 3. `conj` is multiplicative — the ring-homomorphism fact

The key identity: `conj` commutes with the schoolbook product. Both
`conj (x · y)` and `conj x · conj y` equal
`(c0·c0' + ξ·c1·c1') − (c0·c1' + c1·c0')·u`. The `ξ`-reduced real component is
unchanged (`(−b)(−d)·ξ = b·d·ξ`); the imaginary component flips sign. We expose
the structure multiply as `mulSchoolbook ξ` (the opaque-mul `show` trick from
`RelationalFrontBls377Fp2`) so the inner `ZMod` mul stays atomic and `ring`
closes each component. -/

/-- **`conj` is multiplicative** (`conj (x * y) = conj x * conj y`) over the
    `commRing ξ` instance — the key ring-homomorphism fact. The sign
    flip on the `u`-component commutes with the schoolbook product because the
    `ξ`-reduction `(−b)(−d)·ξ = b·d·ξ` is invariant under conjugation. -/
theorem conj_mul (ξ : FpBLS377) (x y : Fp2_377) :
    letI := commRing ξ
    conj (x * y) = conj x * conj y := by
  letI := commRing ξ
  show conj (mulSchoolbook ξ x y) = mulSchoolbook ξ (conj x) (conj y)
  ext <;> simp [mulSchoolbook, add_comm]

/-! ## 4. The `Fp2 → Fp` field norm `norm x = (x · conj x).c0`

The norm is the product of an element with its conjugate, projected to the base
field. Because `(a + b·u)(a − b·u) = (a² − ξ·b²) + 0·u`, the `u`-component of
`x · conj x` vanishes — the norm lands in `FpBLS377`. -/

/-- The **`u`-component of `x · conj x` vanishes** — the field norm lands in the
    base field `FpBLS377`. (`(a + b·u)(a − b·u) = (a² − ξ·b²) + 0·u`.) -/
theorem mul_conj_c1_zero (ξ : FpBLS377) (x : Fp2_377) :
    letI := commRing ξ
    (x * conj x).c1 = 0 := by
  letI := commRing ξ
  show (mulSchoolbook ξ x (conj x)).c1 = 0
  simp [mulSchoolbook]; ring

/-- The **`Fp2_377 → FpBLS377` field norm** `norm x = (x · conj x).c0 =
    a² − ξ·b²`. The product `x · conj x` lands in the base field
    (`mul_conj_c1_zero`), so the norm is well-defined as its `c0` projection.
    This is the building block for `Fp2` inversion and pairing final
    exponentiation. -/
def norm (ξ : FpBLS377) (x : Fp2_377) : FpBLS377 :=
  letI := commRing ξ
  (x * conj x).c0

/-- **The norm in closed form** (`norm ξ x = c0² − ξ·c1²`). -/
theorem norm_eq (ξ : FpBLS377) (x : Fp2_377) :
    norm ξ x = x.c0 * x.c0 - x.c1 * x.c1 * ξ := by
  letI := commRing ξ
  show (mulSchoolbook ξ x (conj x)).c0 = x.c0 * x.c0 - x.c1 * x.c1 * ξ
  simp [mulSchoolbook]; ring

/-- **`x · conj x` is the norm injected into `Fp2_377`** (`= norm ξ x + 0·u`):
    its `c0` is `norm ξ x` and its `c1` is `0`. -/
theorem mul_conj_eq (ξ : FpBLS377) (x : Fp2_377) :
    letI := commRing ξ
    x * conj x = ⟨norm ξ x, 0⟩ := by
  letI := commRing ξ
  ext
  · rfl
  · exact mul_conj_c1_zero ξ x

/-! ## 5. `norm` is multiplicative

The norm is a multiplicative map `Fp2 → Fp` (`norm (x·y) = norm x · norm y`),
immediate from `conj`'s multiplicativity and commutativity of the base ring. -/

/-- **The norm is multiplicative** (`norm ξ (x * y) = norm ξ x * norm ξ y`) —
    a consequence of `conj_mul` and commutativity. -/
theorem norm_mul (ξ : FpBLS377) (x y : Fp2_377) :
    letI := commRing ξ
    norm ξ (x * y) = norm ξ x * norm ξ y := by
  letI := commRing ξ
  have hxy : x * y * conj (x * y) = (x * conj x) * (y * conj y) := by
    rw [conj_mul]; ring
  have h0 : (x * y * conj (x * y)).c0 = ((x * conj x) * (y * conj y)).c0 := by
    rw [hxy]
  rw [mul_conj_eq ξ x, mul_conj_eq ξ y] at h0
  show (x * y * conj (x * y)).c0 = _
  rw [h0]
  show (mulSchoolbook ξ ⟨norm ξ x, 0⟩ ⟨norm ξ y, 0⟩).c0 = norm ξ x * norm ξ y
  simp [mulSchoolbook]

end Fp2_377

end CatCrypt.Crypto.SecureCompilation.RelationalFront
