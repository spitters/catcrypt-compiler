/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp6

/-!
# The `bls12_377` `Fp12` cyclotomic conjugation and `Fp12 → Fp6` norm

`RelationalFrontBls377Fp6` builds the `bls12_377` tower up to the dodecic
extension `Fp12_377 = Fp6_377[w]/(w² − v)` (`c0 + c1·w`, two `Fp6_377`
coordinates, schoolbook / Karatsuba multiply with the `w² = v` reduction
realized by `Fp6_377.mulByV`, componentwise add/neg/sub, and the
`@[reducible] commRing ξ₂ ξ₆` instance). The `Fp2` Galois conjugation
(`RelationalFrontBls377Fp2Conj`) flips the `u`-component one tower level down;
this module builds the **dodecic analogue one level up**: the cyclotomic
conjugation `c0 + c1·w ↦ c0 − c1·w` (the easy `w ↦ −w` automorphism), its
ring-endomorphism / involution facts, and the `Fp12 → Fp6` field norm.

## What this module proves

The headline facts about `conj12 (c0 + c1·w) = c0 − c1·w`:

```
   conj12 (x + y) = conj12 x + conj12 y      -- additive
   conj12 (x * y) = conj12 x * conj12 y      -- multiplicative (ring-hom)
   conj12 (conj12 x) = x                       -- involution (order-2)
   conj12 1 = 1,  conj12 0 = 0                 -- units
```

The multiplicative fact is the load-bearing one: both `conj12 (x*y)` and
`conj12 x · conj12 y` equal `(c0·c0' + v·c1·c1') − (c0·c1' + c1·c0')·w`, i.e.
the sign flip on the `w`-component commutes with the schoolbook product (the
`w² = v` fold is invariant because `(−c1)(−c1')·v = c1·c1'·v`). Together these
say `conj12` is a **ring endomorphism of `Fp12_377` that fixes the `Fp6_377`
subfield pointwise** — the genuine cyclotomic element of `Gal(Fp12 / Fp6)`, the
`x ↦ x̄` map that the pairing's final exponentiation uses (the easy part of
`x^((p⁶−1)) = x̄ / x`).

We then form the **`Fp12 → Fp6` field norm** `norm12 x = (x · conj12 x).c0`,
the product of an element with its conjugate. Because `x · conj12 x =
(c0 + c1·w)(c0 − c1·w) = (c0² − v·c1²) + 0·w`, the norm **lands in `Fp6_377`** —
the `w`-component of `x · conj12 x` vanishes (`mul_conj12_c1_zero`). This
`Fp12 → Fp6` norm is the building block for `Fp12` inversion
(`x⁻¹ = conj12 x · (norm12 x)⁻¹`) and for the pairing's final exponentiation.

## Honesty boundary

This is the abstract `Fp12` cyclotomic conjugation and norm over the relational
`bls12_377` tower carrier. It does **not** wire conjugation/norm down to the
emitted base kernels (the `BaseSubstrate` lift), nor does it use the norm to
construct an inverse (which requires `norm12 x ≠ 0`, i.e. `v` a non-residue in
`Fp6` — a number-theoretic fact about the concrete tower parameters, not proved
here). The conjugation ring-hom facts and the norm's `Fp6`-landing are the
deliverables, mirroring `RelationalFrontBls377Fp2Conj` one tower level up.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

namespace Fp12_377

/-! ## 1. The `Fp12` cyclotomic conjugation `c0 + c1·w ↦ c0 − c1·w`

The conjugation flips the sign of the `w`-component. It is `(ξ₂, ξ₆)`-independent
at the definition level (just a componentwise negation on `c1`); its
multiplicativity does interact with the `w² = v` fold, but invariantly so. We
work over the `commRing ξ₂ ξ₆` instance (so `*` is `mulSchoolbook ξ₂ ξ₆`) for the
multiplicative facts. -/

/-- The **`Fp12_377` cyclotomic conjugate** `conj12 (c0 + c1·w) = c0 − c1·w` —
    the easy automorphism of `Fp12_377` over the `Fp6_377` subfield (`w ↦ −w`). -/
def conj12 (x : Fp12_377) : Fp12_377 := ⟨x.c0, -x.c1⟩

@[simp] theorem conj12_c0 (x : Fp12_377) : (conj12 x).c0 = x.c0 := rfl
@[simp] theorem conj12_c1 (x : Fp12_377) : (conj12 x).c1 = -x.c1 := rfl

/-! ## 2. `conj12` is additive, an involution, and unit-preserving

These are `(ξ₂, ξ₆)`-independent — pure componentwise facts about the
`Fp12_377` add/neg/zero/one instances (the `Fp6_377` add/neg are global
componentwise instances, so the residual `Fp6`-level sign goals close by `ring`
under any `Fp6_377` `CommRing`; we install a fixed one). -/

/-- A fixed `Fp6_377` `CommRing` instance for the `ξ`-independent additive /
    involution facts. The `Fp6_377` `Add`/`Neg` are global componentwise
    instances, so the parameters do not affect those goals; any choice gives
    `ring` an `Fp6`-ring to normalize the sign rearrangements over. -/
private abbrev fp6Ring : CommRing Fp6_377 := Fp6_377.commRing (0 : FpBLS377) (0 : Fp2_377)

/-- **`conj12` is additive** (`conj12 (x + y) = conj12 x + conj12 y`). -/
theorem conj12_add (x y : Fp12_377) : conj12 (x + y) = conj12 x + conj12 y := by
  letI := fp6Ring
  refine Fp12_377.ext rfl ?_; simp only [conj12, add_c1]; ring

/-- **`conj12` is an involution** (`conj12 (conj12 x) = x`) — the order-2 element
    of `Gal(Fp12 / Fp6)`. -/
theorem conj12_conj12 (x : Fp12_377) : conj12 (conj12 x) = x := by
  letI := fp6Ring
  refine Fp12_377.ext rfl ?_; show - -x.c1 = x.c1; ring

/-- **`conj12` fixes `1`** (`conj12 1 = 1`). -/
theorem conj12_one : conj12 (1 : Fp12_377) = 1 := by
  letI := fp6Ring
  refine Fp12_377.ext rfl ?_; simp only [conj12, one_c1]; ring

/-- **`conj12` fixes `0`** (`conj12 0 = 0`). -/
theorem conj12_zero : conj12 (0 : Fp12_377) = 0 := by
  letI := fp6Ring
  refine Fp12_377.ext rfl ?_; simp only [conj12, zero_c1]; ring

/-- **`conj12` negates** (`conj12 (-x) = -conj12 x`). -/
theorem conj12_neg (x : Fp12_377) : conj12 (-x) = -conj12 x := by
  refine Fp12_377.ext rfl ?_; simp only [conj12, neg_c1]

/-! ## 3. `conj12` is multiplicative — the ring-homomorphism fact

The key identity: `conj12` commutes with the schoolbook product. Both
`conj12 (x · y)` and `conj12 x · conj12 y` equal
`(c0·c0' + v·c1·c1') − (c0·c1' + c1·c0')·w`. The `w² = v`-reduced `c0`-component
is unchanged (`(−c1)(−c1')·v = c1·c1'·v`); the `w`-component flips sign. We
expose the structure multiply as `mulSchoolbook ξ₂ ξ₆` (the opaque-mul `show`
trick from `RelationalFrontBls377Fp6`'s `commRing`) so the inner `Fp6` mul stays
atomic; the `w² = v` fold `mulByV` is rewritten to `vGen * _` (`hv`) and `vGen`
is `generalize`d so `ring` over the `Fp6_377` `CommRing` closes each
component. -/

/-- **`conj12` is multiplicative** (`conj12 (x * y) = conj12 x * conj12 y`) over
    the `commRing ξ₂ ξ₆` instance — the load-bearing ring-homomorphism fact. The
    sign flip on the `w`-component commutes with the schoolbook product because
    the `w² = v` fold `(−c1)(−c1')·v = c1·c1'·v` is invariant under
    conjugation. -/
theorem conj12_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp12_377) :
    letI := commRing ξ₂ ξ₆
    conj12 (x * y) = conj12 x * conj12 y := by
  letI := Fp6_377.commRing ξ₂ ξ₆
  have hm : ∀ a b : Fp6_377, mul₆ ξ₂ ξ₆ a b = a * b := fun _ _ => rfl
  have hv : ∀ z : Fp6_377, Fp6_377.mulByV ξ₂ ξ₆ z = Fp6_377.vGen * z := fun z => by
    rw [Fp6_377.mulByV_eq_mul]; rfl
  show conj12 (mulSchoolbook ξ₂ ξ₆ x y)
      = mulSchoolbook ξ₂ ξ₆ (conj12 x) (conj12 y)
  refine Fp12_377.ext ?_ ?_ <;>
    simp only [conj12, mulSchoolbook, hm, hv] <;>
      generalize Fp6_377.vGen = v <;> ring

/-! ## 4. The `Fp12 → Fp6` field norm `norm12 x = (x · conj12 x).c0`

The norm is the product of an element with its conjugate, projected to the
`Fp6_377` subfield. Because `(c0 + c1·w)(c0 − c1·w) = (c0² − v·c1²) + 0·w`, the
`w`-component of `x · conj12 x` vanishes — the norm genuinely lands in
`Fp6_377`. -/

/-- The **`w`-component of `x · conj12 x` vanishes** — the field norm lands in
    the subfield `Fp6_377`. (`(c0 + c1·w)(c0 − c1·w) = (c0² − v·c1²) + 0·w`.) -/
theorem mul_conj12_c1_zero (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp12_377) :
    letI := commRing ξ₂ ξ₆
    (x * conj12 x).c1 = 0 := by
  letI := Fp6_377.commRing ξ₂ ξ₆
  have hm : ∀ a b : Fp6_377, mul₆ ξ₂ ξ₆ a b = a * b := fun _ _ => rfl
  show (mulSchoolbook ξ₂ ξ₆ x (conj12 x)).c1 = 0
  simp only [conj12, mulSchoolbook, hm]; ring

/-- The **`Fp12_377 → Fp6_377` field norm** `norm12 x = (x · conj12 x).c0 =
    c0² − v·c1²`. The product `x · conj12 x` lands in the subfield
    (`mul_conj12_c1_zero`), so the norm is well-defined as its `c0` projection.
    This is the building block for `Fp12` inversion and pairing final
    exponentiation. -/
def norm12 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp12_377) : Fp6_377 :=
  letI := commRing ξ₂ ξ₆
  (x * conj12 x).c0

/-- **`x · conj12 x` is the norm injected into `Fp12_377`** (`= norm12 x + 0·w`):
    its `c0` is `norm12 x` and its `c1` is `0`. -/
theorem mul_conj12_eq (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp12_377) :
    letI := commRing ξ₂ ξ₆
    x * conj12 x = ⟨norm12 ξ₂ ξ₆ x, 0⟩ := by
  letI := commRing ξ₂ ξ₆
  refine Fp12_377.ext ?_ ?_
  · rfl
  · exact mul_conj12_c1_zero ξ₂ ξ₆ x

/-! ## 5. `norm12` is multiplicative

The norm is a multiplicative map `Fp12 → Fp6` (`norm12 (x·y) = norm12 x · norm12 y`),
immediate from `conj12`'s multiplicativity and commutativity of `Fp6_377`. -/

/-- **The norm is multiplicative** (`norm12 ξ₂ ξ₆ (x * y) = norm12 ξ₂ ξ₆ x *
    norm12 ξ₂ ξ₆ y`) — a consequence of `conj12_mul` and `Fp6_377`
    commutativity. -/
theorem norm12_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp12_377) :
    letI := commRing ξ₂ ξ₆
    letI := Fp6_377.commRing ξ₂ ξ₆
    norm12 ξ₂ ξ₆ (x * y) = norm12 ξ₂ ξ₆ x * norm12 ξ₂ ξ₆ y := by
  letI := commRing ξ₂ ξ₆
  have hxy : x * y * conj12 (x * y) = (x * conj12 x) * (y * conj12 y) := by
    rw [conj12_mul]; ring
  have h0 : (x * y * conj12 (x * y)).c0 = ((x * conj12 x) * (y * conj12 y)).c0 := by
    rw [hxy]
  rw [mul_conj12_eq ξ₂ ξ₆ x, mul_conj12_eq ξ₂ ξ₆ y] at h0
  show (x * y * conj12 (x * y)).c0 = _
  rw [h0]
  letI := Fp6_377.commRing ξ₂ ξ₆
  show (mulSchoolbook ξ₂ ξ₆ ⟨norm12 ξ₂ ξ₆ x, 0⟩ ⟨norm12 ξ₂ ξ₆ y, 0⟩).c0
      = norm12 ξ₂ ξ₆ x * norm12 ξ₂ ξ₆ y
  have hm : ∀ a b : Fp6_377, mul₆ ξ₂ ξ₆ a b = a * b := fun _ _ => rfl
  simp only [mulSchoolbook, hm, Fp6_377.mulByV_zero, mul_zero, add_zero]

end Fp12_377

end CatCrypt.Crypto.SecureCompilation.RelationalFront
