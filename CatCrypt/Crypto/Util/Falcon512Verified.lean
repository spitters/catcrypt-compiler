/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Verified Falcon-512 (FN-DSA) inner kernels over `ZMod 12289`

This file provides the *verified reference computation* layer for the
Falcon-512 hax ↔ rustcmd bridge, mirroring the role of
`MAYO/MqEvalVerified.lean` (over `Gf16`) and `UOV/EvalMqVerified.lean`
(over `Gf256`).

Falcon-512 (FN-DSA) operates over the ring

```
   R_q = ℤ_q[X] / (X^N + 1),    q = 12289,    N = 512.
```

Since `q = 12289 = 24·512 + 1` is prime, `ZMod 12289` is a field, and
Mathlib provides full `CommRing`/`Field` structure automatically once
`Fact (Nat.Prime 12289)` is in scope.

## API

* `Zq12289` : `ZMod 12289` — the Falcon-512 prime field
* `Zq12289.asInt`, `Zq12289.fromInt` — `ZMod ↔ Int` encoders
* `Zq12289.fromInt_asInt` — the proved encoder round-trip
* `Zq12289.asInt_center` : centered representation in `[-q/2, q/2)`,
  matching the `center` function in `Fndsa_haxpipe.lean` and the
  `falcon_norm_bound_check` semantics in `Jasmin/FalconReflect.lean`
* `Poly512` : `Vector Zq12289 512` — verified polynomial type
* `Poly512.zero`, `polyAdd`, `polySub`, `polyMul` — pure-Lean poly ops
  in `ℤ_{12289}[X] / (X^512 + 1)`
* `normSq` : verified squared-Euclidean norm with centered coefficients

The bridge file (`FNDSA/FndsaKernelBridge.lean`) reduces the rustcmd
leaf claims to identities at this verified-spec level.

## Reference shape

This is the verified-GF analogue (here verified-`ZMod 12289`) for the
Falcon ring; the bridge layer asserts that the opaque rustcmd leaves
(`falcon_poly_sub_modq`, `falcon_poly_mul_modq`, `falcon_norm_bound_check`)
compute the same functions on the bijected Falcon surface types.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-- The Falcon-512 modulus is prime. -/
instance fact_prime_12289 : Fact (Nat.Prime 12289) := ⟨by native_decide⟩

/-- Sanity: `q = 12289 = 24·512 + 1` (Falcon-512 NTT-friendly form, also
    `2^12 + 2^13 + 1 - 2^13 = 2^13 + 1 = 8193`… no, `12289 = 3·2^12 + 1`). -/
example : 12289 = 3 * 2^12 + 1 := by decide

/-- The Falcon-512 prime field. An `abbrev` so the `ZMod` field/ring
    structure flows through transparently. -/
abbrev Zq12289 : Type := ZMod 12289

namespace Zq12289

/-! ## Field structure (inherited from `Mathlib.Data.ZMod.Basic`) -/

example : Field Zq12289 := inferInstance
example : CommRing Zq12289 := inferInstance

/-! ## Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod 12289) into `Zq12289`. -/
def fromNat (n : Nat) : Zq12289 := (n : ZMod 12289)

/-- Project a `Zq12289` element to a `Nat` in `[0..12288]` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Zq12289) : Nat := ZMod.val g

/-- Project a `Zq12289` element to an `Int`. -/
def asInt (g : Zq12289) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Zq12289` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Zq12289 := (i : ZMod 12289)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Zq12289) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Zq12289) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..12289)`. -/
theorem asNat_lt (g : Zq12289) : asNat g < 12289 := by
  unfold asNat
  exact ZMod.val_lt g

/-! ## Centered representation

Falcon-512's `norm_bound_check` operates on centered coefficients
(canonical `(-q/2, q/2]` representatives). This matches the `center`
helper in `Fndsa_haxpipe.lean`. -/

/-- Centered representative: maps `g ∈ Z_q` to its representative in
    `(-q/2, q/2]` (concretely `(-6144, 6144]` for `q = 12289`). -/
def asIntCentered (g : Zq12289) : Int :=
  if (ZMod.val g : Int) > 6144 then (ZMod.val g : Int) - 12289 else (ZMod.val g : Int)

/-- Centered representation is bounded: |centered g| ≤ 6144 (= q/2). -/
theorem asIntCentered_abs_le (g : Zq12289) : |asIntCentered g| ≤ 6144 := by
  unfold asIntCentered
  have h_lt : (ZMod.val g : Int) < 12289 := by
    exact_mod_cast asNat_lt g
  have h_nn : (0 : Int) ≤ (ZMod.val g : Int) := by exact_mod_cast Nat.zero_le _
  by_cases h : (ZMod.val g : Int) > 6144
  · rw [if_pos h]
    have hneg : (ZMod.val g : Int) - 12289 < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  · rw [if_neg h]
    push Not at h
    rw [abs_of_nonneg h_nn]
    exact h

end Zq12289

/-! ## Verified Falcon-512 polynomial type and operations -/

/-- Falcon-512 polynomials: elements of `ℤ_{12289}[X] / (X^512 + 1)`,
    represented as length-512 vectors of coefficients. -/
abbrev Poly512 : Type := Vector Zq12289 512

namespace Poly512

/-- The zero polynomial. -/
def zero : Poly512 := Vector.replicate 512 (0 : Zq12289)

/-- Polynomial addition: coefficient-wise sum in `Zq12289`. -/
def polyAdd (a b : Poly512) : Poly512 :=
  Vector.ofFn (fun i => a.get i + b.get i)

/-- Polynomial subtraction: coefficient-wise difference in `Zq12289`. -/
def polySub (a b : Poly512) : Poly512 :=
  Vector.ofFn (fun i => a.get i - b.get i)

/-! ### `polyMul` — schoolbook multiplication in `Zq12289[X] / (X^512+1)`

The reduction rule `X^512 ≡ -1` means a degree-`k` product term (with
`512 ≤ k < 1024`) contributes `-c` to coefficient `k - 512`. Concretely:

```
   (Σᵢ aᵢXⁱ) · (Σⱼ bⱼXʲ) mod (X^512+1) =
   Σ_{0 ≤ k < 512} (Σ_{i+j=k} aᵢbⱼ  −  Σ_{i+j=k+512} aᵢbⱼ) Xᵏ
```

The verified body uses Finset.sum over the two index ranges. -/

/-- The `k`-th coefficient of the product `a·b mod (X^512+1)`.

    Σᵢ₊ⱼ₌ₖ a[i]·b[j] − Σᵢ₊ⱼ₌ₖ₊₅₁₂ a[i]·b[j], all in Zq12289. -/
def polyMulCoeff (a b : Poly512) (k : Fin 512) : Zq12289 :=
  (∑ ij ∈ Finset.univ.filter
      (fun ij : Fin 512 × Fin 512 => ij.1.val + ij.2.val = k.val),
        a.get ij.1 * b.get ij.2)
  -
  (∑ ij ∈ Finset.univ.filter
      (fun ij : Fin 512 × Fin 512 => ij.1.val + ij.2.val = k.val + 512),
        a.get ij.1 * b.get ij.2)

/-- Polynomial multiplication in `Zq12289[X] / (X^512+1)`. -/
def polyMul (a b : Poly512) : Poly512 :=
  Vector.ofFn (polyMulCoeff a b)

/-! ### Verified squared-norm on centered coefficients

Mirrors `Fndsa.norm_sq` from `Fndsa_haxpipe.lean`. -/

/-- Squared Euclidean norm of the pair `(s1, s2)` using the centered
    representative of each coefficient. Returns an `Int` (always
    non-negative); the bridge layer ports the result to `Nat`/`u64`. -/
def normSq (s1 s2 : Poly512) : Int :=
  (Finset.univ : Finset (Fin 512)).sum (fun i =>
    let c1 := Zq12289.asIntCentered (s1.get i)
    let c2 := Zq12289.asIntCentered (s2.get i)
    c1 * c1 + c2 * c2)

/-! ### Sanity properties

These structural identities are not required by the bridge layer
(which reduces to per-coefficient identities, not aggregates), but
they document the API. Proven in companion files as needed. -/

end Poly512

end CatCrypt.Util
