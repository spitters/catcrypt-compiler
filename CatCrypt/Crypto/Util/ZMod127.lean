/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Ring

/-!
# Verified `ZMod 127` — the QR-UOV-Is Mersenne base prime field

A computable, verified Lean reference implementation of `Z/127Z` for use by
the QR-UOV bridge (`QruovKernelBridge`) to replace opaque encoder
round-trip axioms with proven identities.

`q = 127 = 2^7 - 1` is the Mersenne prime base field of the QR-UOV-Is
(Round-2 level-I efficient) parameter set, with `ℓ = 3` quotient-ring
degree (`f ∈ GF(127)[x]` an irreducible degree-3 polynomial). Reduction
`mod 127` is a fold-and-conditional-subtract on bytes. Since 127 is
prime, `ZMod 127` is a field — Mathlib provides the full ring/field
structure once `Fact (Nat.Prime 127)` is in scope.

## API

* `Zq127 := ZMod 127` — the verified field
* `Zq127.fromNat`, `Zq127.asNat`, `Zq127.asInt`, `Zq127.fromInt` —
  encoders to/from `Nat`/`Int`
* `Zq127.fromInt_asInt`, `Zq127.fromNat_asNat` — proved round-trip
  identities used by bridge proofs.

This file is the prime-field analogue of `Util/ZMod251.lean` for MQOM /
SDitH at QR-UOV's Mersenne modulus.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-- QR-UOV-Is base field is prime: `q = 127`. -/
instance fact_prime_127 : Fact (Nat.Prime 127) := ⟨by native_decide⟩

/-- The QR-UOV-Is base prime field. An `abbrev` so the `ZMod` field/ring
    structure flows through transparently. -/
abbrev Zq127 : Type := ZMod 127

namespace Zq127

/-! ## Field axioms — inherited from `Mathlib.Data.ZMod.Basic` -/

/-- `Zq127` is a field. -/
example : Field Zq127 := inferInstance

/-- `Zq127` is a commutative ring. -/
example : CommRing Zq127 := inferInstance

/-! ## Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod 127) into `Zq127`. -/
def fromNat (n : Nat) : Zq127 := (n : ZMod 127)

/-- Project a `Zq127` element to a `Nat` in `[0..126]` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Zq127) : Nat := ZMod.val g

/-- Project a `Zq127` element to an `Int`. -/
def asInt (g : Zq127) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Zq127` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Zq127 := (i : ZMod 127)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Zq127) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Zq127) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..127)`. -/
theorem asNat_lt (g : Zq127) : asNat g < 127 := by
  unfold asNat
  exact ZMod.val_lt g

end Zq127

end CatCrypt.Util
