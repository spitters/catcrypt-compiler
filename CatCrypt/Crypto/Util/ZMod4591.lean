/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Verified `ZMod 4591` — the sntrup761 coefficient modulus

A computable, verified Lean reference implementation of `Z/4591Z` for use by
the sntrup761 polynomial-multiply bridge (`Sntrup761HaxLowCTBridge`) to
replace opaque encoder round-trip axioms with proven identities.

`q = 4591` is a **prime** (NTRU Prime's distinctive choice — the field is
chosen so that `q` is prime and `Z/q[x]/(x^p - x - 1)` is irreducible, giving
a *prime field* rather than a power-of-2 ring). This module establishes the
`Fact (Nat.Prime 4591)` instance and exposes the `Field` structure for
downstream bridge proofs that need field arithmetic.

This is the prime-field analogue of `Util/ZMod3329.lean`, `Util/ZMod127.lean`
and `Util/ZMod251.lean`.

## API

* `Zq4591 := ZMod 4591` — the verified prime field
* `Zq4591.fromNat`, `Zq4591.asNat`, `Zq4591.asInt`, `Zq4591.fromInt` —
  encoders to/from `Nat`/`Int`
* `Zq4591.fromInt_asInt`, `Zq4591.fromNat_asNat` — proved round-trip
  identities used by bridge proofs to discharge previously-axiomatised
  encoder round-trips.
-/

set_option autoImplicit false

namespace CatCrypt.Util

/-- 4591 is prime. Closed by `native_decide`. -/
instance fact_prime_4591 : Fact (Nat.Prime 4591) := ⟨by native_decide⟩

/-- The sntrup761 coefficient modulus field. An `abbrev` so the `ZMod`
    field/comm-ring structure flows through transparently. -/
abbrev Zq4591 : Type := ZMod 4591

namespace Zq4591

/-! ## Field / Ring axioms — inherited from `Mathlib.Data.ZMod.Basic`
The `Fact (Nat.Prime 4591)` instance above makes `Zq4591` a `Field`. -/

/-- `Zq4591` is a commutative ring. -/
example : CommRing Zq4591 := inferInstance

/-- `Zq4591` is a field. -/
example : Field Zq4591 := inferInstance

/-! ## Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod 4591) into `Zq4591`. -/
def fromNat (n : Nat) : Zq4591 := (n : ZMod 4591)

/-- Project a `Zq4591` element to a `Nat` in `[0..4590]` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Zq4591) : Nat := ZMod.val g

/-- Project a `Zq4591` element to an `Int`. -/
def asInt (g : Zq4591) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Zq4591` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Zq4591 := (i : ZMod 4591)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Zq4591) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Zq4591) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..4591)`. -/
theorem asNat_lt (g : Zq4591) : asNat g < 4591 := by
  unfold asNat
  exact ZMod.val_lt g

end Zq4591

end CatCrypt.Util
