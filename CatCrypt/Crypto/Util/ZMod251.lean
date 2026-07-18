/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Verified `ZMod 251` — the MQOM / SDitH base prime field

A computable, verified Lean reference implementation of `Z/251Z` for use by
the MQOM and SDitH bridges (`MqomHaxLowCTBridge` and
`SdithHaxLowCTBridge`) to replace opaque encoder round-trip axioms with
proven identities.

`q = 251` is the largest prime fitting in a single byte. It is the base
field of the MQOM2-L1-gf251-fast parameter set (`mqom-hax/src/mq_eval.rs`)
and the SDitH-L1 syndrome / Reed–Solomon evaluation core (`sdith-hax`).
Since 251 is prime, `ZMod 251` is a field — Mathlib provides the full
ring/field structure automatically once `Fact (Nat.Prime 251)` is in scope.

## API

* `Zq251 := ZMod 251` — the verified field
* `Zq251.fromNat`, `Zq251.asNat`, `Zq251.asInt`, `Zq251.fromInt` —
  encoders to/from `Nat`/`Int`
* `Zq251.fromInt_asInt`, `Zq251.fromNat_asNat` — proved round-trip
  identities used by bridge proofs to discharge previously-axiomatised
  encoder round-trips.

This file is the prime-field analogue of `Util/ZMod3329.lean` for ML-KEM
and `Util/ZMod8380417.lean` for ML-DSA.
-/

set_option autoImplicit false

namespace CatCrypt.Util

/-- MQOM / SDitH base field is prime: `q = 251`. -/
instance fact_prime_251 : Fact (Nat.Prime 251) := ⟨by native_decide⟩

/-- The MQOM / SDitH base prime field. An `abbrev` so the `ZMod` field/ring
    structure flows through transparently. -/
abbrev Zq251 : Type := ZMod 251

namespace Zq251

/-! ## Field axioms — inherited from `Mathlib.Data.ZMod.Basic` -/

/-- `Zq251` is a field. -/
example : Field Zq251 := inferInstance

/-- `Zq251` is a commutative ring. -/
example : CommRing Zq251 := inferInstance

/-! ## Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod 251) into `Zq251`. -/
def fromNat (n : Nat) : Zq251 := (n : ZMod 251)

/-- Project a `Zq251` element to a `Nat` in `[0..250]` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Zq251) : Nat := ZMod.val g

/-- Project a `Zq251` element to an `Int`. -/
def asInt (g : Zq251) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Zq251` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Zq251 := (i : ZMod 251)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Zq251) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Zq251) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..251)`. -/
theorem asNat_lt (g : Zq251) : asNat g < 251 := by
  unfold asNat
  exact ZMod.val_lt g

end Zq251

end CatCrypt.Util
