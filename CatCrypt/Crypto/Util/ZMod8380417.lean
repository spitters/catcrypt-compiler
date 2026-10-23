/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Prime

/-!
# Verified `ZMod 8380417` — the ML-DSA prime field

A computable, verified Lean reference implementation of `Z/qZ` with
`q = 8380417 = 2^23 - 2^13 + 1` for use by the ML-DSA bridge
(`MldsaVerifiedZMod`) to replace opaque encoder round-trip axioms
with proven identities.

The prime `q = 2^23 - 2^13 + 1` is the modulus published in FIPS 204
for ML-DSA-44/65/87. Since `q` is prime, `ZMod q` is a field — Mathlib
provides the full ring/field structure automatically once
`Fact (Nat.Prime 8380417)` is in scope.

## API

* `Zq8380417 := ZMod 8380417` — the verified field
* `Zq8380417.ofNat`, `Zq8380417.toNat`, `Zq8380417.asInt`,
  `Zq8380417.fromInt` — encoders to/from `Nat`/`Int`
* `Zq8380417.fromInt_asInt` — the proved round-trip identity used by
  bridge proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-- ML-DSA modulus is prime: `q = 2^23 - 2^13 + 1 = 8380417`. -/
instance fact_prime_8380417 : Fact (Nat.Prime 8380417) := ⟨by norm_num⟩

/-- Sanity: `q = 2^23 - 2^13 + 1`. -/
example : 8380417 = 2^23 - 2^13 + 1 := by decide

/-- The ML-DSA prime field. -/
abbrev Zq8380417 : Type := ZMod 8380417

namespace Zq8380417

/-- `Zq8380417` is a field. -/
example : Field Zq8380417 := inferInstance

/-- `Zq8380417` is a commutative ring. -/
example : CommRing Zq8380417 := inferInstance

/-! ## Encoders to/from Nat, Int -/

def fromNat (n : Nat) : Zq8380417 := (n : ZMod 8380417)
def asNat  (g : Zq8380417) : Nat := ZMod.val g
def asInt  (g : Zq8380417) : Int := (ZMod.val g : Int)
def fromInt (i : Int) : Zq8380417 := (i : ZMod 8380417)

theorem fromNat_asNat (g : Zq8380417) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

theorem fromInt_asInt (g : Zq8380417) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

theorem asNat_lt (g : Zq8380417) : asNat g < 8380417 := by
  unfold asNat
  exact ZMod.val_lt g

end Zq8380417

end CatCrypt.Util
