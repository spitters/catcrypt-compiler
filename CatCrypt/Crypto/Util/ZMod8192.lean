/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Verified `ZMod 8192` — the NTRU-HRSS coefficient modulus

A computable, verified Lean reference implementation of `Z/8192Z` for use by
the NTRU-HRSS-701 polynomial-multiply bridge (`NtruhrssHaxLowCTBridge`) to
replace opaque encoder round-trip axioms with proven identities.

`q = 8192 = 2^13` is a **power of two**, not a prime. Reduction `mod 8192`
is therefore a bit-mask `& 8191` rather than a fold-and-conditional subtract,
and the resulting structure is a **ring** rather than a field — sufficient
for NTRU-HRSS's ring-multiply kernel which only uses add/sub/mul.

This is the lattice/ring-only analogue of `Util/ZMod1024.lean`. The shape is
identical modulo the missing `Fact (Nat.Prime ...)` and `Field` instances
(NTRU-HRSS doesn't need inverses inside the ring-multiply kernel — only ring
arithmetic).

## API

* `Zq8192 := ZMod 8192` — the verified ring
* `Zq8192.fromNat`, `Zq8192.asNat`, `Zq8192.asInt`, `Zq8192.fromInt` —
  encoders to/from `Nat`/`Int`
* `Zq8192.fromInt_asInt`, `Zq8192.fromNat_asNat` — proved round-trip
  identities used by bridge proofs to discharge previously-axiomatised
  encoder round-trips.
-/

set_option autoImplicit false

namespace CatCrypt.Util

/-- The NTRU-HRSS coefficient modulus ring. An `abbrev` so the `ZMod`
    ring/comm-ring structure flows through transparently. Note: NOT a field
    (8192 is not prime). -/
abbrev Zq8192 : Type := ZMod 8192

namespace Zq8192

/-! ## Ring axioms — inherited from `Mathlib.Data.ZMod.Basic`

Unlike the prime-modulus siblings (`Zq3329`, `Zq8380417`, `Zq127`), we do
**not** declare a `Fact (Nat.Prime 8192)` instance — 8192 = 2^13 is
composite, so `ZMod 8192` is a ring (not a field). NTRU-HRSS's ring-multiply
kernel only needs ring operations (add, sub, mul), which work without the
field structure. -/

/-- `Zq8192` is a commutative ring. -/
example : CommRing Zq8192 := inferInstance

/-! ## Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod 8192) into `Zq8192`. -/
def fromNat (n : Nat) : Zq8192 := (n : ZMod 8192)

/-- Project a `Zq8192` element to a `Nat` in `[0..8191]` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Zq8192) : Nat := ZMod.val g

/-- Project a `Zq8192` element to an `Int`. -/
def asInt (g : Zq8192) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Zq8192` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Zq8192 := (i : ZMod 8192)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Zq8192) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Zq8192) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..8192)`. -/
theorem asNat_lt (g : Zq8192) : asNat g < 8192 := by
  unfold asNat
  exact ZMod.val_lt g

end Zq8192

end CatCrypt.Util
