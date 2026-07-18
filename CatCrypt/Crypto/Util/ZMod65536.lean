/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Verified `ZMod 65536` — the FrodoKEM coefficient modulus

A computable, verified Lean reference implementation of `Z/65536Z` for use
by the FrodoKEM matrix-multiply bridge (`FrodoHaxLowCTBridge`) to replace
opaque encoder round-trip axioms with proven identities.

`q = 65536 = 2^16` is a **power of two**, not a prime. Reduction `mod 65536`
is `u16` two's-complement wraparound (free in hardware), and the resulting
structure is a **ring** rather than a field — sufficient for Frodo's
matrix-vector arithmetic which only uses add/sub/mul. This matches the Tier B
`FrodoMatmulEmit` Com which operates over `BitVec 16` (the `reg 16`
`u16` arithmetic IS the modular reduction).

Note: Frodo-640 / Frodo-976 / Frodo-1344 all use `q = 2^16` for the LWE
matrix; the parameter sets differ in the matrix dimensions (640/976/1344)
and noise parameters, not the modulus.

This is the lattice/ring-only analogue of `Util/ZMod1024.lean`. The shape is
identical modulo the missing `Fact (Nat.Prime ...)` and `Field` instances
(Frodo doesn't need inverses inside the matrix-vector kernel — only ring
arithmetic).

## API

* `Zq65536 := ZMod 65536` — the verified ring
* `Zq65536.fromNat`, `Zq65536.asNat`, `Zq65536.asInt`, `Zq65536.fromInt` —
  encoders to/from `Nat`/`Int`
* `Zq65536.fromInt_asInt`, `Zq65536.fromNat_asNat` — proved round-trip
  identities used by bridge proofs to discharge previously-axiomatised
  encoder round-trips.
-/

set_option autoImplicit false

namespace CatCrypt.Util

/-- The FrodoKEM coefficient modulus ring. An `abbrev` so the `ZMod`
    ring/comm-ring structure flows through transparently. Note: NOT a field
    (65536 is not prime). -/
abbrev Zq65536 : Type := ZMod 65536

namespace Zq65536

/-! ## Ring axioms — inherited from `Mathlib.Data.ZMod.Basic`

Unlike the prime-modulus siblings (`Zq3329`, `Zq8380417`, `Zq127`,
`Zq4591`), we do **not** declare a `Fact (Nat.Prime 65536)` instance —
65536 = 2^16 is composite, so `ZMod 65536` is a ring (not a field).
Frodo's matrix-vector kernel only needs ring operations (add, sub, mul),
which work without the field structure. -/

/-- `Zq65536` is a commutative ring. -/
example : CommRing Zq65536 := inferInstance

/-! ## Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod 65536) into `Zq65536`. -/
def fromNat (n : Nat) : Zq65536 := (n : ZMod 65536)

/-- Project a `Zq65536` element to a `Nat` in `[0..65535]` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Zq65536) : Nat := ZMod.val g

/-- Project a `Zq65536` element to an `Int`. -/
def asInt (g : Zq65536) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Zq65536` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Zq65536 := (i : ZMod 65536)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Zq65536) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Zq65536) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..65536)`. -/
theorem asNat_lt (g : Zq65536) : asNat g < 65536 := by
  unfold asNat
  exact ZMod.val_lt g

end Zq65536

end CatCrypt.Util
