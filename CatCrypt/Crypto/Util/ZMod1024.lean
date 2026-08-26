/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Verified `ZMod 1024` — the HAWK per-lane modulus

A computable, verified Lean reference implementation of `Z/1024Z` for use
by the HAWK 4-way ring-multiply bridge (`HawkHaxLowCTBridge`) to replace
opaque encoder round-trip axioms with proven identities.

`q = 1024 = 2^10` is a **power of two**, not a prime. Reduction
`mod 1024` is therefore a bit-mask `& 1023` rather than a fold-and-conditional
subtract, and the resulting structure is a **ring** rather than a field —
sufficient for HAWK's ring-multiply kernel which only uses add/sub/mul.

This is the lattice/ring-only analogue of `Util/ZMod3329.lean`,
`Util/ZMod8380417.lean`, and `Util/ZMod127.lean`. The shape is identical
modulo the missing `Fact (Nat.Prime ...)` and `Field` instances (HAWK doesn't
need inverses inside the 4-way kernel — only ring arithmetic).

## API

* `Zq1024 := ZMod 1024` — the verified ring
* `Zq1024.fromNat`, `Zq1024.asNat`, `Zq1024.asInt`, `Zq1024.fromInt` —
  encoders to/from `Nat`/`Int`
* `Zq1024.fromInt_asInt`, `Zq1024.fromNat_asNat` — proved round-trip
  identities used by bridge proofs to discharge previously-axiomatised
  encoder round-trips.
-/

set_option autoImplicit false

namespace CatCrypt.Util

/-- The HAWK per-lane modulus ring. An `abbrev` so the `ZMod` ring/comm-ring
    structure flows through transparently. Note: NOT a field (1024 is not
    prime). -/
abbrev Zq1024 : Type := ZMod 1024

namespace Zq1024

/-! ## Ring axioms — inherited from `Mathlib.Data.ZMod.Basic`

Unlike the prime-modulus siblings (`Zq3329`, `Zq8380417`, `Zq127`), we
do **not** declare a `Fact (Nat.Prime 1024)` instance — 1024 = 2^10 is
composite, so `ZMod 1024` is a ring (not a field). HAWK's ring-multiply
kernel only needs ring operations (add, sub, mul), which work without
the field structure. -/

/-- `Zq1024` is a commutative ring. -/
example : CommRing Zq1024 := inferInstance

/-! ## Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod 1024) into `Zq1024`. -/
def fromNat (n : Nat) : Zq1024 := (n : ZMod 1024)

/-- Project a `Zq1024` element to a `Nat` in `[0..1023]` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Zq1024) : Nat := ZMod.val g

/-- Project a `Zq1024` element to an `Int`. -/
def asInt (g : Zq1024) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Zq1024` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Zq1024 := (i : ZMod 1024)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Zq1024) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Zq1024) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..1024)`. -/
theorem asNat_lt (g : Zq1024) : asNat g < 1024 := by
  unfold asNat
  exact ZMod.val_lt g

end Zq1024

end CatCrypt.Util
