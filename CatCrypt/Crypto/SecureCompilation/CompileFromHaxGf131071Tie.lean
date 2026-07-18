/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf131071
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# #606 fan-out: the emitted GF(131071) multiply leaf EQUALS the abstract field op

`CompileFromHaxGf131071.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `gf131071MulFold` — the Mersenne `2¹⁷ ≡ 1`
double-fold plus branch-free conditional subtract — and ties it to abstract
`BitVec` modular multiply
`gf131071MulFold_eq_mod : gf131071MulFold a b = (a*b) % 131071#64` on
`a, b < 131071`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
prime field `Zq131071 = ZMod 131071`. The product `a·b ≤ 131070² < 2⁶⁴` never
wraps, so the `BitVec` multiply is the integer multiply, and `(a·b) % 131071`
projected to `ZMod 131071` is the field product `↑a · ↑b`. The genuine
prime-field reduce identity, lifted to the Mathlib field through `ZMod.natCast_*`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf131071Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf131071

/-- `131071 = 2¹⁷ - 1` is the Mersenne-17 prime, so `ZMod 131071` is a field. -/
instance fact_prime_131071 : Fact (Nat.Prime 131071) := ⟨by native_decide⟩

/-- The GF(131071) prime field. -/
abbrev Zq131071 : Type := ZMod 131071

/-- Inject a `Nat` (mod 131071) into the field. -/
def fromNat (n : Nat) : Zq131071 := (n : ZMod 131071)

/-- On the residue domain `a, b < 131071`, the `BitVec 64` product is the integer
    product: it never wraps `2⁶⁴` (`a·b ≤ 131070² < 2³⁵`). -/
theorem gf131071_toNat_mul (a b : BitVec 64)
    (ha : a < 131071#64) (hb : b < 131071#64) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h1 : a.toNat < 131071 := by bv_omega
  have h2 : b.toNat < 131071 := by bv_omega
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat ≤ 131070 * 131070 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

/-- **GF(131071) emit-form ↔ abstract `Zq131071` field tie (#606 fan-out).** On
    `a, b < 131071`, the emitted Mersenne-fold leaf `gf131071MulFold` — read back
    as a `Zq131071 = ZMod 131071` field element via `fromNat ∘ toNat` — equals the
    `Zq131071` field product of the elements the inputs encode. Composed with
    `CompileFromHaxGf131071.gf131071Mul_compiles`, the verified compiler's emitted
    jasmin `Com` computes the Mersenne `GF(2¹⁷-1)` base-field multiply. -/
theorem gf131071MulFold_eq_field (a b : BitVec 64)
    (ha : a < 131071#64) (hb : b < 131071#64) :
    fromNat (gf131071MulFold a b).toNat
      = fromNat a.toNat * fromNat b.toNat := by
  rw [gf131071MulFold_eq_mod a b ha hb]
  unfold fromNat
  have h131071 : (131071#64 : BitVec 64).toNat = 131071 := by decide
  rw [BitVec.toNat_umod, h131071, gf131071_toNat_mul a b ha hb]
  rw [ZMod.natCast_mod, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf131071Tie
