/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf8191
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf8191
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The emitted GF(8191) multiply leaf EQUALS the abstract field op

`CompileFromHaxGf8191.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `gf8191MulFold` — the Mersenne `2¹³ ≡ 1`
double-fold plus branch-free conditional subtract — and ties the emit form to
abstract `BitVec` modular multiply
`gf8191MulFold_eq_mod : gf8191MulFold a b = (a*b) % 8191#64` on the residue
domain `a, b < 8191`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
prime field `Zq8191 = ZMod 8191`. Reading the emitted leaf's output back as a
field element via `fromNat ∘ BitVec.toNat`, it is exactly the `Zq8191` ring
product of the field elements the inputs encode.

The product `a · b ≤ 8190² = 67076100 < 2⁶⁴` never wraps, so the `BitVec`
multiply is the integer multiply, and `(a·b) % 8191` projected to `ZMod 8191`
is the field product `↑a · ↑b`. No `decide`/`native_decide` here — it is the
prime-field reduce identity, lifted to the Mathlib field through
`ZMod.natCast_*`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf8191Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf8191

/-- `8191 = 2¹³ - 1` is the Mersenne-13 prime, so `ZMod 8191` is a field. -/
instance fact_prime_8191 : Fact (Nat.Prime 8191) := ⟨by native_decide⟩

/-- The GF(8191) prime field. -/
abbrev Zq8191 : Type := ZMod 8191

/-- Inject a `Nat` (mod 8191) into the field. -/
def fromNat (n : Nat) : Zq8191 := (n : ZMod 8191)

/-- On the residue domain `a, b < 8191`, the `BitVec 64` product is the integer
    product: it never wraps `2⁶⁴` (`a·b ≤ 8190² = 67076100`). -/
theorem gf8191_toNat_mul (a b : BitVec 64) (ha : a < 8191#64) (hb : b < 8191#64) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h1 : a.toNat < 8191 := by bv_omega
  have h2 : b.toNat < 8191 := by bv_omega
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat ≤ 8190 * 8190 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

/-- **GF(8191) emit-form ↔ abstract `Zq8191` field tie.** On the
    residue domain `a, b < 8191`, the emitted Mersenne-fold leaf `gf8191MulFold`
    — read back as a `Zq8191 = ZMod 8191` field element via `fromNat ∘ toNat` —
    equals the `Zq8191` field product of the elements the inputs encode. Composed
    with `CompileFromHaxGf8191.gf8191Mul_compiles`, the verified compiler's
    emitted jasmin `Com` therefore computes the Mersenne `GF(2¹³-1)` base-field
    multiply. -/
theorem gf8191MulFold_eq_field (a b : BitVec 64)
    (ha : a < 8191#64) (hb : b < 8191#64) :
    fromNat (gf8191MulFold a b).toNat
      = fromNat a.toNat * fromNat b.toNat := by
  rw [gf8191MulFold_eq_mod a b ha hb]
  unfold fromNat
  have h8191 : (8191#64 : BitVec 64).toNat = 8191 := by decide
  rw [BitVec.toNat_umod, h8191, gf8191_toNat_mul a b ha hb]
  rw [ZMod.natCast_mod, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf8191Tie
