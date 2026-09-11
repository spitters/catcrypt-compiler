/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# #606 fan-out: the emitted GF(524287) multiply leaf EQUALS the abstract field op

`CompileFromHaxGf524287.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `gf524287MulFold` — the Mersenne `2¹⁹ ≡ 1`
double-fold plus branch-free conditional subtract — and ties the emit form to
abstract `BitVec` modular multiply
`gf524287MulFold_eq_mod : gf524287MulFold a b = (a*b) % 524287#64` on the residue
domain `a, b < 524287`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
prime field `Zq524287 = ZMod 524287` (`524287 = 2¹⁹ − 1`, the Mersenne-19 prime).
Reading the emitted leaf's output back as a field element via
`fromNat ∘ BitVec.toNat`, it is exactly the `Zq524287` ring product of the field
elements the inputs encode.

The product `a · b ≤ 524286² < 2³⁸` never wraps `2⁶⁴`, so the `BitVec` multiply
is the integer multiply, and `(a·b) % 524287` projected to `ZMod 524287` is the
field product `↑a · ↑b`. The genuine prime-field reduce identity, lifted to the
Mathlib field through `ZMod.natCast_*`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287

/-- `524287 = 2¹⁹ - 1` is the Mersenne-19 prime, so `ZMod 524287` is a field. -/
instance fact_prime_524287 : Fact (Nat.Prime 524287) := ⟨by native_decide⟩

/-- The GF(524287) prime field. -/
abbrev Zq524287 : Type := ZMod 524287

/-- Inject a `Nat` (mod 524287) into the field. -/
def fromNat (n : Nat) : Zq524287 := (n : ZMod 524287)

/-- On the residue domain `a, b < 524287`, the `BitVec 64` product is the integer
    product: it never wraps `2⁶⁴` (`a·b ≤ 524286² < 2³⁸`). -/
theorem gf524287_toNat_mul (a b : BitVec 64)
    (ha : a < 524287#64) (hb : b < 524287#64) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h1 : a.toNat < 524287 := by bv_omega
  have h2 : b.toNat < 524287 := by bv_omega
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat ≤ 524286 * 524286 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

/-- **GF(524287) emit-form ↔ abstract `Zq524287` field tie (#606 fan-out).** On
    `a, b < 524287`, the emitted Mersenne-fold leaf `gf524287MulFold` — read back
    as a `Zq524287 = ZMod 524287` field element via `fromNat ∘ toNat` — equals the
    `Zq524287` field product of the elements the inputs encode. Composed with
    `CompileFromHaxGf524287.gf524287Mul_compiles`, the verified compiler's emitted
    jasmin `Com` computes the Mersenne `GF(2¹⁹−1)` base-field multiply. -/
theorem gf524287MulFold_eq_field (a b : BitVec 64)
    (ha : a < 524287#64) (hb : b < 524287#64) :
    fromNat (gf524287MulFold a b).toNat
      = fromNat a.toNat * fromNat b.toNat := by
  rw [gf524287MulFold_eq_mod a b ha hb]
  unfold fromNat
  have hp : (524287#64 : BitVec 64).toNat = 524287 := by decide
  rw [BitVec.toNat_umod, hp, gf524287_toNat_mul a b ha hb]
  rw [ZMod.natCast_mod, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287Tie
