/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# #606 fan-out: the emitted Mersenne-31 multiply leaf EQUALS the abstract field op

`CompileFromHaxMersenne31.lean` proves the verified compiler *emits* a jasmin
`Com` whose `BitVec 64` denotation is `m31MulFold` — the Mersenne `2³¹ ≡ 1`
double-fold plus branch-free conditional subtract — and ties the emit form to
abstract `BitVec` modular multiply
`m31MulFold_eq_mod : m31MulFold a b = (a*b) % 2147483647#64` on the residue
domain `a, b < p`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
prime field `Zm31 = ZMod 2147483647` (`p = 2³¹ − 1`, the CircleSTARK /
Plonky3-Mersenne31 base field). Reading the emitted leaf's output back as a
field element via `fromNat ∘ BitVec.toNat`, it is exactly the `Zm31` ring
product of the field elements the inputs encode.

The product `a · b ≤ (2³¹−2)² < 2⁶²` never wraps `2⁶⁴`, so the `BitVec`
multiply is the integer multiply, and `(a·b) % p` projected to `ZMod p` is the
field product `↑a · ↑b`. No `decide`/`native_decide` here — it is the genuine
prime-field reduce identity, lifted to the Mathlib field through
`ZMod.natCast_*`. (The `(a·b) % p` identity itself, `m31MulFold_eq_mod`, is
proved over in the leaf module by **`Nat` arithmetic on `toNat`**, not
`bv_decide` — the #117 Barrett seam SAT-times-out at `p = 2³¹`.)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31

/-- `2147483647 = 2³¹ - 1` is the Mersenne-31 prime, so `ZMod 2147483647` is a
    field. -/
instance fact_prime_m31 : Fact (Nat.Prime 2147483647) := ⟨by native_decide⟩

/-- The Mersenne-31 prime field `GF(2³¹−1)` (CircleSTARK / Plonky3-M31). -/
abbrev Zm31 : Type := ZMod 2147483647

/-- Inject a `Nat` (mod p) into the field. -/
def fromNat (n : Nat) : Zm31 := (n : ZMod 2147483647)

/-- On the residue domain `a, b < p = 2³¹−1`, the `BitVec 64` product is the
    integer product: it never wraps `2⁶⁴` (`a·b ≤ (2³¹−2)² < 2⁶²`). -/
theorem m31_toNat_mul' (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    (a * b).toNat = a.toNat * b.toNat :=
  m31_toNat_mul a b ha hb

/-- **Mersenne-31 emit-form ↔ abstract `Zm31` field tie (#606 fan-out).** On the
    residue domain `a, b < p = 2³¹−1`, the emitted Mersenne-fold leaf
    `m31MulFold` — read back as a `Zm31 = ZMod 2147483647` field element via
    `fromNat ∘ toNat` — equals the `Zm31` field product of the elements the
    inputs encode. Composed with `CompileFromHaxMersenne31.m31Mul_compiles`, the
    verified compiler's emitted jasmin `Com` therefore computes the Mersenne
    `GF(2³¹−1)` base-field multiply (the CircleSTARK / Plonky3-Mersenne31 field).
    The underlying `(a·b) % p` identity is `m31MulFold_eq_mod`, proved by `Nat`
    arithmetic on `toNat` (not `bv_decide`). -/
theorem m31MulFold_eq_field (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    fromNat (m31MulFold a b).toNat
      = fromNat a.toNat * fromNat b.toNat := by
  rw [m31MulFold_eq_mod a b ha hb]
  unfold fromNat
  have hp : (2147483647#64 : BitVec 64).toNat = 2147483647 := by decide
  rw [BitVec.toNat_umod, hp, m31_toNat_mul a b ha hb]
  rw [ZMod.natCast_mod, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
