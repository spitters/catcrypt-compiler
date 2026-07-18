/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192
import CatCrypt.Crypto.Util.ZMod8192

/-!
# #606 fan-out: the emitted Z/8192Z multiply leaf EQUALS the abstract ring op

`CompileFromHaxRing8192.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `ring8192MulMask` — the integer multiply plus
low-13-bit mask `& 8191` — and ties it to abstract `BitVec` modular multiply
`ring8192MulMask_eq_mod : ring8192MulMask a b = (a*b) % 8192#64` on
`a, b < 8192`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
coefficient **ring** `Util.Zq8192 = ZMod 8192` that the NTRU-HRSS ring-multiply
bridge reasons over. Reading the emitted leaf's output back as a ring element via
`Zq8192.fromNat ∘ BitVec.toNat`, it is exactly the `Zq8192` ring product of the
elements the inputs encode.

The product `a · b ≤ 8191² = 67092481 < 2⁶⁴` never wraps, so the `BitVec`
multiply is the integer multiply, and `(a·b) % 8192` projected to `ZMod 8192` is
the ring product `↑a · ↑b`. The genuine power-of-two reduce identity, lifted to
the Mathlib ring through `ZMod.natCast_*`. Unlike the prime-field ties this is a
**ring** (`8192 = 2¹³` is composite), reusing the committed `Util/ZMod8192.lean`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192
open CatCrypt.Util

/-- On the residue domain `a, b < 8192`, the `BitVec 64` product is the integer
    product: it never wraps `2⁶⁴` (`a·b ≤ 8191² = 67092481`). -/
theorem ring8192_toNat_mul (a b : BitVec 64) (ha : a < 8192#64) (hb : b < 8192#64) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h1 : a.toNat < 8192 := by bv_omega
  have h2 : b.toNat < 8192 := by bv_omega
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat ≤ 8191 * 8191 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

/-- **Z/8192Z emit-form ↔ abstract `Zq8192` ring tie (#606 fan-out).** On the
    residue domain `a, b < 8192`, the emitted mask leaf `ring8192MulMask` — read
    back as a `Zq8192 = ZMod 8192` ring element via `Zq8192.fromNat ∘ toNat` —
    equals the `Zq8192` ring product of the elements the inputs encode. Composed
    with `CompileFromHaxRing8192.ring8192Mul_compiles`, the verified compiler's
    emitted jasmin `Com` therefore computes the NTRU-HRSS coefficient-ring
    (`Z/2¹³Z`) multiply that the NTRU-HRSS bridge reasons over. -/
theorem ring8192MulMask_eq_ring (a b : BitVec 64)
    (ha : a < 8192#64) (hb : b < 8192#64) :
    Zq8192.fromNat (ring8192MulMask a b).toNat
      = Zq8192.fromNat a.toNat * Zq8192.fromNat b.toNat := by
  rw [ring8192MulMask_eq_mod a b ha hb]
  unfold Zq8192.fromNat
  have h8192 : (8192#64 : BitVec 64).toNat = 8192 := by decide
  rw [BitVec.toNat_umod, h8192, ring8192_toNat_mul a b ha hb]
  rw [ZMod.natCast_mod, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192Tie
