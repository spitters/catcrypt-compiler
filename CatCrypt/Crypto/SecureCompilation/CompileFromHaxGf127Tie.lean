/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf127
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf127
public meta import CatCrypt.Crypto.Util.ZMod127
public import CatCrypt.Crypto.Util.ZMod127

/-!
# #607 fan-out: the emitted GF(127) multiply leaf EQUALS the abstract field op

`CompileFromHaxGf127.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `gf127MulFold` — the Mersenne `128 ≡ 1`
double-fold plus branch-free conditional subtract that the QR-UOV and CROSS
references render for the `GF(127) = ℤ/127ℤ` Mersenne base-field multiply. That
file ties the emit form to abstract `BitVec` modular multiply
`gf127MulFold_eq_mod : gf127MulFold a b = (a*b) % 127#64` on the residue domain
`a, b < 127`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
prime field `CatCrypt.Util.Zq127 = ZMod 127` that the QR-UOV / CROSS security
proofs reason over (their `SurfaceDeps`/syndrome arithmetic lives in `Zq127`, the
Mathlib field). We prove that, reading the emitted leaf's output back as a field
element via `Zq127.fromNat ∘ BitVec.toNat`, it is exactly the `Zq127` ring product
of the field elements the inputs encode.

The product `a · b ≤ 126² = 15876 < 2⁶⁴` never wraps, so the `BitVec` multiply is
the integer multiply, and `(a·b) % 127` projected to `ZMod 127` is the field
product `↑a · ↑b`. No `decide`/`native_decide` here — it is the genuine prime-field
reduce identity, lifted to the Mathlib field through `ZMod.natCast_*`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf127Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf127
open CatCrypt.Util

/-- On the residue domain `a, b < 127`, the `BitVec 64` product is the integer
    product: it never wraps `2⁶⁴` (`a·b ≤ 126² = 15876`). -/
theorem gf127_toNat_mul (a b : BitVec 64) (ha : a < 127#64) (hb : b < 127#64) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h1 : a.toNat < 127 := by bv_omega
  have h2 : b.toNat < 127 := by bv_omega
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat ≤ 126 * 126 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

/-- **GF(127) emit-form ↔ abstract `Zq127` field tie (#607 fan-out).** On the
    residue domain `a, b < 127`, the emitted Mersenne-fold leaf `gf127MulFold` —
    read back as a `Zq127 = ZMod 127` field element via `Zq127.fromNat ∘ toNat` —
    equals the `Zq127` field product of the elements the inputs encode. Composed
    with `CompileFromHaxGf127.gf127Mul_compiles`, the verified compiler's emitted
    jasmin `Com` therefore computes the QR-UOV / CROSS base-field (`ℤ/127ℤ`)
    multiply that those security proofs reason over. -/
theorem gf127MulFold_eq_field (a b : BitVec 64)
    (ha : a < 127#64) (hb : b < 127#64) :
    Zq127.fromNat (gf127MulFold a b).toNat
      = Zq127.fromNat a.toNat * Zq127.fromNat b.toNat := by
  rw [gf127MulFold_eq_mod a b ha hb]
  unfold Zq127.fromNat
  have h127 : (127#64 : BitVec 64).toNat = 127 := by decide
  rw [BitVec.toNat_umod, h127, gf127_toNat_mul a b ha hb]
  rw [ZMod.natCast_mod, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf127Tie
