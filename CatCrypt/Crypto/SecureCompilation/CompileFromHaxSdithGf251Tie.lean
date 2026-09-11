/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSdithGf251
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSdithGf251
public meta import CatCrypt.Crypto.Util.ZMod251
public import CatCrypt.Crypto.Util.ZMod251

/-!
# #607 fan-out: the emitted SDitH GF(251) multiply leaf EQUALS the abstract field op

`CompileFromHaxSdithGf251.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `gf251MulFold` — the Solinas `256 ≡ 5` double-fold
plus branch-free conditional subtract the SDitH-reference renders for the
`GF(251) = ℤ/251ℤ` base-field multiply. That file ties the emit form to abstract
`BitVec` modular multiply `gf251MulFold_eq_mod : gf251MulFold a b = (a*b) % 251#64`
on the residue domain `a, b < 251`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
prime field `CatCrypt.Util.Zq251 = ZMod 251` that the SDitH security proof reasons
over (its `SurfaceDeps`/syndrome arithmetic lives in `Zq251`, the Mathlib field).
We prove that, reading the emitted leaf's output back as a field element via
`Zq251.fromNat ∘ BitVec.toNat`, it is exactly the `Zq251` ring product of the
field elements the inputs encode.

The product `a · b ≤ 250² = 62500 < 2⁶⁴` never wraps, so the `BitVec` multiply is
the integer multiply, and `(a·b) % 251` projected to `ZMod 251` is the field
product `↑a · ↑b`. No `decide`/`native_decide` here — it is the genuine prime-field
reduce identity, lifted to the Mathlib field through `ZMod.natCast_*`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSdithGf251Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSdithGf251
open CatCrypt.Util

/-- On the residue domain `a, b < 251`, the `BitVec 64` product is the integer
    product: it never wraps `2⁶⁴` (`a·b ≤ 250² = 62500`). -/
theorem gf251_toNat_mul (a b : BitVec 64) (ha : a < 251#64) (hb : b < 251#64) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h1 : a.toNat < 251 := by bv_omega
  have h2 : b.toNat < 251 := by bv_omega
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat ≤ 250 * 250 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

/-- **SDitH GF(251) emit-form ↔ abstract `Zq251` field tie (#607 fan-out).** On the
    residue domain `a, b < 251`, the emitted Solinas-fold leaf `gf251MulFold` —
    read back as a `Zq251 = ZMod 251` field element via `Zq251.fromNat ∘ toNat` —
    equals the `Zq251` field product of the elements the inputs encode. Composed
    with `CompileFromHaxSdithGf251.gf251Mul_compiles`, the verified compiler's
    emitted jasmin `Com` therefore computes the SDitH base-field (`ℤ/251ℤ`)
    multiply that the security proof reasons over. -/
theorem gf251MulFold_eq_field (a b : BitVec 64)
    (ha : a < 251#64) (hb : b < 251#64) :
    Zq251.fromNat (gf251MulFold a b).toNat
      = Zq251.fromNat a.toNat * Zq251.fromNat b.toNat := by
  rw [gf251MulFold_eq_mod a b ha hb]
  unfold Zq251.fromNat
  have h251 : (251#64 : BitVec 64).toNat = 251 := by decide
  rw [BitVec.toNat_umod, h251, gf251_toNat_mul a b ha hb]
  -- `(↑((a.toNat*b.toNat) % 251) : ZMod 251) = ↑(a.toNat*b.toNat)`, then split the cast
  rw [ZMod.natCast_mod, Nat.cast_mul]
