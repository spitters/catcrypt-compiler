/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMul
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMul
public meta import CatCrypt.Crypto.Util.ZMod8192
public import CatCrypt.Crypto.Util.ZMod8192

/-!
# C4 fan-out: the emitted NTRU MAC leaf EQUALS the abstract `Zq8192` ring op

`CompileFromHaxNtruMul.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `ntruMacForm` — the integer multiply-accumulate
`acc + a·b` followed by the `& 0x1FFF` mask that is the NTRU-HRSS `mod 2^13`
reduction. That file ties the emit form to abstract `BitVec` modular arithmetic
`ntruMacForm_eq_mod : ntruMacForm acc a b = (acc + a*b) % 8192#64`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
ring `CatCrypt.Util.Zq8192 = ZMod 8192` that the NTRU-HRSS cyclic ring-multiply
verified reference (`NTRU/NtruhrssRingMulVerified.lean`) and the security proof
reason over. We prove that, reading the emitted leaf's output back as a ring
element via `Zq8192.fromNat ∘ BitVec.toNat`, it is exactly the `Zq8192` ring
multiply-accumulate `accZ + aZ · bZ` of the elements the inputs encode.

Because the modulus `8192 = 2^13` is a power of two dividing `2^64`, the `&
0x1FFF` mask is *exactly* `% 8192` and projecting `(acc + a*b) % 8192` into
`ZMod 8192` is the ring MAC `↑acc + ↑a · ↑b`. No `decide`/`native_decide` here —
it is the genuine power-of-two reduce identity, lifted to the Mathlib ring
through `ZMod.natCast_*`. Like the FrodoKEM tie (and unlike the prime-field
GF(127)/sntrup ties) there is **no domain restriction**: the mask handles full
`Z/8192` wraparound for any 64-bit inputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMulTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMul
open CatCrypt.Util

/-- **NTRU MAC emit-form ↔ abstract `Zq8192` ring tie (C4 fan-out).** The
    emitted MAC leaf `ntruMacForm` — read back as a `Zq8192 = ZMod 8192` ring
    element via `Zq8192.fromNat ∘ toNat` — equals the `Zq8192` ring
    multiply-accumulate `accZ + aZ · bZ` of the elements the inputs encode, with
    **no domain restriction** (the `mod 2^13` mask handles full `Z/8192`
    wraparound). Composed with `CompileFromHaxNtruMul.ntruMac_compiles`, the
    verified compiler's emitted jasmin `Com` therefore computes the NTRU-HRSS
    cyclic-convolution inner step (`acc + a[i]·b[j] mod 2^13`) that
    `NTRU/NtruhrssRingMulVerified.ringMulCoeff` sums and the security proof
    reasons over. -/
theorem ntruMacForm_eq_ring (acc a b : BitVec 64) :
    Zq8192.fromNat (ntruMacForm acc a b).toNat
      = Zq8192.fromNat acc.toNat
        + Zq8192.fromNat a.toNat * Zq8192.fromNat b.toNat := by
  rw [ntruMacForm_eq_mod acc a b]
  unfold Zq8192.fromNat
  have h8192 : (8192#64 : BitVec 64).toNat = 8192 := by decide
  -- `8192 = 2^13` divides `2^64`, so any intermediate `% 2^64` BitVec wrap is
  -- invisible mod 8192: casting `n % 2^64` into `ZMod 8192` equals casting `n`.
  have hcast : ∀ n : Nat, ((n % 2 ^ 64 : Nat) : ZMod 8192) = (n : ZMod 8192) := by
    intro n
    rw [← ZMod.natCast_mod n 8192, ← ZMod.natCast_mod (n % 2 ^ 64) 8192,
      Nat.mod_mod_of_dvd n (by norm_num)]
  -- the BitVec `%` projects to `ZMod 8192` as the ring residue of `acc + a*b`
  rw [BitVec.toNat_umod, h8192, ZMod.natCast_mod, BitVec.toNat_add, BitVec.toNat_mul,
    hcast, Nat.cast_add, hcast, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMulTie
