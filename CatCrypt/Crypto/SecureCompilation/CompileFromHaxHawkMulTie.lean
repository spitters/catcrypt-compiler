/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMul
import CatCrypt.Crypto.Util.ZMod1024

/-!
# C4 fan-out: the emitted HAWK MAC leaf EQUALS the abstract `Zq1024` ring op

`CompileFromHaxHawkMul.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `hawkMacForm` — the integer multiply-accumulate
`acc + a·b` followed by the `& 0x3FF` mask that is the HAWK `mod 2^10`
reduction. That file ties the emit form to abstract `BitVec` modular arithmetic
`hawkMacForm_eq_mod : hawkMacForm acc a b = (acc + a*b) % 1024#64`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
ring `CatCrypt.Util.Zq1024 = ZMod 1024` that the HAWK negacyclic ring-multiply
verified reference (`HAWK/RingMul4WayVerified.lean`) and the security proof
reason over. We prove that, reading the emitted leaf's output back as a ring
element via `Zq1024.fromNat ∘ BitVec.toNat`, it is exactly the `Zq1024` ring
multiply-accumulate `accZ + aZ · bZ` of the elements the inputs encode.

Because the modulus `1024 = 2^10` is a power of two dividing `2^64`, the `&
0x3FF` mask is *exactly* `% 1024` and projecting `(acc + a*b) % 1024` into
`ZMod 1024` is the ring MAC `↑acc + ↑a · ↑b`. No `decide`/`native_decide` here —
it is the genuine power-of-two reduce identity, lifted to the Mathlib ring
through `ZMod.natCast_*`. Like the FrodoKEM (`2^16`) and NTRU-HRSS (`2^13`) ties
(and unlike the prime-field GF(127)/sntrup ties) there is **no domain
restriction**: the mask handles full `Z/1024` wraparound for any 64-bit inputs.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMulTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMul
open CatCrypt.Util

/-- **HAWK MAC emit-form ↔ abstract `Zq1024` ring tie (C4 fan-out).** The
    emitted MAC leaf `hawkMacForm` — read back as a `Zq1024 = ZMod 1024` ring
    element via `Zq1024.fromNat ∘ toNat` — equals the `Zq1024` ring
    multiply-accumulate `accZ + aZ · bZ` of the elements the inputs encode, with
    **no domain restriction** (the `mod 2^10` mask handles full `Z/1024`
    wraparound). Composed with `CompileFromHaxHawkMul.hawkMac_compiles`, the
    verified compiler's emitted jasmin `Com` therefore computes the HAWK
    negacyclic-convolution inner step (`acc + a[i]·b[(k-i) mod N] mod 2^10`) that
    `HAWK/RingMul4WayVerified.ringMulCoeff` sums and the security proof reasons
    over. -/
theorem hawkMacForm_eq_ring (acc a b : BitVec 64) :
    Zq1024.fromNat (hawkMacForm acc a b).toNat
      = Zq1024.fromNat acc.toNat
        + Zq1024.fromNat a.toNat * Zq1024.fromNat b.toNat := by
  rw [hawkMacForm_eq_mod acc a b]
  unfold Zq1024.fromNat
  have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
  -- `1024 = 2^10` divides `2^64`, so any intermediate `% 2^64` BitVec wrap is
  -- invisible mod 1024: casting `n % 2^64` into `ZMod 1024` equals casting `n`.
  have hcast : ∀ n : Nat, ((n % 2 ^ 64 : Nat) : ZMod 1024) = (n : ZMod 1024) := by
    intro n
    rw [← ZMod.natCast_mod n 1024, ← ZMod.natCast_mod (n % 2 ^ 64) 1024,
      Nat.mod_mod_of_dvd n (by norm_num)]
  -- the BitVec `%` projects to `ZMod 1024` as the ring residue of `acc + a*b`
  rw [BitVec.toNat_umod, h1024, ZMod.natCast_mod, BitVec.toNat_add, BitVec.toNat_mul,
    hcast, Nat.cast_add, hcast, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMulTie
