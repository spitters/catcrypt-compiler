/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMac
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMac
public meta import CatCrypt.Crypto.Util.ZMod65536
public import CatCrypt.Crypto.Util.ZMod65536

/-!
# C4 fan-out: the emitted Frodo MAC leaf EQUALS the abstract `Zq65536` ring op

`CompileFromHaxFrodoMac.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `frodoMacForm` — the integer multiply-accumulate
`acc + a·b` followed by the `& 0xFFFF` mask that is the FrodoKEM `mod 2^16`
reduction. That file ties the emit form to abstract `BitVec` modular arithmetic
`frodoMacForm_eq_mod : frodoMacForm acc a b = (acc + a*b) % 65536#64`.

This module closes the **last hop**: from the `BitVec`-`%` form to the abstract
ring `CatCrypt.Util.Zq65536 = ZMod 65536` that the FrodoKEM matrix–vector
verified reference (`Frodo/FrodoMatmulVerified.lean`) and the security proof
reason over. We prove that, reading the emitted leaf's output back as a ring
element via `Zq65536.fromNat ∘ BitVec.toNat`, it is exactly the `Zq65536` ring
multiply-accumulate `accZ + aZ · bZ` of the elements the inputs encode.

Because the modulus `65536 = 2^16` is a power of two dividing `2^64`, the `&
0xFFFF` mask is *exactly* `% 65536` and projecting `(acc + a*b) % 65536` into
`ZMod 65536` is the ring MAC `↑acc + ↑a · ↑b`. No `decide`/`native_decide` here —
it is the genuine power-of-two reduce identity, lifted to the Mathlib ring
through `ZMod.natCast_*`. Unlike the prime-field GF(127) tie there is **no domain
restriction**: the mask handles full `u16` wraparound for any 64-bit inputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMacTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMac
open CatCrypt.Util

/-- **Frodo MAC emit-form ↔ abstract `Zq65536` ring tie (C4 fan-out).** The
    emitted MAC leaf `frodoMacForm` — read back as a `Zq65536 = ZMod 65536` ring
    element via `Zq65536.fromNat ∘ toNat` — equals the `Zq65536` ring
    multiply-accumulate `accZ + aZ · bZ` of the elements the inputs encode, with
    **no domain restriction** (the `mod 2^16` mask handles full `u16` wraparound).
    Composed with `CompileFromHaxFrodoMac.frodoMac_compiles`, the verified
    compiler's emitted jasmin `Com` therefore computes the FrodoKEM LWE
    matrix–vector inner step (`acc + A[r][c]·s[c] mod 2^16`) that
    `Frodo/FrodoMatmulVerified.matmulRow` sums and the security proof reasons
    over. -/
theorem frodoMacForm_eq_field (acc a b : BitVec 64) :
    Zq65536.fromNat (frodoMacForm acc a b).toNat
      = Zq65536.fromNat acc.toNat
        + Zq65536.fromNat a.toNat * Zq65536.fromNat b.toNat := by
  rw [frodoMacForm_eq_mod acc a b]
  unfold Zq65536.fromNat
  have h65536 : (65536#64 : BitVec 64).toNat = 65536 := by decide
  -- `65536 = 2^16` divides `2^64`, so any intermediate `% 2^64` BitVec wrap is
  -- invisible mod 65536: casting `n % 2^64` into `ZMod 65536` equals casting `n`.
  have hcast : ∀ n : Nat, ((n % 2 ^ 64 : Nat) : ZMod 65536) = (n : ZMod 65536) := by
    intro n
    rw [← ZMod.natCast_mod n 65536, ← ZMod.natCast_mod (n % 2 ^ 64) 65536,
      Nat.mod_mod_of_dvd n (by norm_num)]
  -- the BitVec `%` projects to `ZMod 65536` as the ring residue of `acc + a*b`
  rw [BitVec.toNat_umod, h65536, ZMod.natCast_mod, BitVec.toNat_add, BitVec.toNat_mul,
    hcast, Nat.cast_add, hcast, Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMacTie
