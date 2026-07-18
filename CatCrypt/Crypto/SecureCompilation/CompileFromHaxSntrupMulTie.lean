/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMul
import CatCrypt.Crypto.Util.ZMod4591

/-!
# C4 fan-out: the emitted sntrup MAC leaf EQUALS the abstract `Zq4591` field op

`CompileFromHaxSntrupMul.lean` proves the verified compiler *emits* a jasmin
`Com` whose `BitVec 64` denotation is `sntrupMacForm` — the integer
multiply-accumulate `acc + a·b`, carried unreduced (sntrup761's modulus
`q = 4591` is **prime**, not a power of two, so there is no bitwise-mask reduce;
the mod-`4591` representative is taken at coefficient readback).

This module closes the **last hop**: from the `BitVec` MAC form to the abstract
prime field `CatCrypt.Util.Zq4591 = ZMod 4591` that the Streamlined NTRU Prime
verified reference (`NTRU/Sntrup761MulVerified.coeffSum`) and the security proof
(`NTRU/Security.lean`, via the SXY transform) reason over. We prove that, reading
the emitted leaf's output back as a field element via
`Zq4591.fromNat ∘ BitVec.toNat`, it is exactly the `Zq4591` field
multiply-accumulate `accZ + aZ · bZ` of the elements the inputs encode.

## The prime-modulus differential (honest)

Unlike the FrodoKEM (`mod 2^16`) and NTRU-HRSS (`mod 2^13`) ties, `4591` is a
**prime that does not divide `2^64`**, so the power-of-two "cast the `% 2^64`
wrap away" lemma is *false* here: a `BitVec 64` wrap corrupts the mod-`4591`
residue. The tie therefore carries a **domain restriction** (exactly like the
GF(127) prime-field tie): the schoolbook coefficient inputs are mod-`4591`
residues (`a, b < 4591`) and the running accumulator is bounded (`acc < 2^63`),
so neither the product `a·b ≤ 4590² < 2^25` nor the accumulate `acc + a·b < 2^64`
wraps. On this domain the `BitVec` ops are the integer ops, and projecting into
`ZMod 4591` is the field MAC `↑acc + ↑a · ↑b`. The `acc < 2^63` bound is
generous: a `width = 16` schoolbook column sums 16 products each `< 4591²`, so
the true accumulator never exceeds `16 · 4591² ≈ 3.4·10^8 < 2^63`.

No `decide`/`native_decide` — it is the genuine prime-field reduce identity,
lifted to the Mathlib field through `ZMod.natCast_*`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMulTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMul
open CatCrypt.Util

/-- On the residue domain `a, b < 4591`, the `BitVec 64` product is the integer
    product: it never wraps `2⁶⁴` (`a·b ≤ 4590² = 21068100 < 2²⁵`). -/
theorem sntrup_toNat_mul (a b : BitVec 64) (ha : a < 4591#64) (hb : b < 4591#64) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h1 : a.toNat < 4591 := by bv_omega
  have h2 : b.toNat < 4591 := by bv_omega
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat ≤ 4590 * 4590 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

/-- On the domain `a, b < 4591`, `acc < 2^63`, the `BitVec 64` MAC `acc + a·b`
    is the integer MAC: neither the product (`< 2²⁵`) nor the sum (`< 2⁶³ + 2²⁵
    < 2⁶⁴`) wraps `2⁶⁴`. -/
theorem sntrup_toNat_mac (acc a b : BitVec 64)
    (hacc : acc.toNat < 2 ^ 63) (ha : a < 4591#64) (hb : b < 4591#64) :
    (acc + a * b).toNat = acc.toNat + a.toNat * b.toNat := by
  have hmul := sntrup_toNat_mul a b ha hb
  have h1 : a.toNat < 4591 := by bv_omega
  have h2 : b.toNat < 4591 := by bv_omega
  have hprodlt : a.toNat * b.toNat ≤ 4590 * 4590 := Nat.mul_le_mul (by omega) (by omega)
  have hsumlt : acc.toNat + a.toNat * b.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, hmul]
  exact Nat.mod_eq_of_lt hsumlt

/-- **sntrup MAC emit-form ↔ abstract `Zq4591` field tie (C4 fan-out).** On the
    schoolbook domain (`a, b < 4591` mod-`4591` residues, `acc < 2^63` partial
    sum), the emitted MAC leaf `sntrupMacForm` — read back as a `Zq4591 = ZMod
    4591` field element via `Zq4591.fromNat ∘ toNat` — equals the `Zq4591` field
    multiply-accumulate `accZ + aZ · bZ` of the elements the inputs encode.
    Composed with `CompileFromHaxSntrupMul.sntrupMac_compiles`, the verified
    compiler's emitted jasmin `Com` therefore computes the Streamlined NTRU Prime
    schoolbook-convolution inner step (`acc + a[i]·b[j]`, reduced mod `4591` at
    readback) that `NTRU/Sntrup761MulVerified.coeffSum` sums and the security
    proof reasons over. The domain restriction is the prime-modulus differential
    (cf. the GF(127) tie): `4591` does not divide `2^64`, so a wrap would corrupt
    the residue — the schoolbook bounds keep every intermediate below `2^64`. -/
theorem sntrupMacForm_eq_ring (acc a b : BitVec 64)
    (hacc : acc.toNat < 2 ^ 63) (ha : a < 4591#64) (hb : b < 4591#64) :
    Zq4591.fromNat (sntrupMacForm acc a b).toNat
      = Zq4591.fromNat acc.toNat
        + Zq4591.fromNat a.toNat * Zq4591.fromNat b.toNat := by
  unfold sntrupMacForm Zq4591.fromNat
  rw [sntrup_toNat_mac acc a b hacc ha hb]
  push_cast
  ring

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMulTie
