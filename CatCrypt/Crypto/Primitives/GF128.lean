/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# GF(2^128) Arithmetic for GHASH

Constructive implementation of GF(2^128) multiplication used in
AES-GCM's GHASH universal hash (NIST SP 800-38D, Algorithm 1).

The reducing polynomial is `x^128 + x^7 + x^2 + x + 1`, represented
in bit-reflected form as `R = 0xE100...00`.

All definitions are marked `@[irreducible]` after the section, to prevent
the kernel from attempting to evaluate 128-iteration loops during proof
checking.

## References

* NIST SP 800-38D, Section 6.3 — Multiplication Operation on Blocks
* McGrew, Viega — *The Galois/Counter Mode of Operation (GCM)*, 2004
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.GF128

/-! ## Core Definitions -/

/-- The GCM reducing polynomial in bit-reflected form:
    `R = 0xE1000000000000000000000000000000`.
    Represents `x^128 + x^7 + x^2 + x + 1` under MSB-first bit ordering. -/
def gf128R : BitVec 128 := 0xE1000000000000000000000000000000#128

/-- One step of the GCM multiplication algorithm (SP 800-38D, Algorithm 1).

    Given accumulator `z`, running value `v`, and bit `xi`:
    - If `xi = 1`, XOR `v` into `z`
    - Shift `v` right; if the lost bit was 1, reduce by `R` -/
def gf128_step (z v : BitVec 128) (xi : Bool) : BitVec 128 × BitVec 128 :=
  let z' := if xi then z ^^^ v else z
  let v' := if v.getLsbD 0 then (v >>> 1) ^^^ gf128R else v >>> 1
  (z', v')

/-- GF(2^128) multiplication (NIST SP 800-38D, Algorithm 1).

    Multiplies `a` and `b` in GF(2^128) using the bit-reflected
    reduction polynomial. Iterates MSB-first over the bits of `a`. -/
def gf128_mul (a b : BitVec 128) : BitVec 128 :=
  let acc := Fin.foldl 128 (init := (0#128, b)) fun (z, v) (i : Fin 128) =>
    gf128_step z v (a.getLsbD (127 - i.val))
  acc.1

/-- XOR two 128-bit blocks (convenience wrapper). -/
def gf128_xor (a b : BitVec 128) : BitVec 128 := a ^^^ b

/-! ## Seal the definitions

After this point, `simp`/`rfl`/`decide`/`norm_num` will not attempt to
unfold these definitions. Use `unfold gf128_mul` or `delta gf128_mul`
explicitly when needed. -/

attribute [irreducible] gf128_mul gf128_step gf128R

end CatCrypt.Crypto.Primitives.GF128
