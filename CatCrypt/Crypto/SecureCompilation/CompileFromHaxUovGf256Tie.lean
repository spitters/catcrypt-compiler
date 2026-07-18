/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256
import CatCrypt.Crypto.Util.Gf256

/-!
# #606 fan-out: the emitted GF(2⁸) carryless multiply leaf EQUALS the abstract field op

`CompileFromHaxUovGf256.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 32` denotation is `gf256MulSpec` — the bit-serial
shift-and-conditional-XOR (Russian-peasant) form for the binary field
`GF(2⁸) = GF(2)[x]/(x⁸+x⁴+x³+x+1)` (reduction polynomial `0x11b`, low byte `0x1b`),
the AES / Rijndael field shared by UOV's `OV-Ip` public map and the binary-field
Category-C MPC-in-the-head arithmetic. That file ties the emit form only to itself
(`gf256MulSrc_denoteScalar`, a `rfl` against the masked shift-and-XOR `def`).

This module closes the **last hop** for the `GF(2^k)` shape, the binary-field
analogue of `CompileFromHaxSdithGf251Tie` for the GF(251) prime: from the
emit-form `gf256MulSpec` to the **abstract Mathlib-style field** the security side
reasons over — `CatCrypt.Util.Gf256.mul`, the verified Russian-peasant
`GF(2)[x]/0x11b` multiply on `BitVec 8` that `Util/Gf256.lean` establishes the
field laws for (`mul_one`, `mul_zero`, `mul_comm`, …).

Unlike the prime field, there is no `%`-reduction identity: the tie is the
**carryless-multiply = field-multiply** equation. The emit form runs at width 32
with the byte confined to the low 8 bits (`sh0 = a &&& 0xff`, every `xtime` masks
`& 0xff`, the output masks `& 0xff`), so reading the leaf's low byte back as a
`Gf256 = BitVec 8` element it is exactly the abstract field product of the input
low bytes. Closed by `native_decide` over the `2¹⁶` byte pairs — the binary-field
sibling of `gf251MulFold_eq_field`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256
open CatCrypt.Util

/-- **GF(2⁸) carryless-mul = field-mul tie (#606 fan-out).** Feeding two field
    bytes `a, b : BitVec 8` (zero-extended into the width-32 emit form), the
    emitted bit-serial leaf `gf256MulSpec` — whose low byte the compiled jasmin
    `Com` computes — equals the abstract `GF(2)[x]/(x⁸+x⁴+x³+x+1)` field multiply
    `Util.Gf256.mul a b` (zero-extended). This is the binary-field analogue of the
    prime-field `gf251MulFold_eq_field`: there is no modular reduction, the
    identity is exactly *carryless polynomial multiply mod `0x11b` = abstract field
    product*. Composed with
    `CompileFromHaxUovGf256.gf256Mul_compiles`, the verified compiler's emitted
    jasmin `Com` therefore computes the AES / UOV `GF(256)` field multiply that the
    `Util.Gf256` field laws (and the UOV bridge) reason over. -/
theorem gf256MulSpec_eq_field :
    ∀ (a b : BitVec 8),
      gf256MulSpec (BitVec.setWidth 32 a) (BitVec.setWidth 32 b)
        = BitVec.setWidth 32 (Gf256.mul a b) := by
  native_decide

/-- The low-byte projection form: reading the emitted leaf's result back as a
    `Gf256 = BitVec 8` element (truncate to the low byte) on byte inputs gives the
    abstract field product directly. A corollary of `gf256MulSpec_eq_field` via the
    `setWidth 8 ∘ setWidth 32` round-trip on the 8-bit result. -/
theorem gf256MulSpec_setWidth8_eq_field (a b : BitVec 8) :
    BitVec.setWidth 8 (gf256MulSpec (BitVec.setWidth 32 a) (BitVec.setWidth 32 b))
      = Gf256.mul a b := by
  rw [gf256MulSpec_eq_field a b]
  simp [BitVec.setWidth_setWidth_of_le]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256Tie
