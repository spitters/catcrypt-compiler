/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMayoGf16
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMayoGf16
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256
public meta import CatCrypt.Crypto.Util.Gf16
public import CatCrypt.Crypto.Util.Gf16
public meta import CatCrypt.Crypto.Util.Gf256
public import CatCrypt.Crypto.Util.Gf256

/-!
# #607 Phase 3d: the emitted GF(16) multiply leaf EQUALS the abstract field op

`CompileFromHaxMayoGf16.lean` proves that the verified compiler *emits* a jasmin
`Com` whose `BitVec 32` denotation is `gf16MulSpec` — the bit-serial straight
line the extracted source computes (per-step `xtime` reduction by the constant
`poly = 0x3 = x+1`, since `x⁴ ≡ x+1` in `GF(2)[x]/(x⁴+x+1)`). That file ties the
leaf to its own closed form, but the field-product agreement was checked only on
two **sample** KAT vectors (`gf16MulSpec_kat`: `7·11=4`, `3·6=0xa`).

This module closes the gap to a **universal** abstract-spec tie. The abstract
GF(16) field multiply is `CatCrypt.Util.Gf16.mul : BitVec 4 → BitVec 4 → BitVec 4`
(`Gf16 := BitVec 4`), defined by lifting to a `BitVec 8` polynomial product and
reducing **at the end** by `0x13 = x⁴+x+1` (`Gf16.mulAux`). The emit-form
`gf16MulSpec` instead reduces **per step** by `0x3` over the low nibble of a
`BitVec 32`. The two straight lines are operationally different, but compute the
same field element. We prove the tie holds for **all** inputs.

## Representation coercion

`gf16MulSpec : BitVec 32 → BitVec 32 → BitVec 32` reads the low nibble of each
operand and returns the product in the low nibble (its body ends `… &&& lo4`).
`Gf16.mul` works on `BitVec 4`. The clean statement is, for every `a b : BitVec 32`:

  `(gf16MulSpec a b).setWidth 4 = Gf16.mul (a.setWidth 4) (b.setWidth 4)`

Both sides depend only on the low 4 bits of `a` and `b`, so this is a finite
identity over `16 × 16 = 256` nibble pairs, closed by `decide` after reducing
both sides to the 4-bit normal form.

## Method

`gf16MulSpec` is stated over `BitVec 32` with a `4294967295` mask constant; a
direct `decide` over all `2³²` inputs is infeasible. We first reduce to the
4-bit core via `gf16MulSpec_setWidth4`, which expresses `(gf16MulSpec a b)`
truncated to 4 bits in terms of `a.setWidth 4` and `b.setWidth 4` (proved by
`bv_decide`: both sides are pure `BitVec` straight lines, and the high bits of
the `32`-bit operands are masked away by the `&&& lo4` / `&&& one` steps). The
core tie `gf16MulCore = Gf16.mul` is then `decide` over `BitVec 4 × BitVec 4`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf16AbstractTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMayoGf16
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256
open CatCrypt.Util

/-- The emit-form GF(16) multiply restricted to its 4-bit core: the same
    bit-serial straight line as `gf16MulSpec`, but over `BitVec 4` operands.
    `gf16MulSpec` masks both operands' high bits away (`b >>> k &&& one`,
    `sh := a &&& lo4`), so its low-nibble output depends only on these. -/
def gf16MulCore (a b : BitVec 4) : BitVec 4 :=
  (gf16MulSpec (a.setWidth 32) (b.setWidth 32)).setWidth 4

/-- The emit-form spec, truncated to 4 bits, depends only on the low nibbles of
    its `BitVec 32` operands — i.e. it factors through `gf16MulCore` on the
    truncations. Pure `BitVec` straight-line identity, closed by `bv_decide`. -/
theorem gf16MulSpec_setWidth4 (a b : BitVec 32) :
    (gf16MulSpec a b).setWidth 4
      = gf16MulCore (a.setWidth 4) (b.setWidth 4) := by
  unfold gf16MulCore gf16MulSpec
  bv_decide

/-- **The core abstract-spec tie.** The emit-form bit-serial GF(16) multiply
    (per-step reduce by `0x3`) equals the abstract field product
    `CatCrypt.Util.Gf16.mul` (end-of-line reduce by `0x13 = x⁴+x+1`) on **all**
    `16 × 16` nibble pairs. Closed by `decide` over `BitVec 4 × BitVec 4`. -/
theorem gf16MulCore_eq_field (a b : BitVec 4) :
    gf16MulCore a b = Gf16.mul a b := by
  revert a b; decide

/-- **Universal GF(16) emit-form ↔ abstract-field tie (#607 Phase 3d).**
    For every `a b : BitVec 32`, the emitted leaf's spec `gf16MulSpec`, read on
    the low nibble, equals the abstract GF(16) field multiply `Gf16.mul`
    (`CatCrypt.Util.Gf16`) on the truncated nibbles. This upgrades the leaf from
    KAT-only (`gf16MulSpec_kat`, two sample vectors) to a genuine universal tie
    to the field op the MAYO/SNOVA spec uses. Composed with
    `CompileFromHaxMayoGf16.gf16Mul_compiles`, the verified compiler's emitted
    jasmin `Com` therefore computes the abstract GF(16) field product. -/
theorem gf16MulSpec_eq_field (a b : BitVec 32) :
    (gf16MulSpec a b).setWidth 4
      = Gf16.mul (a.setWidth 4) (b.setWidth 4) := by
  rw [gf16MulSpec_setWidth4, gf16MulCore_eq_field]

/-- The KAT vectors of `CompileFromHaxMayoGf16.gf16MulSpec_kat`, re-derived as a
    special case of the universal field tie: `7 · 11 = 4` and `3 · 6 = 0xa` over
    `GF(2)[x]/(x⁴+x+1)`, now via `Gf16.mul`. -/
theorem gf16MulSpec_kat_via_field :
    Gf16.mul (0x7 : BitVec 4) (0xb : BitVec 4) = (0x4 : BitVec 4)
      ∧ Gf16.mul (0x3 : BitVec 4) (0x6 : BitVec 4) = (0xa : BitVec 4) := by
  decide

/-! ## GF(256) follow-up: the UOV/AES field multiply leaf tie

The same upgrade for the GF(256) = `GF(2)[x]/(x⁸+x⁴+x³+x+1)` (AES / UOV Rijndael
field, poly `0x11b`, reduce constant `0x1b`) leaf of
`CompileFromHaxUovGf256.lean`. The emit-form `gf256MulSpec : BitVec 32 → BitVec 32
→ BitVec 32` runs eight bit-steps over the low byte with a per-step `(0−carry) &&&
0x1b` reduce; the abstract field op is `CatCrypt.Util.Gf256.mul : BitVec 8 →
BitVec 8 → BitVec 8` (Russian-peasant shift-and-XOR, same `0x1b` reduce).

`gf256MulSpec` outputs the product in the low byte (`… &&& 0xff`), so the tie is
on the 8-bit truncation. The core tie ranges over `256 × 256 = 65536` byte pairs,
so it is closed by `native_decide` (kernel `decide` would be too slow at 16 bits);
the `BitVec 32 → BitVec 8` reduction is again a pure `bv_decide`. -/

/-- The emit-form GF(256) multiply restricted to its 8-bit core. -/
def gf256MulCore (a b : BitVec 8) : BitVec 8 :=
  (gf256MulSpec (a.setWidth 32) (b.setWidth 32)).setWidth 8

/-- `gf256MulSpec`, truncated to 8 bits, depends only on the low bytes of its
    `BitVec 32` operands. Pure `BitVec` straight line, closed by `bv_decide`. -/
theorem gf256MulSpec_setWidth8 (a b : BitVec 32) :
    (gf256MulSpec a b).setWidth 8
      = gf256MulCore (a.setWidth 8) (b.setWidth 8) := by
  unfold gf256MulCore gf256MulSpec gf256Step
  bv_decide

/-- **The GF(256) core abstract-spec tie.** The emit-form bit-serial GF(256)
    multiply equals the abstract AES-field product `CatCrypt.Util.Gf256.mul` on
    all `256 × 256` byte pairs. Closed by `native_decide` over `BitVec 8 ×
    BitVec 8`. -/
theorem gf256MulCore_eq_field (a b : BitVec 8) :
    gf256MulCore a b = Gf256.mul a b := by
  revert a b; native_decide

/-- **Universal GF(256) emit-form ↔ abstract-field tie (#607 Phase 3d, AES /
    UOV field).** For every `a b : BitVec 32`, the emitted leaf's spec
    `gf256MulSpec`, read on the low byte, equals the abstract GF(256) field
    multiply `Gf256.mul` (`CatCrypt.Util.Gf256`) on the truncated bytes.
    Composed with `CompileFromHaxUovGf256.gf256Mul_compiles`, the verified
    compiler's emitted jasmin `Com` computes the abstract GF(256) field
    product. -/
theorem gf256MulSpec_eq_field (a b : BitVec 32) :
    (gf256MulSpec a b).setWidth 8
      = Gf256.mul (a.setWidth 8) (b.setWidth 8) := by
  rw [gf256MulSpec_setWidth8, gf256MulCore_eq_field]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf16AbstractTie
