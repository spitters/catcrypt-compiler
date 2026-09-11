/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSnovaGf16
public import CatCrypt.Crypto.Util.Gf16

/-!
# #607 fan-out: the emitted SNOVA GF(16) multiply leaf EQUALS the abstract field op

`CompileFromHaxSnovaGf16.lean` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 32` denotation is `snovaGf16MulSpec` — the bit-serial straight line
the SNOVA-reference computes per ring-dot term (per-step `xtime` reduction by the
constant `poly = 0x3 = x+1`, since `x⁴ ≡ x+1` in `GF(2)[x]/(x⁴+x+1)`). That file
ties the leaf to its own closed form and checks two **sample** KAT vectors
(`snovaGf16MulSpec_kat`: `7·11 = 4`, `3·6 = 0xa`).

This module closes the gap to a **universal** abstract-spec tie for SNOVA,
mirroring `CompileFromHaxGf16AbstractTie` (which does the same for the MAYO leaf).
The abstract GF(16) field multiply is `CatCrypt.Util.Gf16.mul : BitVec 4 →
BitVec 4 → BitVec 4` (`Gf16 := BitVec 4`), defined by lifting to a `BitVec 8`
polynomial product and reducing **at the end** by `0x13 = x⁴+x+1`. The emit-form
`snovaGf16MulSpec` instead reduces **per step** by `0x3` over the low nibble of a
`BitVec 32`. The two straight lines are operationally different, but compute the
same field element; we prove the tie holds for **all** inputs.

`snovaGf16MulSpec` is byte-for-byte the same field arithmetic as MAYO's
`gf16MulSpec` (SNOVA and MAYO use the same `GF(2)[x]/(x⁴+x+1)` field; the
matrix-ring/rank only sets the index walk that selects the per-term operands), so
this tie corroborates the MAYO tie on the SNOVA-named leaf. The core tie ranges
over `16 × 16 = 256` nibble pairs (`decide`); the `BitVec 32 → BitVec 4`
truncation is a pure `bv_decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSnovaGf16Tie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSnovaGf16
open CatCrypt.Util

/-- The emit-form SNOVA GF(16) multiply restricted to its 4-bit core: the same
    bit-serial straight line as `snovaGf16MulSpec`, but over `BitVec 4` operands.
    `snovaGf16MulSpec` masks both operands' high bits away, so its low-nibble
    output depends only on these. -/
def snovaGf16MulCore (a b : BitVec 4) : BitVec 4 :=
  (snovaGf16MulSpec (a.setWidth 32) (b.setWidth 32)).setWidth 4

/-- The emit-form spec, truncated to 4 bits, depends only on the low nibbles of
    its `BitVec 32` operands — i.e. it factors through `snovaGf16MulCore` on the
    truncations. Pure `BitVec` straight-line identity, closed by `bv_decide`. -/
theorem snovaGf16MulSpec_setWidth4 (a b : BitVec 32) :
    (snovaGf16MulSpec a b).setWidth 4
      = snovaGf16MulCore (a.setWidth 4) (b.setWidth 4) := by
  unfold snovaGf16MulCore snovaGf16MulSpec
  bv_decide

/-- **The core abstract-spec tie.** The emit-form bit-serial SNOVA GF(16) multiply
    (per-step reduce by `0x3`) equals the abstract field product
    `CatCrypt.Util.Gf16.mul` (end-of-line reduce by `0x13 = x⁴+x+1`) on **all**
    `16 × 16` nibble pairs. Closed by `decide` over `BitVec 4 × BitVec 4`. -/
theorem snovaGf16MulCore_eq_field (a b : BitVec 4) :
    snovaGf16MulCore a b = Gf16.mul a b := by
  revert a b; decide

/-- **Universal SNOVA GF(16) emit-form ↔ abstract-field tie (#607 fan-out).**
    For every `a b : BitVec 32`, the emitted leaf's spec `snovaGf16MulSpec`, read
    on the low nibble, equals the abstract GF(16) field multiply `Gf16.mul`
    (`CatCrypt.Util.Gf16`) on the truncated nibbles. This upgrades the SNOVA leaf
    from KAT-only (`snovaGf16MulSpec_kat`, two sample vectors) to a genuine
    universal tie to the field op the SNOVA ring-dot multiply-accumulate is built
    from. Composed with `CompileFromHaxSnovaGf16.snovaGf16Mul_compiles`, the
    verified compiler's emitted jasmin `Com` therefore computes the abstract
    GF(16) field product per ring-dot term. -/
theorem snovaGf16MulSpec_eq_field (a b : BitVec 32) :
    (snovaGf16MulSpec a b).setWidth 4
      = Gf16.mul (a.setWidth 4) (b.setWidth 4) := by
  rw [snovaGf16MulSpec_setWidth4, snovaGf16MulCore_eq_field]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSnovaGf16Tie
