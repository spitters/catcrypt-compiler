/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import Std.Tactic.BVDecide

/-!
# Golden-path capstone: 2-limb × 1-word multiply from the emitted primitives

The multiply analogue of `field_two_limb_add`. For a 2-limb operand
`a = a0 + a1·2^64` times a single word `b`, the full product
`a · b = r0 + r1·2^64 + r2·2^128` is reconstructed from the EMITTED single-word
primitives of `FieldEmitGoldenPath` — the widening multiply
(`fieldMulLoCom` / `fieldMulHiCom`, the `MUL`/`UMULH` pair) and the carry chain
(`fieldAddCom` low word + `fieldAddCarryCom` carry-out). No new `Com`s, no new
compiler machinery: every product and low word comes from a primitive that the
verified compiler emits to AArch64, RISC-V, and x86.

Writing each single-word product `aᵢ · b` as `hiᵢ : loᵢ` (one `MUL`/`UMULH`
pair on the emitted Coms):

```
lo0 = a0·b ,  hi0 = mulHiW a0 b          -- fieldMul{Lo,Hi}Com on ⟨b, a0⟩
lo1 = a1·b ,  hi1 = mulHiW a1 b          -- fieldMul{Lo,Hi}Com on ⟨b, a1⟩
r0  = lo0
r1  = lo1 + hi0  with carry-out c1       -- fieldAddCom / fieldAddCarryCom on ⟨hi0, lo1⟩
r2  = hi1 + c1
```

`r2` needs no further carry (a 2×1-limb product fits in three limbs). The
reconstruction is closed by the single-`MULX` widening law
`MontMulFragmentDemo.mulx_reconstruct` (twice, for `a0·b` and `a1·b`), the
limb-1 carry split `fieldAdd_carry_reconstruct`, and `omega`. -/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldMul2x1GoldenPath

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-- **The 2-limb × 1-word multiply capstone.** For `a = a0 + a1·2^64` and a single
    word `b`, the EMITTED single-word primitives reconstruct the exact integer product
    `a · b = r0 + r1·2^64 + r2·2^128`:

    * `r0` is the low word `lo0` of `a0·b` (`fieldMulLoCom`);
    * `r1` is the low word of `lo1 + hi0` (`fieldAddCom`), where `lo1` is the low word of
      `a1·b` and `hi0` the high word of `a0·b` (`fieldMulLoCom`/`fieldMulHiCom`);
    * `c1` is the carry-out of that add (`fieldAddCarryCom`), threading into limb 2;
    * `r2` is `hi1 + c1`, the high word of `a1·b` plus the propagated carry.

    Every product and low word comes from a primitive the verified compiler emits.
    Closes by the single-`MULX` widening law `mulx_reconstruct` (for `a0·b` and `a1·b`),
    the limb-1 carry split `fieldAdd_carry_reconstruct`, and `omega`. -/
theorem field_mul_2x1 (a0 a1 b : BitVec 64) :
    let lo0 := Com.denote fieldMulLoCom (.cons b (.cons a0 .nil))
    let hi0 := Com.denote fieldMulHiCom (.cons b (.cons a0 .nil))
    let lo1 := Com.denote fieldMulLoCom (.cons b (.cons a1 .nil))
    let hi1 := Com.denote fieldMulHiCom (.cons b (.cons a1 .nil))
    let r0  := lo0
    let r1  := Com.denote fieldAddCom (.cons hi0 (.cons lo1 .nil))
    let c1  := Com.denote fieldAddCarryCom (.cons hi0 (.cons lo1 .nil))
    let r2  := Com.denote fieldAddCom (.cons c1 (.cons hi1 .nil))
    (a0.toNat + a1.toNat * 2 ^ 64) * b.toNat
      = r0.toNat + r1.toNat * 2 ^ 64 + r2.toNat * 2 ^ 128 := by
  intro lo0 hi0 lo1 hi1 r0 r1 c1 r2
  -- Unfold the emitted denotes to their values (a0·b = hi0:lo0, a1·b = hi1:lo1,
  -- r1 = lo1+hi0, c1 = carry, r2 = hi1+c1) — all `rfl` through the `_denote` lemmas.
  show (a0.toNat + a1.toNat * 2 ^ 64) * b.toNat
      = (a0 * b).toNat
        + (Com.denote fieldAddCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat * 2 ^ 64
        + (Com.denote fieldAddCom
            (.cons (Com.denote fieldAddCarryCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil)))
              (.cons (mulHiW a1 b) .nil))).toNat * 2 ^ 128
  -- The two single-`MULX` widening laws.
  have e0 : (a0 * b).toNat + (mulHiW a0 b).toNat * 2 ^ 64 = a0.toNat * b.toNat :=
    MontMulFragmentDemo.mulx_reconstruct a0 b
  have e1 : (a1 * b).toNat + (mulHiW a1 b).toNat * 2 ^ 64 = a1.toNat * b.toNat :=
    MontMulFragmentDemo.mulx_reconstruct a1 b
  -- The limb-1 carry split: r1 + c1·2^64 = lo1 + hi0  (emitted add low word + carry-out).
  have ec : (Com.denote fieldAddCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat
        + (Com.denote fieldAddCarryCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat * 2 ^ 64
      = (a1 * b).toNat + (mulHiW a0 b).toNat :=
    fieldAdd_carry_reconstruct (mulHiW a0 b) (a1 * b)
  -- Abbreviations for the carry bit and the high word of a1·b.
  set c1v := (Com.denote fieldAddCarryCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat with hc1
  set hi1v := (mulHiW a1 b).toNat with hhi1
  -- The carry is a single bit: from `ec` and the limb bounds, c1v ≤ 1.
  have hlo1 := (a1 * b).isLt
  have hhi0 := (mulHiW a0 b).isLt
  have hc1le : c1v ≤ 1 := by
    have hr1 := (Com.denote fieldAddCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).isLt
    omega
  -- hi1 ≤ 2^64 - 2, so hi1 + c1 never wraps: r2 = hi1 + c1 exactly.
  have hhi1le : hi1v ≤ 2 ^ 64 - 2 := MontMulFragmentDemo.mulHiW_le a1 b
  have hr2 : (Com.denote fieldAddCom
        (.cons (Com.denote fieldAddCarryCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil)))
          (.cons (mulHiW a1 b) .nil))).toNat = hi1v + c1v := by
    rw [fieldAddCom_denote, BitVec.toNat_add, ← hc1, ← hhi1]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hr2]
  rw [fieldAddCom_denote, BitVec.toNat_add] at ec
  -- `2^128 = 2^64 * 2^64`; everything below is core Nat algebra.
  have e128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
  rw [e128]
  set lo0v := (a0 * b).toNat with hlo0
  set lo1v := (a1 * b).toNat with hlo1v
  set hi0v := (mulHiW a0 b).toNat with hhi0v
  set r1v := (Com.denote fieldAddCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat with hr1v
  -- r1v is the low word (lo1+hi0) mod 2^64 (so ec speaks about r1v).
  have hr1eq : r1v = (lo1v + hi0v) % 2 ^ 64 := by
    rw [hr1v, fieldAddCom_denote, BitVec.toNat_add, hlo1v, hhi0v]
  rw [hr1eq]
  -- Bridge the products: expand the goal product and substitute e0/e1.
  set a0n := a0.toNat with ha0
  set a1n := a1.toNat with ha1
  set bn := b.toNat with hbn
  -- a1n * 2^64 * bn = (a1n*bn) * 2^64 = (lo1v + hi1v*2^64)*2^64  [by e1]
  have b4 : (a0n + a1n * 2 ^ 64) * bn = a0n * bn + a1n * bn * 2 ^ 64 := by
    rw [Nat.add_mul, Nat.mul_right_comm a1n (2 ^ 64) bn]
  have b5 : a1n * bn * 2 ^ 64 = (lo1v + hi1v * 2 ^ 64) * 2 ^ 64 := by rw [e1]
  have b6 : (lo1v + hi1v * 2 ^ 64) * 2 ^ 64 = lo1v * 2 ^ 64 + hi1v * (2 ^ 64 * 2 ^ 64) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have b7 : (hi1v + c1v) * (2 ^ 64 * 2 ^ 64) = hi1v * (2 ^ 64 * 2 ^ 64) + c1v * (2 ^ 64 * 2 ^ 64) := by
    rw [Nat.add_mul]
  have b8 : c1v * (2 ^ 64 * 2 ^ 64) = c1v * 2 ^ 64 * 2 ^ 64 := by rw [Nat.mul_assoc]
  rw [b4, b5, b6, ← e0, b7, b8]
  -- Remaining is linear over {lo0v, lo1v, hi0v, hi1v*(2^64*2^64), c1v*2^64, the mod term},
  -- closed by the carry split `ec` (which equates the mod + c1v·2^64 to lo1v + hi0v).
  omega

end CatCrypt.Crypto.SecureCompilation.FieldMul2x1GoldenPath
