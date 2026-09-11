/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithGoldenPathField
public import CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo
public import Std.Tactic.BVDecide

@[expose] public section

set_option autoImplicit false

/-!
# Golden-path capstone, at the neutral `arith` level: 2-limb × 1-word multiply

The arith-dialect lift of `FieldMul2x1GoldenPath.field_mul_2x1`. The field kernels
it composes — the widening multiply (`fieldMulLoArithCom` / `fieldMulHiArithCom`,
the `MUL`/`UMULH` pair), the carry-chain low word (`arithAddCom`, the template's
`a + b`), and the carry-out (`fieldAddCarryArithCom`) — are **already** lifted to
`Com arithDialect` in `ArithFieldGoldenPath` / `ArithGoldenPathField`. This file
composes them: a pure value-level reconstruction proof, no new `Com`s.

For a 2-limb operand `a = a0 + a1·2^64` times a single word `b`, the full product
`a · b = r0 + r1·2^64 + r2·2^128` is reconstructed entirely from the lifted
single-word arith kernels:

```
lo0 = a0·b ,  hi0 = mulHiW a0 b          -- fieldMul{Lo,Hi}ArithCom on ⟨b, a0⟩
lo1 = a1·b ,  hi1 = mulHiW a1 b          -- fieldMul{Lo,Hi}ArithCom on ⟨b, a1⟩
r0  = lo0
r1  = lo1 + hi0  with carry-out c1       -- arithAddCom / fieldAddCarryArithCom on ⟨hi0, lo1⟩
r2  = hi1 + c1
```

`r2` needs no further carry (a 2×1-limb product fits in three limbs). The
reconstruction is closed by the single-`MULX` widening law
`MontMulFragmentDemo.mulx_reconstruct` (twice, for `a0·b` and `a1·b`), the limb-1
carry split `ArithFieldGoldenPath.fieldAdd_carry_reconstruct`, and `omega` — the
same proof as the jasmin twin, now over the neutral-`arith` denotes. -/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldMul2x1GoldenPath

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithGoldenPathField
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldGoldenPath

/-- **The 2-limb × 1-word multiply capstone, at the neutral `arith` level.** For
    `a = a0 + a1·2^64` and a single word `b`, the lifted single-word arith
    primitives reconstruct the exact integer product `a · b = r0 + r1·2^64 + r2·2^128`:

    * `r0` is the low word `lo0` of `a0·b` (`fieldMulLoArithCom`);
    * `r1` is the low word of `lo1 + hi0` (`arithAddCom`), where `lo1` is the low word of
      `a1·b` and `hi0` the high word of `a0·b` (`fieldMulLoArithCom`/`fieldMulHiArithCom`);
    * `c1` is the carry-out of that add (`fieldAddCarryArithCom`), threading into limb 2;
    * `r2` is `hi1 + c1`, the high word of `a1·b` plus the propagated carry.

    Every product and low word is an `arith`-kernel denote that rides the proven
    arith→jasmin lowering to AArch64, RISC-V, and x86. Closes by the single-`MULX`
    widening law `mulx_reconstruct` (for `a0·b` and `a1·b`), the limb-1 carry split
    `fieldAdd_carry_reconstruct`, and `omega`. -/
theorem field_mul_2x1_arith (a0 a1 b : BitVec 64) :
    let lo0 := Com.denote fieldMulLoArithCom (.cons b (.cons a0 .nil))
    let hi0 := Com.denote fieldMulHiArithCom (.cons b (.cons a0 .nil))
    let lo1 := Com.denote fieldMulLoArithCom (.cons b (.cons a1 .nil))
    let hi1 := Com.denote fieldMulHiArithCom (.cons b (.cons a1 .nil))
    let r0  := lo0
    let r1  := Com.denote arithAddCom (.cons hi0 (.cons lo1 .nil))
    let c1  := Com.denote fieldAddCarryArithCom (.cons hi0 (.cons lo1 .nil))
    let r2  := Com.denote arithAddCom (.cons c1 (.cons hi1 .nil))
    (a0.toNat + a1.toNat * 2 ^ 64) * b.toNat
      = r0.toNat + r1.toNat * 2 ^ 64 + r2.toNat * 2 ^ 128 := by
  intro lo0 hi0 lo1 hi1 r0 r1 c1 r2
  -- Rewrite the fieldMul denotes to their values via the `_denote` lemmas (matched
  -- syntactically after unfolding the `let`s), avoiding a deep-whnf `show`. The
  -- `arithAddCom` / `fieldAddCarryArithCom` denotes stay symbolic for the carry algebra.
  simp only [r0, r1, r2, c1, lo0, lo1, hi0, hi1, fieldMulLoArithCom_denote,
    fieldMulHiArithCom_denote]
  -- The two single-`MULX` widening laws.
  have e0 : (a0 * b).toNat + (mulHiW a0 b).toNat * 2 ^ 64 = a0.toNat * b.toNat :=
    MontMulFragmentDemo.mulx_reconstruct a0 b
  have e1 : (a1 * b).toNat + (mulHiW a1 b).toNat * 2 ^ 64 = a1.toNat * b.toNat :=
    MontMulFragmentDemo.mulx_reconstruct a1 b
  -- The limb-1 carry split: r1 + c1·2^64 = lo1 + hi0  (arith add low word + carry-out).
  have ec : (Com.denote arithAddCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat
        + (Com.denote fieldAddCarryArithCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat * 2 ^ 64
      = (a1 * b).toNat + (mulHiW a0 b).toNat :=
    fieldAdd_carry_reconstruct (mulHiW a0 b) (a1 * b)
  -- Abbreviations for the carry bit and the high word of a1·b.
  set c1v := (Com.denote fieldAddCarryArithCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat with hc1
  set hi1v := (mulHiW a1 b).toNat with hhi1
  -- The carry is a single bit: from `ec` and the limb bounds, c1v ≤ 1.
  have hlo1 := (a1 * b).isLt
  have hhi0 := (mulHiW a0 b).isLt
  have hc1le : c1v ≤ 1 := by
    have hr1 := (Com.denote arithAddCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).isLt
    omega
  -- hi1 ≤ 2^64 - 2, so hi1 + c1 never wraps: r2 = hi1 + c1 exactly.
  have hhi1le : hi1v ≤ 2 ^ 64 - 2 := MontMulFragmentDemo.mulHiW_le a1 b
  have hr2 : (Com.denote arithAddCom
        (.cons (Com.denote fieldAddCarryArithCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil)))
          (.cons (mulHiW a1 b) .nil))).toNat = hi1v + c1v := by
    rw [arithAddCom_denote, BitVec.toNat_add, ← hc1, ← hhi1]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hr2]
  rw [arithAddCom_denote, BitVec.toNat_add] at ec
  -- `2^128 = 2^64 * 2^64`; everything below is core Nat algebra.
  have e128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
  rw [e128]
  set lo0v := (a0 * b).toNat with hlo0
  set lo1v := (a1 * b).toNat with hlo1v
  set hi0v := (mulHiW a0 b).toNat with hhi0v
  set r1v := (Com.denote arithAddCom (.cons (mulHiW a0 b) (.cons (a1 * b) .nil))).toNat with hr1v
  -- r1v is the low word (lo1+hi0) mod 2^64 (so ec speaks about r1v).
  have hr1eq : r1v = (lo1v + hi0v) % 2 ^ 64 := by
    rw [hr1v, arithAddCom_denote, BitVec.toNat_add, hlo1v, hhi0v]
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

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldMul2x1GoldenPath
