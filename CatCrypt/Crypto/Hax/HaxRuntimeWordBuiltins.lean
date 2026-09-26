/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTWordOpsSim

/-!
# The `u64` word table of hax-lean meets the word contracts

`Hax.hax64Builtins` is hax-lean's builtin table of `u64` code: the Rust meaning
of each width-tagged word call on `.int` values, then the array operations on
`.array`.  It gives the call `Add` Rust's `+` on `u64`, undefined when the sum
reaches `2^64`, where `wordOpNat "Add"` is the unbounded sum.  The contract
`WordBuiltins'` (`HaxToLowCTWordOpsSim`) asks the word calls only for results
below `2^64`, the bound every straight-line binding carries in `WBind.Ok`.

## Main results

* `hax64Builtins_wordBuiltins'` — `WordBuiltins' Hax.hax64Builtins`.
* `hax64Builtins_mulHiBuiltins` — `MulHiBuiltins Hax.hax64Builtins`: the steps of
  the unfused multiply-high idiom and the fused `mulhi#64` run in the table.
* `hax64Builtins_narrowBuiltins8`, `hax64Builtins_narrowBuiltins32` —
  `NarrowBuiltins 8` and `NarrowBuiltins 32` of `Hax.hax64Builtins`.
* `hax64Builtins_mulModBuiltins` — `MulModBuiltins Hax.hax64Builtins`: the `u128`
  remainder and the fused `mulmod#64` run in the table.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.WordOpsSim

open _root_.Hax (Value Builtins hax64Builtins hax64WordOps_wrapping_add
  hax64WordOps_wrapping_sub hax64WordOps_wrapping_mul hax64WordOps_mulhi hax64WordOps_bitAnd
  hax64WordOps_bitXor hax64WordOps_shl hax64WordOps_shr hax64WordOps_add hax64WordOps_cast64
  hax64WordOps_cast128 hax64WordOps_mul hax64WordOps_shr128 hax64WordOps_index
  hax64WordOps_array_update widthArrayOps_index_int widthArrayOps_array_update_int
  hax64Builtins_of_none u64BinOp_natCast hax64WordOps_rem hax64WordOps_mulmod hax64WordOps_cast8
  hax64WordOps_cast32 hax64WordOps_wrapping_add8 hax64WordOps_wrapping_sub8
  hax64WordOps_wrapping_mul8 hax64WordOps_bitAnd8 hax64WordOps_bitXor8 hax64WordOps_shl8
  hax64WordOps_shr8 hax64WordOps_wrapping_add32 hax64WordOps_wrapping_sub32
  hax64WordOps_wrapping_mul32 hax64WordOps_bitAnd32 hax64WordOps_bitXor32 hax64WordOps_shl32
  hax64WordOps_shr32)
open CatCrypt.Crypto.Hax (wordOpNames wordOpNat MulHiBuiltins mulHiCallName sexprMulHiU_of_lt
  NarrowOp narrowOpOf narrowCastOf MulModBuiltins mulModCallName)

/-- **hax-lean's `u64` table meets the bounded word contract.** -/
theorem hax64Builtins_wordBuiltins' : WordBuiltins' hax64Builtins where
  word f hf n m r hn hm hr hrL := by
    simp only [wordOpNames, List.mem_cons, List.not_mem_nil, or_false] at hf
    unfold hax64Builtins
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hax64WordOps_wrapping_add, u64BinOp_natCast hn hm]; cases hr; rfl
    · rw [hax64WordOps_wrapping_sub, u64BinOp_natCast hn hm]; cases hr; rfl
    · rw [hax64WordOps_wrapping_mul, u64BinOp_natCast hn hm]; cases hr; rfl
    · rw [hax64WordOps_mulhi, u64BinOp_natCast hn hm]; cases hr
      rw [sexprMulHiU_of_lt hn hm]; rfl
    · rw [hax64WordOps_bitAnd, u64BinOp_natCast hn hm]; cases hr; rfl
    · rw [hax64WordOps_bitXor, u64BinOp_natCast hn hm]; cases hr; rfl
    · rw [hax64WordOps_shr, u64BinOp_natCast hn hm]
      by_cases h : m < 64
      · rw [show wordOpNat "Shr#64" n m = some ((n % 2 ^ 64) >>> m) from if_pos h] at hr
        cases hr; rw [if_pos h]; rfl
      · cases hr.symm.trans (show wordOpNat "Shr#64" n m = none from if_neg h)
    · rw [hax64WordOps_shl, u64BinOp_natCast hn hm]
      by_cases h : m < 64
      · rw [show wordOpNat "Shl#64" n m = some (((n % 2 ^ 64) <<< m) % 2 ^ 64) from
          if_pos h] at hr
        cases hr; rw [if_pos h]; rfl
      · cases hr.symm.trans (show wordOpNat "Shl#64" n m = none from if_neg h)
    · rw [hax64WordOps_add, u64BinOp_natCast hn hm]; cases hr; rw [if_pos hrL]; rfl
  index vs i w h := by
    rw [hax64Builtins_of_none (hax64WordOps_index _ vs), widthArrayOps_index_int,
      if_pos (Int.natCast_nonneg i), Int.toNat_natCast, h]
    rfl
  update vs i v h := by
    rw [hax64Builtins_of_none (hax64WordOps_array_update _ vs v), widthArrayOps_array_update_int,
      Int.toNat_natCast, if_pos (by simp [h])]

/-- **hax-lean's `u64` table runs the multiply-high idiom**: the casts, the
    128-bit product and shift, and the fused `mulhi#64`. -/
theorem hax64Builtins_mulHiBuiltins : MulHiBuiltins hax64Builtins where
  cast128 n hn := by
    unfold hax64Builtins
    rw [hax64WordOps_cast128, if_pos (Int.natCast_nonneg n), Int.toNat_natCast,
      Nat.mod_eq_of_lt (show n < 2 ^ 128 by omega)]
    rfl
  mul n m hn hm := by
    have h := Nat.mul_lt_mul'' hn hm
    rw [← Nat.pow_add] at h
    unfold hax64Builtins
    rw [hax64WordOps_mul, Int.toNat_natCast, Int.toNat_natCast,
      if_pos ⟨Int.natCast_nonneg n, Int.natCast_nonneg m, h⟩]
    rfl
  shr128 n hn := by
    have hn' : (n : Int) < 2 ^ 128 := by exact_mod_cast hn
    unfold hax64Builtins
    rw [hax64WordOps_shr128, if_pos ⟨Int.natCast_nonneg n, hn', by decide, by decide⟩,
      Int.toNat_natCast]
    rfl
  cast64 n hn := by
    unfold hax64Builtins
    rw [hax64WordOps_cast64, if_pos (Int.natCast_nonneg n), Int.toNat_natCast,
      Nat.mod_eq_of_lt hn]
    rfl
  mulhi n m hn hm := by
    unfold hax64Builtins
    rw [mulHiCallName, hax64WordOps_mulhi, u64BinOp_natCast hn hm, sexprMulHiU_of_lt hn hm]
    rfl

/-- **hax-lean's table meets the narrow contract at width `8`.** -/
theorem hax64Builtins_narrowBuiltins8 : NarrowBuiltins 8 hax64Builtins where
  op f op hf n m r hn hm hr := by
    unfold narrowOpOf at hf
    unfold hax64Builtins
    split at hf <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hf
    all_goals obtain ⟨hw, rfl⟩ := hf
    all_goals try (exfalso; omega)
    all_goals
      first
      | rw [hax64WordOps_wrapping_add8] | rw [hax64WordOps_wrapping_sub8]
      | rw [hax64WordOps_wrapping_mul8] | rw [hax64WordOps_bitAnd8] | rw [hax64WordOps_bitXor8]
      | rw [hax64WordOps_shl8] | rw [hax64WordOps_shr8]
      rw [u64BinOp_natCast hn hm]
      simp only [NarrowOp.nat] at hr
      first
      | (cases hr; rfl)
      | (split at hr
         · cases hr; rw [if_pos ‹_›]; rfl
         · cases hr)
  cast f hf n := by
    unfold narrowCastOf at hf
    unfold hax64Builtins
    split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf
    · rw [hax64WordOps_cast8, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]; rfl
    · omega

/-- **hax-lean's table meets the narrow contract at width `32`.** -/
theorem hax64Builtins_narrowBuiltins32 : NarrowBuiltins 32 hax64Builtins where
  op f op hf n m r hn hm hr := by
    unfold narrowOpOf at hf
    unfold hax64Builtins
    split at hf <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hf
    all_goals obtain ⟨hw, rfl⟩ := hf
    all_goals try (exfalso; omega)
    all_goals
      first
      | rw [hax64WordOps_wrapping_add32] | rw [hax64WordOps_wrapping_sub32]
      | rw [hax64WordOps_wrapping_mul32] | rw [hax64WordOps_bitAnd32] | rw [hax64WordOps_bitXor32]
      | rw [hax64WordOps_shl32] | rw [hax64WordOps_shr32]
      rw [u64BinOp_natCast hn hm]
      simp only [NarrowOp.nat] at hr
      first
      | (cases hr; rfl)
      | (split at hr
         · cases hr; rw [if_pos ‹_›]; rfl
         · cases hr)
  cast f hf n := by
    unfold narrowCastOf at hf
    unfold hax64Builtins
    split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf
    · omega
    · rw [hax64WordOps_cast32, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]; rfl

/-- **hax-lean's table runs the modular-multiplication idiom**: the `u128`
    remainder and the fused `mulmod#64`. -/
theorem hax64Builtins_mulModBuiltins : MulModBuiltins hax64Builtins where
  rem n q hn hq0 hq := by
    have hn' : (n : Int) < 2 ^ 128 := by exact_mod_cast hn
    have hq0' : (0 : Int) < q := by exact_mod_cast hq0
    have hq' : (q : Int) < 2 ^ 128 := by exact_mod_cast hq
    unfold hax64Builtins
    rw [hax64WordOps_rem, if_pos ⟨Int.natCast_nonneg n, hn', hq0', hq'⟩, Int.toNat_natCast,
      Int.toNat_natCast]
    rfl
  mulmod n m q hn hm hq0 hq := by
    have hq0' : (0 : Int) < q := by exact_mod_cast hq0
    have hq' : (q : Int) < 2 ^ 64 := by exact_mod_cast hq
    unfold hax64Builtins
    rw [mulModCallName, hax64WordOps_mulmod, if_pos ⟨hq0', hq'⟩, u64BinOp_natCast hn hm,
      Int.toNat_natCast]
    rfl

end CatCrypt.Crypto.Hax.WordOpsSim
