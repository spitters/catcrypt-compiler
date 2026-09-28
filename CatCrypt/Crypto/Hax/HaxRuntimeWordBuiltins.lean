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
* `hax64Builtins_narrowBuiltins` — `NarrowBuiltins w` of `Hax.hax64Builtins` for
  every `w`, with the instances `hax64Builtins_narrowBuiltins8`, `…16`, `…32` and
  `…64`.
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
  hax64WordOps_wrapping_mul8 hax64WordOps_bitAnd8 hax64WordOps_bitOr8 hax64WordOps_bitXor8
  hax64WordOps_shl8 hax64WordOps_shr8 hax64WordOps_wrapping_add32 hax64WordOps_wrapping_sub32
  hax64WordOps_wrapping_mul32 hax64WordOps_bitAnd32 hax64WordOps_bitOr32 hax64WordOps_bitXor32
  hax64WordOps_shl32 hax64WordOps_shr32 hax64WordOps u64BinOp u64UnOp u64UnOp_natCast
  hax64WordOps_cast16 hax64WordOps_castSize hax64WordOps_wrapping_add16
  hax64WordOps_wrapping_sub16 hax64WordOps_wrapping_mul16 hax64WordOps_bitAnd16
  hax64WordOps_bitOr16 hax64WordOps_bitXor16 hax64WordOps_shl16 hax64WordOps_shr16
  hax64WordOps_wrapping_addSize hax64WordOps_wrapping_subSize hax64WordOps_wrapping_mulSize
  hax64WordOps_bitAndSize hax64WordOps_bitOrSize hax64WordOps_bitXorSize hax64WordOps_shlSize
  hax64WordOps_shrSize hax64WordOps_rotr8 hax64WordOps_rotr16 hax64WordOps_rotr32
  hax64WordOps_rotr64 hax64WordOps_rotrSize hax64WordOps_rotl8 hax64WordOps_rotl16
  hax64WordOps_rotl32 hax64WordOps_rotl64 hax64WordOps_rotlSize hax64WordOps_not8
  hax64WordOps_not16 hax64WordOps_not32 hax64WordOps_not64 hax64WordOps_notSize)
open CatCrypt.Crypto.Hax (wordOpNames wordOpNat MulHiBuiltins mulHiCallName sexprMulHiU_of_lt
  NarrowOp narrowOpOf narrowCastOf narrowNotOf MulModBuiltins mulModCallName)

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

/-- A value of `hax64WordOps` is the value of `hax64Builtins`. -/
theorem hax64Builtins_of_some {f : String} {args : List Value} {v : Value}
    (h : hax64WordOps f args = some v) : hax64Builtins f args = some v := by
  unfold hax64Builtins
  rw [h]
  rfl

/-- A two-operand arm `u64BinOp n m g` of `hax64WordOps` on words below `2^64`
    whose operation `g` returns `r` gives `hax64Builtins` the value `r`. -/
theorem hax64Builtins_binArm {f : String} {n m r : Nat} {g : Nat → Nat → Option Nat}
    (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (harm : hax64WordOps f [.int n, .int m] = u64BinOp n m g) (hr : g n m = some r) :
    hax64Builtins f [.int n, .int m] = some (.int r) := by
  apply hax64Builtins_of_some
  rw [harm, u64BinOp_natCast hn hm, hr]
  rfl

/-- A one-operand arm `u64UnOp n g` of `hax64WordOps` on a word below `2^64`
    gives `hax64Builtins` the value `g n`. -/
theorem hax64Builtins_unArm {f : String} {n : Nat} {g : Nat → Nat} (hn : n < 2 ^ 64)
    (harm : hax64WordOps f [.int n] = u64UnOp n g) :
    hax64Builtins f [.int n] = some (.int (g n : Nat)) := by
  apply hax64Builtins_of_some
  rw [harm, u64UnOp_natCast hn]

/-- The `u64` bitwise OR of `hax64WordOps` on two `int` operands. -/
theorem hax64WordOps_bitOr64 {a b : Int} : hax64WordOps "BitOr#64" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64) ||| (y % 2 ^ 64)) := rfl

/-- Each call of `narrowOpOf` runs in `hax64Builtins` as its natural-number
    operation.  The cases follow the arms of `narrowOpOf`. -/
theorem hax64Builtins_narrowOp {w : Nat} (f : String) (op : NarrowOp)
    (hf : narrowOpOf f = some (w, op)) (n m r : Nat) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (hr : op.nat w n m = some r) : hax64Builtins f [.int n, .int m] = some (.int r) := by
  unfold narrowOpOf at hf
  split at hf <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hf
  all_goals obtain ⟨rfl, rfl⟩ := hf
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_add8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_sub8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_mul8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitAnd8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitOr8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitXor8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_shl8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_shr8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_add16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_sub16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_mul16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitAnd16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitOr16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitXor16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_shl16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_shr16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_add32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_sub32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_mul32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitAnd32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitOr32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitXor32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_shl32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_shr32 _ _) hr
  · exact hax64Builtins_binArm hn hm hax64WordOps_bitOr64 hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_addSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_subSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_wrapping_mulSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitAndSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitOrSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_bitXorSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_shlSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_shrSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotr8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotr16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotr32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotr64 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotrSize _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotl8 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotl16 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotl32 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotl64 _ _) hr
  · exact hax64Builtins_binArm hn hm (hax64WordOps_rotlSize _ _) hr

/-- Each cast of `narrowCastOf` runs in `hax64Builtins` as the reduction modulo
    `2^w`. -/
theorem hax64Builtins_narrowCast {w : Nat} (f : String) (hf : narrowCastOf f = some w)
    (n : Nat) : hax64Builtins f [.int n] = some (.int ((n % 2 ^ w : Nat) : Int)) := by
  unfold narrowCastOf at hf
  split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf
  all_goals (subst hf; apply hax64Builtins_of_some)
  · rw [hax64WordOps_cast8, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
  · rw [hax64WordOps_cast16, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
  · rw [hax64WordOps_cast32, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
  · rw [hax64WordOps_cast64, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
  · rw [hax64WordOps_castSize, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]

/-- Each complement of `narrowNotOf` runs in `hax64Builtins` as `2^w - 1` minus
    the word modulo `2^w`. -/
theorem hax64Builtins_narrowNot {w : Nat} (f : String) (hf : narrowNotOf f = some w)
    (n : Nat) (hn : n < 2 ^ 64) :
    hax64Builtins f [.int n] = some (.int ((2 ^ w - 1 - n % 2 ^ w : Nat) : Int)) := by
  unfold narrowNotOf at hf
  split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf
  all_goals subst hf
  · exact hax64Builtins_unArm hn (hax64WordOps_not8 _)
  · exact hax64Builtins_unArm hn (hax64WordOps_not16 _)
  · exact hax64Builtins_unArm hn (hax64WordOps_not32 _)
  · exact hax64Builtins_unArm hn (hax64WordOps_not64 _)
  · exact hax64Builtins_unArm hn (hax64WordOps_notSize _)

/-- **hax-lean's table meets the narrow contract at every width**: each call of
    `narrowOpOf`, `narrowCastOf` and `narrowNotOf` has an arm of `hax64WordOps`
    computing its natural-number operation. -/
theorem hax64Builtins_narrowBuiltins (w : Nat) : NarrowBuiltins w hax64Builtins where
  op := hax64Builtins_narrowOp
  cast := hax64Builtins_narrowCast
  not := hax64Builtins_narrowNot

/-- **hax-lean's table meets the narrow contract at width `8`.** -/
theorem hax64Builtins_narrowBuiltins8 : NarrowBuiltins 8 hax64Builtins :=
  hax64Builtins_narrowBuiltins 8

/-- **hax-lean's table meets the narrow contract at width `16`.** -/
theorem hax64Builtins_narrowBuiltins16 : NarrowBuiltins 16 hax64Builtins :=
  hax64Builtins_narrowBuiltins 16

/-- **hax-lean's table meets the narrow contract at width `32`.** -/
theorem hax64Builtins_narrowBuiltins32 : NarrowBuiltins 32 hax64Builtins :=
  hax64Builtins_narrowBuiltins 32

/-- **hax-lean's table meets the width-tagged contract at width `64`**: the
    `u64` bitwise OR and rotations, the `usize` operations, the casts to `u64`
    and `usize` and the `u64` and `usize` complements. -/
theorem hax64Builtins_narrowBuiltins64 : NarrowBuiltins 64 hax64Builtins :=
  hax64Builtins_narrowBuiltins 64

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
