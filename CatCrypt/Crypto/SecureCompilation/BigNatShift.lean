/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.BigNatCompare
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit

/-!
# Shift operations on the `BigNat` carrier

Left and right shift on the variable-width limb-list carrier `bignumVal`, at the
`Nat` semantics `Nat.shiftLeft x y = x * 2 ^ y` and
`Nat.shiftRight x y = x / 2 ^ y`.

A shift by `y = 64 * q + r` (`r = y % 64 < 64`) is a whole-limb prepend/drop of
`q` limbs composed with a sub-word (`≤ 64`-bit) shift:

* `bignumVal (List.replicate q 0 ++ l) = (2 ^ 64) ^ q * bignumVal l` scales by
  the whole-limb factor `2 ^ (64 q)` (`bignumVal_replicate_append`);
* `bignumVal (l.drop q) = bignumVal l / (2 ^ 64) ^ q` (`bignumVal_drop`, from
  `MultiLimbKernel`) divides by it.

The sub-word part is the emitted `mpn_lshift` / `mpn_rshift` runtime-trip loop.
Its front value specs `lshiftFold_val` / `rshiftFold_val` fold over the memref
`cells`; `lshift_carrier` / `rshift_carrier` read them as carrier-list equations
through the `cells ↔ bignumVal` adapter (`bignumVal_cells_full`), giving the
`≤ 64` cases `bignumVal result = bignumVal a * 2 ^ cnt` and
`bignumVal (result.drop 1) = bignumVal a / 2 ^ cnt`.

## Main results

* `bignumVal_replicate_append` — the whole-limb left-shift scaling law.
* `shl` / `shr` and `shl_val` / `shr_val` — the whole (arbitrary `y : Nat`)
  carrier shifts, with `bignumVal (shl a y) = bignumVal a * 2 ^ y` and
  `bignumVal (shr a y) = bignumVal a / 2 ^ y`.
* `shl_shiftLeft` / `shr_shiftRight` — the same equations read as
  `Nat.shiftLeft` / `Nat.shiftRight` of the abstracted value.
* `lshift_carrier` / `rshift_carrier` — the `≤ 64`-bit front loop result, read
  through the adapter as `* 2 ^ cnt` / `/ 2 ^ cnt` of the carrier list.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatShift

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal bignumVal_drop)
open CatCrypt.Crypto.SecureCompilation.BigNat (ofNat toNat_ofNat)
open CatCrypt.Crypto.SecureCompilation.BigNatCompare (bignumVal_cells_full)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
  (shiftFold lshiftFold_val rshiftFold_val)

/-! ## 1. The whole-limb scaling law -/

/-- Prepending `q` zero limbs scales the value by the whole-limb factor
    `(2 ^ 64) ^ q`. -/
theorem bignumVal_replicate_append : ∀ (q : Nat) (l : List (BitVec 64)),
    bignumVal (List.replicate q 0 ++ l) = (2 ^ 64) ^ q * bignumVal l
  | 0, l => by simp
  | q + 1, l => by
      have ih := bignumVal_replicate_append q l
      simp only [List.replicate_succ, List.cons_append, bignumVal, pow_succ]
      rw [ih]; simp <;> ring

/-! ## 2. Whole (arbitrary `y : Nat`) carrier shifts

`y = 64 * (y / 64) + y % 64`: shift the whole `y / 64` limbs, then the residual
`y % 64 < 64` bits within a limb. The sub-word residual is represented by the
canonical digit expansion of its value; `lshift_carrier` / `rshift_carrier`
certify that the emitted `mpn_lshift` / `mpn_rshift` loop computes a limb list of
that same value. -/

/-- Left shift of the carrier value by `y` bits. -/
def shl (a : List (BitVec 64)) (y : Nat) : List (BitVec 64) :=
  List.replicate (y / 64) 0 ++ ofNat (bignumVal a * 2 ^ (y % 64))

/-- Right shift of the carrier value by `y` bits. -/
def shr (a : List (BitVec 64)) (y : Nat) : List (BitVec 64) :=
  ofNat (bignumVal (a.drop (y / 64)) / 2 ^ (y % 64))

/-- **Left shift.** `bignumVal (shl a y) = bignumVal a * 2 ^ y`. -/
theorem shl_val (a : List (BitVec 64)) (y : Nat) :
    bignumVal (shl a y) = bignumVal a * 2 ^ y := by
  have hy : 64 * (y / 64) + y % 64 = y := Nat.div_add_mod y 64
  unfold shl
  rw [bignumVal_replicate_append, toNat_ofNat, ← pow_mul]
  calc (2 : ℕ) ^ (64 * (y / 64)) * (bignumVal a * 2 ^ (y % 64))
      = bignumVal a * (2 ^ (64 * (y / 64)) * 2 ^ (y % 64)) := by ring
    _ = bignumVal a * 2 ^ (64 * (y / 64) + y % 64) := by rw [← pow_add]
    _ = bignumVal a * 2 ^ y := by rw [hy]

/-- **Right shift.** `bignumVal (shr a y) = bignumVal a / 2 ^ y`. -/
theorem shr_val (a : List (BitVec 64)) (y : Nat) :
    bignumVal (shr a y) = bignumVal a / 2 ^ y := by
  have hy : 64 * (y / 64) + y % 64 = y := Nat.div_add_mod y 64
  unfold shr
  rw [toNat_ofNat, bignumVal_drop, ← pow_mul, Nat.div_div_eq_div_mul, ← pow_add, hy]

/-- **Left shift as `Nat.shiftLeft`.** `bignumVal (shl a y) = bignumVal a <<< y`. -/
theorem shl_shiftLeft (a : List (BitVec 64)) (y : Nat) :
    bignumVal (shl a y) = bignumVal a <<< y := by
  rw [shl_val, Nat.shiftLeft_eq]

/-- **Right shift as `Nat.shiftRight`.** `bignumVal (shr a y) = bignumVal a >>> y`. -/
theorem shr_shiftRight (a : List (BitVec 64)) (y : Nat) :
    bignumVal (shr a y) = bignumVal a >>> y := by
  rw [shr_val, Nat.shiftRight_eq_div_pow]

/-! ## 3. The emitted sub-word (`≤ 64`-bit) shift loop, through the adapter

The `mpn_lshift` / `mpn_rshift` loop folds over the memref `cells`; these read
its result as a carrier-list equation once the operand memref agrees with the
carrier list `a` on its accessed prefix. -/

/-- The emitted `mpn_lshift` loop's `n + 1` result cells, read as the left shift
    of the carrier operand list by `cnt ≤ 64` bits. -/
theorem lshift_carrier {NR NUp : Nat} (up : Fin NUp → BitVec 64) (cnt : Nat)
    (hcnt : cnt ≤ 64) (acc : Fin NR → BitVec 64) (h0 : memGetDyn acc 0 = 0)
    (n : Nat) (hnr : n < NR) (a result : List (BitVec 64))
    (ha : cells up n = a)
    (hres : cells (shiftFold up cnt n acc) (n + 1) = result) :
    bignumVal result = bignumVal a * 2 ^ cnt := by
  rw [← bignumVal_cells_full up a n ha,
    ← bignumVal_cells_full (shiftFold up cnt n acc) result (n + 1) hres]
  exact lshiftFold_val up cnt hcnt acc h0 n hnr

/-- The emitted `mpn_rshift` loop's result limbs (the `n + 1` accumulator cells
    with the shifted-off low word dropped), read as the right shift of the
    carrier operand list by `cnt ≤ 64` bits. -/
theorem rshift_carrier {NR NUp : Nat} (up : Fin NUp → BitVec 64) (cnt : Nat)
    (hcnt : cnt ≤ 64) (acc : Fin NR → BitVec 64) (h0 : memGetDyn acc 0 = 0)
    (n : Nat) (hnr : n < NR) (a : List (BitVec 64)) (ha : cells up n = a) :
    bignumVal ((cells (shiftFold up (64 - cnt) n acc) (n + 1)).drop 1)
      = bignumVal a / 2 ^ cnt := by
  have hV : bignumVal (cells up n) = bignumVal a := bignumVal_cells_full up a n ha
  have key : bignumVal (cells (shiftFold up (64 - cnt) n acc) (n + 1)) * 2 ^ cnt
      = bignumVal a * 2 ^ 64 := by
    rw [← hV]; exact rshiftFold_val up cnt hcnt acc h0 n hnr
  have hpc : 0 < (2 : ℕ) ^ cnt := pow_pos (by norm_num) cnt
  have hpd : 0 < (2 : ℕ) ^ (64 - cnt) := pow_pos (by norm_num) (64 - cnt)
  have hR : bignumVal (cells (shiftFold up (64 - cnt) n acc) (n + 1))
      = bignumVal a * 2 ^ (64 - cnt) := by
    apply Nat.eq_of_mul_eq_mul_right hpc
    rw [key, show (2 : ℕ) ^ 64 = 2 ^ (64 - cnt) * 2 ^ cnt from by
      rw [← pow_add]; congr 1; omega]
    ring
  rw [bignumVal_drop, pow_one, hR,
    show (2 : ℕ) ^ 64 = 2 ^ cnt * 2 ^ (64 - cnt) from by rw [← pow_add]; congr 1; omega,
    Nat.mul_div_mul_right _ _ hpd]

end CatCrypt.Crypto.SecureCompilation.BigNatShift
