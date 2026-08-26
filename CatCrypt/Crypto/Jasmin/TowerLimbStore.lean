/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# Limb-level store on tower values

`LowCT.RLimbStore loc idx w` writes the `u64` word `w` into limb `idx` of the
tower value held at `loc`, and `RustExec.limbStore` routes that write through
the `LeafSpec.limbStore` oracle.  This module supplies the oracle's value:
`towerLimbSet` overwrites the eight little-endian bytes at byte offset
`idx * 8` and leaves every other byte alone, and `concreteLimbStore` packages
it as a `LimbStoreSpec`.

The AUCurves model (`SafeRustSimulation.v`) represents a field element as a
`list nat` of limbs and writes with `set_nth`, which returns the list
unchanged when the index is out of range.  Here a tower value is a byte array
(`RustVal t = JArray t.storageBytes`) and the limb at index `i` is the
little-endian `u64` at byte offset `i * 8` (`towerLimb`), so the same write is
a byte-window overwrite, guarded by the eight-byte window fitting inside the
value.  Out of range the value is returned unchanged, so the store needs no
side condition.

`towerLimb_towerLimbSet_self` and `towerLimb_towerLimbSet_ne` are the frame
pair: the written limb reads back, and every other limb is untouched.  The
byte width of a tower value is fixed by its `TowerType`, so the `set_nth`
length property holds by typing.

The upstream definition is specific to `TFp`, and its semantic rule carries a
`loc_dst loc = TFp` side condition.  The byte-window write is stated here for
every `TowerType`: `RLimbStore` is `u64`-granular, so a limb is eight bytes
whatever the slot's type, and a slot narrower than the window (`TU8`, `TU32`,
a short `TBytes`) admits no write at any index.

## Main results

* `towerLimbSet` / `concreteLimbStore` — the byte-window limb write and the
  `LeafSpec` field that uses it.
* `towerLimb_towerLimbSet_self` — the written limb reads back, when the window
  fits inside the slot.
* `towerLimb_towerLimbSet_ne` — every other limb is unchanged.
* `rustValByte_towerLimbSet_inside` / `_outside` — the byte-level frame.
-/

namespace CatCrypt.Crypto.Jasmin.LowCT

/-- Byte `k` (little-endian) of the `u64` word `w`. -/
def limbByte (w : BitVec 64) (k : Nat) : BitVec 8 := (w >>> (k * 8)).truncate 8

/-- Write the `u64` word `w` into limb `i` of the tower value `v`: the eight
    little-endian bytes at offsets `i * 8 .. i * 8 + 7`.  When that window
    does not fit inside the value, `v` is returned unchanged. -/
def towerLimbSet {t : TowerType} (v : RustVal t) (i : Nat) (w : BitVec 64) :
    RustVal t :=
  fun j =>
    if i * 8 + 8 ≤ t.storageBytes ∧ i * 8 ≤ j.val ∧ j.val < i * 8 + 8 then
      limbByte w (j.val - i * 8)
    else v j

/-- Inside the written window, the bytes of `towerLimbSet v i w` are the bytes
    of `w`. -/
theorem rustValByte_towerLimbSet_inside {t : TowerType} (v : RustVal t)
    (i k : Nat) (w : BitVec 64) (hk : k < 8) (hfit : i * 8 + 8 ≤ t.storageBytes) :
    rustValByte (towerLimbSet v i w) (i * 8 + k) = limbByte w k := by
  have hlt : i * 8 + k < t.storageBytes := by omega
  simp only [rustValByte, towerLimbSet, dif_pos hlt]
  rw [if_pos (by omega)]
  congr 1
  omega

/-- Outside the written window, `towerLimbSet` leaves the bytes alone. -/
theorem rustValByte_towerLimbSet_outside {t : TowerType} (v : RustVal t)
    (i m : Nat) (w : BitVec 64) (hm : m < i * 8 ∨ i * 8 + 8 ≤ m) :
    rustValByte (towerLimbSet v i w) m = rustValByte v m := by
  simp only [rustValByte, towerLimbSet]
  split
  · rw [if_neg (by omega)]
  · rfl

/-- The written limb reads back: the AUCurves `nth_set_nth_same`. -/
theorem towerLimb_towerLimbSet_self {t : TowerType} (v : RustVal t) (i : Nat)
    (w : BitVec 64) (hfit : i * 8 + 8 ≤ t.storageBytes) :
    towerLimb (towerLimbSet v i w) i = w.toNat := by
  have key : ∀ k, k < 8 →
      rustValByte (towerLimbSet v i w) (i * 8 + k) = limbByte w k :=
    fun k hk => rustValByte_towerLimbSet_inside v i k w hk hfit
  have hw : w.toNat < 2 ^ 64 := w.isLt
  simp only [towerLimb, key 0 (by omega), key 1 (by omega), key 2 (by omega), key 3 (by omega),
    key 4 (by omega), key 5 (by omega), key 6 (by omega), key 7 (by omega),
    limbByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

/-- Every other limb is unchanged: the AUCurves `nth_set_nth_other`. -/
theorem towerLimb_towerLimbSet_ne {t : TowerType} (v : RustVal t) (i j : Nat)
    (w : BitVec 64) (hne : j ≠ i) :
    towerLimb (towerLimbSet v i w) j = towerLimb v j := by
  have key : ∀ k, k < 8 →
      rustValByte (towerLimbSet v i w) (j * 8 + k) = rustValByte v (j * 8 + k) :=
    fun k hk => rustValByte_towerLimbSet_outside v i (j * 8 + k) w (by omega)
  simp only [towerLimb, key 0 (by omega), key 1 (by omega), key 2 (by omega),
    key 3 (by omega), key 4 (by omega), key 5 (by omega), key 6 (by omega),
    key 7 (by omega)]

/-- The limb-store oracle: `RLimbStore loc idx w` replaces limb `idx` of the
    old value at `loc` with `w`. -/
def concreteLimbStore : LimbStoreSpec :=
  fun _loc oldV idx w => towerLimbSet oldV idx w

/-! ## Round trip on a concrete `TFp` value

`TFp` is 48 bytes, i.e. six `u64` limbs: indices 0–5 fit, index 6 does not. -/

/-- A `TFp` value carrying `7` in limb 2 and zero elsewhere. -/
private def limbStoreFixture : RustVal .TFp := towerLimbSet default 2 7

-- The written limb reads back.
#guard towerLimb (towerLimbSet limbStoreFixture 1 0x0123456789ABCDEF) 1 == 0x0123456789ABCDEF
-- Its neighbours keep their values.
#guard towerLimb (towerLimbSet limbStoreFixture 1 0x0123456789ABCDEF) 2 == 7
#guard towerLimb (towerLimbSet limbStoreFixture 1 0x0123456789ABCDEF) 0 == 0
-- Limb 6 is past the end of a `TFp`, so the store leaves the value alone.
#guard towerLimb (towerLimbSet limbStoreFixture 6 0xFF) 2 == 7
#guard towerLimb (towerLimbSet limbStoreFixture 6 0xFF) 6 == 0

end CatCrypt.Crypto.Jasmin.LowCT
