/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigNat
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit

/-!
# Comparison on the `BigNat` carrier, and the `cells ↔ bignumVal` adapter

Two pieces sit here. The first is the reusable bridge between the fixed-width
`Fin N` memref store the runtime-trip fronts fold over and the variable-width
limb list `bignumVal` reads: `cells arr k` (the first `k` cells of a memref)
against `bignumVal` of a carrier list. Later shift/divide/modulo fronts read
their `*Fold_val` specs through the same adapter.

The second lifts `mpn_cmp`'s value-level sign `cmpSign` (from
`MpnCmpFrontEmit`) to the carrier comparisons `beq` and `ble` — `Nat.beq` and
`Nat.ble` on the abstracted values — and reads the emitted comparison loop's
result cell as those carrier operations.

## Main results

* `cells_take`, `cells_eq_take`, `bignumVal_cells_eq_take` — the `cells ↔
  bignumVal` adapter: a partial-length prefix of a memref reads as the `take`
  of its carrier list.
* `segCells_zero`, `bignumVal_segCells_zero` — a zero-based segment is the plain
  cell prefix.
* `cmpSign_eq_one_iff`, `cmpSign_ne_one_iff` — the sign word's contract: `1`
  exactly on `n < m`, so `≠ 1` exactly on `m ≤ n`.
* `beq` / `ble` and `beq_val` / `ble_val` — the carrier comparisons as
  `Nat.beq` / `Nat.ble` of the values, with `beq_eq_true_iff` / `ble_eq_true_iff`.
* `bignumVal_eq_iff_norm_eq`, `beq_eq_true_iff_norm` — carrier equality against
  the `BigNat` canonical form.
* `cmpFold_carrier`, `cmpFold_beq`, `cmpFold_ble` — the emitted comparison
  loop's result cell, read through the adapter as `cmpSign` / `beq` / `ble` of
  the carrier lists.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatCompare

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_succ cells_length)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (segCells segCells_cons)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
  (cmpSign cmpSign_eq_zero_iff cmpFold cmpFold_val_full)
open CatCrypt.Crypto.SecureCompilation.BigNat (norm bignumVal_norm ofNat_norm)

/-! ## 1. The `cells ↔ bignumVal` adapter

`cells arr k` is the first `k` cells of a memref as a little-endian limb list;
`segCells arr lo k` starts the read at cell `lo`. A front `*Fold_val` states its
invariant over `cells`/`segCells` of the accumulator; these lemmas re-read that
as a statement about a carrier `List (BitVec 64)` once the memref agrees with the
carrier list on the accessed prefix. -/

/-- A prefix of a memref cell list is the `take` of a longer prefix. -/
theorem cells_take {N : Nat} (arr : Fin N → BitVec 64) {k m : Nat} (h : k ≤ m) :
    (cells arr m).take k = cells arr k := by
  unfold cells
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-- **The adapter.** If a memref agrees with the carrier list `l` on its first
    `n` cells, then any shorter prefix `cells arr k` (`k ≤ n`) is `l.take k`. -/
theorem cells_eq_take {N : Nat} (arr : Fin N → BitVec 64) (l : List (BitVec 64))
    (n : Nat) (h : cells arr n = l) {k : Nat} (hk : k ≤ n) :
    cells arr k = l.take k := by
  rw [← h, cells_take arr hk]

/-- The adapter at the value level: a partial memref prefix reads as `bignumVal`
    of the carrier `take`. -/
theorem bignumVal_cells_eq_take {N : Nat} (arr : Fin N → BitVec 64)
    (l : List (BitVec 64)) (n : Nat) (h : cells arr n = l) {k : Nat} (hk : k ≤ n) :
    bignumVal (cells arr k) = bignumVal (l.take k) := by
  rw [cells_eq_take arr l n h hk]

/-- The adapter at full length: the whole read prefix is `bignumVal` of the
    carrier list. -/
theorem bignumVal_cells_full {N : Nat} (arr : Fin N → BitVec 64)
    (l : List (BitVec 64)) (n : Nat) (h : cells arr n = l) :
    bignumVal (cells arr n) = bignumVal l := by
  rw [h]

/-- A zero-based segment is the plain cell prefix. -/
theorem segCells_zero {N : Nat} (arr : Fin N → BitVec 64) (k : Nat) :
    segCells arr 0 k = cells arr k := by
  simp [segCells, cells]

/-- Value of a zero-based segment is the value of the cell prefix. -/
theorem bignumVal_segCells_zero {N : Nat} (arr : Fin N → BitVec 64) (k : Nat) :
    bignumVal (segCells arr 0 k) = bignumVal (cells arr k) := by
  rw [segCells_zero]

/-! ## 2. The comparison sign word's contract

`cmpSign m n` is `-1`/`0`/`1` on `<`/`=`/`>`. `cmpSign_eq_zero_iff` is the `=`
case (from `MpnCmpFrontEmit`); here are the `1` and `≤` cases. -/

/-- The sign word is `1` exactly when `n < m`. -/
theorem cmpSign_eq_one_iff (m n : Nat) : cmpSign m n = 1 ↔ n < m := by
  unfold cmpSign
  constructor
  · intro h
    by_cases h1 : m < n
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : n < m
      · exact h2
      · rw [if_neg h2] at h; exact absurd h (by decide)
  · intro h
    rw [if_neg (by omega), if_pos h]

/-- The sign word is not `1` exactly when `m ≤ n`. -/
theorem cmpSign_ne_one_iff (m n : Nat) : cmpSign m n ≠ 1 ↔ m ≤ n := by
  rw [ne_eq, cmpSign_eq_one_iff, not_lt]

/-! ## 3. Carrier comparisons -/

variable (a b : List (BitVec 64))

/-- Carrier equality test: `Nat.beq` of the two abstracted values. -/
def beq : Bool := Nat.beq (bignumVal a) (bignumVal b)

/-- Carrier `≤` test: `Nat.ble` of the two abstracted values. -/
def ble : Bool := Nat.ble (bignumVal a) (bignumVal b)

/-- `beq` is `Nat.beq` of the values. -/
theorem beq_val : beq a b = Nat.beq (bignumVal a) (bignumVal b) := rfl

/-- `ble` is `Nat.ble` of the values. -/
theorem ble_val : ble a b = (bignumVal a).ble (bignumVal b) := rfl

/-- `beq` holds exactly on equal values. -/
theorem beq_eq_true_iff : beq a b = true ↔ bignumVal a = bignumVal b := by
  simp only [beq, Nat.beq_eq]

/-- `ble` holds exactly on `≤` of the values. -/
theorem ble_eq_true_iff : ble a b = true ↔ bignumVal a ≤ bignumVal b := by
  simp only [ble, Nat.ble_eq]

/-- `beq` through the sign word: equal values are the zero sign. -/
theorem beq_iff_cmpSign_zero :
    beq a b = true ↔ cmpSign (bignumVal a) (bignumVal b) = 0 := by
  rw [beq_eq_true_iff, cmpSign_eq_zero_iff]

/-- `ble` through the sign word: `≤` is a non-`1` sign. -/
theorem ble_iff_cmpSign_ne_one :
    ble a b = true ↔ cmpSign (bignumVal a) (bignumVal b) ≠ 1 := by
  rw [ble_eq_true_iff, cmpSign_ne_one_iff]

/-! ## 4. Carrier equality against the canonical form -/

/-- Two carrier lists have the same value exactly when they normalize to the
    same canonical limb list. -/
theorem bignumVal_eq_iff_norm_eq :
    bignumVal a = bignumVal b ↔ norm a = norm b := by
  constructor
  · intro h; rw [← ofNat_norm a, ← ofNat_norm b, h]
  · intro h; rw [← bignumVal_norm a, ← bignumVal_norm b, h]

/-- `beq` in terms of the canonical form. -/
theorem beq_eq_true_iff_norm : beq a b = true ↔ norm a = norm b := by
  rw [beq_eq_true_iff, bignumVal_eq_iff_norm_eq]

/-! ## 5. Reading the emitted comparison loop as a carrier comparison

The `mpn_cmp` runtime-trip loop leaves `cmpSign` of the two operands in cell `0`
of its accumulator (`cmpFold_val_full`). When the two operand memrefs agree with
carrier lists `la`, `lb` on their `top + 1` accessed cells, that result reads as
the carrier `cmpSign` / `beq` / `ble`. -/

/-- The emitted comparison loop's result cell, read as `cmpSign` of the carrier
    operand lists. -/
theorem cmpFold_carrier {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (la lb : List (BitVec 64)) (top : Nat)
    (acc : Fin NR → BitVec 64) (hNR : 0 < NR) (h0 : memGetDyn acc 0 = 0)
    (hla : cells ap (top + 1) = la) (hlb : cells bp (top + 1) = lb) :
    memGetDyn (cmpFold ap bp top (top + 1) acc) 0
      = cmpSign (bignumVal la) (bignumVal lb) := by
  rw [cmpFold_val_full ap bp top acc hNR h0, bignumVal_segCells_zero,
    bignumVal_segCells_zero, hla, hlb]

/-- The emitted result cell is zero exactly when the carrier `beq` holds. -/
theorem cmpFold_beq {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (la lb : List (BitVec 64)) (top : Nat)
    (acc : Fin NR → BitVec 64) (hNR : 0 < NR) (h0 : memGetDyn acc 0 = 0)
    (hla : cells ap (top + 1) = la) (hlb : cells bp (top + 1) = lb) :
    memGetDyn (cmpFold ap bp top (top + 1) acc) 0 = 0 ↔ beq la lb = true := by
  rw [cmpFold_carrier ap bp la lb top acc hNR h0 hla hlb]
  exact (beq_iff_cmpSign_zero la lb).symm

/-- The emitted result cell is not `1` exactly when the carrier `ble` holds. -/
theorem cmpFold_ble {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (la lb : List (BitVec 64)) (top : Nat)
    (acc : Fin NR → BitVec 64) (hNR : 0 < NR) (h0 : memGetDyn acc 0 = 0)
    (hla : cells ap (top + 1) = la) (hlb : cells bp (top + 1) = lb) :
    memGetDyn (cmpFold ap bp top (top + 1) acc) 0 ≠ 1 ↔ ble la lb = true := by
  rw [cmpFold_carrier ap bp la lb top acc hNR h0 hla hlb]
  exact (ble_iff_cmpSign_ne_one la lb).symm

end CatCrypt.Crypto.SecureCompilation.BigNatCompare
